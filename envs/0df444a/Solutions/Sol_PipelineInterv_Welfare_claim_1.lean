-- Prove2me | solution 1 for PipelineInterv.Welfare.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:53:33.921681+00:00
-- url     : https://prove2.me/submissions/7dcbc8e1-2d39-4c2b-9b95-2219299e795f

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model
import Theorems.Thm_PipelineInterv_Welfare_claim_1_budget_saving
open Matrix

namespace PIWAux
open PipelineInterv.Welfare

theorem filter_ge_succ {K t : ℕ} (ht : t < K) :
    (List.finRange K).filter (fun s : Fin K => t ≤ s.val) =
      ⟨t, ht⟩ :: (List.finRange K).filter (fun s : Fin K => t + 1 ≤ s.val) := by
  apply List.Subset.antisymm_of_pairwise (r := fun a b : Fin K => a < b)
  · exact (List.pairwise_lt_finRange K).filter _
  · refine List.Pairwise.cons ?_ ((List.pairwise_lt_finRange K).filter _)
    intro a ha
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at ha
    exact Fin.lt_def.2 (by simp; omega)
  · intro a ha
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at ha
    simp only [List.mem_cons, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    by_cases h : a.val = t
    · left; exact Fin.ext h
    · right; omega
  · intro a ha
    simp only [List.mem_cons, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at ha
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    rcases ha with h | h
    · subst h; simp
    · omega

theorem filter_lt_succ {K t : ℕ} (ht : t < K) :
    (List.finRange K).filter (fun s : Fin K => s.val < t + 1) =
      (List.finRange K).filter (fun s : Fin K => s.val < t) ++ [⟨t, ht⟩] := by
  apply List.Subset.antisymm_of_pairwise (r := fun a b : Fin K => a < b)
  · exact (List.pairwise_lt_finRange K).filter _
  · rw [List.pairwise_append]
    refine ⟨(List.pairwise_lt_finRange K).filter _, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at ha
    simp only [List.mem_singleton] at hb
    subst hb
    exact Fin.lt_def.2 (by simp; omega)
  · intro a ha
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at ha
    simp only [List.mem_append, List.mem_singleton, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    by_cases h : a.val = t
    · right; exact Fin.ext h
    · left; omega
  · intro a ha
    simp only [List.mem_append, List.mem_singleton, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at ha
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    rcases ha with h | h
    · omega
    · subst h; simp

variable {w K : ℕ}

theorem sufProd_succ (M : Fin K → Matrix (Fin w) (Fin w) ℝ) {t : ℕ} (ht : t < K) :
    sufProd M t = sufProd M (t + 1) * M ⟨t, ht⟩ := by
  unfold sufProd
  rw [filter_ge_succ ht]
  simp [List.reverse_cons, List.map_append, List.prod_append]

theorem prefProd_succ (M : Fin K → Matrix (Fin w) (Fin w) ℝ) {t : ℕ} (ht : t < K) :
    prefProd M (t + 1) = M ⟨t, ht⟩ * prefProd M t := by
  unfold prefProd
  rw [filter_lt_succ ht]
  simp [List.reverse_append]

theorem sufProd_of_ge (M : Fin K → Matrix (Fin w) (Fin w) ℝ) {t : ℕ} (ht : K ≤ t) :
    sufProd M t = 1 := by
  unfold sufProd
  rw [List.filter_eq_nil_iff.2]
  · simp
  · intro a _; simp; omega

theorem prefProd_zero (M : Fin K → Matrix (Fin w) (Fin w) ℝ) : prefProd M 0 = 1 := by
  unfold prefProd
  rw [List.filter_eq_nil_iff.2]
  · simp
  · intro a _; simp

theorem sufProd_congr (M M' : Fin K → Matrix (Fin w) (Fin w) ℝ) (t : ℕ)
    (h : ∀ s : Fin K, t ≤ s.val → M s = M' s) : sufProd M t = sufProd M' t := by
  unfold sufProd
  congr 1
  apply List.map_congr_left
  intro a ha
  simp only [List.mem_reverse, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] at ha
  exact h a ha

theorem prefProd_congr (M M' : Fin K → Matrix (Fin w) (Fin w) ℝ) (t : ℕ)
    (h : ∀ s : Fin K, s.val < t → M s = M' s) : prefProd M t = prefProd M' t := by
  unfold prefProd
  congr 1
  apply List.map_congr_left
  intro a ha
  simp only [List.mem_reverse, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] at ha
  exact h a ha

theorem suf_mul_pref (M : Fin K → Matrix (Fin w) (Fin w) ℝ) :
    ∀ t, t ≤ K → sufProd M t * prefProd M t = sufProd M 0 := by
  intro t
  induction t with
  | zero => intro _; simp [prefProd_zero]
  | succ t ih =>
    intro ht
    rw [← ih (by omega), sufProd_succ M (show t < K by omega), prefProd_succ M (show t < K by omega)]
    simp [Matrix.mul_assoc]

theorem sufProd_mem (M : Fin K → Matrix (Fin w) (Fin w) ℝ) (t : ℕ)
    (h : ∀ s : Fin K, t ≤ s.val → M s ∈ colStochastic ℝ (Fin w)) :
    sufProd M t ∈ colStochastic ℝ (Fin w) := by
  unfold sufProd
  apply Submonoid.list_prod_mem
  intro x hx
  simp only [List.mem_map, List.mem_reverse, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact h a ha

theorem prefProd_mem (M : Fin K → Matrix (Fin w) (Fin w) ℝ) (t : ℕ)
    (h : ∀ s : Fin K, s.val < t → M s ∈ colStochastic ℝ (Fin w)) :
    prefProd M t ∈ colStochastic ℝ (Fin w) := by
  unfold prefProd
  apply Submonoid.list_prod_mem
  intro x hx
  simp only [List.mem_map, List.mem_reverse, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact h a ha

theorem isDist_mulVec {M : Matrix (Fin w) (Fin w) ℝ} (hM : M ∈ colStochastic ℝ (Fin w))
    {D : Fin w → ℝ} (hD : IsDist D) : IsDist (M *ᵥ D) := by
  obtain ⟨hM0, hcol⟩ := mem_colStochastic_iff_sum.1 hM
  refine ⟨fun i => ?_, ?_⟩
  · simp only [mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hM0 i j) (hD.1 j)
  · simp only [mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol, one_mul]
    exact hD.2

theorem supNorm_nonneg (R : Fin w → ℝ) : 0 ≤ supNorm R := by
  rw [supNorm]; exact Real.iSup_nonneg fun i => abs_nonneg (R i)

theorem le_supNorm (R : Fin w → ℝ) (i : Fin w) : |R i| ≤ supNorm R := by
  rw [supNorm]; exact le_ciSup (f := fun i => |R i|) (Finite.bddAbove_range _) i

theorem l1_comm (x y : Fin w → ℝ) : l1 (x - y) = l1 (y - x) := by
  unfold l1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]; exact abs_sub_comm _ _

theorem filter_ge_finset {t : ℕ} (ht : t < K) :
    Finset.univ.filter (fun s : Fin K => t ≤ s.val) =
      insert ⟨t, ht⟩ (Finset.univ.filter (fun s : Fin K => t + 1 ≤ s.val)) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    by_cases h' : a.val = t
    · left; exact Fin.ext h'
    · right; omega
  · rintro (h | h)
    · subst h; simp
    · omega

theorem sum_ge_split (f : Fin K → ℝ) {t : ℕ} (ht : t < K) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin K => t ≤ s.val), f s =
      f ⟨t, ht⟩ + ∑ s ∈ Finset.univ.filter (fun s : Fin K => t + 1 ≤ s.val), f s := by
  rw [filter_ge_finset ht, Finset.sum_insert]
  simp

theorem valueFrom_update (I : Instance w K) (X : Fin K → Matrix (Fin w) (Fin w) ℝ)
    {t : ℕ} (ht : t < K) (Y : Matrix (Fin w) (Fin w) ℝ) (D : Fin w → ℝ) :
    valueFrom I (Function.update X ⟨t, ht⟩ Y) t D =
      I.R ⬝ᵥ ((sufProd X (t + 1) * Y) *ᵥ D) := by
  unfold valueFrom
  rw [sufProd_succ _ ht, Function.update_self]
  congr 3
  apply sufProd_congr
  intro s hs
  rw [Function.update_of_ne]
  intro h; subst h; simp at hs

end PIWAux

open PipelineInterv.Welfare PIWAux in
theorem solution {w K : ℕ} (I : Instance w K) (hI : I.Standing) (B ε : ℝ) (hB : 0 ≤ B)
    (hε : 0 < ε) (M : Fin K → Matrix (Fin w) (Fin w) ℝ) (hM : Feasible I B M) :
    ∃ (n : Fin K → ℕ) (Meps : Fin K → Matrix (Fin w) (Fin w) ℝ),
      ∑ t, (n t : ℝ) * ε ≤ B ∧
      (∀ t, Prog7Feasible I t ((n t : ℝ) * ε) (Meps t)) ∧
      welfare I M - (K : ℝ) * ε * supNorm I.R ≤ welfare I Meps := by
  set ρ := supNorm I.R with hρ
  have hρ0 : 0 ≤ ρ := supNorm_nonneg _
  have hex := fun t => claim_1_budget_saving I hI t (M t) (hM.1 t) (hM.2.1 t) ε hε
  choose Meps hMs hMr hMc hMl using hex
  have hcost0 : ∀ t, 0 ≤ cost (M t) (I.M0 t) := fun t => by
    unfold cost; exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨fun t => ⌊cost (M t) (I.M0 t) / ε⌋₊, Meps, ?_, ?_, ?_⟩
  · refine le_trans (Finset.sum_le_sum fun t _ => ?_) hM.2.2
    have := Nat.floor_le (div_nonneg (hcost0 t) hε.le)
    rw [le_div_iff₀ hε] at this; exact this
  · intro t
    refine ⟨hMs t, hMr t, ?_⟩
    rw [hMc t]
    have h1 := Nat.lt_floor_add_one (cost (M t) (I.M0 t) / ε)
    rw [div_lt_iff₀ hε] at h1
    apply max_le
    · exact mul_nonneg (Nat.cast_nonneg _) hε.le
    · linarith
  · -- hybrid argument
    let H : ℕ → Fin K → Matrix (Fin w) (Fin w) ℝ := fun j s => if s.val < j then Meps s else M s
    have hHmem : ∀ j s, H j s ∈ colStochastic ℝ (Fin w) := fun j s => by
      simp only [H]; split_ifs; exacts [hMs s, hM.1 s]
    have hsplit : ∀ (X : Fin K → Matrix (Fin w) (Fin w) ℝ) (j : ℕ) (hj : j < K),
        welfare I X = (I.R ᵥ* sufProd X (j + 1)) ⬝ᵥ (X ⟨j, hj⟩ *ᵥ (prefProd X j *ᵥ I.D1)) := by
      intro X j hj
      unfold welfare valueFrom
      rw [← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← suf_mul_pref X j hj.le,
        sufProd_succ X hj]
    have hstep : ∀ j (hj : j < K), welfare I (H j) - ε * ρ ≤ welfare I (H (j + 1)) := by
      intro j hj
      rw [hsplit (H j) j hj, hsplit (H (j + 1)) j hj]
      have hsuf : sufProd (H (j + 1)) (j + 1) = sufProd (H j) (j + 1) := by
        apply sufProd_congr; intro s hs; simp only [H]
        rw [if_neg (by omega), if_neg (by omega)]
      have hpref : prefProd (H (j + 1)) j = prefProd (H j) j := by
        apply prefProd_congr; intro s hs; simp only [H]
        rw [if_pos (by omega), if_pos (by omega)]
      have hj1 : H j ⟨j, hj⟩ = M ⟨j, hj⟩ := by simp [H]
      have hj2 : H (j + 1) ⟨j, hj⟩ = Meps ⟨j, hj⟩ := by simp [H]
      rw [hsuf, hpref, hj1, hj2]
      set A := sufProd (H j) (j + 1)
      have hA : A ∈ colStochastic ℝ (Fin w) := sufProd_mem _ _ fun s _ => hHmem j s
      obtain ⟨hA0, hAcol⟩ := mem_colStochastic_iff_sum.1 hA
      have hr : ∀ v, 0 ≤ (I.R ᵥ* A) v ∧ (I.R ᵥ* A) v ≤ ρ := by
        intro v
        simp only [vecMul, dotProduct]
        constructor
        · exact Finset.sum_nonneg fun i _ => mul_nonneg (hI.2.2 i) (hA0 i v)
        · calc ∑ i, I.R i * A i v ≤ ∑ i, ρ * A i v := Finset.sum_le_sum fun i _ =>
                mul_le_mul_of_nonneg_right
                  (le_trans (le_abs_self _) (le_supNorm I.R i)) (hA0 i v)
            _ = ρ := by rw [← Finset.mul_sum, hAcol, mul_one]
      have hD : IsDist (prefProd (H j) j *ᵥ I.D1) :=
        isDist_mulVec (prefProd_mem _ _ fun s _ => hHmem j s) hI.2.1
      have := hMl ⟨j, hj⟩ (I.R ᵥ* A) _ ρ hr hD
      linarith
    have hall : ∀ j, j ≤ K → welfare I M - (j : ℝ) * ε * ρ ≤ welfare I (H j) := by
      intro j
      induction j with
      | zero =>
        intro _
        have : H 0 = M := by funext s; simp [H]
        rw [this]; simp
      | succ j ih =>
        intro hj
        have h1 := ih (by omega)
        have h2 := hstep j (by omega)
        push_cast
        linarith
    have hK : H K = Meps := by funext s; simp [H, s.isLt]
    have := hall K le_rfl
    rw [hK] at this
    exact this
