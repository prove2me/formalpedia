-- Prove2me | solution 1 for PipelineInterv.Welfare.theorem_1_invariant
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:52:12.611219+00:00
-- url     : https://prove2.me/submissions/f5247501-a79a-42b9-b6eb-4553ff78b581

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model
import Theorems.Thm_PipelineInterv_Welfare_corollary_2
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
theorem solution {w K : ℕ} (I : Instance w K) (hI : I.Standing) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) (S : Finset (Fin w → ℝ)) (hS : IsEpsNet ε S) (tab : Table w K)
    (hrun : IsAlg1Run I B ε S tab) (n : Fin K → ℕ) (Meps : Fin K → Matrix (Fin w) (Fin w) ℝ)
    (hn : ∑ s, (n s : ℝ) * ε ≤ B) (hfeas : ∀ s, Prog7Feasible I s ((n s : ℝ) * ε) (Meps s)) :
    ∀ t < K, ∀ b ∈ budgetGrid ε B,
      ∑ s ∈ Finset.univ.filter (fun s : Fin K => t ≤ s.val), (n s : ℝ) * ε ≤ b →
      ∀ D ∈ startSet I S t, l1 (D - prefProd Meps t *ᵥ I.D1) ≤ ε →
        welfare I Meps - 2 * ((K - t : ℕ) : ℝ) * ε * supNorm I.R ≤
          valueFrom I (tab t b D) t D := by
  set ρ := supNorm I.R with hρ
  have hρ0 : 0 ≤ ρ := supNorm_nonneg _
  have hMs : ∀ s, Meps s ∈ colStochastic ℝ (Fin w) := fun s => (hfeas s).1
  have hDist : ∀ t, IsDist (prefProd Meps t *ᵥ I.D1) := fun t =>
    isDist_mulVec (prefProd_mem _ _ fun s _ => hMs s) hI.2.1
  -- welfare seen from layer t
  have hW : ∀ t, t ≤ K → welfare I Meps = I.R ⬝ᵥ (sufProd Meps t *ᵥ (prefProd Meps t *ᵥ I.D1)) := by
    intro t ht
    rw [mulVec_mulVec, suf_mul_pref Meps t ht]; rfl
  -- stochasticity of the table entries
  have hTS : ∀ m t, t + m = K → ∀ b ∈ budgetGrid ε B, ∀ D ∈ startSet I S t,
      ∀ s : Fin K, t ≤ s.val → tab t b D s ∈ colStochastic ℝ (Fin w) := by
    intro m
    induction m with
    | zero => intro t ht b _ D _ s hs; omega
    | succ m ih =>
      intro t ht b hb D hD s hs
      obtain ⟨b', hb', _, D', hD', Mt, hMt, heq, _⟩ := hrun.2 t (by omega) b hb D hD
      rw [heq]
      by_cases hst : s = ⟨t, by omega⟩
      · simp only [hst, Function.update_self]; exact hMt.1
      · rw [Function.update_of_ne hst]
        have hs' : t + 1 ≤ s.val := by
          by_contra h; apply hst; ext; simp; omega
        refine ih (t + 1) (by omega) b' hb' D' ?_ s hs'
        simp [startSet, hD']
  -- one step of the dynamic program
  have step : ∀ t (ht : t < K), ∀ b ∈ budgetGrid ε B,
      ∑ s ∈ Finset.univ.filter (fun s : Fin K => t ≤ s.val), (n s : ℝ) * ε ≤ b →
      ∀ D ∈ startSet I S t, l1 (D - prefProd Meps t *ᵥ I.D1) ≤ ε →
      ∃ b' ∈ budgetGrid ε B,
        ∑ s ∈ Finset.univ.filter (fun s : Fin K => t + 1 ≤ s.val), (n s : ℝ) * ε ≤ b' ∧
        ∀ D'' ∈ S, I.R ⬝ᵥ (sufProd (tab (t + 1) b' D'') (t + 1) *ᵥ
            (prefProd Meps (t + 1) *ᵥ I.D1)) - ρ * ε ≤ valueFrom I (tab t b D) t D := by
    intro t ht b hb hsum D hD hDD
    set N : ℕ := ∑ s ∈ Finset.univ.filter (fun s : Fin K => t + 1 ≤ s.val), n s with hN
    have hNsum : (N : ℝ) * ε =
        ∑ s ∈ Finset.univ.filter (fun s : Fin K => t + 1 ≤ s.val), (n s : ℝ) * ε := by
      rw [hN]; push_cast; rw [Finset.sum_mul]
    have hsplit := sum_ge_split (fun s : Fin K => (n s : ℝ) * ε) ht
    have hNB : (N : ℝ) * ε ≤ B := by
      rw [hNsum]
      refine le_trans ?_ hn
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun s _ _ => mul_nonneg (Nat.cast_nonneg _) hε.le)
    have hNle : N ≤ ⌊B / ε⌋₊ := by
      apply Nat.le_floor
      rw [le_div_iff₀ hε]; exact hNB
    have hb'grid : (N : ℝ) * ε ∈ budgetGrid ε B := by
      unfold budgetGrid
      exact Finset.mem_image.2 ⟨N, Finset.mem_range.2 (by omega), rfl⟩
    have hnt0 : 0 ≤ (n ⟨t, ht⟩ : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε.le
    have hb'b : (N : ℝ) * ε ≤ b := by linarith
    have hfeas' : Prog7Feasible I ⟨t, ht⟩ (b - (N : ℝ) * ε) (Meps ⟨t, ht⟩) := by
      refine ⟨(hfeas _).1, (hfeas _).2.1, ?_⟩
      have := (hfeas ⟨t, ht⟩).2.2
      linarith
    refine ⟨(N : ℝ) * ε, hb'grid, hNsum.ge, ?_⟩
    intro D'' hD''
    obtain ⟨_, _, _, _, _, _, _, _, hopt⟩ := hrun.2 t ht b hb D hD
    have h1 := hopt _ hb'grid hb'b D'' hD'' _ hfeas'
    rw [valueFrom_update] at h1
    set A := sufProd (tab (t + 1) ((N : ℝ) * ε) D'') (t + 1) with hA
    have hAmem : A ∈ colStochastic ℝ (Fin w) := by
      apply sufProd_mem
      intro s hs
      refine hTS (K - (t + 1)) (t + 1) (by omega) _ hb'grid D'' ?_ s hs
      simp [startSet, hD'']
    have hDdist : IsDist D := by
      unfold startSet at hD
      split_ifs at hD
      · rw [Finset.mem_singleton] at hD; rw [hD]; exact hI.2.1
      · exact hS.1 D hD
    have h2 := corollary_2 I.R D (prefProd Meps t *ᵥ I.D1) hDdist (hDist t) ε hDD
      (A * Meps ⟨t, ht⟩) (Submonoid.mul_mem _ hAmem (hMs _))
    rw [prefProd_succ Meps ht, ← mulVec_mulVec]
    rw [← mulVec_mulVec] at h2
    rw [← hρ] at h2
    linarith
  -- strengthened invariant
  have key : ∀ m t, t + m + 1 = K → ∀ b ∈ budgetGrid ε B,
      ∑ s ∈ Finset.univ.filter (fun s : Fin K => t ≤ s.val), (n s : ℝ) * ε ≤ b →
      ∀ D ∈ startSet I S t, l1 (D - prefProd Meps t *ᵥ I.D1) ≤ ε →
        welfare I Meps - (2 * (m : ℝ) + 1) * ε * ρ ≤ valueFrom I (tab t b D) t D := by
    intro m
    induction m with
    | zero =>
      intro t htK b hb hsum D hD hDD
      obtain ⟨b', hb', _, hfin⟩ := step t (by omega) b hb hsum D hD hDD
      obtain ⟨D'', hD''S, _⟩ := hS.2 _ (hDist (t + 1))
      have h := hfin D'' hD''S
      rw [sufProd_of_ge _ (show K ≤ t + 1 by omega), one_mulVec, ← one_mulVec
        (prefProd Meps (t + 1) *ᵥ I.D1), ← sufProd_of_ge Meps (show K ≤ t + 1 by omega),
        ← hW (t + 1) (by omega)] at h
      push_cast
      linarith
    | succ m ih =>
      intro t htK b hb hsum D hD hDD
      obtain ⟨b', hb', hsum', hfin⟩ := step t (by omega) b hb hsum D hD hDD
      obtain ⟨D'', hD''S, hD''⟩ := hS.2 _ (hDist (t + 1))
      have h := hfin D'' hD''S
      have hAmem : sufProd (tab (t + 1) b' D'') (t + 1) ∈ colStochastic ℝ (Fin w) := by
        apply sufProd_mem
        intro s hs
        refine hTS (K - (t + 1)) (t + 1) (by omega) _ hb' D'' ?_ s hs
        simp [startSet, hD''S]
      have h2 := corollary_2 I.R (prefProd Meps (t + 1) *ᵥ I.D1) D'' (hDist (t + 1))
        (hS.1 D'' hD''S) ε hD'' _ hAmem
      have h3 := ih (t + 1) (by omega) b' hb' hsum' D'' (by simp [startSet, hD''S])
        (by rw [l1_comm]; exact hD'')
      unfold valueFrom at h3
      rw [← hρ] at h2
      push_cast at h3 ⊢
      linarith
  intro t ht b hb hsum D hD hDD
  have := key (K - t - 1) t (by omega) b hb hsum D hD hDD
  have hcast : ((K - t : ℕ) : ℝ) = ((K - t - 1 : ℕ) : ℝ) + 1 := by
    rw [show K - t = (K - t - 1) + 1 by omega]; push_cast; ring
  rw [hcast]
  nlinarith [mul_nonneg hε.le hρ0]
