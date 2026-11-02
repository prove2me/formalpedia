-- Prove2me | solution 1 for PipelineInterv.Welfare.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:57:12.799517+00:00
-- url     : https://prove2.me/submissions/db5b7285-71df-416d-a087-f27255f836cf

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model
import Theorems.Thm_PipelineInterv_Welfare_claim_1
import Theorems.Thm_PipelineInterv_Welfare_theorem_1_invariant
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

namespace PIWAux
open PipelineInterv.Welfare
variable {w K : ℕ}

theorem prog7_isCompact (I : Instance w K) (t : Fin K) (c : ℝ) :
    IsCompact {M : Matrix (Fin w) (Fin w) ℝ | Prog7Feasible I t c M} := by
  have hcont : ∀ i j, Continuous fun M : Matrix (Fin w) (Fin w) ℝ => M i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun _ : Fin w => isCompact_univ_pi (fun _ : Fin w => isCompact_Icc
      (a := (0 : ℝ)) (b := 1))))
  · have h1 : IsClosed {M : Matrix (Fin w) (Fin w) ℝ | ∀ i j, 0 ≤ M i j} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le continuous_const (hcont i j)
    have h2 : IsClosed {M : Matrix (Fin w) (Fin w) ℝ | ∀ j, ∑ i, M i j = 1} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun j =>
        isClosed_eq (continuous_finset_sum _ fun i _ => hcont i j) continuous_const
    have h3 : IsClosed {M : Matrix (Fin w) (Fin w) ℝ | Respects I t M} := by
      unfold Respects
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      by_cases h : (i, j) ∈ I.mal t
      · simp [h]
      · exact isClosed_iInter fun _ => isClosed_eq (hcont i j) continuous_const
    have h4 : IsClosed {M : Matrix (Fin w) (Fin w) ℝ | cost M (I.M0 t) ≤ c} := by
      unfold cost
      exact isClosed_le (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
        ((hcont i j).sub continuous_const).abs) continuous_const
    have : {M : Matrix (Fin w) (Fin w) ℝ | Prog7Feasible I t c M} =
        (({M | ∀ i j, 0 ≤ M i j} ∩ {M | ∀ j, ∑ i, M i j = 1}) ∩
          {M | Respects I t M}) ∩ {M | cost M (I.M0 t) ≤ c} := by
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Prog7Feasible, mem_colStochastic_iff_sum]
      tauto
    rw [this]
    exact ((h1.inter h2).inter h3).inter h4
  · intro M hM
    obtain ⟨h0, hcol⟩ := mem_colStochastic_iff_sum.1 hM.1
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    intro i j
    refine ⟨h0 i j, ?_⟩
    rw [← hcol j]
    exact Finset.single_le_sum (f := fun i => M i j) (fun k _ => h0 k j) (Finset.mem_univ i)

theorem M0_prog7 (I : Instance w K) (hI : I.Standing) (t : Fin K) {c : ℝ} (hc : 0 ≤ c) :
    Prog7Feasible I t c (I.M0 t) := by
  refine ⟨hI.1 t, fun _ _ _ => rfl, ?_⟩
  unfold cost; simpa using hc

theorem exists_prog7_max (I : Instance w K) (hI : I.Standing) (t : Fin K) {c : ℝ} (hc : 0 ≤ c)
    (A : Matrix (Fin w) (Fin w) ℝ) (D : Fin w → ℝ) :
    ∃ Mo, Prog7Feasible I t c Mo ∧ ∀ M, Prog7Feasible I t c M →
      I.R ⬝ᵥ ((A * M) *ᵥ D) ≤ I.R ⬝ᵥ ((A * Mo) *ᵥ D) := by
  obtain ⟨Mo, hMo, hmax⟩ := (prog7_isCompact I t c).exists_isMaxOn ⟨I.M0 t, M0_prog7 I hI t hc⟩
    (f := fun M => I.R ⬝ᵥ ((A * M) *ᵥ D)) (by fun_prop)
  exact ⟨Mo, hMo, fun M hM => hmax hM⟩

end PIWAux

namespace PIWAux
open PipelineInterv.Welfare
variable {w K : ℕ}

/-- The maximization property of one cell of Algorithm 1, relative to a next-layer table `X`. -/
def CellOK (I : Instance w K) (B ε : ℝ) (S : Finset (Fin w → ℝ))
    (X : ℝ → (Fin w → ℝ) → (Fin K → Matrix (Fin w) (Fin w) ℝ)) (t : ℕ) (ht : t < K) (b : ℝ)
    (D : Fin w → ℝ) (Y : Fin K → Matrix (Fin w) (Fin w) ℝ) : Prop :=
  ∃ b' ∈ budgetGrid ε B, b' ≤ b ∧ ∃ D' ∈ S, ∃ Mt, Prog7Feasible I ⟨t, ht⟩ (b - b') Mt ∧
    Y = Function.update (X b' D') ⟨t, ht⟩ Mt ∧
    ∀ b'' ∈ budgetGrid ε B, b'' ≤ b → ∀ D'' ∈ S, ∀ M'', Prog7Feasible I ⟨t, ht⟩ (b - b'') M'' →
      valueFrom I (Function.update (X b'' D'') ⟨t, ht⟩ M'') t D ≤ valueFrom I Y t D

open Classical in
noncomputable def algStep (I : Instance w K) (B ε : ℝ) (S : Finset (Fin w → ℝ))
    (X : ℝ → (Fin w → ℝ) → (Fin K → Matrix (Fin w) (Fin w) ℝ)) (t : ℕ) (b : ℝ)
    (D : Fin w → ℝ) : Fin K → Matrix (Fin w) (Fin w) ℝ :=
  if ht : t < K then
    (if h : ∃ Y, CellOK I B ε S X t ht b D Y then h.choose else I.M0)
  else I.M0

noncomputable def algG (I : Instance w K) (B ε : ℝ) (S : Finset (Fin w → ℝ)) :
    ℕ → ℝ → (Fin w → ℝ) → (Fin K → Matrix (Fin w) (Fin w) ℝ)
  | 0 => fun _ _ => I.M0
  | m + 1 => fun b D => algStep I B ε S (algG I B ε S m) (K - (m + 1)) b D

theorem cellOK_exists (I : Instance w K) (hI : I.Standing) (B ε : ℝ) (S : Finset (Fin w → ℝ))
    (hS : S.Nonempty) (X : ℝ → (Fin w → ℝ) → (Fin K → Matrix (Fin w) (Fin w) ℝ)) (t : ℕ)
    (ht : t < K) (b : ℝ) (hb : b ∈ budgetGrid ε B) (D : Fin w → ℝ) :
    ∃ Y, CellOK I B ε S X t ht b D Y := by
  have hex : ∀ p : ℝ × (Fin w → ℝ), ∃ Mo, 0 ≤ b - p.1 → (Prog7Feasible I ⟨t, ht⟩ (b - p.1) Mo ∧
      ∀ M, Prog7Feasible I ⟨t, ht⟩ (b - p.1) M →
        I.R ⬝ᵥ ((sufProd (X p.1 p.2) (t + 1) * M) *ᵥ D) ≤
          I.R ⬝ᵥ ((sufProd (X p.1 p.2) (t + 1) * Mo) *ᵥ D)) := by
    intro p
    by_cases hp : 0 ≤ b - p.1
    · obtain ⟨Mo, h1, h2⟩ := exists_prog7_max I hI ⟨t, ht⟩ hp (sufProd (X p.1 p.2) (t + 1)) D
      exact ⟨Mo, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose Mo hMo using hex
  set P := ((budgetGrid ε B).filter (· ≤ b)) ×ˢ S with hP
  have hPne : P.Nonempty := by
    obtain ⟨D0, hD0⟩ := hS
    exact ⟨(b, D0), Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hb, le_rfl⟩, hD0⟩⟩
  obtain ⟨p, hpP, hpmax⟩ := Finset.exists_max_image P
    (fun p => I.R ⬝ᵥ ((sufProd (X p.1 p.2) (t + 1) * Mo p) *ᵥ D)) hPne
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hpP
  obtain ⟨hp1g, hp1b⟩ := Finset.mem_filter.1 hp1
  refine ⟨Function.update (X p.1 p.2) ⟨t, ht⟩ (Mo p), p.1, hp1g, hp1b, p.2, hp2, Mo p,
    (hMo p (by linarith)).1, rfl, ?_⟩
  intro b'' hb'' hb''b D'' hD'' M'' hM''
  rw [valueFrom_update, valueFrom_update]
  have hq : (b'', D'') ∈ P := Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hb'', hb''b⟩, hD''⟩
  have h1 := (hMo (b'', D'') (by simp; linarith)).2 M'' hM''
  have h2 := hpmax (b'', D'') hq
  exact le_trans h1 h2

theorem budgetGrid_nonneg {ε B : ℝ} (hε : 0 < ε) {b : ℝ} (hb : b ∈ budgetGrid ε B) : 0 ≤ b := by
  unfold budgetGrid at hb
  obtain ⟨n, _, rfl⟩ := Finset.mem_image.1 hb
  exact mul_nonneg (Nat.cast_nonneg _) hε.le

theorem algRun (I : Instance w K) (hI : I.Standing) (B ε : ℝ) (S : Finset (Fin w → ℝ))
    (hS : S.Nonempty) : IsAlg1Run I B ε S (fun t => algG I B ε S (K - t)) := by
  refine ⟨fun b _ D => by simp [algG], ?_⟩
  intro t ht b hb D _
  have hKt : K - t = (K - (t + 1)) + 1 := by omega
  have hex := cellOK_exists I hI B ε S hS (algG I B ε S (K - (t + 1))) t ht b hb D
  have heq : algG I B ε S (K - t) b D = hex.choose := by
    rw [hKt, algG]
    simp only
    rw [show K - (K - (t + 1) + 1) = t by omega]
    unfold algStep
    rw [dif_pos ht, dif_pos hex]
  have := hex.choose_spec
  rw [← heq] at this
  exact this

end PIWAux

open PipelineInterv.Welfare PIWAux in
theorem solution {w K : ℕ} (I : Instance w K) (hI : I.Standing) (B ε : ℝ) (hB : 0 ≤ B)
    (hε : 0 < ε) (S : Finset (Fin w → ℝ)) (hS : IsEpsNet ε S) :
    (∃ tab : Table w K, IsAlg1Run I B ε S tab) ∧
    (∀ tab : Table w K, IsAlg1Run I B ε S tab →
      Feasible I B (alg1Output I B ε tab) ∧
      ∀ M, Feasible I B M →
        welfare I M - 3 * (K : ℝ) * ε * supNorm I.R ≤ welfare I (alg1Output I B ε tab)) ∧
    alg1LPCount I B ε S ≤ K * (⌊B / ε⌋₊ + 1) ^ 2 * S.card ^ 2 := by
  have hSne : S.Nonempty := by
    obtain ⟨D', hD', _⟩ := hS.2 I.D1 hI.2.1
    exact ⟨D', hD'⟩
  have hBeps : Beps ε B ∈ budgetGrid ε B := by
    unfold budgetGrid Beps
    exact Finset.mem_image.2 ⟨⌊B / ε⌋₊, Finset.mem_range.2 (by omega), rfl⟩
  have hBepsB : Beps ε B ≤ B := by
    unfold Beps
    have := Nat.floor_le (div_nonneg hB hε.le)
    rw [le_div_iff₀ hε] at this; exact this
  refine ⟨⟨_, algRun I hI B ε S hSne⟩, ?_, ?_⟩
  · intro tab hrun
    refine ⟨?_, ?_⟩
    · -- feasibility of the output, by downward induction
      have hF : ∀ m t, t + m = K → ∀ b ∈ budgetGrid ε B, ∀ D ∈ startSet I S t,
          (∀ s, tab t b D s ∈ colStochastic ℝ (Fin w) ∧ Respects I s (tab t b D s)) ∧
          ∑ s ∈ Finset.univ.filter (fun s : Fin K => t ≤ s.val), cost (tab t b D s) (I.M0 s) ≤ b := by
        intro m
        induction m with
        | zero =>
          intro t ht b hb D _
          rw [show t = K by omega, hrun.1 b hb D]
          refine ⟨fun s => ⟨hI.1 s, fun _ _ _ => rfl⟩, ?_⟩
          rw [Finset.filter_false_of_mem (fun s _ => by omega)]
          simpa using budgetGrid_nonneg hε hb
        | succ m ih =>
          intro t ht b hb D hD
          have htK : t < K := by omega
          obtain ⟨b', hb', hb'b, D', hD', Mt, hMt, heq, _⟩ := hrun.2 t htK b hb D hD
          have hD't : D' ∈ startSet I S (t + 1) := by simp [startSet, hD']
          obtain ⟨ihA, ihB⟩ := ih (t + 1) (by omega) b' hb' D' hD't
          rw [heq]
          refine ⟨fun s => ?_, ?_⟩
          · by_cases hst : s = ⟨t, htK⟩
            · simp only [hst, Function.update_self]; exact ⟨hMt.1, hMt.2.1⟩
            · rw [Function.update_of_ne hst]; exact ihA s
          · rw [sum_ge_split (fun s => cost (Function.update (tab (t + 1) b' D') ⟨t, htK⟩ Mt s)
              (I.M0 s)) htK]
            simp only [Function.update_self]
            have hrest : ∑ s ∈ Finset.univ.filter (fun s : Fin K => t + 1 ≤ s.val),
                cost (Function.update (tab (t + 1) b' D') ⟨t, htK⟩ Mt s) (I.M0 s) =
                ∑ s ∈ Finset.univ.filter (fun s : Fin K => t + 1 ≤ s.val),
                cost (tab (t + 1) b' D' s) (I.M0 s) := by
              refine Finset.sum_congr rfl fun s hs => ?_
              rw [Function.update_of_ne]
              intro h; subst h; simp at hs
            rw [hrest]
            have := hMt.2.2
            linarith
      obtain ⟨hA, hBud⟩ := hF K 0 (by omega) (Beps ε B) hBeps I.D1 (by simp [startSet])
      refine ⟨fun s => (hA s).1, fun s => (hA s).2, ?_⟩
      rw [Finset.filter_true_of_mem (fun s _ => Nat.zero_le _)] at hBud
      exact le_trans hBud hBepsB
    · intro M hM
      obtain ⟨n, Meps, hn, hfeas, hW⟩ := claim_1 I hI B ε hB hε M hM
      have hρ0 : 0 ≤ supNorm I.R := supNorm_nonneg _
      rcases Nat.eq_zero_or_pos K with hK | hK
      · have hconst : ∀ X : Fin K → Matrix (Fin w) (Fin w) ℝ, welfare I X = I.R ⬝ᵥ I.D1 := by
          intro X; unfold welfare valueFrom; rw [sufProd_of_ge X (by omega), one_mulVec]
        rw [hconst, hconst]; subst hK; simp
      · have hsum : ∑ s ∈ Finset.univ.filter (fun s : Fin K => 0 ≤ s.val), (n s : ℝ) * ε ≤
            Beps ε B := by
          rw [Finset.filter_true_of_mem (fun s _ => Nat.zero_le _)]
          have hle : (∑ s, n s : ℕ) ≤ ⌊B / ε⌋₊ := by
            apply Nat.le_floor
            rw [le_div_iff₀ hε]; push_cast; rw [Finset.sum_mul]; exact hn
          unfold Beps
          rw [← Finset.sum_mul]
          push_cast at hle ⊢
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hε.le
        have hinv := theorem_1_invariant I hI B ε hB hε S hS tab hrun n Meps hn hfeas 0 hK
          (Beps ε B) hBeps hsum I.D1 (by simp [startSet])
          (by rw [prefProd_zero, one_mulVec, sub_self]; unfold l1; simp [hε.le])
        have : welfare I (alg1Output I B ε tab) = valueFrom I (tab 0 (Beps ε B) I.D1) 0 I.D1 := rfl
        rw [this]
        simp only [Nat.sub_zero] at hinv
        nlinarith [mul_nonneg hε.le hρ0]
  · -- counting the instances of Program (7)
    unfold alg1LPCount
    set N := ⌊B / ε⌋₊
    have hgrid : (budgetGrid ε B).card ≤ N + 1 := by
      unfold budgetGrid
      exact le_trans Finset.card_image_le (by simp [N])
    have hterm : ∀ t, ∀ b ∈ budgetGrid ε B,
        (startSet I S t).card * (((budgetGrid ε B).filter (· ≤ b)).card * S.card) ≤
          (N + 1) * S.card ^ 2 := by
      intro t b _
      have hf : ((budgetGrid ε B).filter (· ≤ b)).card ≤ N + 1 :=
        le_trans (Finset.card_filter_le _ _) hgrid
      have hss : (startSet I S t).card * S.card ≤ S.card ^ 2 := by
        unfold startSet
        split_ifs
        · simp only [Finset.card_singleton, one_mul]; nlinarith
        · rw [sq]
      calc (startSet I S t).card * (((budgetGrid ε B).filter (· ≤ b)).card * S.card)
          = ((budgetGrid ε B).filter (· ≤ b)).card * ((startSet I S t).card * S.card) := by ring
        _ ≤ (N + 1) * S.card ^ 2 := Nat.mul_le_mul hf hss
    calc ∑ t ∈ Finset.range K, ∑ b ∈ budgetGrid ε B,
          (startSet I S t).card * (((budgetGrid ε B).filter (· ≤ b)).card * S.card)
        ≤ ∑ t ∈ Finset.range K, ∑ b ∈ budgetGrid ε B, (N + 1) * S.card ^ 2 :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun b hb => hterm t b hb
      _ = K * ((budgetGrid ε B).card * ((N + 1) * S.card ^ 2)) := by simp
      _ ≤ K * ((N + 1) * ((N + 1) * S.card ^ 2)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hgrid)
      _ = K * (N + 1) ^ 2 * S.card ^ 2 := by ring
