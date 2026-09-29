-- Prove2me | solution 1 for SatiaLave.MaxMin.prop1_eq4_unique_solution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:08:09.796378+00:00
-- url     : https://prove2.me/submissions/a335ae24-d2dc-4239-823a-0f0cb60f973b

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Eq4

namespace SatiaLave.MaxMin

open Finset MeasureTheory

set_option linter.unusedSectionVars false

section aux_pl

variable {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)]

/-- the linear functional `p ↦ Σ_l p_l (r_{jkl} + β v_l)` -/
noncomputable def aux_pl_f (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) (p : S → ℝ) : ℝ :=
  ∑ l, p l * (M.r j k l + M.β * v l)

/-- nature's row minimum -/
noncomputable def aux_pl_rowMin (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) : ℝ :=
  ⨅ p : M.U j k, aux_pl_f M j k v p

lemma aux_pl_U_compact (M : UncertainMDP S D) (j : S) (k : D j) : IsCompact (M.U j k) :=
  (isCompact_stdSimplex (𝕜 := ℝ) (ι := S)).of_isClosed_subset (M.U_closed j k) (M.U_subset j k)

lemma aux_pl_f_cont (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) :
    Continuous (aux_pl_f M j k v) := by
  unfold aux_pl_f
  fun_prop

lemma aux_pl_rowMin_spec (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) :
    ∃ p ∈ M.U j k, aux_pl_rowMin M j k v = aux_pl_f M j k v p ∧
      ∀ q ∈ M.U j k, aux_pl_f M j k v p ≤ aux_pl_f M j k v q := by
  obtain ⟨p, hp, hmin⟩ := (aux_pl_U_compact M j k).exists_isMinOn (M.U_nonempty j k)
    (aux_pl_f_cont M j k v).continuousOn
  have hmin' : ∀ q ∈ M.U j k, aux_pl_f M j k v p ≤ aux_pl_f M j k v q := isMinOn_iff.1 hmin
  refine ⟨p, hp, ?_, hmin'⟩
  unfold aux_pl_rowMin
  apply le_antisymm
  · exact ciInf_le ⟨aux_pl_f M j k v p, Set.forall_mem_range.2 fun (q : M.U j k) => hmin' q.1 q.2⟩ ⟨p, hp⟩
  · haveI : Nonempty (M.U j k) := ⟨⟨p, hp⟩⟩
    exact le_ciInf fun q => hmin' q.1 q.2

lemma aux_pl_rowMin_le (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) (q : S → ℝ)
    (hq : q ∈ M.U j k) : aux_pl_rowMin M j k v ≤ aux_pl_f M j k v q := by
  obtain ⟨p, _, h1, h2⟩ := aux_pl_rowMin_spec M j k v
  rw [h1]; exact h2 q hq

lemma aux_pl_inner (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) :
    (⨅ α : {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1},
      ∫ p, ∑ l, p l * (M.r j k l + M.β * v l) ∂(α.1 : Measure (S → ℝ))) =
      aux_pl_rowMin M j k v := by
  obtain ⟨p0, hp0, h1, h2⟩ := aux_pl_rowMin_spec M j k v
  have hmeas : MeasurableSet (M.U j k) := (M.U_closed j k).measurableSet
  have lower : ∀ α : {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1},
      aux_pl_rowMin M j k v ≤
        ∫ p, ∑ l, p l * (M.r j k l + M.β * v l) ∂(α.1 : Measure (S → ℝ)) := by
    rintro ⟨μ, hμ⟩
    have hae : ∀ᵐ p ∂(μ : Measure (S → ℝ)), p ∈ M.U j k := by
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff hmeas).2 hμ
    have hint : Integrable (fun p : S → ℝ => ∑ l, p l * (M.r j k l + M.β * v l))
        (μ : Measure (S → ℝ)) := by
      refine Integrable.of_bound ((aux_pl_f_cont M j k v).aestronglyMeasurable)
        (∑ l, |M.r j k l + M.β * v l|) ?_
      filter_upwards [hae] with p hp
      have hps := M.U_subset j k hp
      rw [Real.norm_eq_abs]
      refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [abs_mul]
      have h0 : 0 ≤ p l := hps.1 l
      have h1' : p l ≤ 1 := by
        rw [← hps.2]
        exact Finset.single_le_sum (fun i _ => hps.1 i) (mem_univ l)
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_left (abs_nonneg _) h1'
    rw [h1]
    calc aux_pl_f M j k v p0 = ∫ _p, aux_pl_f M j k v p0 ∂(μ : Measure (S → ℝ)) := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hint
          (by filter_upwards [hae] with p hp; exact h2 p hp)
  have hd : ((⟨Measure.dirac p0, inferInstance⟩ : ProbabilityMeasure (S → ℝ)) :
      Measure (S → ℝ)) (M.U j k) = 1 := Measure.dirac_apply_of_mem hp0
  apply le_antisymm
  · refine (ciInf_le ⟨_, Set.forall_mem_range.2 lower⟩ ⟨⟨Measure.dirac p0, inferInstance⟩, hd⟩).trans ?_
    rw [h1]
    show ∫ p, aux_pl_f M j k v p ∂(Measure.dirac p0) ≤ aux_pl_f M j k v p0
    rw [integral_dirac' _ _ (aux_pl_f_cont M j k v).stronglyMeasurable]
  · haveI : Nonempty {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1} :=
      ⟨⟨_, hd⟩⟩
    exact le_ciInf lower

lemma aux_pl_sup (j : S) [Nonempty (D j)] (m : D j → ℝ) :
    (⨆ τ : stdSimplex ℝ (D j), ∑ k, (τ : D j → ℝ) k * m k) = univ.sup' univ_nonempty m := by
  classical
  obtain ⟨k0, -, hk0⟩ := Finset.exists_mem_eq_sup' univ_nonempty m
  have upper : ∀ τ : stdSimplex ℝ (D j), ∑ k, (τ : D j → ℝ) k * m k ≤ univ.sup' univ_nonempty m := by
    rintro ⟨τ, hτ0, hτ1⟩
    calc ∑ k, τ k * m k ≤ ∑ k, τ k * univ.sup' univ_nonempty m :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (Finset.le_sup' m (mem_univ k)) (hτ0 k)
      _ = _ := by rw [← Finset.sum_mul, hτ1, one_mul]
  apply le_antisymm
  · haveI : Nonempty (stdSimplex ℝ (D j)) := ⟨⟨_, single_mem_stdSimplex ℝ k0⟩⟩
    exact ciSup_le upper
  · refine le_trans ?_ (le_ciSup ⟨_, Set.forall_mem_range.2 upper⟩ ⟨_, single_mem_stdSimplex ℝ k0⟩)
    simp [hk0, Pi.single_apply]

lemma aux_pl_eq4 [∀ i, Nonempty (D i)] (M : UncertainMDP S D) (v : S → ℝ) (j : S) :
    eq4Op M v j = univ.sup' univ_nonempty (fun k => aux_pl_rowMin M j k v) := by
  unfold eq4Op
  simp only [aux_pl_inner]
  exact aux_pl_sup j _

/-- the generalized Bellman operator -/
noncomputable def aux_pl_T (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) (v : S → ℝ) : S → ℝ :=
  fun j => (F j).sup' (hF j) (fun k => aux_pl_rowMin M j k v)

lemma aux_pl_simplex_le (p : S → ℝ) (hp : p ∈ stdSimplex ℝ S) (d : S → ℝ) (c : ℝ)
    (hd : ∀ l, d l ≤ c) : ∑ l, p l * d l ≤ c := by
  calc ∑ l, p l * d l ≤ ∑ l, p l * c :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hd l) (hp.1 l)
    _ = c := by rw [← Finset.sum_mul, hp.2, one_mul]

lemma aux_pl_f_sub (M : UncertainMDP S D) (j : S) (k : D j) (v u p : S → ℝ) :
    aux_pl_f M j k v p - aux_pl_f M j k u p = M.β * ∑ l, p l * (v l - u l) := by
  unfold aux_pl_f
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma aux_pl_rowMin_lip (M : UncertainMDP S D) (j : S) (k : D j) (v u : S → ℝ) :
    aux_pl_rowMin M j k v ≤ aux_pl_rowMin M j k u + M.β * dist v u := by
  obtain ⟨p, hp, h1, _⟩ := aux_pl_rowMin_spec M j k u
  have h2 := aux_pl_rowMin_le M j k v p hp
  have h3 := aux_pl_f_sub M j k v u p
  have h4 : ∑ l, p l * (v l - u l) ≤ dist v u :=
    aux_pl_simplex_le p (M.U_subset j k hp) _ _ fun l => by
      have := dist_le_pi_dist v u l
      rw [Real.dist_eq] at this
      exact (le_abs_self _).trans this
  have h5 := mul_le_mul_of_nonneg_left h4 M.β_nonneg
  linarith

lemma aux_pl_T_lip (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) (v u : S → ℝ) (j : S) :
    aux_pl_T M F hF v j ≤ aux_pl_T M F hF u j + M.β * dist v u := by
  unfold aux_pl_T
  refine Finset.sup'_le _ _ fun k hk => ?_
  exact (aux_pl_rowMin_lip M j k v u).trans
    (add_le_add_left (Finset.le_sup' (fun k => aux_pl_rowMin M j k u) hk) _)

lemma aux_pl_T_dist (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) (v u : S → ℝ) :
    dist (aux_pl_T M F hF v) (aux_pl_T M F hF u) ≤ M.β * dist v u := by
  refine (dist_pi_le_iff (mul_nonneg M.β_nonneg dist_nonneg)).2 fun j => ?_
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor
  · linarith [aux_pl_T_lip M F hF v u j]
  · have := aux_pl_T_lip M F hF u v j
    rw [dist_comm u v] at this
    linarith

lemma aux_pl_T_contr (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) :
    ContractingWith (⟨M.β, M.β_nonneg⟩ : NNReal) (aux_pl_T M F hF) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun v u => ?_⟩
  · exact NNReal.coe_lt_coe.1 M.β_lt_one
  · exact aux_pl_T_dist M F hF v u

noncomputable def aux_pl_fix (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) : S → ℝ :=
  ContractingWith.fixedPoint (aux_pl_T M F hF) (aux_pl_T_contr M F hF)

lemma aux_pl_fix_eq (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) : aux_pl_T M F hF (aux_pl_fix M F hF) = aux_pl_fix M F hF :=
  ContractingWith.fixedPoint_isFixedPt (aux_pl_T_contr M F hF)

lemma aux_pl_fix_unique (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) (v : S → ℝ) (hv : aux_pl_T M F hF v = v) :
    v = aux_pl_fix M F hF :=
  ContractingWith.fixedPoint_unique (aux_pl_T_contr M F hF) hv

lemma aux_pl_min_nonneg (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (q : S → S → ℝ)
    (hq : ∀ i, q i ∈ stdSimplex ℝ S) (d : S → ℝ) (h : ∀ i, β * ∑ l, q i l * d l ≤ d i) :
    ∀ i, 0 ≤ d i := by
  intro i
  by_contra hneg
  push Not at hneg
  haveI : Nonempty S := ⟨i⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_min d
  have h1 : d i0 ≤ ∑ l, q i0 l * d l := by
    calc d i0 = ∑ l, q i0 l * d i0 := by rw [← Finset.sum_mul, (hq i0).2, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hi0 l) ((hq i0).1 l)
  have h2 := h i0
  have h3 : β * d i0 ≤ β * ∑ l, q i0 l * d l := mul_le_mul_of_nonneg_left h1 hβ0
  have h4 := hi0 i
  nlinarith [mul_pos (sub_pos.2 hβ1) (neg_pos.2 (lt_of_le_of_lt h4 hneg))]

lemma aux_pl_max_nonpos (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (q : S → S → ℝ)
    (hq : ∀ i, q i ∈ stdSimplex ℝ S) (d : S → ℝ) (h : ∀ i, d i ≤ β * ∑ l, q i l * d l) :
    ∀ i, d i ≤ 0 := by
  intro i
  have := aux_pl_min_nonneg β hβ0 hβ1 q hq (fun i => -d i) (fun i => by
    simp only [mul_neg, Finset.sum_neg_distrib]
    linarith [h i]) i
  linarith

lemma aux_pl_zero (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (q : S → S → ℝ)
    (hq : ∀ i, q i ∈ stdSimplex ℝ S) (d : S → ℝ) (h : ∀ i, d i = β * ∑ l, q i l * d l) :
    ∀ i, d i = 0 := fun i =>
  le_antisymm (aux_pl_max_nonpos β hβ0 hβ1 q hq d (fun i => (h i).le) i)
    (aux_pl_min_nonneg β hβ0 hβ1 q hq d (fun i => (h i).symm.le) i)

lemma aux_pl_Bmul (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (z : S → ℝ) (i : S) :
    Matrix.mulVec (1 - M.β • transMat M A P) z i = z i - M.β * ∑ l, P.1 i (A i) l * z l := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rfl

lemma aux_pl_pv_solves (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) :
    SolvesEq5 M A P (presentValue M A P) := by
  have hrow : ∀ i, P.1 i (A i) ∈ stdSimplex ℝ S := fun i => M.U_subset _ _ (P.2 i (A i))
  have hinj : Function.Injective (1 - M.β • transMat M A P).mulVec := by
    intro x y hxy
    have e : ∀ i, (x - y) i = M.β * ∑ l, P.1 i (A i) l * (x - y) l := by
      intro i
      have hz : Matrix.mulVec (1 - M.β • transMat M A P) (x - y) i = 0 := by
        rw [Matrix.mulVec_sub, hxy, sub_self]; rfl
      rw [aux_pl_Bmul] at hz
      linarith
    have := aux_pl_zero M.β M.β_nonneg M.β_lt_one (fun i => P.1 i (A i)) hrow (x - y) e
    funext i
    have := this i
    simp only [Pi.sub_apply] at this
    linarith
  have hunit : IsUnit (1 - M.β • transMat M A P) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit (1 - M.β • transMat M A P).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 hunit
  have key : Matrix.mulVec (1 - M.β • transMat M A P) (presentValue M A P) = rewardVec M A P := by
    unfold presentValue
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  intro i
  have := congrFun key i
  rw [aux_pl_Bmul] at this
  simp only [rewardVec] at this
  have hs : ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) =
      ∑ j, P.1 i (A i) j * M.r i (A i) j + M.β * ∑ j, P.1 i (A i) j * presentValue M A P j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hs]
  linarith

lemma aux_pl_eq5_unique (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (v w : S → ℝ)
    (hv : SolvesEq5 M A P v) (hw : SolvesEq5 M A P w) : v = w := by
  have hrow : ∀ i, P.1 i (A i) ∈ stdSimplex ℝ S := fun i => M.U_subset _ _ (P.2 i (A i))
  have e : ∀ i, (v - w) i = M.β * ∑ l, P.1 i (A i) l * (v - w) l := by
    intro i
    have h4 := aux_pl_f_sub M i (A i) v w (P.1 i (A i))
    unfold aux_pl_f at h4
    rw [← hv i, ← hw i] at h4
    simpa using h4
  have := aux_pl_zero M.β M.β_nonneg M.β_lt_one (fun i => P.1 i (A i)) hrow (v - w) e
  funext i
  have := this i
  simp only [Pi.sub_apply] at this
  linarith

variable [∀ i, Nonempty (D i)]

noncomputable def aux_pl_w (M : UncertainMDP S D) (A : Policy S D) : S → ℝ :=
  aux_pl_fix M (fun j => {A j}) (fun _ => singleton_nonempty _)

noncomputable def aux_pl_vstar (M : UncertainMDP S D) : S → ℝ :=
  aux_pl_fix M (fun j => (univ : Finset (D j))) (fun _ => univ_nonempty)

lemma aux_pl_w_eq (M : UncertainMDP S D) (A : Policy S D) (i : S) :
    aux_pl_w M A i = aux_pl_rowMin M i (A i) (aux_pl_w M A) := by
  have := congrFun (aux_pl_fix_eq M (fun j => {A j}) (fun _ => singleton_nonempty _)) i
  unfold aux_pl_w
  rw [← this]
  simp only [aux_pl_T, Finset.sup'_singleton]

lemma aux_pl_vstar_eq (M : UncertainMDP S D) (i : S) :
    aux_pl_vstar M i = univ.sup' univ_nonempty (fun k => aux_pl_rowMin M i k (aux_pl_vstar M)) :=
  (congrFun (aux_pl_fix_eq M (fun j => (univ : Finset (D j))) (fun _ => univ_nonempty)) i).symm

noncomputable def aux_pl_Pstar (M : UncertainMDP S D) (w : S → ℝ) : Sel M :=
  Subtype.mk (fun i k => Classical.choose (aux_pl_rowMin_spec M i k w))
    (fun i k => (Classical.choose_spec (aux_pl_rowMin_spec M i k w)).1)

lemma aux_pl_Pstar_spec (M : UncertainMDP S D) (w : S → ℝ) (i : S) (k : D i) :
    aux_pl_rowMin M i k w = aux_pl_f M i k w ((aux_pl_Pstar M w).1 i k) :=
  (Classical.choose_spec (aux_pl_rowMin_spec M i k w)).2.1

lemma aux_pl_w_le_pv (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (i : S) :
    aux_pl_w M A i ≤ presentValue M A P i := by
  have hsol := aux_pl_pv_solves M A P
  have key : ∀ i, M.β * ∑ l, P.1 i (A i) l * (presentValue M A P l - aux_pl_w M A l) ≤
      presentValue M A P i - aux_pl_w M A i := by
    intro i
    have h1 := hsol i
    have h2 := aux_pl_rowMin_le M i (A i) (aux_pl_w M A) (P.1 i (A i)) (P.2 i (A i))
    have h3 := aux_pl_w_eq M A i
    have h4 := aux_pl_f_sub M i (A i) (presentValue M A P) (aux_pl_w M A) (P.1 i (A i))
    unfold aux_pl_f at h2 h4
    rw [← h1] at h4
    linarith
  have := aux_pl_min_nonneg M.β M.β_nonneg M.β_lt_one (fun i => P.1 i (A i))
    (fun i => M.U_subset _ _ (P.2 i (A i))) (fun i => presentValue M A P i - aux_pl_w M A i) key i
  linarith

lemma aux_pl_pv_Pstar (M : UncertainMDP S D) (A : Policy S D) :
    presentValue M A (aux_pl_Pstar M (aux_pl_w M A)) = aux_pl_w M A := by
  apply aux_pl_eq5_unique M A (aux_pl_Pstar M (aux_pl_w M A)) _ _
    (aux_pl_pv_solves M A _)
  intro i
  rw [aux_pl_w_eq M A i, aux_pl_Pstar_spec M (aux_pl_w M A) i (A i)]
  rfl

lemma aux_pl_robust (M : UncertainMDP S D) (A : Policy S D) (i : S) :
    robustValue M A i = aux_pl_w M A i := by
  unfold robustValue
  have hP := aux_pl_pv_Pstar M A
  apply le_antisymm
  · refine (ciInf_le ⟨aux_pl_w M A i, Set.forall_mem_range.2 fun P => aux_pl_w_le_pv M A P i⟩
      (aux_pl_Pstar M (aux_pl_w M A))).trans ?_
    rw [hP]
  · haveI : Nonempty (Sel M) := ⟨aux_pl_Pstar M (aux_pl_w M A)⟩
    exact le_ciInf fun P => aux_pl_w_le_pv M A P i

lemma aux_pl_w_le_vstar (M : UncertainMDP S D) (A : Policy S D) (i : S) :
    aux_pl_w M A i ≤ aux_pl_vstar M i := by
  let q : S → S → ℝ := fun i => (aux_pl_Pstar M (aux_pl_vstar M)).1 i (A i)
  have hq : ∀ i, q i ∈ M.U i (A i) := fun i => (aux_pl_Pstar M (aux_pl_vstar M)).2 i (A i)
  have key : ∀ i, aux_pl_w M A i - aux_pl_vstar M i ≤
      M.β * ∑ l, q i l * (aux_pl_w M A l - aux_pl_vstar M l) := by
    intro i
    have h1 := aux_pl_w_eq M A i
    have h2 := aux_pl_rowMin_le M i (A i) (aux_pl_w M A) (q i) (hq i)
    have h3 : aux_pl_rowMin M i (A i) (aux_pl_vstar M) ≤ aux_pl_vstar M i :=
      (Finset.le_sup' (fun k => aux_pl_rowMin M i k (aux_pl_vstar M)) (mem_univ (A i))).trans_eq
        (aux_pl_vstar_eq M i).symm
    have h4 := aux_pl_f_sub M i (A i) (aux_pl_w M A) (aux_pl_vstar M) (q i)
    have h5 := aux_pl_Pstar_spec M (aux_pl_vstar M) i (A i)
    linarith
  have := aux_pl_max_nonpos M.β M.β_nonneg M.β_lt_one q (fun i => M.U_subset _ _ (hq i))
    (fun i => aux_pl_w M A i - aux_pl_vstar M i) key i
  linarith

lemma aux_pl_exists_opt (M : UncertainMDP S D) : ∃ A : Policy S D, aux_pl_w M A = aux_pl_vstar M := by
  choose A hA using fun i => Finset.exists_mem_eq_sup' (univ_nonempty (α := D i))
    (fun k => aux_pl_rowMin M i k (aux_pl_vstar M))
  refine ⟨A, ?_⟩
  unfold aux_pl_w
  refine (aux_pl_fix_unique M (fun j => {A j}) (fun _ => singleton_nonempty _) (aux_pl_vstar M) ?_).symm
  funext i
  show ({A i} : Finset (D i)).sup' _ (fun k => aux_pl_rowMin M i k (aux_pl_vstar M)) =
    aux_pl_vstar M i
  rw [Finset.sup'_singleton, aux_pl_vstar_eq M i, (hA i).2]

lemma aux_pl_maxMin (M : UncertainMDP S D) : maxMinValue M = aux_pl_vstar M := by
  funext i
  unfold maxMinValue
  obtain ⟨A, hA⟩ := aux_pl_exists_opt M
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun B _ => ?_
    rw [aux_pl_robust]
    exact aux_pl_w_le_vstar M B i
  · refine le_trans ?_ (Finset.le_sup' (fun B => robustValue M B i) (mem_univ A))
    show aux_pl_vstar M i ≤ robustValue M A i
    rw [aux_pl_robust, hA]

end aux_pl

end SatiaLave.MaxMin

open SatiaLave.MaxMin Finset

theorem solution {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    (∃! v : S → ℝ, ∀ j, v j = eq4Op M v j) ∧ ∀ j, maxMinValue M j = eq4Op M (maxMinValue M) j := by
  have hT : ∀ v j, eq4Op M v j =
      aux_pl_T M (fun j => (univ : Finset (D j))) (fun _ => univ_nonempty) v j :=
    fun v j => aux_pl_eq4 M v j
  have hfix := aux_pl_fix_eq M (fun j => (univ : Finset (D j))) (fun _ => univ_nonempty)
  refine ⟨⟨aux_pl_vstar M, fun j => ?_, fun v hv => ?_⟩, fun j => ?_⟩
  · rw [hT]
    exact (congrFun hfix j).symm
  · apply aux_pl_fix_unique
    funext j
    rw [← hT]
    exact (hv j).symm
  · rw [aux_pl_maxMin, hT]
    exact (congrFun hfix j).symm
