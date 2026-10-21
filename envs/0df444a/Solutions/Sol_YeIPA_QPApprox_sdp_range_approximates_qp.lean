-- Prove2me | solution 1 for YeIPA.QPApprox.sdp_range_approximates_qp
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-21T02:29:40.72199+00:00
-- url     : https://prove2.me/submissions/e28c09cb-a02a-4838-9ae8-eb701178a441

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_YeIPA_QPApprox_Relaxation
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs
import Theorems.Thm_ConvexOptAlg_GoemansWilliamson_lemma_6_12
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Theorems.Thm_YeIPA_QPApprox_arcsin_entrywise_dominates

open Matrix

namespace IP8Normalization

variable {n : ℕ}

theorem entry_zero_of_diag_zero {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) {i : Fin n} (hi : X i i = 0) (j : Fin n) : X i j = 0 := by
  have hsym : X j i = X i j := by simpa using hX.isHermitian.apply i j
  have hnonneg (t : ℝ) : 0 ≤ 2 * t * X i j + X j j := by
    have h := hX.dotProduct_mulVec_nonneg (Pi.single i t + Pi.single j 1)
    simp [star_trivial, Matrix.mulVec_add,
      Matrix.mulVec_single, add_dotProduct, dotProduct_add, single_dotProduct,
      hi, hsym] at h
    nlinarith
  by_contra hij
  have h := hnonneg (-(X j j + 1) / (2 * X i j))
  have heq : 2 * (-(X j j + 1) / (2 * X i j)) * X i j + X j j = -1 := by
    field_simp
    ring
  rw [heq] at h
  linarith

noncomputable def scale (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  Real.sqrt (X i i)

noncomputable def inverseScale (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  (scale X i)⁻¹

noncomputable def correlation (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (inverseScale X) * X * diagonal (inverseScale X) +
    diagonal (fun i => if X i i = 0 then 1 else 0)

theorem correlation_posSemidef {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) : (correlation X).PosSemidef := by
  unfold correlation
  apply Matrix.PosSemidef.add
  · simpa using hX.conjTranspose_mul_mul_same (diagonal (inverseScale X))
  · apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ if X i i = 0 then (1 : ℝ) else 0
    split <;> norm_num

theorem correlation_diag {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (i : Fin n) : correlation X i i = 1 := by
  have hnonneg := hX.diag_nonneg (i := i)
  by_cases hz : X i i = 0
  · simp [correlation, scale, inverseScale, hz, Matrix.diagonal_mul, Matrix.mul_diagonal]
  · have hs : Real.sqrt (X i i) ≠ 0 := (Real.sqrt_ne_zero hnonneg).mpr hz
    have hsquare := Real.sq_sqrt hnonneg
    simp only [correlation, Matrix.add_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.diagonal_apply_eq, inverseScale, scale, hz,
      ↓reduceIte, add_zero]
    field_simp
    nlinarith [hsquare]

theorem scale_correlation_scale {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) :
    diagonal (scale X) * correlation X * diagonal (scale X) = X := by
  ext i j
  by_cases hi : X i i = 0
  · have hij := entry_zero_of_diag_zero hX hi j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, scale, hi, hij]
  · by_cases hj : X j j = 0
    · have hji := entry_zero_of_diag_zero hX hj i
      have hij : X i j = 0 := by simpa using hX.isHermitian.apply j i |>.trans hji
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, scale, hj, hij]
    · have hsi : scale X i ≠ 0 := (Real.sqrt_ne_zero (hX.diag_nonneg (i := i))).mpr hi
      have hsj : scale X j ≠ 0 := (Real.sqrt_ne_zero (hX.diag_nonneg (i := j))).mpr hj
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, correlation,
        Matrix.add_apply, inverseScale]
      have hfill : (diagonal (fun k => if X k k = 0 then (1 : ℝ) else 0)) i j = 0 := by
        by_cases hij : i = j
        · subst j
          simp [hi]
        · simp [Matrix.diagonal_apply_ne _ hij]
      rw [hfill, add_zero]
      field_simp


end IP8Normalization


set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix Set
open YeIPA.QPApprox

namespace IP8Core
variable {m n : ℕ}

@[simp] theorem frob_constr (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    frob (constrMat A i) X = ∑ j, A i j * X j j := by
  simp [frob, constrMat, Matrix.diagonal_apply]

@[simp] theorem frob_rankOne (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    frob Q (Matrix.vecMulVec x x) = quadForm Q x := by
  simp only [frob, Matrix.vecMulVec_apply, quadForm, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

@[simp] theorem quadForm_neg (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadForm (-Q) x = -quadForm Q x := by
  simp [quadForm, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_neg_distrib]

@[simp] theorem frob_neg (Q X : Matrix (Fin n) (Fin n) ℝ) : frob (-Q) X = -frob Q X := by
  simp [frob, Finset.sum_neg_distrib]

 theorem rankOne_feasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (hx : IsQPFeasible A b x) :
    IsRelaxFeasible A b (Matrix.vecMulVec x x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [frob_constr]
    simpa only [Matrix.vecMulVec_apply, pow_two] using hx.1 i
  · intro j
    have hprod := mul_nonneg (sub_nonneg.mpr (hx.2 j).1) (sub_nonneg.mpr (hx.2 j).2)
    change x j * x j ≤ 1
    nlinarith
  · simpa using Matrix.posSemidef_vecMulVec_self_star x

 theorem continuous_quadForm (Q : Matrix (Fin n) (Fin n) ℝ) : Continuous (quadForm Q) := by
  unfold quadForm dotProduct Matrix.mulVec
  fun_prop

 theorem continuous_frob (Q : Matrix (Fin n) (Fin n) ℝ) : Continuous (frob Q) := by
  unfold frob
  fun_prop

 theorem closed_qp_feasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    IsClosed {x | IsQPFeasible A b x} := by
  unfold IsQPFeasible
  simp_rw [Set.setOf_and, Set.setOf_forall]
  exact (isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const).inter
    (isClosed_iInter fun j => (isClosed_le
      (f := fun _ : Fin n → ℝ => (-1 : ℝ)) continuous_const (continuous_apply j)).inter
      (isClosed_le (g := fun _ : Fin n → ℝ => (1 : ℝ)) (continuous_apply j) continuous_const))

 theorem compact_qp_feasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    IsCompact {x | IsQPFeasible A b x} := by
  apply (isCompact_Icc (a := fun _ : Fin n => (-1 : ℝ)) (b := fun _ => 1)).of_isClosed_subset
    (closed_qp_feasible A b)
  intro x hx
  exact ⟨fun j => (hx.2 j).1, fun j => (hx.2 j).2⟩

 theorem qpMin_attained (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : ∃ x, IsQPFeasible A b x) :
    ∃ x, IsQPFeasible A b x ∧ quadForm Q x = qpMin Q A b := by
  obtain ⟨x, hx, heq⟩ := (compact_qp_feasible A b).exists_sInf_image_eq hfeas
    (continuous_quadForm Q).continuousOn
  exact ⟨x, hx, heq.symm⟩

 theorem qpMin_le (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (hx : IsQPFeasible A b x) : qpMin Q A b ≤ quadForm Q x := by
  apply csInf_le
  · exact ((compact_qp_feasible A b).image (continuous_quadForm Q)).bddBelow
  · exact ⟨x, hx, rfl⟩

 theorem le_qpMax (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (hx : IsQPFeasible A b x) : quadForm Q x ≤ qpMax Q A b := by
  have h := qpMin_le (-Q) A b x hx
  simp only [quadForm_neg] at h
  change quadForm Q x ≤ -qpMin (-Q) A b
  linarith

 theorem qpMax_attained (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : ∃ x, IsQPFeasible A b x) :
    ∃ x, IsQPFeasible A b x ∧ quadForm Q x = qpMax Q A b := by
  obtain ⟨x, hx, heq⟩ := qpMin_attained (-Q) A b hfeas
  refine ⟨x, hx, ?_⟩
  simp only [quadForm_neg] at heq
  change quadForm Q x = -qpMin (-Q) A b
  linarith

theorem closed_psd : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} := by
  have hs : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.IsHermitian} := by
    change IsClosed {X : Matrix (Fin n) (Fin n) ℝ | Xᴴ = X}
    exact isClosed_eq (by fun_prop) continuous_id
  have hq : IsClosed {X : Matrix (Fin n) (Fin n) ℝ |
      ∀ v : Fin n → ℝ, 0 ≤ star v ⬝ᵥ (X *ᵥ v)} := by
    simp_rw [Set.setOf_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    unfold dotProduct Matrix.mulVec
    fun_prop
  simpa only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.setOf_and] using hs.inter hq

theorem closed_relax_feasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    IsClosed {X | IsRelaxFeasible A b X} := by
  have hlin : IsClosed {X : Matrix (Fin n) (Fin n) ℝ |
      ∀ i, frob (constrMat A i) X = b i} := by
    simp_rw [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_eq (continuous_frob _) continuous_const
  have hd : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | ∀ j, diagVec X j ≤ 1} := by
    simp_rw [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le (by unfold diagVec; fun_prop) continuous_const
  simpa only [IsRelaxFeasible, Set.setOf_and] using hlin.inter (hd.inter closed_psd)

theorem abs_entry_le_one (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : X.PosSemidef) (hd : ∀ i, X i i ≤ 1) (i j : Fin n) : |X i j| ≤ 1 := by
  have hsub := hX.submatrix (![i, j] : Fin 2 → Fin n)
  have hp := hsub.dotProduct_mulVec_nonneg (![1, 1] : Fin 2 → ℝ)
  have hm := hsub.dotProduct_mulVec_nonneg (![1, -1] : Fin 2 → ℝ)
  norm_num [dotProduct, mulVec, Fin.sum_univ_two, Matrix.submatrix] at hp hm
  have hsym : X j i = X i j := by simpa using hX.isHermitian.apply i j
  rw [hsym] at hp hm
  exact abs_le.mpr ⟨by linarith [hd i, hd j], by linarith [hd i, hd j]⟩

theorem compact_relax_feasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    IsCompact {X | IsRelaxFeasible A b X} := by
  apply (isCompact_Icc (a := fun _ _ : Fin n => (-1 : ℝ))
    (b := fun _ _ => 1)).of_isClosed_subset (closed_relax_feasible A b)
  intro X hX
  exact ⟨fun i j => (abs_le.mp (abs_entry_le_one X hX.2.2 hX.2.1 i j)).1,
    fun i j => (abs_le.mp (abs_entry_le_one X hX.2.2 hX.2.1 i j)).2⟩

theorem sdpMin_attained (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : ∃ x, IsQPFeasible A b x) :
    ∃ X, IsRelaxFeasible A b X ∧ frob Q X = sdpMin Q A b := by
  have hnonempty : {X | IsRelaxFeasible A b X}.Nonempty := by
    obtain ⟨x, hx⟩ := hfeas
    exact ⟨Matrix.vecMulVec x x, rankOne_feasible A b x hx⟩
  obtain ⟨X, hX, heq⟩ := (compact_relax_feasible A b).exists_sInf_image_eq hnonempty
    (continuous_frob Q).continuousOn
  exact ⟨X, hX, heq.symm⟩

theorem sdpMin_le (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : IsRelaxFeasible A b X) :
    sdpMin Q A b ≤ frob Q X := by
  apply csInf_le
  · exact ((compact_relax_feasible A b).image (continuous_frob Q)).bddBelow
  · exact ⟨X, hX, rfl⟩

theorem le_sdpMax (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : IsRelaxFeasible A b X) :
    frob Q X ≤ sdpMax Q A b := by
  have h := sdpMin_le (-Q) A b X hX
  simp only [frob_neg] at h
  change frob Q X ≤ -sdpMin (-Q) A b
  linarith

theorem sdpMax_attained (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : ∃ x, IsQPFeasible A b x) :
    ∃ X, IsRelaxFeasible A b X ∧ frob Q X = sdpMax Q A b := by
  obtain ⟨X, hX, heq⟩ := sdpMin_attained (-Q) A b hfeas
  refine ⟨X, hX, ?_⟩
  simp only [frob_neg] at heq
  change frob Q X = -sdpMin (-Q) A b
  linarith

theorem sdpMin_le_qpMin (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : ∃ x, IsQPFeasible A b x) : sdpMin Q A b ≤ qpMin Q A b := by
  obtain ⟨x, hx, heq⟩ := qpMin_attained Q A b hfeas
  have h := sdpMin_le Q A b (Matrix.vecMulVec x x) (rankOne_feasible A b x hx)
  simpa only [frob_rankOne, heq] using h

theorem sandwich (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : ∃ x, IsQPFeasible A b x) :
    sdpMin Q A b ≤ qpMin Q A b ∧ qpMin Q A b ≤ qpMax Q A b ∧
      qpMax Q A b ≤ sdpMax Q A b := by
  refine ⟨sdpMin_le_qpMin Q A b hfeas, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hfeas
    exact (qpMin_le Q A b x hx).trans (le_qpMax Q A b x hx)
  · have h := sdpMin_le_qpMin (-Q) A b hfeas
    exact neg_le_neg h

end IP8Core



open Matrix MeasureTheory
open YeIPA.QPApprox
open scoped BigOperators

namespace IP8GaussianRounding

variable {m n : ℕ}

noncomputable def point (X : Matrix (Fin n) (Fin n) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ :=
  fun i => IP8Normalization.scale X i * ConvexOptAlg.GoemansWilliamson.sgn (ξ i)

theorem point_sq {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n) : point X ξ i ^ 2 = X i i := by
  have hsgn : ConvexOptAlg.GoemansWilliamson.sgn (ξ i) ^ 2 = 1 := by
    unfold ConvexOptAlg.GoemansWilliamson.sgn
    split <;> norm_num
  simp only [point, mul_pow, hsgn, mul_one, IP8Normalization.scale]
  exact Real.sq_sqrt hX.diag_nonneg

theorem point_feasible {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : IsRelaxFeasible A b X)
    (ξ : EuclideanSpace ℝ (Fin n)) : IsQPFeasible A b (point X ξ) := by
  constructor
  · intro i
    simp_rw [point_sq hX.2.2]
    have hc := hX.1 i
    simpa [frob, constrMat, Matrix.diagonal] using hc
  · intro j
    have hj := point_sq hX.2.2 ξ j
    have hupper := hX.2.1 j
    change X j j ≤ 1 at hupper
    constructor <;> nlinarith

private noncomputable def coefficient (Q X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  Q i j * IP8Normalization.scale X i * IP8Normalization.scale X j

private theorem quad_expansion (Q X : Matrix (Fin n) (Fin n) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    quadForm Q (point X ξ) = ∑ i, ∑ j, coefficient Q X i j *
      (ConvexOptAlg.GoemansWilliamson.sgn (ξ i) * ConvexOptAlg.GoemansWilliamson.sgn (ξ j)) := by
  simp only [quadForm, dotProduct, Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [point, coefficient]
  ring

theorem expected_quad_form
    (Q X C : Matrix (Fin n) (Fin n) ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hid : ∀ i j, Integrable (fun ξ : EuclideanSpace ℝ (Fin n) =>
        ConvexOptAlg.GoemansWilliamson.sgn (ξ i) * ConvexOptAlg.GoemansWilliamson.sgn (ξ j)) μ ∧
      (∫ ξ, ConvexOptAlg.GoemansWilliamson.sgn (ξ i) *
        ConvexOptAlg.GoemansWilliamson.sgn (ξ j) ∂μ) =
        (2 / Real.pi) * Real.arcsin (C i j)) :
    Integrable (fun ξ => quadForm Q (point X ξ)) μ ∧
      (∫ ξ, quadForm Q (point X ξ) ∂μ) =
      (2 / Real.pi) * frob Q (diagonal (IP8Normalization.scale X) *
        entrywise Real.arcsin C * diagonal (IP8Normalization.scale X)) := by
  have hp (i j : Fin n) : Integrable (fun ξ : EuclideanSpace ℝ (Fin n) =>
      coefficient Q X i j * (ConvexOptAlg.GoemansWilliamson.sgn (ξ i) *
        ConvexOptAlg.GoemansWilliamson.sgn (ξ j))) μ := (hid i j).1.const_mul _
  have hi (i : Fin n) : Integrable (fun ξ : EuclideanSpace ℝ (Fin n) =>
      ∑ j, coefficient Q X i j * (ConvexOptAlg.GoemansWilliamson.sgn (ξ i) *
        ConvexOptAlg.GoemansWilliamson.sgn (ξ j))) μ := by
    exact integrable_finsetSum Finset.univ (fun j _ => hp i j)
  constructor
  · simp_rw [quad_expansion]
    exact integrable_finsetSum Finset.univ (fun i _ => hi i)
  · simp_rw [quad_expansion]
    rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
    calc
      (∑ i, ∫ ξ, ∑ j, coefficient Q X i j *
          (ConvexOptAlg.GoemansWilliamson.sgn (ξ i) *
            ConvexOptAlg.GoemansWilliamson.sgn (ξ j)) ∂μ) =
          ∑ i, ∑ j, coefficient Q X i j * ((2 / Real.pi) * Real.arcsin (C i j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum Finset.univ (fun j _ => hp i j)]
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul, (hid i j).2]
      _ = (2 / Real.pi) * frob Q (diagonal (IP8Normalization.scale X) *
          entrywise Real.arcsin C * diagonal (IP8Normalization.scale X)) := by
        unfold frob
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [coefficient, Matrix.diagonal_mul, Matrix.mul_diagonal, entrywise]
        ring


noncomputable def law (X : Matrix (Fin n) (Fin n) ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  ProbabilityTheory.multivariateGaussian 0 (IP8Normalization.correlation X)

instance law_isProbabilityMeasure (X : Matrix (Fin n) (Fin n) ℝ) :
    IsProbabilityMeasure (law X) := by
  unfold law
  infer_instance

theorem gaussian_expected_quad_form (Q X : Matrix (Fin n) (Fin n) ℝ)
    (hX : X.PosSemidef) :
    Integrable (fun ξ => quadForm Q (point X ξ)) (law X) ∧
      (∫ ξ, quadForm Q (point X ξ) ∂law X) =
      (2 / Real.pi) * frob Q (diagonal (IP8Normalization.scale X) *
        entrywise Real.arcsin (IP8Normalization.correlation X) *
          diagonal (IP8Normalization.scale X)) := by
  apply expected_quad_form
  intro i j
  exact ConvexOptAlg.GoemansWilliamson.lemma_6_12
    (IP8Normalization.correlation X) (IP8Normalization.correlation_posSemidef hX)
    (IP8Normalization.correlation_diag hX) i j


end IP8GaussianRounding


set_option autoImplicit false
set_option maxHeartbeats 1000000
open Matrix MeasureTheory
open YeIPA.QPApprox

namespace IP8OneSided
variable {m n : ℕ}

@[simp] theorem frob_sub (Q X Y : Matrix (Fin n) (Fin n) ℝ) :
    frob Q (X - Y) = frob Q X - frob Q Y := by
  simp [frob, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem frob_smul (Q X : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    frob Q (c • X) = c * frob Q X := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A same-diagonal positive residual gives the one-sided approximation
bound. No dual optimal pair or strictly feasible primal matrix is assumed. -/
theorem from_feasible (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : IsRelaxFeasible A b X)
    (harc : (entrywise Real.arcsin (IP8Normalization.correlation X) -
      IP8Normalization.correlation X).PosSemidef) :
    qpMin Q A b ≤ (2 / Real.pi) * frob Q X +
      (1 - 2 / Real.pi) * sdpMax Q A b := by
  let C := IP8Normalization.correlation X
  let D := diagonal (IP8Normalization.scale X)
  let T := D * entrywise Real.arcsin C * D
  let β := Real.pi / 2 - 1
  have hβ : 0 < β := by
    dsimp [β]
    linarith [Real.pi_gt_three]
  have hα : 0 ≤ 2 / Real.pi := le_of_lt (div_pos (by norm_num) Real.pi_pos)
  have hDC : D * C * D = X := IP8Normalization.scale_correlation_scale hX.2.2
  have hres : (T - X).PosSemidef := by
    have h := harc.conjTranspose_mul_mul_same D
    have hD : Dᴴ = D := by simp [D]
    rw [hD, Matrix.mul_sub, Matrix.sub_mul, hDC] at h
    exact h
  let Y := β⁻¹ • (T - X)
  have hTd (j : Fin n) : T j j = (Real.pi / 2) * X j j := by
    dsimp [T, D]
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, entrywise]
    have hCj : C j j = 1 := IP8Normalization.correlation_diag hX.2.2 j
    rw [hCj, Real.arcsin_one]
    dsimp [IP8Normalization.scale]
    calc
      Real.sqrt (X j j) * (Real.pi / 2) * Real.sqrt (X j j) =
          (Real.pi / 2) * (Real.sqrt (X j j)) ^ 2 := by ring
      _ = (Real.pi / 2) * X j j := by rw [Real.sq_sqrt hX.2.2.diag_nonneg]
  have hYd (j : Fin n) : Y j j = X j j := by
    change β⁻¹ * (T j j - X j j) = X j j
    rw [hTd]
    have hr : (Real.pi / 2) * X j j - X j j = β * X j j := by dsimp [β]; ring
    rw [hr, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hβ), one_mul]
  have hY : IsRelaxFeasible A b Y := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [IP8Core.frob_constr]
      simp_rw [hYd]
      simpa only [IP8Core.frob_constr] using hX.1 i
    · intro j
      change Y j j ≤ 1
      rw [hYd]
      exact hX.2.1 j
    · exact hres.smul (le_of_lt (inv_pos.mpr hβ))
  have hFY : frob Q Y = β⁻¹ * (frob Q T - frob Q X) := by
    change frob Q (β⁻¹ • (T - X)) = _
    rw [frob_smul, frob_sub]
  have hFYrel : β * frob Q Y = frob Q T - frob Q X := by
    rw [hFY, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hβ), one_mul]
  have hupper := mul_le_mul_of_nonneg_left (IP8Core.le_sdpMax Q A b Y hY) (le_of_lt hβ)
  have hTupper : frob Q T ≤ frob Q X + β * sdpMax Q A b := by linarith
  have hexpect := IP8GaussianRounding.gaussian_expected_quad_form Q X hX.2.2
  have hmean : qpMin Q A b ≤ (2 / Real.pi) * frob Q T := by
    have hi := integral_mono (integrable_const (qpMin Q A b)) hexpect.1
      (fun ξ => IP8Core.qpMin_le Q A b _ (IP8GaussianRounding.point_feasible hX ξ))
    rw [hexpect.2] at hi
    simpa only [integral_const, probReal_univ, one_smul] using hi
  have hαβ : (2 / Real.pi) * β = 1 - 2 / Real.pi := by
    dsimp [β]
    field_simp
  calc
    qpMin Q A b ≤ (2 / Real.pi) * frob Q T := hmean
    _ ≤ (2 / Real.pi) * (frob Q X + β * sdpMax Q A b) :=
      mul_le_mul_of_nonneg_left hTupper hα
    _ = (2 / Real.pi) * frob Q X + (1 - 2 / Real.pi) * sdpMax Q A b := by
      rw [mul_add, ← mul_assoc, hαβ]

end IP8OneSided


set_option autoImplicit false

namespace IP8RangeAlgebra

/-- The four range inequalities follow algebraically from the relaxation sandwich
and the two affine one-sided approximation estimates. -/
theorem range_bounds_of_affine_sandwich
    (qmin qmax pmin pmax α : ℝ)
    (hmin : pmin ≤ qmin) (hmid : qmin ≤ qmax) (hmax : qmax ≤ pmax)
    (hlo : qmin ≤ α * pmin + (1 - α) * pmax)
    (hhi : α * pmax + (1 - α) * pmin ≤ qmax) :
    pmax - qmin ≥ α * (pmax - pmin) ∧
    qmax - pmin ≥ α * (pmax - pmin) ∧
    pmax - pmin ≥ qmax - qmin ∧
    qmax - qmin ≥ (2 * α - 1) * (pmax - pmin) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · linarith
  · nlinarith

/-- The exact π/2 range constants of the SDP approximation theorem. -/
theorem range_bounds_pi
    (qmin qmax pmin pmax : ℝ)
    (hmin : pmin ≤ qmin) (hmid : qmin ≤ qmax) (hmax : qmax ≤ pmax)
    (hlo : qmin ≤ (2 / Real.pi) * pmin + (1 - 2 / Real.pi) * pmax)
    (hhi : (2 / Real.pi) * pmax + (1 - 2 / Real.pi) * pmin ≤ qmax) :
    pmax - qmin ≥ (2 / Real.pi) * (pmax - pmin) ∧
    qmax - pmin ≥ (2 / Real.pi) * (pmax - pmin) ∧
    pmax - pmin ≥ qmax - qmin ∧
    qmax - qmin ≥ ((4 - Real.pi) / Real.pi) * (pmax - pmin) := by
  have hc : 2 * (2 / Real.pi) - 1 = (4 - Real.pi) / Real.pi := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  simpa only [hc] using
    range_bounds_of_affine_sandwich qmin qmax pmin pmax (2 / Real.pi)
      hmin hmid hmax hlo hhi

end IP8RangeAlgebra


namespace IP8Main
open YeIPA.QPApprox
variable {m n : ℕ}

theorem lower_affine (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : ∃ x, IsQPFeasible A b x) :
    qpMin Q A b ≤ (2 / Real.pi) * sdpMin Q A b +
      (1 - 2 / Real.pi) * sdpMax Q A b := by
  obtain ⟨X, hX, hopt⟩ := IP8Core.sdpMin_attained Q A b hfeas
  have harc := YeIPA.QPApprox.arcsin_entrywise_dominates
    (IP8Normalization.correlation X) (IP8Normalization.correlation_posSemidef hX.2.2)
    (by intro j; exact le_of_eq (IP8Normalization.correlation_diag hX.2.2 j))
  have h := IP8OneSided.from_feasible Q A b X hX harc
  simpa only [hopt] using h

theorem upper_affine (Q : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : ∃ x, IsQPFeasible A b x) :
    (2 / Real.pi) * sdpMax Q A b + (1 - 2 / Real.pi) * sdpMin Q A b ≤
      qpMax Q A b := by
  have h := lower_affine (-Q) A b hfeas
  have h' : -qpMax Q A b ≤ (2 / Real.pi) * (-sdpMax Q A b) +
      (1 - 2 / Real.pi) * (-sdpMin Q A b) := by
    simpa only [qpMax, sdpMax, neg_neg] using h
  nlinarith

end IP8Main

open YeIPA.QPApprox
variable {m n : ℕ}

/-- Theorem 9.33, with the source's exact hypotheses. The covariance
decomposition avoids assuming primal strict feasibility or dual attainment. -/
theorem solution (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x) :
    sdpMax Q A b - qpMin Q A b ≥ (2 / Real.pi) * (sdpMax Q A b - sdpMin Q A b) ∧
    qpMax Q A b - sdpMin Q A b ≥ (2 / Real.pi) * (sdpMax Q A b - sdpMin Q A b) ∧
    sdpMax Q A b - sdpMin Q A b ≥ qpMax Q A b - qpMin Q A b ∧
    qpMax Q A b - qpMin Q A b ≥ ((4 - Real.pi) / Real.pi) *
      (sdpMax Q A b - sdpMin Q A b) := by
  have hs := IP8Core.sandwich Q A b hfeas
  exact IP8RangeAlgebra.range_bounds_pi (qpMin Q A b) (qpMax Q A b)
    (sdpMin Q A b) (sdpMax Q A b) hs.1 hs.2.1 hs.2.2
    (IP8Main.lower_affine Q A b hfeas) (IP8Main.upper_affine Q A b hfeas)

#print axioms solution
