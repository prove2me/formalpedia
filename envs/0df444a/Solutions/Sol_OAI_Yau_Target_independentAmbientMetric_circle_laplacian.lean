-- Prove2me | solution 1 for OAI.Yau.Target.independentAmbientMetric_circle_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:31:23.258806+00:00
-- url     : https://prove2.me/submissions/0106d63c-fdf1-4701-961a-8fd92cd04156

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IndependentWeightedMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma weightedBaseMatrix_inverse {A : Matrix n n ℝ} (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) : (weightedBaseMatrix A rho)⁻¹ = rho⁻¹ • A := by
  let : Invertible rho := invertibleOfNonzero hr.ne'
  rw [weightedBaseMatrix,Matrix.inv_smul A⁻¹ rho (isUnit_iff_ne_zero.mpr hA.inv.det_pos.ne'),
    invOf_eq_inv,Matrix.nonsing_inv_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TangentialMatrixInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma radial_fixed_inverse (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : n → ℝ) (hx : A *ᵥ x = x) : A⁻¹ *ᵥ x = x := by
  calc
    A⁻¹ *ᵥ x = A⁻¹ *ᵥ (A *ᵥ x) := congrArg (fun v ↦ A⁻¹ *ᵥ v) hx.symm
    _ = x := by
      rw [mulVec_mulVec,A.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),one_mulVec]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RadialVolumeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section

local instance instDecidableEqFinOfNatNat_solutions_rb1a1cd_1 : DecidableEq (Fin 1) := fun a b ↦ decidableEq_of_subsingleton a b
attribute [local instance] OAI.Yau.Geometry.instFintypeFinOfNatNat_solutions
lemma radialVolumeMatrix_tangent (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ)
    (x v : Fin 5 → ℝ) (hv : x ⬝ᵥ v = 0) :
    radialVolumeMatrix A rho x *ᵥ v = weightedBaseMatrix A rho *ᵥ v := by
  rw [radialVolumeMatrix,add_mulVec,← mulVec_mulVec,replicateRow_mulVec_eq_const,hv]
  simp

lemma radialVolumeMatrix_radial (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    (rho : ℝ) (x : Fin 5 → ℝ) (hx : A *ᵥ x = x) (hn : x ⬝ᵥ x = 1) :
    radialVolumeMatrix A rho x *ᵥ x = x := by
  simp only [radialVolumeMatrix,add_mulVec,weightedBaseMatrix,smul_mulVec,
    radial_fixed_inverse A hA x hx,← mulVec_mulVec,replicateRow_mulVec_eq_const,hn]
  ext i
  simp [mulVec,dotProduct]
  ring

lemma radialVolumeMatrix_det (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (x : Fin 5 → ℝ)
    (hx : A *ᵥ x = x) (hn : x ⬝ᵥ x = 1) :
    (radialVolumeMatrix A rho x).det = rho^4 / A.det := by
  have hh := weightedBaseMatrix_posDef hA hr
  rw [radialVolumeMatrix,det_add_replicateCol_mul_replicateRow (ι := Fin 1)
    (isUnit_iff_ne_zero.mpr hh.det_pos.ne'),weightedBaseMatrix_inverse hA hr]
  rw [Matrix.mul_assoc,← replicateCol_mulVec,smul_mulVec,mulVec_smul,hx,
    replicateRow_mul_replicateCol]
  conv_lhs => arg 2; rw [det_unique]

  simp only [Matrix.add_apply,Matrix.one_apply_eq,Matrix.of_apply,
    dotProduct_smul,hn,smul_eq_mul,mul_one]
  rw [weightedBaseMatrix,Matrix.det_smul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
  simp only [Fintype.card_fin]
  field_simp
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TangentGramDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section

lemma rectangular_congruence_det {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : n ≃ m)
    (R : Matrix m m ℝ) (F : Matrix m n ℝ) :
    (F.transpose * R * F).det = R.det * (F.transpose * F).det := by
  let G := F.submatrix e id
  have h : G.transpose * R.submatrix e e * G = F.transpose * R * F := by
    simp only [G,transpose_submatrix,submatrix_mul_equiv,submatrix_id_id]
  have h0 : G.transpose * G = F.transpose * F := by
    simp only [G,transpose_submatrix,submatrix_mul_equiv,submatrix_id_id]
  rw [← h,← h0]
  simp only [det_mul,det_transpose,det_submatrix_equiv_self]
  ring

lemma augmented_gram_det {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k] [Unique k]
    (R : Matrix m m ℝ) (J : Matrix m n ℝ) (x : m → ℝ)
    (hx : R *ᵥ x = x) (hn : x ⬝ᵥ x = 1) (hJ : J.transpose *ᵥ x = 0) :
    ((fromCols J (replicateCol k x)).transpose * R *
      fromCols J (replicateCol k x)).det = (J.transpose * R * J).det := by
  rw [transpose_fromCols,fromRows_mul,fromRows_mul_fromCols]
  have ht : J.transpose * R * replicateCol k x = 0 := by
    rw [Matrix.mul_assoc,← replicateCol_mulVec,hx,← replicateCol_mulVec,hJ]
    rfl
  have hb : (replicateCol k x).transpose * R * replicateCol k x = 1 := by
    rw [Matrix.mul_assoc,← replicateCol_mulVec,hx]
    ext i j
    simpa [mul_apply,replicateCol,dotProduct,Matrix.one_apply,Subsingleton.elim i j] using hn
  rw [ht,hb,det_fromBlocks_zero₁₂,det_one,mul_one]

lemma tangent_gram_det {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n] [DecidableEq k] [Unique k]
    (e : (n ⊕ k) ≃ m) (R : Matrix m m ℝ) (J : Matrix m n ℝ) (x : m → ℝ)
    (hx : R *ᵥ x = x) (hn : x ⬝ᵥ x = 1) (hJ : J.transpose *ᵥ x = 0) :
    (J.transpose * R * J).det = R.det * (J.transpose * J).det := by
  have h := rectangular_congruence_det e R (fromCols J (replicateCol k x))
  rw [augmented_gram_det R J x hx hn hJ] at h
  have h0 := augmented_gram_det (k := k) (1 : Matrix m m ℝ) J x
    (one_mulVec x) hn hJ
  simp only [Matrix.mul_one] at h0
  rwa [h0] at h

attribute [local instance] OAI.Yau.Geometry.instDecidableEqFinOfNatNat_solutions_1
attribute [local instance] OAI.Yau.Geometry.instFintypeFinOfNatNat_solutions_1
lemma radial_tangent_gram_det (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (x : Fin 5 → ℝ) (J : Matrix (Fin 5) (Fin 4) ℝ)
    (hx : A *ᵥ x = x) (hn : x ⬝ᵥ x = 1) (hJ : J.transpose *ᵥ x = 0) :
    (J.transpose * weightedBaseMatrix A rho * J).det =
      (rho^4 / A.det) * (J.transpose * J).det := by
  have hcol (j : Fin 4) : x ⬝ᵥ (fun i ↦ J i j) = 0 := by
    have h := congrFun hJ j
    simpa only [mulVec,transpose_apply,Pi.zero_apply,dotProduct_comm] using h
  have he : radialVolumeMatrix A rho x * J = weightedBaseMatrix A rho * J := by
    ext i j
    exact congrFun (radialVolumeMatrix_tangent A rho x (fun i ↦ J i j) (hcol j)) i
  have h := tangent_gram_det (finSumFinEquiv : (Fin 4 ⊕ Fin 1) ≃ Fin 5)
    (radialVolumeMatrix A rho x) J x (radialVolumeMatrix_radial A hA rho x hx hn) hn hJ
  rw [radialVolumeMatrix_det A hA hr x hx hn,Matrix.mul_assoc,he,← Matrix.mul_assoc] at h
  exact h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

attribute [local instance] OAI.Yau.Target.instFactEqNatFinrankRealAmbientBaseHAddOfNat_2
lemma sphere_radial_dot (x : Base) :
    (fun i ↦ (x : AmbientBase) i) ⬝ᵥ (fun i ↦ (x : AmbientBase) i) = 1 := by
  have hn := mem_sphere_zero_iff_norm.mp x.property
  have h := real_inner_self_eq_norm_sq (x : AmbientBase)
  rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,hn,one_pow] at h
  exact h

lemma sphereRoundChartMatrix_posDef (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) : (sphereRoundChartMatrix p y).PosDef := by
  simpa [sphereRoundChartMatrix,conjTranspose_eq_transpose_of_trivial] using
    (PosDef.one : (1 : Matrix (Fin 5) (Fin 5) ℝ).PosDef).conjTranspose_mul_mul_same
      (sphereChartFrame_injective p hy)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CircleChartFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
noncomputable section
attribute [local instance] finrank_real_complex_fact'

lemma circleChartDerivative_injective (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    Function.Injective (circleChartDerivative p y) := by
  apply (injective_mvfderiv_subtypeVal_sphere (n := 1) ((extChartAt (𝓡 1) p).symm y)).comp
  have h := (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 1) hy).injective
  rw [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

lemma circleChartFactor_pos (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) : 0 < circleChartFactor p y := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  have he := circleChartDerivative_injective p hy (h.trans (map_zero _).symm)
  exact (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.ne_zero 0 he

lemma circleChartDerivative_inner_basis (p : Circle) (y : CircleModel) (i j : Fin 1) :
    @inner ℝ ℂ _ (circleChartDerivative p y (EuclideanSpace.basisFun (Fin 1) ℝ i))
      (circleChartDerivative p y (EuclideanSpace.basisFun (Fin 1) ℝ j)) =
      circleChartFactor p y := by
  rw [Subsingleton.elim i 0,Subsingleton.elim j 0,real_inner_self_eq_norm_sq]
  rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartFrameSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section
attribute [local instance] finrank_real_complex_fact'

attribute [local instance] OAI.Yau.Target.instFactEqNatFinrankRealAmbientBaseHAddOfNat_3
lemma circleChartDerivative_eq_fderiv (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    circleChartDerivative p y =
      fderiv ℝ ((fun z : Circle ↦ (z : ℂ)) ∘ (extChartAt (𝓡 1) p).symm) y := by
  exact (inverse_chart_comp_derivative _ (contMDiff_coe_sphere (E := ℂ) (n := 1)) p hy).symm

lemma circleChartDerivative_smooth_at (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    ContDiffAt ℝ ∞ (circleChartDerivative p) y := by
  apply (smooth_inverse_chart_derivative _ (contMDiff_coe_sphere (E := ℂ) (n := 1)) p hy).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
  exact circleChartDerivative_eq_fderiv p hz

lemma circleChartFactor_smooth_at (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    ContDiffAt ℝ ∞ (circleChartFactor p) y := by
  have h := (circleChartDerivative_smooth_at p hy).clm_apply
    (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 1) ℝ 0))
  convert! h.inner ℝ h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [real_inner_self_eq_norm_sq]
  rfl

lemma circleChartDensity_smooth_at (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    ContDiffAt ℝ ∞ (fun z ↦ Real.sqrt (circleChartFactor p z)) y :=
  (circleChartFactor_smooth_at p hy).sqrt (circleChartFactor_pos p hy).ne'

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ProductChartPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma product_chart_target (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    y.1 ∈ (extChartAt (𝓡 4) p.1).target ∧ y.2 ∈ (extChartAt (𝓡 1) p.2).target := by
  rw [extChartAt_prod] at hy
  exact hy

lemma product_chart_inverse_derivative (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    mfderiv 𝓘(ℝ,Model) modelWithCorners (extChartAt modelWithCorners p).symm y =
      (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p.1).symm y.1).prodMap
      (mfderiv 𝓘(ℝ,CircleModel) (𝓡 1) (extChartAt (𝓡 1) p.2).symm y.2) := by
  have hb : MDifferentiableAt 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p.1).symm y.1 := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 4) (product_chart_target p hy).1
    rw [ModelWithCorners.range_eq_univ,mdifferentiableWithinAt_univ] at h
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
  have hc : MDifferentiableAt 𝓘(ℝ,CircleModel) (𝓡 1) (extChartAt (𝓡 1) p.2).symm y.2 := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 1) (product_chart_target p hy).2
    rw [ModelWithCorners.range_eq_univ,mdifferentiableWithinAt_univ] at h
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
  rw [show 𝓘(ℝ,Model) = 𝓘(ℝ,BaseModel).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod,
    ← chartedSpaceSelf_prod]
  convert! mfderiv_prodMap hb hc using 1
  all_goals try with_reducible_and_instances rfl

lemma product_chart_embedding_derivative (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (v : Model) :
    mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding ((extChartAt modelWithCorners p).symm y)
      (mfderiv 𝓘(ℝ,Model) modelWithCorners (extChartAt modelWithCorners p).symm y v) =
      (sphereChartDerivative p.1 y.1 v.1,circleChartDerivative p.2 y.2 v.2) := by
  rw [targetEmbedding_derivative,product_chart_inverse_derivative p hy]
  rfl

lemma sphereWeightedChartMatrix_apply (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ)
    (p : Base) (y : BaseModel) (i j : Fin 4) :
    sphereWeightedChartMatrix A rho p y i j =
      ambientMatrixForm (weightedBaseMatrix A rho)
        (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))
        (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ j)) := by
  rw [ambientMatrixForm_dot]
  unfold sphereWeightedChartMatrix
  rw [Matrix.mul_assoc]
  simp only [mul_apply,transpose_apply,
    sphereChartFrame_apply,mulVec,dotProduct]

lemma independentAmbientMetric_productMatrix
    (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y =
      fromBlocks (sphereWeightedChartMatrix (A ((extChartAt (𝓡 4) p.1).symm y.1))
        (rho ((extChartAt (𝓡 4) p.1).symm y.1)) p.1 y.1) 0 0
        (Matrix.of fun _ _ : Fin 1 ↦
          (ambientCircleWeight (A ((extChartAt (𝓡 4) p.1).symm y.1))
            (rho ((extChartAt (𝓡 4) p.1).symm y.1)))^2 * circleChartFactor p.2 y.2) := by
  ext i j
  change warpedAmbientForm _ _
    (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding _
      (mfderiv 𝓘(ℝ,Model) modelWithCorners _ y (productFrame i)))
    (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding _
      (mfderiv 𝓘(ℝ,Model) modelWithCorners _ y (productFrame j))) = _
  rw [product_chart_embedding_derivative p hy,product_chart_embedding_derivative p hy,
    warpedAmbientForm_apply]
  have hpnt : ((extChartAt modelWithCorners p).symm y).1 =
      (extChartAt (𝓡 4) p.1).symm y.1 := by
    rw [extChartAt_prod]
    rfl
  rw [hpnt]
  cases i <;> cases j <;>
    simp only [productFrame,Module.Basis.prod_apply_inl_fst,Module.Basis.prod_apply_inl_snd,
      Module.Basis.prod_apply_inr_fst,Module.Basis.prod_apply_inr_snd,
      OrthonormalBasis.coe_toBasis,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.of_apply,
      map_zero,inner_zero_left,inner_zero_right,mul_zero,zero_add,add_zero,
      sphereWeightedChartMatrix_apply,circleChartDerivative_inner_basis]
  all_goals simp

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalMatrixSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype n] [DecidableEq n] in
lemma matrix_gram_smooth_at (J : E → Matrix m n ℝ) {x : E}
    (hJ : ∀ i j, ContDiffAt ℝ ∞ (fun z ↦ J z i j) x) (i j : n) :
    ContDiffAt ℝ ∞ (fun z ↦ ((J z).transpose * J z) i j) x := by
  simp only [mul_apply,transpose_apply]
  exact ContDiffAt.sum (fun k _ ↦ (hJ k i).mul (hJ k j))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_BaseChartFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma roundChartDensity_smooth_at (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (roundChartDensity p) z := by
  exact (matrix_det_smooth_at _ (matrix_gram_smooth_at _ (sphereChartFrame_smooth_at p hz))).sqrt
    (sphereRoundChartMatrix_posDef p hz).det_pos.ne'

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)

include hr in
lemma baseChartDensity_smooth_at (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (baseChartDensity rho p) z :=
  (smooth_inverse_chart_comp rho hr p hz).mul (roundChartDensity_smooth_at p hz)

include hA hp hr hrp in
lemma baseChartFlux_smooth_at (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i : Fin 4) :
    ContDiffAt ℝ ∞ (baseChartFlux A rho f p i) z := by
  apply (baseChartDensity_smooth_at rho hr p hz).mul
  apply ContDiffAt.sum
  intro j _
  exact (baseChartMetric_inverse_smooth_at A rho hA hp hr hrp p hz i j).mul
    ((smooth_inverse_chart_derivative f hf p hz).clm_apply contDiffAt_const)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CircleInvariantDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma circleLift_chart (f : Base → ℝ) (p : Manifold5) :
    circleLift f ∘ (extChartAt modelWithCorners p).symm =
      (f ∘ (extChartAt (𝓡 4) p.1).symm) ∘ Prod.fst := by
  rw [extChartAt_prod]
  rfl

lemma circleLift_chart_derivative (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    fderiv ℝ (circleLift f ∘ (extChartAt modelWithCorners p).symm) y =
      (fderiv ℝ (f ∘ (extChartAt (𝓡 4) p.1).symm) y.1).comp
        (ContinuousLinearMap.fst ℝ BaseModel CircleModel) := by
  rw [circleLift_chart,fderiv_comp y
    ((smooth_inverse_chart_comp f hf p.1 (product_chart_target p hy).1).differentiableAt (by simp))
    differentiableAt_fst,fderiv_fst]

lemma circleLift_product_covector (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    fderiv ℝ (circleLift f ∘ (extChartAt modelWithCorners p).symm) y (productFrame i) =
      Sum.elim (fun j ↦ fderiv ℝ (f ∘ (extChartAt (𝓡 4) p.1).symm) y.1
        (EuclideanSpace.basisFun (Fin 4) ℝ j)) (fun _ ↦ 0) i := by
  rw [circleLift_chart_derivative f hf p hy]
  cases i <;> simp [productFrame]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_BasisDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma constant_matrix_flux_derivative (D : Matrix n n ℝ) (F : n → E → ℝ)
    {x : E} (hF : ∀ a, DifferentiableAt ℝ (F a) x) (i : n) (v : E) :
    fderiv ℝ (fun y ↦ ∑ a, D i a * F a y) x v =
      ∑ a, D i a * fderiv ℝ (F a) x v := by
  rw [show (fun y ↦ ∑ a, D i a * F a y) =
    ∑ a, (fun y ↦ D i a * F a y) by ext y; simp]
  rw [fderiv_sum (fun a _ ↦ (hF a).const_mul (D i a))]
  simp only [_root_.sum_apply,fderiv_const_mul (hF _) _,
    _root_.smul_apply,smul_eq_mul]

omit [DecidableEq n] in
lemma basis_divergence_change (b c : Module.Basis n ℝ E) (F : n → E → ℝ)
    {x : E} (hF : ∀ a, DifferentiableAt ℝ (F a) x) :
    ∑ i, fderiv ℝ (fun y ↦ ∑ a, c.toMatrix b i a * F a y) x (c i) =
      ∑ a, fderiv ℝ (F a) x (b a) := by
  simp_rw [constant_matrix_flux_derivative _ F hF]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [← c.sum_toMatrix_smul_self b a]
  simp only [map_sum,map_smul,smul_eq_mul]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeparatedCircleDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n m : Type*} [Fintype n] [Fintype m]

lemma separated_factor_horizontal_derivative (a : E → ℝ) (k : F → ℝ)
    {x : E} {t : F} (ha : DifferentiableAt ℝ a x) (hk : DifferentiableAt ℝ k t) (v : E) :
    fderiv ℝ (fun y : E × F ↦ k y.2 * a y.1) (x,t) (v,0) =
      k t * fderiv ℝ a x v := by
  have ha' : DifferentiableAt ℝ (fun y : E × F ↦ a y.1) (x,t) :=
    ha.comp (x,t) differentiableAt_fst
  have hk' : DifferentiableAt ℝ (fun y : E × F ↦ k y.2) (x,t) :=
    hk.comp (x,t) differentiableAt_snd
  rw [show (fun y : E × F ↦ k y.2 * a y.1) =
    (fun y : E × F ↦ k y.2) * (fun y : E × F ↦ a y.1) by rfl, fderiv_mul hk' ha']
  have hd1 : fderiv ℝ (fun y : E × F ↦ a y.1) (x,t) =
      (fderiv ℝ a x).comp (ContinuousLinearMap.fst ℝ E F) := by
    rw [show (fun y : E × F ↦ a y.1) = a ∘ Prod.fst from rfl]
    convert! fderiv_comp (𝕜 := ℝ) (f := Prod.fst) (g := a) (x,t) ha differentiableAt_fst using 1
    all_goals try with_reducible_and_instances rfl
    simp only [fderiv_fst]
  have hd2 : fderiv ℝ (fun y : E × F ↦ k y.2) (x,t) =
      (fderiv ℝ k t).comp (ContinuousLinearMap.snd ℝ E F) := by
    rw [show (fun y : E × F ↦ k y.2) = k ∘ Prod.snd from rfl]
    convert! fderiv_comp (𝕜 := ℝ) (f := Prod.snd) (g := k) (x,t) hk differentiableAt_snd using 1
    all_goals try with_reducible_and_instances rfl
    simp only [fderiv_snd]
  rw [hd1,hd2]
  simp

lemma separated_factor_divergence (b : Module.Basis n ℝ E) (c : Module.Basis m ℝ F)
    (a : n → E → ℝ) (k : F → ℝ) {x : E} {t : F}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hk : DifferentiableAt ℝ k t) :
    ∑ i : n ⊕ m, fderiv ℝ
      (fun y : E × F ↦ Sum.elim (fun j ↦ k y.2 * a j y.1) (fun _ ↦ 0) i)
      (x,t) ((b.prod c) i) = k t * ∑ i, fderiv ℝ (a i) x (b i) := by
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  have hb (i : n) : (b.prod c) (Sum.inl i) = (b i,0) := by
    ext <;> simp
  simp_rw [hb]
  simp only [fderiv_fun_const,Pi.zero_apply,zero_apply,Finset.sum_const_zero,add_zero]
  simp_rw [separated_factor_horizontal_derivative _ k (ha _) hk]
  rw [Finset.mul_sum]

lemma separated_density_cancellation (b : Module.Basis n ℝ E) (c : Module.Basis m ℝ F)
    (a : n → E → ℝ) (k : F → ℝ) (d : ℝ) {x : E} {t : F}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hk : DifferentiableAt ℝ k t) (hkp : k t ≠ 0) :
    (d*k t)⁻¹ * ∑ i : n ⊕ m, fderiv ℝ
      (fun y : E × F ↦ Sum.elim (fun j ↦ k y.2 * a j y.1) (fun _ ↦ 0) i)
      (x,t) ((b.prod c) i) = d⁻¹ * ∑ i, fderiv ℝ (a i) x (b i) := by
  rw [separated_factor_divergence b c a k ha hk,_root_.mul_inv_rev]
  field_simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ProductChartVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))

include hrad

lemma independentAmbientMetric_product_det (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y).det =
      (rho ((extChartAt (𝓡 4) p.1).symm y.1))^2 *
        (sphereRoundChartMatrix p.1 y.1).det * circleChartFactor p.2 y.2 := by
  rw [independentAmbientMetric_productMatrix A rho hA hp hr hrp p hy,
    det_fromBlocks_zero₂₁,det_fin_one]
  dsimp only [Matrix.of_apply]
  have he := radial_tangent_gram_det _ (hp _) (hrp ((extChartAt (𝓡 4) p.1).symm y.1)) _ (sphereChartFrame p.1 y.1)
    (hrad _) (sphere_radial_dot _) (sphereChartFrame_orthogonal p.1 y.1)
  change (sphereWeightedChartMatrix _ _ _ _).det = _ at he
  rw [he,ambientCircleWeight,div_pow,Real.sq_sqrt (hp _).det_pos.le]
  have halg (r d H k : ℝ) (hr0 : r ≠ 0) (hd0 : d ≠ 0) :
      (r^4/d)*H*(d/r^2*k) = r^2*H*k := by
    field_simp
  convert! halg _ _ _ _ (hrp ((extChartAt (𝓡 4) p.1).symm y.1)).ne'
    (hp ((extChartAt (𝓡 4) p.1).symm y.1)).det_pos.ne' using 1
  all_goals try with_reducible_and_instances rfl

lemma independentAmbientMetric_product_volume (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    Real.sqrt (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y).det =
      rho ((extChartAt (𝓡 4) p.1).symm y.1) *
        Real.sqrt (sphereRoundChartMatrix p.1 y.1).det * Real.sqrt (circleChartFactor p.2 y.2) := by
  rw [independentAmbientMetric_product_det A rho hA hp hr hrp hrad p hy,
    Real.sqrt_mul (mul_nonneg (sq_nonneg _) (sphereRoundChartMatrix_posDef p.1 (product_chart_target p hy).1).det_pos.le),
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (hrp _).le]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ProductChartFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma positive_circle_block_inverse {H : Matrix (Fin 4) (Fin 4) ℝ} (hH : H.PosDef)
    {d : ℝ} (hd : 0 < d) :
    (fromBlocks H 0 0 (Matrix.of (fun _ _ : Fin 1 ↦ d)))⁻¹ =
      fromBlocks H⁻¹ 0 0 (Matrix.of (fun _ _ : Fin 1 ↦ d))⁻¹ := by
  have hD : IsUnit (Matrix.of (fun _ _ : Fin 1 ↦ d)) := by
    rw [Matrix.isUnit_iff_isUnit_det,det_fin_one]
    exact isUnit_iff_ne_zero.mpr hd.ne'
  rw [inv_fromBlocks_zero₂₁_of_isUnit_iff H 0 _ (iff_of_true hH.isUnit hD)]
  simp

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)

lemma independentAmbientMetric_product_inverse (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y)⁻¹ =
      fromBlocks (sphereWeightedChartMatrix (A ((extChartAt (𝓡 4) p.1).symm y.1))
        (rho ((extChartAt (𝓡 4) p.1).symm y.1)) p.1 y.1)⁻¹ 0 0
        (Matrix.of fun _ _ : Fin 1 ↦
          (ambientCircleWeight (A ((extChartAt (𝓡 4) p.1).symm y.1))
            (rho ((extChartAt (𝓡 4) p.1).symm y.1)))^2 * circleChartFactor p.2 y.2)⁻¹ := by
  rw [independentAmbientMetric_productMatrix A rho hA hp hr hrp p hy]
  apply positive_circle_block_inverse
    (sphereWeightedChartMatrix_posDef _ (hp _) (hrp _) p.1 (product_chart_target p hy).1)
  exact mul_pos (sq_pos_of_pos (ambientCircleWeight_pos _ (hp _) (hrp _)))
    (circleChartFactor_pos p.2 (product_chart_target p hy).2)

lemma independentAmbientMetric_product_flux
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))
    (p : Manifold5) {y : Model} (hy : y ∈ (extChartAt modelWithCorners p).target)
    (v : Fin 4 → ℝ) (i : Fin 4 ⊕ Fin 1) :
    Real.sqrt (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y).det *
      ∑ j, (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y)⁻¹ i j *
        Sum.elim v (fun _ ↦ 0) j =
    Sum.elim (fun a ↦ Real.sqrt (circleChartFactor p.2 y.2) *
      (rho ((extChartAt (𝓡 4) p.1).symm y.1) * Real.sqrt (sphereRoundChartMatrix p.1 y.1).det *
        ∑ b, (sphereWeightedChartMatrix (A ((extChartAt (𝓡 4) p.1).symm y.1))
          (rho ((extChartAt (𝓡 4) p.1).symm y.1)) p.1 y.1)⁻¹ a b * v b)) (fun _ ↦ 0) i := by
  rw [independentAmbientMetric_product_volume A rho hA hp hr hrp hrad p hy,
    independentAmbientMetric_product_inverse A rho hA hp hr hrp p hy]
  cases i with
  | inl a =>
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,fromBlocks_apply₁₁,
      fromBlocks_apply₁₂,mul_zero,Finset.sum_const_zero,add_zero]
    ring
  | inr a => simp [Fintype.sum_sum_type,Matrix.fromBlocks]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_BasisLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]

lemma basis_change_det_ne_zero (b c : Module.Basis n ℝ E) : (b.toMatrix c).det ≠ 0 := by
  have h := congrArg Matrix.det (b.toMatrix_mul_toMatrix_flip c)
  rw [det_mul,det_one] at h
  exact (mul_ne_zero_iff.mp (h ▸ one_ne_zero)).1

lemma basis_change_inverse (b c : Module.Basis n ℝ E) : (b.toMatrix c)⁻¹ = c.toMatrix b :=
  inv_eq_left_inv (c.toMatrix_mul_toMatrix_flip b)

lemma basisMetricMatrix_change (b c : Module.Basis n ℝ E) (B : LinearMap.BilinForm ℝ E) :
    basisMetricMatrix c B = (b.toMatrix c).transpose * basisMetricMatrix b B * b.toMatrix c :=
  (LinearMap.toMatrix₂_mul_basis_toMatrix b b c c B).symm

lemma basisMetricMatrix_volume_change (b c : Module.Basis n ℝ E) (B : LinearMap.BilinForm ℝ E) :
    Real.sqrt (basisMetricMatrix c B).det =
      |(b.toMatrix c).det| * Real.sqrt (basisMetricMatrix b B).det := by
  rw [basisMetricMatrix_change,det_mul,det_mul,det_transpose]
  rw [show (b.toMatrix c).det * (basisMetricMatrix b B).det * (b.toMatrix c).det =
    (b.toMatrix c).det^2 * (basisMetricMatrix b B).det by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]

omit [DecidableEq n] in
lemma basis_derivative_vector (b c : Module.Basis n ℝ E) (f : E → ℝ) (y : E) :
    (fun j ↦ fderiv ℝ f y (c j)) = (b.toMatrix c).transpose *ᵥ (fun a ↦ fderiv ℝ f y (b a)) := by
  ext j
  conv_lhs => rw [← b.sum_toMatrix_smul_self c j]
  simp only [map_sum,map_smul,smul_eq_mul,mulVec,dotProduct,transpose_apply]

lemma basis_inverse_derivative_vector (b c : Module.Basis n ℝ E)
    (B : LinearMap.BilinForm ℝ E) (f : E → ℝ) (y : E) :
    (basisMetricMatrix c B)⁻¹ *ᵥ (fun j ↦ fderiv ℝ f y (c j)) =
      c.toMatrix b *ᵥ ((basisMetricMatrix b B)⁻¹ *ᵥ (fun a ↦ fderiv ℝ f y (b a))) := by
  rw [basis_derivative_vector b c f y,mulVec_mulVec,basisMetricMatrix_change b c,
    Matrix.mul_inv_rev,Matrix.mul_inv_rev]
  have hc : IsUnit ((b.toMatrix c).transpose.det) := by
    rw [det_transpose]
    exact isUnit_iff_ne_zero.mpr (basis_change_det_ne_zero b c)
  rw [Matrix.mul_assoc,Matrix.mul_assoc,nonsing_inv_mul _ hc,Matrix.mul_one,
    basis_change_inverse, ← mulVec_mulVec]

lemma basisMetricFlux_change (b c : Module.Basis n ℝ E) (B : E → LinearMap.BilinForm ℝ E)
    (f : E → ℝ) (i : n) (y : E) :
    basisMetricFlux c B f i y = |(b.toMatrix c).det| *
      ∑ a, c.toMatrix b i a * basisMetricFlux b B f a y := by
  have h := congrFun (basis_inverse_derivative_vector b c (B y) f y) i
  change (∑ j, _ * _) = _ at h
  rw [basisMetricFlux,basisMetricMatrix_volume_change b c,h]
  simp only [mulVec,dotProduct,basisMetricFlux,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma basisMetricLaplacian_change (b c : Module.Basis n ℝ E) (B : E → LinearMap.BilinForm ℝ E)
    (f : E → ℝ) {y : E} (hF : ∀ i, DifferentiableAt ℝ (basisMetricFlux b B f i) y) :
    basisMetricLaplacian c B f y = basisMetricLaplacian b B f y := by
  have hfun (i : n) : basisMetricFlux c B f i = fun z ↦ |(b.toMatrix c).det| *
      ∑ a, c.toMatrix b i a * basisMetricFlux b B f a z := by
    funext z; exact basisMetricFlux_change b c B f i z
  unfold basisMetricLaplacian
  simp_rw [hfun]
  have hd (i : n) : DifferentiableAt ℝ
      (fun z ↦ ∑ a, c.toMatrix b i a * basisMetricFlux b B f a z) y :=
    by
      convert! (DifferentiableAt.sum (u := Finset.univ)
        (fun a _ ↦ (hF a).const_mul (c.toMatrix b i a))) using 1
      all_goals try with_reducible_and_instances rfl
      ext z; simp
  simp_rw [fderiv_const_mul (hd _) _,_root_.smul_apply,smul_eq_mul]
  rw [← Finset.mul_sum,basis_divergence_change b c _ hF,basisMetricMatrix_volume_change b c]
  have hn := (abs_pos.mpr (basis_change_det_ne_zero b c)).ne'
  rw [_root_.mul_inv_rev]
  field_simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_BasisLaplacianReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma basisMetricMatrix_reindex (b : Module.Basis n ℝ E) (e : n ≃ m)
    (B : LinearMap.BilinForm ℝ E) :
    basisMetricMatrix (b.reindex e) B = (basisMetricMatrix b B).submatrix e.symm e.symm := by
  ext i j
  simp [basisMetricMatrix,LinearMap.toMatrix₂_apply]

lemma basisMetricFlux_reindex (b : Module.Basis n ℝ E) (e : n ≃ m)
    (B : E → LinearMap.BilinForm ℝ E) (f : E → ℝ) (i : m) (y : E) :
    basisMetricFlux (b.reindex e) B f i y = basisMetricFlux b B f (e.symm i) y := by
  simp only [basisMetricFlux,basisMetricMatrix_reindex,det_submatrix_equiv_self,
    inv_submatrix_equiv,submatrix_apply,Module.Basis.reindex_apply]
  congr 1
  exact e.symm.sum_comp (fun j : n ↦ (basisMetricMatrix b (B y))⁻¹ (e.symm i) j *
    fderiv ℝ f y (b j))

lemma basisMetricLaplacian_reindex (b : Module.Basis n ℝ E) (e : n ≃ m)
    (B : E → LinearMap.BilinForm ℝ E) (f : E → ℝ) (y : E) :
    basisMetricLaplacian (b.reindex e) B f y = basisMetricLaplacian b B f y := by
  have hf (i : m) : basisMetricFlux (b.reindex e) B f i = basisMetricFlux b B f (e.symm i) := by
    funext z; exact basisMetricFlux_reindex b e B f i z
  simp only [basisMetricLaplacian,basisMetricMatrix_reindex,det_submatrix_equiv_self,hf,
    Module.Basis.reindex_apply]
  congr 1
  exact e.symm.sum_comp (fun j : n ↦ fderiv ℝ (basisMetricFlux b B f j) y (b j))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TargetLaplacianBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

lemma basisMetricMatrix_target (g : SmoothMetric) (c : PartialEquiv Manifold5 Model) (y : Model) :
    basisMetricMatrix frame (chartBilinearForm g c y) = metricMatrix g c y := by
  ext i j
  simp only [basisMetricMatrix,LinearMap.toMatrix₂_apply,chartBilinearForm,metricMatrix]
  rfl

lemma basisMetricMatrix_product (g : SmoothMetric) (p : Manifold5) (y : Model) :
    basisMetricMatrix productFrame (chartBilinearForm g (extChartAt modelWithCorners p) y) =
      productMetricMatrix g p y := by
  ext i j
  simp only [basisMetricMatrix,LinearMap.toMatrix₂_apply,chartBilinearForm,productMetricMatrix]
  rfl

lemma chartLaplacian_basisMetricLaplacian (g : SmoothMetric)
    (c : PartialEquiv Manifold5 Model) (u : Manifold5 → ℝ) (y : Model) :
    chartLaplacian g c u y = basisMetricLaplacian frame (chartBilinearForm g c) (u ∘ c.symm) y := by
  simp only [basisMetricLaplacian,basisMetricMatrix_target,
    chartLaplacian,volumeFactor]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  funext z
  simp only [basisMetricFlux,basisMetricMatrix_target]

lemma chartLaplacian_product_basis (g : SmoothMetric) (p : Manifold5)
    (u : Manifold5 → ℝ) {y : Model}
    (hF : ∀ i, DifferentiableAt ℝ
      (basisMetricFlux productFrame (chartBilinearForm g (extChartAt modelWithCorners p))
        (u ∘ (extChartAt modelWithCorners p).symm) i) y) :
    chartLaplacian g (extChartAt modelWithCorners p) u y =
      basisMetricLaplacian productFrame (chartBilinearForm g (extChartAt modelWithCorners p))
        (u ∘ (extChartAt modelWithCorners p).symm) y := by
  rw [chartLaplacian_basisMetricLaplacian]
  have hr (i : Index) :
      basisMetricFlux indexedProductFrame (chartBilinearForm g (extChartAt modelWithCorners p))
          (u ∘ (extChartAt modelWithCorners p).symm) i =
      basisMetricFlux productFrame (chartBilinearForm g (extChartAt modelWithCorners p))
          (u ∘ (extChartAt modelWithCorners p).symm) (productIndexEquiv.symm i) := by
    funext z
    exact basisMetricFlux_reindex productFrame productIndexEquiv _ _ i z
  rw [basisMetricLaplacian_change indexedProductFrame frame _ _ (fun i ↦ by rw [hr]; exact hF _)]
  exact basisMetricLaplacian_reindex productFrame productIndexEquiv _ _ y

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ProductFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section
variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f)

include hrad hf

lemma circleLift_actual_product_flux (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    basisMetricFlux productFrame
      (chartBilinearForm (independentAmbientMetric A rho hA hp hr hrp) (extChartAt modelWithCorners p))
      (circleLift f ∘ (extChartAt modelWithCorners p).symm) i y =
    Sum.elim (fun j ↦ Real.sqrt (circleChartFactor p.2 y.2) * baseChartFlux A rho f p.1 j y.1)
      (fun _ ↦ 0) i := by
  unfold basisMetricFlux
  simp only [basisMetricMatrix_product,circleLift_product_covector f hf p hy]
  exact independentAmbientMetric_product_flux A rho hA hp hr hrp hrad p hy _ i

lemma circleLift_product_flux_eventually (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    basisMetricFlux productFrame
      (chartBilinearForm (independentAmbientMetric A rho hA hp hr hrp) (extChartAt modelWithCorners p))
      (circleLift f ∘ (extChartAt modelWithCorners p).symm) i =ᶠ[𝓝 y]
    (fun w ↦ Sum.elim (fun j ↦ Real.sqrt (circleChartFactor p.2 w.2) * baseChartFlux A rho f p.1 j w.1)
      (fun _ ↦ 0) i) := by
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with w hw
  exact circleLift_actual_product_flux A rho hA hp hr hrp hrad f hf p hw i

lemma circleLift_product_flux_smooth_at (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    ContDiffAt ℝ ∞ (basisMetricFlux productFrame
      (chartBilinearForm (independentAmbientMetric A rho hA hp hr hrp) (extChartAt modelWithCorners p))
      (circleLift f ∘ (extChartAt modelWithCorners p).symm) i) y := by
  have hs : ContDiffAt ℝ ∞
      (fun w : Model ↦ Sum.elim (fun j ↦ Real.sqrt (circleChartFactor p.2 w.2) *
        baseChartFlux A rho f p.1 j w.1) (fun _ ↦ 0) i) y := by
    cases i with
    | inl j =>
      exact ((circleChartDensity_smooth_at p.2 (product_chart_target p hy).2).comp y contDiffAt_snd).mul
        ((baseChartFlux_smooth_at A rho hA hp hr hrp f hf p.1 (product_chart_target p hy).1 j).comp y contDiffAt_fst)
    | inr j => exact contDiffAt_const
  exact hs.congr_of_eventuallyEq
    (circleLift_product_flux_eventually A rho hA hp hr hrp hrad f hf p hy i)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CircleLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section
variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f)
include hrad hf

lemma independentAmbientMetric_circle_laplacian_oai (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    chartLaplacian (independentAmbientMetric A rho hA hp hr hrp)
      (extChartAt modelWithCorners p) (circleLift f) y =
    (baseChartDensity rho p.1 y.1)⁻¹ * ∑ i,
      fderiv ℝ (baseChartFlux A rho f p.1 i) y.1 (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  rw [chartLaplacian_product_basis _ p _ (fun i ↦
    (circleLift_product_flux_smooth_at A rho hA hp hr hrp hrad f hf p hy i).differentiableAt (by simp))]
  unfold basisMetricLaplacian
  rw [basisMetricMatrix_product,independentAmbientMetric_product_volume A rho hA hp hr hrp hrad p hy]
  have hd (i : Fin 4 ⊕ Fin 1) :=
    (circleLift_product_flux_eventually A rho hA hp hr hrp hrad f hf p hy i).fderiv_eq (𝕜 := ℝ)
  simp_rw [hd]
  exact separated_density_cancellation (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis (baseChartFlux A rho f p.1)
    (fun t ↦ Real.sqrt (circleChartFactor p.2 t)) (baseChartDensity rho p.1 y.1)
    (fun i ↦ (baseChartFlux_smooth_at A rho hA hp hr hrp f hf p.1
      (product_chart_target p hy).1 i).differentiableAt (by simp))
    ((circleChartDensity_smooth_at p.2 (product_chart_target p hy).2).differentiableAt (by simp))
    (Real.sqrt_pos.mpr (circleChartFactor_pos p.2 (product_chart_target p hy).2)).ne'

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.independentAmbientMetric_circle_laplacian_oai := @OAI.Yau.Target.independentAmbientMetric_circle_laplacian_oai
