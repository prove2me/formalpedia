-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_areaJacobian_coneMapE_d9a776937d95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:08.651085+00:00
-- url     : https://prove2.me/submissions/3de39e45-fcde-4e2f-8bf3-af8691fb65b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMapAreaOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_gramVol_eq_967d5336b167
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_fderiv_coneMapE_single_5ae304af17b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_norm_eq_re_of_nonneg_81519d3969bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_areaJacobian_restrictScalars_31766ed81e91
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_det_adjoint_comp_cac87e9cc559


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal NNReal ComplexOrder
open GroundTheory.Heights₂.Heights.ConeMapAreaFormula
namespace GroundTheory.Heights₂.Heights.ConeMapAreaFormula
theorem _root_.solution {e n : ℕ} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {p : EuclideanSpace ℂ (Fin (e + 1))} (hv : DifferentiableAt ℂ v (tailL e p)) :
    areaJacobian ((fderiv ℂ (coneMapE v) p : EuclideanSpace ℂ (Fin (e + 1)) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) = ‖p 0‖ ^ (2 * e) * gramVol v (tailL e p) := by
  set S : EuclideanSpace ℂ (Fin (e + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    ↑(fderiv ℂ (coneMapE v) p)
  rw [FrameJacobianSumAlt.areaJacobian_restrictScalars, FrameJacobianSumAlt.det_adjoint_comp]
  obtain ⟨c, hcdef⟩ : ∃ c : Fin (e + 1) → ℂ, c = Fin.cons 1 (fun _ => p 0) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = gramVecs v (tailL e p) := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ,
      G = Matrix.of fun a b => ∑ i, star (w a i) * w b i := ⟨_, rfl⟩
  have hM : (Matrix.of fun i j : Fin (e + 1) => inner ℂ (S (EuclideanSpace.basisFun (Fin (e + 1)) ℂ i))
      (S (EuclideanSpace.basisFun (Fin (e + 1)) ℂ j))) =
      Matrix.diagonal (fun a => star (c a)) * G * Matrix.diagonal c := by
    ext a b
    simp only [S, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
      fderiv_coneMapE_single hv, inner_smul_left, inner_smul_right, Matrix.of_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal, hGdef, PiLp.inner_apply,
      RCLike.inner_apply, Complex.star_def, hcdef, hw]
    rw [Finset.sum_congr rfl fun x _ => mul_comm (gramVecs v (tailL e p) b x) _]
    ring
  have hG : G = Matrix.conjTranspose (Matrix.of fun i a => w a i) * Matrix.of fun i a => w a i := by
    ext a b
    simp [hGdef, Matrix.mul_apply]
  have hpsd : 0 ≤ G.det := by
    rw [hG]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg
  have hc : ∏ a, c a = p 0 ^ e := by
    simp [hcdef, Fin.prod_univ_succ]
  have hcs : ∏ a, star (c a) = star (p 0) ^ e := by
    simp [hcdef, Fin.prod_univ_succ]
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hc, hcs,
    norm_mul, norm_mul, norm_pow, norm_pow, norm_star, gramVol_eq, ← hw, ← hGdef, norm_eq_re_of_nonneg hpsd]
  ring
end GroundTheory.Heights₂.Heights.ConeMapAreaFormula
