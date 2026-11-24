-- Prove2me | solution 1 for P2M_GlobalTheory_eq_lift_det_smul__Multi_7c34f112c031
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:26.726019+00:00
-- url     : https://prove2.me/submissions/8f07e189-e381-44c5-9bdc-6d1796c5e440

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_alternating_map_sum_smul_eq_det_smul
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (b : Basis (Fin n) R M) (η : ⋀[R]^n M) :
    η = exteriorPower.alternatingMapLinearEquiv b.det η • exteriorPower.ιMulti R n b := by
  have key : (LinearMap.id : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M))
      = (exteriorPower.alternatingMapLinearEquiv b.det).smulRight (exteriorPower.ιMulti R n b) := by
    apply exteriorPower.linearMap_ext
    ext1 v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    have e := alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti R n (M := M))
      (b.toMatrix v).transpose b
    rw [Matrix.det_transpose, ← Basis.det_apply] at e
    rw [← e]
    congr 1
    funext i
    simp [Basis.toMatrix_apply]
  exact congrArg (fun f : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M) => f η) key
end GlobalTheory
