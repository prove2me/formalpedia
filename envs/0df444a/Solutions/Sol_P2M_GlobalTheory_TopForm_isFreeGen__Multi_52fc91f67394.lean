-- Prove2me | solution 1 for P2M_GlobalTheory_TopForm_isFreeGen__Multi_52fc91f67394
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:14.933006+00:00
-- url     : https://prove2.me/submissions/158363a9-3e77-4cb3-aa11-af5aca361299

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
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
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
namespace GlobalTheory.TopForm
theorem _root_.solution {D : ℕ} (b : Module.Basis (Fin D) A M) :
    IsFreeGen A (exteriorPower.ιMulti A D b) := by
  have key : (LinearMap.toSpanSingleton A _ (exteriorPower.ιMulti A D b)) ∘ₗ
      exteriorPower.alternatingMapLinearEquiv b.det = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    refine Module.Basis.ext_alternating b fun v hv => ?_
    have hb : Function.Bijective v := Finite.injective_iff_bijective.mp hv
    let σ : Equiv.Perm (Fin D) := Equiv.ofBijective v hb
    have e1 : (fun i => b (v i)) = b ∘ σ := rfl
    rw [e1, AlternatingMap.map_perm, AlternatingMap.map_perm]
    simp [Module.Basis.det_self]
  refine ⟨fun a a' h => ?_, fun x => ⟨_, LinearMap.congr_fun key x⟩⟩
  simpa [Module.Basis.det_self] using congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h
end GlobalTheory.TopForm
