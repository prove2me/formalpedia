-- Prove2me | solution 1 for UpperTheory.rootOfUnity_galois_action_CMDatum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:04:53.91565+00:00
-- url     : https://prove2.me/submissions/fef8e47b-e111-4cb5-ac71-6deac8e26dfb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcEqOfPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_RootOfUnityGaloisActionCMDatum
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_HC_Der_kc_conj_mul_self
import Theorems.Thm_Formalism_HC_Der_kc_iod_fix
import Theorems.Thm_Formalism_HC_Frame_cc_mul_iod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HC
namespace UpperTheory
theorem _root_.solution :
    ∀ (φ : Frame) (H : HostAx φ) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) →
      H.gal.symm φ.iod z = z ∧ H.conj z = z⁻¹ ∧ H.gal.symm φ.sg z = z⁻¹ := by
  intro φ H z hz
  have C : HostCore H.toHostRaw := { H.der with }
  have h1 : H.gal.symm φ.iod z = z :=
    Der.kc_iod_fix H.toHostRaw C _ (H.gal.apply_symm_apply _) z hz
  have h2 : H.conj z = z⁻¹ :=
    eq_inv_of_mul_eq_one_right (Der.kc_conj_mul_self H.toHostRaw C z hz)
  refine ⟨h1, h2, ?_⟩
  rw [← φ.cc_mul_iod, map_mul, AlgEquiv.mul_apply, h1]
  exact h2
end UpperTheory
