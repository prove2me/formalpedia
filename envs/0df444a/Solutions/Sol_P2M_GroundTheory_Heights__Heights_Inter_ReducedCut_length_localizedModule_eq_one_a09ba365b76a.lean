-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_length_localizedModule_eq_one_a09ba365b76a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:14:55.377808+00:00
-- url     : https://prove2.me/submissions/3dfb16f4-2599-4bb1-8046-d79533815d7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsReducedCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PReducedCutLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_localMult_eq_one_of_isRadical_c91ebf588e5e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Inter.ReducedCut
open IsLocalRing
namespace GroundTheory.Heights₂.Heights.Inter.ReducedCut
theorem _root_.solution {B : Type*} [CommRing B] (hB : (⊥ : Ideal B).IsRadical)
    (p : Ideal B) [p.IsPrime] (hp : p ∈ (⊥ : Ideal B).minimalPrimes) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl B) = 1 := by
  have h1 := localMult_eq_one_of_isRadical hB hp
  unfold localMult at h1
  rw [dif_pos ‹p.IsPrime›, Ideal.map_bot] at h1
  have h2 : Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ (⊥ : Ideal (Localization.AtPrime p))) = 1 := by
    have hne : Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ (⊥ : Ideal (Localization.AtPrime p))) ≠ ⊤ :=
      fun h => by rw [h] at h1; simp at h1
    rw [← ENat.natCast_toNat hne, h1]
    rfl
  have := IsLocalization.linearMap_compatibleSMul p.primeCompl
  let e1 := (IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl B)
    (Algebra.linearMap B (Localization.AtPrime p))).restrictScalars (Localization.AtPrime p)
  rw [e1.length_eq, ← h2]
  exact (Submodule.quotEquivOfEqBot ⊥ rfl).length_eq.symm
end GroundTheory.Heights₂.Heights.Inter.ReducedCut
