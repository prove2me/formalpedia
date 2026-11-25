-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:28.840654+00:00
-- url     : https://prove2.me/submissions/20a9edd8-b74e-42a4-a452-b82ee9ff85a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twistA_iff_917ff1481aae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twist_twistSys_iff_89a1717ba8b8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace twist
theorem _root_.solution (F : Kleiman.SubSystem S x E) (c : ℤ) {i : Fin (N + 1)} (h : x i ≠ 0) :
    IndefiniteRowSideFullHecke.Kleiman.twistA S x (toIndefiniteRowSideFullHecke F) c i = toIndefiniteRowSideFullHecke (F.twist (Kleiman.twistSys S x c)) i := by
  ext z
  rw [mem_twistA_iff, chartModule_of_ne_zero F h, chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem,
    mem_twist_twistSys_iff F c (Kleiman.singleChart h) (Finset.mem_singleton_self i)]
  rfl
end twist
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
