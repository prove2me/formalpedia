-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_coe_d_sub_61e0f8775efc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:39.524961+00:00
-- url     : https://prove2.me/submissions/1fd5d087-6183-4b5a-8098-2c77a1cdbb69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (F : SubSystem S x E) {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥(F.sub I)) i)
    (J : Cech.Idx (support x) (i + 1)) :
    ((Cech.d (fun I : Chart x => ↥(F.sub I)) F.res i t J : F.sub J.1) : E) =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • (t (Cech.face J j) : E) := by
  rw [Cech.d_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul_of_tower]
  rfl
end GroundTheory.Heights₂.Heights.Kleiman
