-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_injective_e55cadb52ac8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:19.312701+00:00
-- url     : https://prove2.me/submissions/88125be4-388a-473a-b5e0-d3467077fe31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_mk_f17973bed795

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
  (M : FinGradedSub (S := S) (x := x) E)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    Function.Injective (locConeE M I hI) := by
  refine (injective_iff_map_eq_zero _).mpr fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSubE => locConeE M I hI z = 0 → z = 0)
    (fun m s hz => ?_) z
  have h := locConeE_mk M I hI m s
  rw [hz, smul_zero] at h
  have hm : m = 0 := Subtype.ext h.symm
  rw [hm, LocalizedModule.zero_mk]
end GroundTheory.Heights₂.Heights.Kleiman
