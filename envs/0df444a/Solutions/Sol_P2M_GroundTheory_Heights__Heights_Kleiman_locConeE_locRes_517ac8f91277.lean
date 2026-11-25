-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_locRes_517ac8f91277
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:34.005697+00:00
-- url     : https://prove2.me/submissions/a230e499-5b22-44c2-afb9-e4bf937fff66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_mk_f17973bed795
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_mk_eq_3d2fa305b23b

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
theorem _root_.solution {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : J ⊆ support x)
    (z : LocMod S N M.coneSubE I) :
    locConeE M J hJ (locRes h z) = locConeE M I (h.trans hJ) z := by
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSubE =>
      locConeE M J hJ (locRes h z) = locConeE M I (h.trans hJ) z) (fun m s => ?_) z
  rw [locRes_mk]
  exact locConeE_mk_eq M hJ (locConeE_mk M I _ m s)
end GroundTheory.Heights₂.Heights.Kleiman
