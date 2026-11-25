-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locCone_locRes_374e5d5036f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:20:27.113178+00:00
-- url     : https://prove2.me/submissions/65fd7f41-93dc-4c28-a2c0-72baecb44aa4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_mk_027744b712cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_mk_eq_99b34d9786d2

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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : J ⊆ support x)
    (z : LocMod S N M.coneSub I) :
    locCone M J hJ (locRes h z) = locCone M I (h.trans hJ) z := by
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSub =>
      locCone M J hJ (locRes h z) = locCone M I (h.trans hJ) z) (fun m s => ?_) z
  rw [locRes_mk]
  exact locCone_mk_eq M hJ (locCone_mk M I _ m s)
end GroundTheory.Heights₂.Heights.Kleiman
