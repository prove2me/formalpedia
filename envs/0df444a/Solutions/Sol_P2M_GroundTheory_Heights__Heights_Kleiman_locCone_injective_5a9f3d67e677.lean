-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locCone_injective_5a9f3d67e677
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:22.509162+00:00
-- url     : https://prove2.me/submissions/b7cb1a16-77aa-4516-beaa-13498b884edf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_mk_027744b712cb

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
theorem _root_.solution (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    Function.Injective (locCone M I hI) := by
  refine (injective_iff_map_eq_zero _).mpr fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSub => locCone M I hI z = 0 → z = 0)
    (fun m s hz => ?_) z
  have h := locCone_mk M I hI m s
  rw [hz, mul_zero] at h
  have hm : m = 0 := Subtype.ext h.symm
  rw [hm, LocalizedModule.zero_mk]
end GroundTheory.Heights₂.Heights.Kleiman
