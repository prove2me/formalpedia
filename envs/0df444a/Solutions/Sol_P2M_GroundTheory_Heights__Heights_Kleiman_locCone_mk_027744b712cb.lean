-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locCone_mk_027744b712cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:07.958535+00:00
-- url     : https://prove2.me/submissions/281fbc68-23da-4701-aeec-b285714c3c65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc

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
theorem _root_.solution (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) (m : M.coneSub)
    (s : monos (S := S) I) :
    coneLaurent S x s * locCone M I hI (LocalizedModule.mk m s) = m := by
  have h1 : (s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSub) =
      LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel s m
  have h2 : locCone M I hI ((s : Poly S N) • LocalizedModule.mk m s) = m := by
    change LocalizedModule.lift (monos I) M.coneSub.subtype _
      ((s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSub)) = m
    rw [h1]
    simp
  have h3 := (locCone M I hI).map_smul (s : Poly S N) (LocalizedModule.mk m s : LocMod S N M.coneSub I)
  exact h3.symm.trans h2
end GroundTheory.Heights₂.Heights.Kleiman
