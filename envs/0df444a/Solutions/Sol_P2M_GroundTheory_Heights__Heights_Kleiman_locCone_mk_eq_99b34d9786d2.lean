-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locCone_mk_eq_99b34d9786d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:10.091747+00:00
-- url     : https://prove2.me/submissions/283aaa22-0e26-435e-bab9-b470f2814028

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
theorem _root_.solution {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) {m : M.coneSub}
    {s : monos (S := S) I} {w : ConeLaurent S x} (h : coneLaurent S x s * w = m) :
    locCone M I hI (LocalizedModule.mk m s) = w :=
  (isUnit_coneLaurent_of_mem_monos hI s.2).mul_left_cancel ((locCone_mk M I hI m s).trans h.symm)
end GroundTheory.Heights₂.Heights.Kleiman
