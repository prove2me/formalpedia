-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_locRes_483e11a5c0b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:13:36.646703+00:00
-- url     : https://prove2.me/submissions/5519f36a-a159-447a-8427-5d5cb043faf2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_xyHom_mul_locEmb_mk_c65ae6a1d680

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
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I J : Finset (Fin (N + 1))} (hI : I ⊆ support x) (hJ : J ⊆ support x) (h : I ⊆ J)
    (w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I) :
    locEmb η M₀ J hJ (locRes h w) = locEmb η M₀ I hI w := by
  induction w using LocalizedModule.induction_on with
  | h m s =>
    rw [locRes_mk]
    have hu := isUnit_xyHom η hJ (monos_mono h s.2)
    have k1 := xyHom_mul_locEmb_mk η M₀ hJ m ⟨(s : Poly _ N), monos_mono h s.2⟩
    have k2 := xyHom_mul_locEmb_mk η M₀ hI m s
    exact hu.mul_left_cancel (k1.trans k2.symm)
end GroundTheory.Heights₂.Heights.Kleiman
