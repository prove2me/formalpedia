-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_locRes_269addb87c40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:13.87015+00:00
-- url     : https://prove2.me/submissions/7e146a65-01f2-4cf5-9878-ce8469f0c069

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_Graded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_mul_locL_mk_5f722498f58b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_mk_eq_9e340803afc7

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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : ∀ i ∈ J, x i ≠ 0)
    (z : LocMod (Sy S r) N (TMod x η S n0 d0 g0) I) :
    locL x η S n0 d0 g0 J hJ (locRes h z) = locL x η S n0 d0 g0 I (fun i hi => hJ i (h hi)) z := by
  change LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at z
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [locRes_mk]
    apply locL_mk_eq
    exact phi_mul_locL_mk x η S n0 d0 g0 I _ m s
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
