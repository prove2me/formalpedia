-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_mk_eq_9e340803afc7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:39:36.091053+00:00
-- url     : https://prove2.me/submissions/e43d3a4f-59e7-441c-8621-ddd764cc1c7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_Graded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_mul_locL_mk_5f722498f58b

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
theorem _root_.solution (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) (m : TMod x η S n0 d0 g0)
    (s : monos (S := Sy S r) I) (a : Amb x η) (ha : phi x η S s * toA x η a = toA x η m) :
    locL x η S n0 d0 g0 I hI
      (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) = a := by
  obtain ⟨u, hu⟩ := isUnit_phi_of_mem_monos x η S hI s.2
  apply (toA x η).injective
  have h1 := phi_mul_locL_mk x η S n0 d0 g0 I hI m s
  rw [← ha, ← hu] at h1
  exact (Units.mul_right_inj u).mp h1
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
