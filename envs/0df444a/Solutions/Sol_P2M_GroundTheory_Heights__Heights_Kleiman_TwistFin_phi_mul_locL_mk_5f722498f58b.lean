-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_mul_locL_mk_5f722498f58b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:13.702316+00:00
-- url     : https://prove2.me/submissions/421e2054-927b-4f0a-97dd-e70b2166a774

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_Graded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_mk_46d22d970e92

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
    (s : monos (S := Sy S r) I) :
    phi x η S s * toA x η (locL x η S n0 d0 g0 I hI
      (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0))) =
      toA x η m := by
  rw [← toA_smulP]
  congr 1
  rw [locL_mk]
  set e := (isUnit_end x η S hI s).unit
  have hspec : (e : Module.End (Poly (Sy S r) N) (Amb x η)) =
      algebraMap (Poly (Sy S r) N) (Module.End (Poly (Sy S r) N) (Amb x η)) (s : Poly (Sy S r) N) :=
    IsUnit.unit_spec _
  have h1 : (e : Module.End (Poly (Sy S r) N) (Amb x η))
      (((e⁻¹ : (Module.End (Poly (Sy S r) N) (Amb x η))ˣ) : Module.End (Poly (Sy S r) N) (Amb x η))
        (m : Amb x η)) = (m : Amb x η) := by
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  rw [hspec, Module.algebraMap_end_apply] at h1
  exact h1
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
