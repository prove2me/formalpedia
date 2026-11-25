-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_injective_0670b52721eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:39:08.381295+00:00
-- url     : https://prove2.me/submissions/a48b0427-3b2d-464e-a348-a783ce2c7e84

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
theorem _root_.solution (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) :
    Function.Injective (locL x η S n0 d0 g0 I hI) := by
  intro a b hab
  change LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at a b
  induction a using LocalizedModule.induction_on with
  | h m s =>
    induction b using LocalizedModule.induction_on with
    | h m' s' =>
      show (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) =
        LocalizedModule.mk m' s'
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      have h1 := phi_mul_locL_mk x η S n0 d0 g0 I hI m s
      have h2 := phi_mul_locL_mk x η S n0 d0 g0 I hI m' s'
      simp only [Submonoid.smul_def, one_smul]
      apply Subtype.ext
      apply (toA x η).injective
      rw [Submodule.coe_smul, Submodule.coe_smul, toA_smulP, toA_smulP, ← h1, ← h2, hab]
      ring
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
