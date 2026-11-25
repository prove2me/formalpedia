-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_subsingleton_loc_6c2981eed93b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:06.692465+00:00
-- url     : https://prove2.me/submissions/6d9ae42a-7e35-4f94-b805-40f574e9d679

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_Graded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_X_e9b8826858c3


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
theorem _root_.solution {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) (hx : x i = 0) :
    Subsingleton (LocMod (Sy S r) N (TMod x η S n0 d0 g0) I) := by
  have hkill : ∀ m : TMod x η S n0 d0 g0, (X i : Poly (Sy S r) N) • m = 0 := by
    intro m
    apply Subtype.ext
    apply (toA x η).injective
    rw [Submodule.coe_smul, toA_smulP, phi_X, hx, single_zero, zero_mul, Submodule.coe_zero, map_zero]
  refine ⟨fun a b => ?_⟩
  change LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at a b
  induction a using LocalizedModule.induction_on with
  | h m s =>
    induction b using LocalizedModule.induction_on with
    | h m' s' =>
      show (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) =
        LocalizedModule.mk m' s'
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨X i, X_mem_monos hi⟩, ?_⟩
      change (X i : Poly (Sy S r) N) • (s' : Poly (Sy S r) N) • m =
        (X i : Poly (Sy S r) N) • (s : Poly (Sy S r) N) • m'
      rw [smul_comm, hkill, smul_zero, smul_comm, hkill, smul_zero]
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
