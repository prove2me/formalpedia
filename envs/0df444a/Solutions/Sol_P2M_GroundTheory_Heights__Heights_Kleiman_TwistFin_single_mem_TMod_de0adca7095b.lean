-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_TMod_de0adca7095b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:04.39885+00:00
-- url     : https://prove2.me/submissions/e591d50a-5ff8-4215-a121-cdba8546d06d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_CoeffPsiMulSingle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_algebraMap_LA_e2e747c45c95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_map_C_3e351123070f


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
theorem _root_.solution (M0 : FinGradedSub (S := S) (x := x) Ω)
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    {a : ℤ} {m : Ω} (hm : m ∈ M0.piece a) :
    (toA x η).symm (single (a, (0 : ℤ)) m) ∈ TMod x η S n0 d0 g0 := by
  suffices key : ∀ z ∈ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = a ∧ z = aeval x f • g0 j},
      (toA x η).symm (single (a, (0 : ℤ)) z) ∈ TMod x η S n0 d0 g0 from key m (hspan a hm)
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, f, e, hf, he, rfl⟩ := hz
    have : (toA x η).symm (single (a, (0 : ℤ)) (aeval x f • g0 j)) =
        (MvPolynomial.map (C : S →+* Sy S r) f : Poly (Sy S r) N) • genT x η n0 d0 g0 j := by
      apply (toA x η).injective
      rw [AddEquiv.apply_symm_apply, toA_smulP, genT, AddEquiv.apply_symm_apply, phi_map_C x η S hf,
        single_mul_single, smul_eq_mul, ← he]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  | zero => rw [single_zero, map_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [single_add, map_add]; exact add_mem hp hq
  | smul s p _ hp =>
    have : (toA x η).symm (single (a, (0 : ℤ)) (s • p)) =
        (C (C s) : Poly (Sy S r) N) • (toA x η).symm (single (a, (0 : ℤ)) p) := by
      apply (toA x η).injective
      rw [AddEquiv.apply_symm_apply, toA_smulP, AddEquiv.apply_symm_apply, phi_C, psi, aeval_C,
        algebraMap_LA, single_mul_single, Algebra.smul_def]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ hp
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
