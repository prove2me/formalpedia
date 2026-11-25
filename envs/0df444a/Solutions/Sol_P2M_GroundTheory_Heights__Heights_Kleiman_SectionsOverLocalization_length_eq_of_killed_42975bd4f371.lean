-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_length_eq_of_killed_42975bd4f371
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:36.018007+00:00
-- url     : https://prove2.me/submissions/8f5780fa-0efb-4783-8f58-2a96c5db0ff1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
noncomputable section
variable {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] {O : Type*} [CommRing O] [Algebra S O]
  [IsLocalization.AtPrime O 𝔪] {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
  {N : ℕ} {x : Fin (N + 1) → Ω}
omit [IsScalarTower S O Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution {Q : Type*} [AddCommGroup Q] [Module O Q] [Module S Q] [IsScalarTower S O Q]
    (hkill : ∀ m ∈ 𝔪, ∀ q : Q, m • q = 0) : Module.length S Q = Module.length O Q := by
  have stable : ∀ (P : Submodule S Q) (o : O) (n : Q), n ∈ P → o • n ∈ P := by
    intro P o n hn
    obtain ⟨⟨a, ⟨t, ht⟩⟩, h⟩ := IsLocalization.surj 𝔪.primeCompl o
    obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) ht
    have h' : algebraMap S O y * algebraMap S O t + algebraMap S O i = 1 := by
      rw [← map_mul, ← map_add, hyi, map_one]
    have ho : o = algebraMap S O (y * a) + o * algebraMap S O i := by
      simp only at h
      rw [map_mul]
      linear_combination (algebraMap S O y) * h - o * h'
    rw [ho, add_smul, mul_smul, algebraMap_smul, algebraMap_smul, hkill i hi n, smul_zero, add_zero]
    exact P.smul_mem _ hn
  let e : Submodule O Q ≃o Submodule S Q :=
    { toFun := fun P => P.restrictScalars S
      invFun := fun P => { toAddSubmonoid := P.toAddSubmonoid, smul_mem' := fun o n hn => stable P o n hn }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [Module.length_eq_height, Module.length_eq_height, ← Order.height_orderIso e ⊤, e.map_top]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
