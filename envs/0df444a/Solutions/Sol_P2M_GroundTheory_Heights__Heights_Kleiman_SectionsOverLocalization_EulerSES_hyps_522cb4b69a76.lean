-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_hyps_522cb4b69a76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:38.399587+00:00
-- url     : https://prove2.me/submissions/1d597960-4073-40fa-81d8-ad21d88358ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero

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
noncomputable section
open EulerSES
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace EulerSES
theorem _root_.solution :
    let CA : ∀ _ : ℕ, Submodule ℚ ℚ := fun _ => ⊥
    let CB : ∀ _ : ℕ, Submodule ℚ ℚ := EulerSES.degZero
    let d : ∀ n : ℕ, (fun _ : ℕ => ℚ) n →ₗ[ℚ] (fun _ : ℕ => ℚ) (n + 1) := fun _ => 0
    let f : ∀ n : ℕ, (fun _ : ℕ => ℚ) n →ₗ[ℚ] (fun _ : ℕ => ℚ) n := fun _ => 0
    let g : ∀ n : ℕ, (fun _ : ℕ => ℚ) n →ₗ[ℚ] (fun _ : ℕ => ℚ) n := fun _ => LinearMap.id
    (∀ n, ∀ x ∈ CA n, d n x ∈ CA (n + 1)) ∧ (∀ n, ∀ x ∈ CB n, d n x ∈ CB (n + 1)) ∧
    (∀ n, ∀ x ∈ CA n, d (n + 1) (d n x) = 0) ∧ (∀ n, ∀ x ∈ CB n, d (n + 1) (d n x) = 0) ∧
    (∀ n, ∀ x ∈ CA n, f n x ∈ CB n) ∧ (∀ n, ∀ y ∈ CB n, g n y ∈ CB n) ∧
    (∀ n, ∀ x ∈ CA n, d n (f n x) = f (n + 1) (d n x)) ∧
    (∀ n, ∀ y ∈ CB n, d n (g n y) = g (n + 1) (d n y)) ∧
    (∀ n, ∀ x ∈ CA n, f n x = 0 → x = 0) ∧
    (∀ n, ∀ x ∈ CA n, g n (f n x) = 0) ∧
    (∀ n, ∀ y ∈ CB n, g n y = 0 → ∃ x ∈ CA n, f n x = y) ∧
    (∀ n, ∀ z ∈ CB n, ∃ y ∈ CB n, g n y = z) ∧
    (∀ n, FiniteDimensional ℚ (coh CA d n)) ∧ (∀ n, FiniteDimensional ℚ (coh CB d n)) ∧
    Subsingleton (coh CA d 1) ∧ Module.finrank ℚ (coh CB d 0) = 1 := by
  intro CA CB d f g
  refine ⟨fun _ _ _ => zero_mem _, fun _ _ _ => zero_mem _, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => zero_mem _, fun _ _ h => h, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ x hx _ => (Submodule.mem_bot ℚ).1 hx, fun _ _ _ => rfl,
    fun _ y _ hy => ⟨0, zero_mem _, hy.symm⟩, fun _ z hz => ⟨z, hz, rfl⟩,
    fun _ => inferInstance, fun _ => inferInstance, ?_, ?_⟩
  · refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    have ha := (Submodule.mem_bot ℚ).1 (Submodule.mem_inf.1 a.2).1
    have hb := (Submodule.mem_bot ℚ).1 (Submodule.mem_inf.1 b.2).1
    congr 1
    exact Subtype.ext (ha.trans hb.symm)
  · have hcyc : cyc CB d 0 = ⊤ := by
      simp [cyc, CB, EulerSES.degZero, d]
    have hbnd : bnd CB d 0 = ⊥ := rfl
    rw [Submodule.Quotient.equiv _ ⊥ (LinearEquiv.ofTop _ hcyc) (by
      rw [hbnd, Submodule.comap_bot, Submodule.map_eq_bot_iff, Submodule.ker_subtype]) |>.finrank_eq]
    rw [(Submodule.quotEquivOfEqBot ⊥ rfl).finrank_eq, Module.finrank_self]
end EulerSES
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
