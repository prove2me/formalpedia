-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_isLocalizedModule_powers_mul_0b09b1d3491f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:37.501828+00:00
-- url     : https://prove2.me/submissions/1bb7451f-6d6d-4ae2-a1df-6da6fbef8f9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.GenericFreeness
open Module
universe u
variable {A : Type u} [CommRing A]
namespace GroundTheory.Heights₂.Heights.GenericFreeness
theorem _root_.solution (a c : A) {M N P : Type*} [AddCommGroup M] [Module A M]
    {Ra : Type*} [CommRing Ra] [Algebra A Ra] [IsLocalization.Away a Ra]
    [AddCommGroup N] [Module A N] [Module Ra N] [IsScalarTower A Ra N]
    [AddCommGroup P] [Module A P] [Module Ra P] [IsScalarTower A Ra P]
    (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers a) g]
    (h : N →ₗ[Ra] P) [IsLocalizedModule (Submonoid.powers (algebraMap A Ra c)) h] :
    IsLocalizedModule (Submonoid.powers (a * c)) (h.restrictScalars A ∘ₗ g) := by
  have hh : IsLocalizedModule (Submonoid.powers c) (h.restrictScalars A) :=
    IsLocalizedModule.restrictScalars_powers c h
  have ha : IsUnit (algebraMap A (Module.End A P) a) := by
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Ra) a
    rw [Module.End.isUnit_iff]
    have hb : Function.Bijective (fun p : P ↦ (u : Ra) • p) := by
      refine ⟨fun p q hpq ↦ ?_, fun p ↦ ⟨(↑u⁻¹ : Ra) • p, ?_⟩⟩
      · have := congr_arg (fun x : P ↦ (↑u⁻¹ : Ra) • x) hpq
        simpa only [smul_smul, Units.inv_mul, one_smul] using this
      · show (u : Ra) • ((↑u⁻¹ : Ra) • p) = p
        rw [smul_smul, Units.mul_inv, one_smul]
    convert hb using 1
    funext p
    simp [hu]
  have hc : IsUnit (algebraMap A (Module.End A P) c) :=
    hh.map_units ⟨c, Submonoid.mem_powers c⟩
  constructor
  · rintro ⟨_, k, rfl⟩
    show IsUnit (algebraMap A (Module.End A P) ((a * c) ^ k))
    rw [map_pow, map_mul]
    exact (ha.mul hc).pow k
  · intro y
    obtain ⟨⟨n, ⟨_, j, rfl⟩⟩, hn⟩ := hh.surj y
    obtain ⟨⟨m, ⟨_, i, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers a) g n
    refine ⟨⟨(a ^ j * c ^ i) • m, ⟨(a * c) ^ (i + j), i + j, rfl⟩⟩, ?_⟩
    simp only [Submonoid.smul_def] at hn hm ⊢
    have e1 : (h.restrictScalars A ∘ₗ g) ((a ^ j * c ^ i) • m) =
        (a ^ j * c ^ i * a ^ i) • (h.restrictScalars A) n := by
      rw [LinearMap.comp_apply, map_smul, ← hm, map_smul, map_smul, smul_smul]
    rw [e1, ← hn, smul_smul]
    congr 1
    ring
  · intro m₁ m₂ e
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := hh.exists_of_eq e
    simp only [Submonoid.smul_def] at hj
    rw [← map_smul, ← map_smul] at hj
    obtain ⟨⟨_, i, rfl⟩, hi⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers a) (f := g) hj
    refine ⟨⟨(a * c) ^ (i + j), i + j, rfl⟩, ?_⟩
    simp only [Submonoid.smul_def] at hi ⊢
    have : (a * c) ^ (i + j) = a ^ j * c ^ i * (a ^ i * c ^ j) := by ring
    rw [this]
    simp only [mul_smul (a ^ j * c ^ i), mul_smul (a ^ i) (c ^ j), hi]
end GroundTheory.Heights₂.Heights.GenericFreeness
