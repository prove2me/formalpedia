-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_DoubleCosetCovolume_hypotheses_met_fa2eff07614e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:55:54.204597+00:00
-- url     : https://prove2.me/submissions/f2049c2c-ac25-491e-8a8e-f5ebc383b774

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_sliceGroup_67318eca5e77

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace DoubleCosetCovolume
theorem _root_.solution :
    ∃ (Φ : C3 × C3 ≃ₜ* C3 × C3) (Γ : Subgroup (C3 × C3)) (_ : Countable Γ) (K : Subgroup C3)
      (S : Finset C3), Γ ≠ ⊥ ∧ IsCompact (K : Set C3) ∧ IsOpen (K : Set C3) ∧
      (∀ γ ∈ Γ, (Φ γ).1 = 1 → γ = 1) ∧
      (∀ y : C3, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K, y = (Φ γ).2 * s * k) ∧
      (∀ s ∈ S, ∀ (μ₁ : Measure C3) [μ₁.IsHaarMeasure], ∃ FD₁ : Set C3,
        IsFundamentalDomain (sliceGroup Φ Γ K s) FD₁ μ₁ ∧ μ₁ FD₁ < ⊤) := by
  refine ⟨ContinuousMulEquiv.refl _, isHyperbolicPair_isotropic_dual, inferInstance, ⊥, {1}, ?_,
    (Set.finite_singleton 1).isCompact, isOpen_discrete _, ?_, ?_, ?_⟩
  · intro h
    have : ((Multiplicative.ofAdd (1 : ZMod 3), Multiplicative.ofAdd (1 : ZMod 3)) : C3 × C3) ∈
        isHyperbolicPair_isotropic_dual := ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact absurd (congrArg Prod.fst this) (by decide)
  · rintro γ ⟨a, rfl⟩ h1
    simp only [ContinuousMulEquiv.refl_apply, MonoidHom.prod_apply, MonoidHom.id_apply] at h1 ⊢
    simp [h1]
  · intro y
    exact ⟨(y, y), ⟨y, rfl⟩, 1, Finset.mem_singleton_self 1, 1, Subgroup.one_mem _, by simp⟩
  · intro s hs μ₁ _
    rw [Finset.mem_singleton] at hs
    subst hs
    have hbot : sliceGroup (ContinuousMulEquiv.refl (C3 × C3)) isHyperbolicPair_isotropic_dual ⊥ 1 = ⊥ := by
      ext x
      rw [mem_sliceGroup, Subgroup.mem_bot]
      constructor
      · rintro ⟨γ, ⟨a, rfl⟩, hk, rfl⟩
        simp only [ContinuousMulEquiv.refl_apply, MonoidHom.prod_apply, MonoidHom.id_apply,
          inv_one, one_mul, mul_one, Subgroup.mem_bot] at hk ⊢
        exact hk
      · rintro rfl
        exact ⟨1, Subgroup.one_mem _, by simp, by simp⟩
    refine ⟨Set.univ, ?_, isCompact_univ.measure_lt_top⟩
    rw [hbot]
    exact IsFundamentalDomain.mk' MeasurableSet.univ.nullMeasurableSet fun x =>
      ⟨1, Set.mem_univ _, fun γ _ => Subsingleton.elim _ _⟩
end DoubleCosetCovolume
end GroundTheory.Heights₂.Heights.FiniteCovolume
