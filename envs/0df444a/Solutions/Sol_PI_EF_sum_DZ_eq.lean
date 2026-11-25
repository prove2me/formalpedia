-- Prove2me | solution 1 for PI.EF.sum_DZ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:23.040358+00:00
-- url     : https://prove2.me/submissions/1a88555d-b7c4-4ac3-a418-6ad262b45223

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogWindowLe
import Theorems.Thm_PI_EF_ctr_im
import Theorems.Thm_PI_EF_ctr_re
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.EF.ctr_im
attribute [local simp] PI.EF.ctr_re



set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution {χ : DirichletCharacter ℂ N} (t : ℝ)
    (hfin : (DZ χ t).Finite) (F : ℂ → ℂ) :
    ∃ E : Finset ℂ, (∀ ρ ∈ E, ρ ∈ DZ χ t ∧ ρ ∉ ZerosNear χ t ∧ ρ ≠ 0) ∧
      ∑ᶠ ρ ∈ DZ χ t, F ρ = ∑ᶠ ρ ∈ ZerosNear χ t, F ρ + ∑ ρ ∈ E, F ρ +
        (open Classical in if (0 : ℂ) ∈ DZ χ t then F 0 else 0) := by
  classical
  have hsub : ZerosNear χ t ⊆ DZ χ t := by
    intro ρ hρ
    rw [ZerosNear.eq_1] at hρ
    obtain ⟨h0, h1, him, hL⟩ := hρ
    rw [DZ.eq_1, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, ctr.eq_1, Complex.dist_eq]
      have hre : (ρ - (2 + (t : ℂ) * Complex.I)).re = ρ.re - 2 := by simp
      have him' : (ρ - (2 + (t : ℂ) * Complex.I)).im = ρ.im - t := by simp
      obtain ⟨ha, hb⟩ := abs_le.mp him
      rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply,
        hre, him']
      nlinarith
    · have hne : ρ ≠ 1 := by
        intro h
        rw [h] at h1
        norm_num at h1
      rw [Lent.eq_1]
      split_ifs with hχ
      · subst hχ
        have key : DirichletCharacter.LFunctionTrivChar₁ N ρ =
            (ρ - 1) * DirichletCharacter.LFunctionTrivChar N ρ := by
          first
          | simp [DirichletCharacter.LFunctionTrivChar₁, Function.update_apply, hne]
          | (unfold DirichletCharacter.LFunctionTrivChar₁; rw [Function.update_of_ne hne])
          | exact DirichletCharacter.LFunctionTrivChar₁_apply_ne_one N hne
        rw [key]
        exact mul_eq_zero_of_right _ hL
      · exact hL
  have h0Z : (0 : ℂ) ∉ ZerosNear χ t := by
    intro h
    rw [ZerosNear.eq_1] at h
    obtain ⟨h0, -⟩ := h
    simp at h0
  have hZ : (ZerosNear χ t).Finite := hfin.subset hsub
  refine ⟨(hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)).filter (fun ρ => ρ ≠ 0), ?_, ?_⟩
  · intro ρ hρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.1.1, hρ.1.2, hρ.2⟩
  · rw [finsum_mem_eq_finite_toFinset_sum F hfin, finsum_mem_eq_finite_toFinset_sum F hZ,
      ← Finset.sum_filter_add_sum_filter_not hfin.toFinset (fun ρ => ρ ∈ ZerosNear χ t)]
    have e1 : hfin.toFinset.filter (fun ρ => ρ ∈ ZerosNear χ t) = hZ.toFinset := by
      ext ρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
    rw [e1, add_assoc]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not
      (hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)) (fun ρ => ρ ≠ 0)]
    congr 1
    split_ifs with hD
    · have e2 : (hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)).filter
          (fun ρ => ¬ ρ ≠ 0) = {0} := by
        ext ρ
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_singleton, ne_eq,
          not_not]
        constructor
        · rintro ⟨-, h⟩
          exact h
        · rintro rfl
          exact ⟨⟨hD, h0Z⟩, rfl⟩
      rw [e2, Finset.sum_singleton]
    · apply Finset.sum_eq_zero
      intro ρ hρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, ne_eq, not_not] at hρ
      exact absurd (hρ.2 ▸ hρ.1.1) hD
end PI.EF
