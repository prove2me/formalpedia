-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.SwLocFin.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:39.664432+00:00
-- url     : https://prove2.me/submissions/133fc351-4a0b-4d48-ae1c-2f13923c4e99

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalCharacterIntegrals_DifferentiableSetIntegralFz
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_SwLocFin_integrableOn_fz
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_SwLocFin_differentiable_setIntegral_fz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.SwLocFin
open MeasureTheory Filter Topology Set
variable {H : Type*} [MeasurableSpace H]
namespace PositivityTheory.SiegelWeilFormula.SwLocFin
theorem _root_.solution (ν : Measure H) (r : H → ℝ) (u : H → ℂ) (s₀ w₀ : ℂ) (B : ℕ → Set H)
    (hBm : ∀ j, MeasurableSet (B j)) (hmono : Monotone B) (hcov : ⋃ j, B j = univ)
    (hfin : ∀ j, ν (B j) < ⊤) (hr1 : ∀ b, 1 ≤ r b) (hrm : Measurable r) (hrb : ∀ j, ∃ Rm, ∀ b ∈ B j, r b ≤ Rm)
    (hum : AEStronglyMeasurable u ν) (hub : ∃ C, ∀ b, ‖u b‖ ≤ C)
    (hshell : ∀ z j, ∫ b in B (j + 1) \ B j, fz r u s₀ z b ∂ν = 0)
    (hint : ∃ t : ℝ, ∀ z : ℂ, t < z.re → Integrable (fz r u s₀ z) ν)
    (hval : Tendsto (fun j => ∫ b in B j, u b ∂ν) atTop (𝓝 w₀)) :
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ W s₀ = w₀ ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (fz r u s₀ z) ν ∧ W z = ∫ b, fz r u s₀ z b ∂ν := by
  obtain ⟨C, hC⟩ := hub
  have hon : ∀ z j, IntegrableOn (PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z) (B j) ν := fun z j => by
    obtain ⟨Rm, hRm⟩ := hrb j
    exact PositivityTheory.SiegelWeilFormula.SwLocFin.integrableOn_fz hr1 hrm hum hC (hBm j) (hfin j) hRm z
  have hG : ∀ z j, ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν =
      ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν := by
    intro z j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← ih]
      have hsub : B j ⊆ B (j + 1) := hmono (Nat.le_succ j)
      rw [← Set.union_diff_cancel hsub, setIntegral_union Set.disjoint_sdiff_right
        ((hBm _).diff (hBm _)) (hon z j) ((hon z (j + 1)).mono_set diff_subset), hshell, add_zero]
  obtain ⟨R0, hR0⟩ := hrb 0
  refine ⟨fun z => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν,
    PositivityTheory.SiegelWeilFormula.SwLocFin.differentiable_setIntegral_fz hr1 hrm hum hC (hBm 0) (hfin 0) hR0, ?_, ?_⟩
  · have hfs : ∀ j, ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ s₀ b ∂ν = ∫ b in B j, u b ∂ν := by
      intro j
      simp only [PositivityTheory.SiegelWeilFormula.SwLocFin.fz, sub_self, neg_zero, Complex.cpow_zero, one_mul]
    have e : (fun j => ∫ b in B j, u b ∂ν) =
        fun _ => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ s₀ b ∂ν := by
      funext j
      rw [← hfs j, hG]
    rw [e] at hval
    exact tendsto_nhds_unique tendsto_const_nhds hval
  · obtain ⟨t, ht⟩ := hint
    refine ⟨t, fun z hz => ⟨ht z hz, ?_⟩⟩
    have hlim := tendsto_setIntegral_of_monotone hBm hmono (ht z hz).integrableOn
    rw [hcov, Measure.restrict_univ] at hlim
    have e : (fun j => ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν) =
        fun _ => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν := funext (hG z)
    rw [e] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
end PositivityTheory.SiegelWeilFormula.SwLocFin
