-- Prove2me | solution 1 for QFS.cor_rescaled_kernel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-06T19:12:11.384491+00:00
-- url     : https://prove2.me/submissions/e1d8147b-0665-46da-96aa-11d264144925

import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Theorems.Thm_QFS_cor_rescaled_kernel_uniform
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Real Set Metric MeasureTheory ENNReal

open QFS

variable {d : ℕ}

/-- **Corollary 3.6 exactly as the source states it**: the constant `C` is produced
after the configuration `Γ` and the kernel `k`, so it is allowed to depend on both.
Derived from `QFS.cor_rescaled_kernel_uniform`, which produces `C` from `d`, `ϑ`, `α`
and `Λ` alone and is therefore strictly stronger. -/
theorem solution {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hd : 2 ≤ d)
    {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 2) :
    ∃ θ' : ℝ, 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ (Λ : ℝ) (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
        KernelBounds Γ α Λ k →
      ∃ C : ℝ, 0 < C ∧
      ∀ h : ℝ, 0 < h →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin d)),
        (∀ u, (Γ' u).apex = θ') ∧ IsBounded Γ' θ' ∧
        ∀ x ∈ scaledLattice d h, ∀ y ∈ scaledLattice d h, Real.sqrt d * h < ‖x - y‖ →
          ENNReal.ofReal C⁻¹ *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel d α x y)
            ≤ discreteKernel d k h x y ∧
          discreteKernel d k h x y ≤ ENNReal.ofReal C * jumpKernel d α x y := by
  obtain ⟨θ', hθ0, hθle, hmain⟩ := QFS.cor_rescaled_kernel_uniform hϑ hϑ' hd hα hα2
  refine ⟨θ', hθ0, hθle, fun Γ hΓ hmeas Λ k hk => ?_⟩
  obtain ⟨C, hC0, hCmain⟩ := hmain Λ hk.one_le
  exact ⟨C, hC0, fun h hh => hCmain Γ hΓ hmeas k hk h hh⟩
