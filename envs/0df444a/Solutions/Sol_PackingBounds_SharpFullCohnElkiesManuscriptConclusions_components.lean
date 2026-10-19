-- Prove2me | solution 1 for PackingBounds.SharpFullCohnElkiesManuscriptConclusions.components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/e7aedf26-4c29-4cbc-9132-ecfc91f12144

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PackingBounds_SharpFullCohnElkiesManuscriptConclusions_ofRadial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open Filter
open scoped Topology
open PackingBounds
namespace PackingBounds
namespace SharpFullCohnElkiesManuscriptConclusions
theorem _root_.solution :
    Tendsto
        (fun d : ℕ =>
          sInf {q : ℝ | ∃ f : FullAdmissible d,
            fullQuotient f ^ ((d : ℝ)⁻¹) = q} /
            Real.sqrt (d : ℝ))
        atTop (𝓝 (1 / Real.pi)) ∧
      (∃ err : ℕ → ℝ,
        Tendsto err atTop (𝓝 0) ∧
        ∀ d : ℕ, 0 < d →
          sInf {q : ℝ | ∃ f : FullAdmissible d,
            fullQuotient f ^ ((d : ℝ)⁻¹) = q} =
            (1 / Real.pi + err d) * Real.sqrt (d : ℝ)) ∧
      Tendsto
        (fun d : ℕ => (fullLinearProgram d) ^ ((d : ℝ)⁻¹))
        atTop (𝓝 (Real.sqrt (Real.exp 1 / (2 * Real.pi)))) ∧
      Tendsto
        (fun d : ℕ => Real.log (fullLinearProgram d) / (d : ℝ))
        atTop
        (𝓝 ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi)))) ∧
      (∃ err : ℕ → ℝ,
        Tendsto err atTop (𝓝 0) ∧
        (∀ᶠ d : ℕ in atTop,
          fullLinearProgram d =
            (Real.sqrt (Real.exp 1 / (2 * Real.pi)) + err d) ^ d)) ∧
      (∃ δ : ℕ → ℝ,
        Tendsto δ atTop (𝓝 0) ∧
        (∀ d : ℕ, 0 ≤ δ d) ∧
        (∀ᶠ d : ℕ in atTop, ∀ f : FullAdmissible d,
          (2 : ℝ) ^ d / CohnElkies.unitBallVolume d *
            (Real.sqrt (Real.exp 1 / (2 * Real.pi)) - δ d) ^ d ≤
              fullQuotient f)) ∧
      0 < (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1) ∧
      (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1) ∈
        Set.Ioo
          (0.604400544291677695341677307053 : ℝ)
          0.604400544291677695341677307054 ∧
      Tendsto
        (fun d : ℕ => Real.logb 2 (fullLinearProgram d) / (d : ℝ))
        atTop
        (𝓝 (-((1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1)))) ∧
      (∃ err : ℕ → ℝ,
        Tendsto err atTop (𝓝 0) ∧
        (∀ᶠ d : ℕ in atTop,
          fullLinearProgram d =
            (2 : ℝ) ^
              (-((1 / 2 : ℝ) *
                  Real.logb 2 (2 * Real.pi / Real.exp 1) + err d) *
                (d : ℝ)))) :=
  ⟨SharpFullCohnElkiesManuscriptConclusions.ofRadial.root_before_infimum,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.root_before_infimum_vanishing_error,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.linear_program_root,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.natural_logarithmic_rate,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.natural_vanishing_exponential_error,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.universal_nonnegative_delta,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.base_two_exponent_positive,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.base_two_decimal_certificate,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.base_two_logarithmic_rate,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.base_two_vanishing_exponential_error⟩
end SharpFullCohnElkiesManuscriptConclusions
end PackingBounds
