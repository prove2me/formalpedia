-- Prove2me | solution 1 for PositivityTheory.CW.FormEigenMonotone.beta_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:25:09.127566+00:00
-- url     : https://prove2.me/submissions/bbe52d0e-abb1-45d2-a8f3-82cd419d1c13

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FormEigenMonotone
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
namespace PositivityTheory.CW.FormEigenMonotone
theorem _root_.solution
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (φ ψ : ℝ → ℝ) (h : ∀ x, 0 ≤ x → φ x ≤ ψ x) (v : V) :
    (beta ε E (fc b μ φ) v v).re ≤ (beta ε E (fc b μ ψ) v v).re := by
  simp only [beta, Complex.re_sum]
  exact Finset.sum_le_sum fun p _ => hmono φ ψ h _
end PositivityTheory.CW.FormEigenMonotone
