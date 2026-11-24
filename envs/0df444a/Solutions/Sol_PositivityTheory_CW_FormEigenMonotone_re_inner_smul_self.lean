-- Prove2me | solution 1 for PositivityTheory.CW.FormEigenMonotone.re_inner_smul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:17.846001+00:00
-- url     : https://prove2.me/submissions/9a8f86b2-194c-4f37-8517-23aac9c01c13

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
theorem _root_.solution (r : ℝ) (v : V) : (inner ℂ v ((r : ℂ) • v)).re = r * ‖v‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) v
end PositivityTheory.CW.FormEigenMonotone
