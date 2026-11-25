-- Prove2me | solution 1 for PositivityTheory.CW.FormEigenMonotone.beta_const_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:10.182951+00:00
-- url     : https://prove2.me/submissions/9a489a97-5845-43df-a94f-b7bf65f6e1bf

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_re_inner_smul_self

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
theorem _root_.solution (r : ℝ) (v : V) :
    (beta ε E ((r : ℂ) • 1) v v).re = r * ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 := by
  simp only [beta, LinearMap.smul_apply, Module.End.one_apply, Complex.re_sum, re_inner_smul_self,
    Finset.mul_sum]
end PositivityTheory.CW.FormEigenMonotone
