-- Prove2me | solution 1 for PositivityTheory.CW.FunctionalCalculusInner.repr_fc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:38.817802+00:00
-- url     : https://prove2.me/submissions/f9d144c6-2dc7-43a2-b430-c688983894ee

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusOfBasic
import Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_fc_basis

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
open PositivityTheory.CW.FunctionalCalculusInner
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
namespace PositivityTheory.CW.FunctionalCalculusInner
theorem _root_.solution (b : Module.Basis ι ℂ V) (μ : ι → ℝ) (φ : ℝ → ℝ) (v : V) (i : ι) :
    b.repr (fc b μ φ v) i = ((φ (μ i) : ℝ) : ℂ) * b.repr v i := by
  have key : (b.coord i).comp (fc b μ φ) = ((φ (μ i) : ℝ) : ℂ) • b.coord i := by
    refine b.ext fun j => ?_
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, fc_basis, map_smul,
      LinearMap.smul_apply, Module.Basis.repr_self]
    by_cases hji : j = i
    · subst hji; simp
    · simp [Finsupp.single_apply, hji]
  exact LinearMap.congr_fun key v
end PositivityTheory.CW.FunctionalCalculusInner
