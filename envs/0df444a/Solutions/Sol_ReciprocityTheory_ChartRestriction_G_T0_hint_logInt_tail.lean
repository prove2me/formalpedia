-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hint_logInt_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:27:14.684338+00:00
-- url     : https://prove2.me/submissions/de228756-9af9-44e6-b86c-d6c1fa685f02

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_mpTail
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_blockPoint_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_eval_indep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_continuous_pt
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_sphereLogIntegrable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hq0 : q ≠ 0) (hq : IsMultiHomogeneous a q)
    (ha : a 0 = 0) (t0 : Fin n → ℂ) :
    Integrable (fun z : BlockSphere D n => Real.log ‖MvPolynomial.eval (hintPt t0 z) q‖)
      (blockSphereProb D n) := by
  have hmeas : AEStronglyMeasurable
      (fun z : BlockSphere D n => Real.log ‖MvPolynomial.eval (hintPt t0 z) q‖)
      (blockSphereProb D n) :=
    ((continuous_norm.comp ((MvPolynomial.continuous_eval q).comp
      (hint_continuous_pt t0))).measurable.log).aestronglyMeasurable
  rw [← (hint_mpTail D n hn).integrable_comp hmeas]
  refine (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable (D + 1) n a q hq0 hq).congr
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply]
  rw [hint_blockPoint_eq, hint_eval_indep hq ha _ (hintPt t0 (fun i : Fin D => z i.succ))]
  rintro ⟨i, j⟩ hi
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
  rfl
end ReciprocityTheory.ChartRestriction.G.T0
