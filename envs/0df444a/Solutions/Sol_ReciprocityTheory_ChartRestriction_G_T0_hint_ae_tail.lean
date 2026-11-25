-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hint_ae_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:08:35.602865+00:00
-- url     : https://prove2.me/submissions/522a3e36-e16f-4d2d-a2fe-a7ab92f59a10

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
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_blockSphere_eval_ne_zero


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
    ∀ᵐ z ∂(blockSphereProb D n), MvPolynomial.eval (hintPt t0 z) q ≠ 0 := by
  have hA : MeasurableSet {z : BlockSphere D n | MvPolynomial.eval (hintPt t0 z) q = 0} :=
    (isClosed_eq ((MvPolynomial.continuous_eval q).comp (hint_continuous_pt t0))
      continuous_const).measurableSet
  rw [ae_iff]
  simp only [not_not]
  rw [← (hint_mpTail D n hn).measure_preimage hA.nullMeasurableSet]
  have h0 := ae_blockSphere_eval_ne_zero (D + 1) n a q hq0 hq
  rw [ae_iff] at h0
  refine measure_mono_null (fun z hz => ?_) h0
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz
  simp only [Set.mem_ofPred_eq, not_not]
  rw [hint_blockPoint_eq, hint_eval_indep hq ha _ (hintPt t0 (fun i : Fin D => z i.succ))]
  · exact hz
  rintro ⟨i, j⟩ hi
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
  rfl
end ReciprocityTheory.ChartRestriction.G.T0
