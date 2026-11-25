-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.prodChart_holo_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:55.994743+00:00
-- url     : https://prove2.me/submissions/f033aac0-92de-4212-9a8f-c517baee9e5b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_FubiniStudyPotentialProductIsPotential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint CompatibleChartOperations
noncomputable section
variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y)
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (j : Fin A.n) (k : Fin B.n) (l : Fin A.n) :
    AnalyticOnNhd ℂ (A.chart l ∘ Prod.fst ∘ (prodChart A B j k).symm)
      ((prodChart A B j k).target ∩ (prodChart A B j k).symm ⁻¹' (Prod.fst ⁻¹' (A.chart l).source)) := by
  intro z ⟨ht, hs⟩
  rw [mem_prodChart_target] at ht
  rw [Set.mem_preimage, Set.mem_preimage, prodChart_symm_apply] at hs
  have h1 := A.holo j l _ ⟨ht.1, hs⟩
  have hF : AnalyticAt ℂ (fun z => ((appendCLE e e').symm z).1) z :=
    ((ContinuousLinearMap.fst ℂ _ _).comp (appendCLE e e').symm.toContinuousLinearMap).analyticAt z
  have := h1.comp_of_eq hF rfl
  exact this
end ReciprocityTheory.AnForm.M
