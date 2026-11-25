-- Prove2me | solution 1 for ReciprocityTheory.AnForm.sum_mul_leviC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:36.971161+00:00
-- url     : https://prove2.me/submissions/d0c80032-977d-48ac-8e08-32703749b3b3

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Theorems.Thm_ReciprocityTheory_AnForm_leviC_add
import Theorems.Thm_ReciprocityTheory_AnForm_leviC_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Complex Filter Topology
open scoped Matrix
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (v b : Fin e → ℂ) :
    ∑ i, v i * leviC H (Pi.single i 1) b = leviC H v b := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin e → ℂ) := by
    funext k
    simp [Pi.single_apply]
  have key : ∀ s : Finset (Fin e), leviC H (∑ i ∈ s, v i • (Pi.single i 1 : Fin e → ℂ)) b =
      ∑ i ∈ s, v i * leviC H (Pi.single i 1) b := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using leviC_smul H 0 0 b
    · intro i s hi ih
      rw [Finset.sum_insert hi, Finset.sum_insert hi, leviC_add, leviC_smul, ih]
  rw [← key, ← hv]
end ReciprocityTheory.AnForm
