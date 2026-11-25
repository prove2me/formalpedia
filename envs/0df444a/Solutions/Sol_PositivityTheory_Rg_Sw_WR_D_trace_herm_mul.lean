-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.trace_herm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:56.527054+00:00
-- url     : https://prove2.me/submissions/56620a21-0fed-4d4c-b3c9-801d7fb1a224

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_herm_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (y y' : E n) : (herm y * herm y').trace = ((ip y y' : ℝ) : ℂ) := by
  have h1 : ∑ i, ∑ j, (y i j * y' j i - y j i * y' i j) / 2 = 0 := by
    simp only [sub_div, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => y j i * y' i j / 2)]
    exact sub_self _
  have h2 : ∑ i, ∑ j, (y i j * y' i j + y j i * y' j i) / 2 = ip y y' := by
    simp only [add_div, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => y j i * y' j i / 2)]
    simp only [ip, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  calc (herm y * herm y').trace = ∑ i, ∑ j, herm y i j * herm y' j i := by
        simp [Matrix.trace, Matrix.mul_apply]
    _ = ((∑ i, ∑ j, (y i j * y' i j + y j i * y' j i) / 2 : ℝ) : ℂ) +
          Complex.I * ((∑ i, ∑ j, (y i j * y' j i - y j i * y' i j) / 2 : ℝ) : ℂ) := by
        simp only [herm_mul_apply, Finset.sum_add_distrib, Complex.ofReal_sum, Finset.mul_sum]
    _ = ((ip y y' : ℝ) : ℂ) := by rw [h1, h2]; simp
end PositivityTheory.Rg.Sw.WR.D
