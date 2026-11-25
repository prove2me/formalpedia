-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_PshInh_ii_sup__a1047692b6a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:32.638043+00:00
-- url     : https://prove2.me/submissions/dc62bb31-0976-440b-adc0-5ba438c67792

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshInh
open MeasureTheory Metric Set Filter Topology Real
noncomputable section
namespace ReciprocityTheory.AnForm.A.PshInh
theorem _root_.solution {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ j, IntervalIntegrable (f j) volume a b) :
    IntervalIntegrable (fun θ => Finset.univ.sup' Finset.univ_nonempty (fun j => f j θ))
      volume a b := by
  have e : (fun θ => Finset.univ.sup' Finset.univ_nonempty (fun j => f j θ)) =
      Finset.univ.sup' Finset.univ_nonempty f := by
    funext θ; rw [Finset.sup'_apply]
  rw [e]
  refine Finset.sup'_induction _ _ (p := fun g => IntervalIntegrable g volume a b) ?_
    (fun j _ => hf j)
  intro g hg h hh
  exact ⟨hg.1.sup hh.1, hg.2.sup hh.2⟩
end ReciprocityTheory.AnForm.A.PshInh
