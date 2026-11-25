-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.cont_bco
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:16.761228+00:00
-- url     : https://prove2.me/submissions/bd0e5a48-31f0-417c-8872-4bd68d738fd8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => bco x l) := by
  have h00 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ i, ‖x.2.2.1 i‖ ^ 2 :=
    continuous_finsetSum _ (fun i _ => by fun_prop)
  have h0 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m =>
      (((-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 : ℝ)) : ℂ) + (x.2.2.2 : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp (h00.neg.div_const 2)).add
      ((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => x.2.2.2)).mul continuous_const)
  have hs : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ j : Fin p, if l.val ≤ j.val then x.2.1 j * star (x.1 j) else 0 :=
    continuous_finsetSum _ (fun j _ => by
      by_cases h : l.val ≤ j.val <;> simp only [h, ↓reduceIte] <;> fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.bco
  exact h0.sub hs
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
