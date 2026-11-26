-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.resSeries_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:26:25.967778+00:00
-- url     : https://prove2.me/submissions/ac61697b-530e-4610-869a-1e749d67c946

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
theorem _root_.solution (a : Fin n → ℂ) : PowerSeries.coeff 0 (resSeries a) = 0 := by
  first
    | (intros; simp [resSeries])
    | (intros; unfold resSeries; simp)
    | (intros; simp [resSeries]; done)
    | (intros; ext; simp [resSeries])
    | (intros; simp only [resSeries]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [resSeries])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [resSeries])
    | (intros; unfold resSeries; split_ifs <;> simp_all)
    | (intros; unfold resSeries; positivity)
    | (intros; unfold resSeries; ring)
    | (intros; unfold resSeries; exact?)
    | (intros; aesop (add norm simp [resSeries]))
    | (intros; simp [resSeries] <;> aesop)
    | (intros; exact resSeries.symm ..)
    | (intros; exact resSeries.comm ..)
  trace "HIT_100_0"

end 
