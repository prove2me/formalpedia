-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_sg__Multi_6b63c33631c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:49:23.090683+00:00
-- url     : https://prove2.me/submissions/fc4f0fe9-72c9-4501-9140-57e738b392cc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sg_prod_list

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
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (c : Fin n) {k : ℕ} (v : Fin k → Fin n × Fin n) :
    sgE ε cpFock cmFock c c (ExteriorAlgebra.ιMulti ℂ k (fun i => Pi.single (v i) (1 : ℂ))) =
      ((∑ i, modeWt ε (v i) c : ℝ) : ℂ) • ExteriorAlgebra.ιMulti ℂ k (fun i => Pi.single (v i) (1 : ℂ)) := by
  have hl : (List.ofFn fun i => ExteriorAlgebra.ι ℂ (Pi.single (v i) (1 : ℂ))) =
      (List.ofFn v).map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ)) := by
    rw [List.map_ofFn]
    rfl
  rw [ExteriorAlgebra.ιMulti_apply, hl, sg_prod_list, List.map_ofFn, List.sum_ofFn]
  rfl
end ReciprocityTheory.ChartRestriction.DS
