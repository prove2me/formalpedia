-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.layer_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:41.001228+00:00
-- url     : https://prove2.me/submissions/98ccda10-e66e-4b62-9a40-96bbe0602cd0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_le_succ

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k l : ℕ} (hkl : k ≤ l) : layer ε E V k ≤ layer ε E V l := by
  exact monotone_nat_of_le_succ (fun k => layer_le_succ (ε := ε) (E := E) (V := V) k) hkl
end ReciprocityTheory.ChartRestriction.DS
