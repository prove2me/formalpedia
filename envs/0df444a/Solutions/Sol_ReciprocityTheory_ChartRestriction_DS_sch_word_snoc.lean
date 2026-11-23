-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sch_word_snoc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:27.213041+00:00
-- url     : https://prove2.me/submissions/549ae7bc-194a-4893-9f98-b3c3544cc06d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchPhiOneApply

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : ℕ} (init : Fin k → Fin n × Fin n) (p : Fin n × Fin n) :
    word E (Fin.snoc init p : Fin (k + 1) → Fin n × Fin n) = word E init * E p.1 p.2 := by
  simp only [word, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one]
end ReciprocityTheory.ChartRestriction.DS
