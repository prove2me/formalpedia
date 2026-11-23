-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.DS.sch_word_snoc
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:14:25.764011+00:00
-- url     : https://prove2.me/submissions/13578f0b-2fcf-46bc-a317-2c3fc0391a31

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

theorem ReciprocityTheory.ChartRestriction.DS.sch_word_snoc {k : ℕ} (init : Fin k → Fin n × Fin n) (p : Fin n × Fin n) :
    word E (Fin.snoc init p : Fin (k + 1) → Fin n × Fin n) = word E init * E p.1 p.2 := by
  unfold word
  rw [List.ofFn_succ', List.prod_concat]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]


end

theorem solution {n : ℕ} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    {E : Fin n → Fin n → Module.End ℂ M} {k : ℕ} (init : Fin k → Fin n × Fin n) (p : Fin n × Fin n) :
    ReciprocityTheory.ChartRestriction.DS.word E (Fin.snoc init p : Fin (k + 1) → Fin n × Fin n) =
      ReciprocityTheory.ChartRestriction.DS.word E init * E p.1 p.2 :=
  ReciprocityTheory.ChartRestriction.DS.sch_word_snoc init p
