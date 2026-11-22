-- Prove2me | solution 1 for ZhangYeung.shannon_incomplete_ge_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:19.889184+00:00
-- url     : https://prove2.me/submissions/f4e456be-d14b-438a-aec4-6d5eb8ee7770

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
public import Theorems.Thm_ZhangYeung_shannonCone_of_witness_n
public import Theorems.Thm_ZhangYeung_not_zhangYeungHolds_witness_n

set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u
namespace ZhangYeung
namespace _root_.ZhangYeung
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ, shannonConeN F ∧ ¬ zhangYeungHoldsN F :=
  ⟨FWitnessN hn, shannonCone_of_witness_n hn, not_zhangYeungHolds_witness_n hn⟩
end _root_.ZhangYeung
end ZhangYeung
