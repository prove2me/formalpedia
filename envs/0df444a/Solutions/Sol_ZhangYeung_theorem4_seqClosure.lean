-- Prove2me | solution 1 for ZhangYeung.theorem4_seqClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:13.798454+00:00
-- url     : https://prove2.me/submissions/575fd299-752f-47f5-b1ee-e93e721fb098

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
public import Theorems.Thm_ZhangYeung_shannonCone_of_witness
public import Theorems.Thm_ZhangYeung_not_zhangYeungHolds_witness
public import Theorems.Thm_ZhangYeung_zhangYeungHolds_of_tendsto

set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u
namespace ZhangYeung
namespace _root_.ZhangYeung
theorem _root_.solution :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧
      ∀ (F_seq : ℕ → Finset (Fin 4) → ℝ),
        (∀ k, zhangYeungHolds (F_seq k)) →
        (∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) →
        False := by
  refine ⟨FWitness, shannonCone_of_witness, ?_⟩
  intro F_seq h_seq h_lim
  exact not_zhangYeungHolds_witness (zhangYeungHolds_of_tendsto h_seq h_lim)
end _root_.ZhangYeung
end ZhangYeung
