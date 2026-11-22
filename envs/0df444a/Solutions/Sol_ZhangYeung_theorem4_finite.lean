-- Prove2me | solution 1 for ZhangYeung.theorem4_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:20:29.357877+00:00
-- url     : https://prove2.me/submissions/46af50f8-d027-41eb-83ea-629f0f360d7f

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
public import Theorems.Thm_ZhangYeung_shannonCone_of_witness
public import Theorems.Thm_ZhangYeung_not_zhangYeungHolds_witness
public import Theorems.Thm_ZhangYeung_zhangYeungHolds_of_entropy

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
    ∃ F : Finset (Fin 4) → ℝ,
      shannonCone F ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        {S : Fin 4 → Type u}
        [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
        [∀ i, MeasurableSingletonClass (S i)]
        (X : ∀ i : Fin 4, Ω → S i) (_ : ∀ i, Measurable (X i)),
        F ≠ entropyFn X μ := by
  refine ⟨FWitness, shannonCone_of_witness, ?_⟩
  intro Ω _ μ _ S _ _ _ X hX heq
  apply not_zhangYeungHolds_witness
  rw [heq]
  exact zhangYeungHolds_of_entropy hX μ
end _root_.ZhangYeung
end ZhangYeung
