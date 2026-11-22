-- Prove2me | solution 1 for ProbabilityTheory.independent_copies3_nondep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:44:22.348431+00:00
-- url     : https://prove2.me/submissions/fea4fedf-cde2-4741-836d-5c2774355cd2

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_mul
public import Theorems.Thm_ProbabilityTheory_identDistrib_ulift_self
public import Theorems.Thm_P2M_ProbabilityTheory_independent_copies__65d5e66cdf90
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
attribute [local simp] ProbabilityTheory.indepFun_zero_measure


attribute [local simp] ProbabilityTheory.identDistrib_id

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Measure Filter Set
open scoped Topology MeasureTheory ENNReal NNReal
attribute [symm] ProbabilityTheory.IdentDistrib.symm
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]
open MeasureTheory ProbabilityTheory Function Set
open ProbabilityTheory
universe u u' v
variable {Ω Ω' α ι β β' T : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {ν : Measure Ω'} {f g : Ω
    → β} {f' g' : Ω' → β}
variable [MeasurableSpace α] [MeasurableSpace β]
namespace ProbabilityTheory
theorem _root_.solution {α : Type u}
    [mS : MeasurableSpace α]
    {Ω₁ : Type u_1} {Ω₂ : Type u_2} {Ω₃ : Type u_3}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {X₁ : Ω₁ → α} {X₂ : Ω₂ → α} {X₃ : Ω₃ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃)
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₃] :
    ∃ (A : Type (max u_1 u_2 u_3)) (_ : MeasurableSpace A) (μA :
      Measure A) (X₁' X₂' X₃' : A → α),
      IsProbabilityMeasure μA ∧ iIndepFun ![X₁', X₂', X₃'] μA ∧
      Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧
      IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂
        ∧ IdentDistrib X₃' X₃ μA μ₃ := by
  let Ω₁' : Type (max u_1 u_2 u_3) := ULift.{max u_2 u_3} Ω₁
  let Ω₂' : Type (max u_1 u_2 u_3) := ULift.{max u_1 u_3} Ω₂
  let Ω₃' : Type (max u_1 u_2 u_3) := ULift.{max u_1 u_2} Ω₃
  let Ω : Fin 3 → Type (max u_1 u_2 u_3) := ![Ω₁', Ω₂', Ω₃']
  let mΩ : (i : Fin 3) → MeasurableSpace (Ω i) :=
    Fin.cases (inferInstance : MeasurableSpace Ω₁') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₂') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₃') Fin.rec0
  let X : (i : Fin 3) → Ω i → α :=
    Fin.cases (X₁ ∘ ULift.down) <| Fin.cases (X₂ ∘ ULift.down) <|
    Fin.cases (X₃ ∘ ULift.down) Fin.rec0
  have hX : ∀ (i : Fin 3), @Measurable _ _ (mΩ i) mS (X i) :=
    Fin.cases (hX₁.comp measurable_down) <|
    Fin.cases (hX₂.comp measurable_down) <|
    Fin.cases (hX₃.comp measurable_down) Fin.rec0
  let μ : (i : Fin 3) → @Measure (Ω i) (mΩ i) :=
    Fin.cases (μ₁.comap ULift.down) <|
    Fin.cases (μ₂.comap ULift.down) <|
    Fin.cases (μ₃.comap ULift.down) Fin.rec0
  have hμ : (i : Fin 3) → IsProbabilityMeasure (μ i) :=
    Fin.cases isProbabilityMeasure_comap_down <|
    Fin.cases isProbabilityMeasure_comap_down <|
    Fin.cases isProbabilityMeasure_comap_down Fin.rec0
  obtain ⟨A, mA, μA, X', hμ, hi, hX'⟩ := independent_copies' X hX μ
  refine ⟨A, mA, μA, X' 0, X' 1, X' 2, hμ, ?_,
    (hX' 0).1, (hX' 1).1, (hX' 2).1,
    (hX' 0).2.trans ((identDistrib_ulift_self hX₁).symm),
    (hX' 1).2.trans (identDistrib_ulift_self hX₂).symm,
    (hX' 2).2.trans (identDistrib_ulift_self hX₃).symm⟩
  convert hi; ext i; fin_cases i <;> rfl
end ProbabilityTheory
