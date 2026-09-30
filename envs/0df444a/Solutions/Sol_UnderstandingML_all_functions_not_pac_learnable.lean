-- Prove2me | solution 1 for UnderstandingML.all_functions_not_pac_learnable
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T13:41:06.484288+00:00
-- url     : https://prove2.me/submissions/14e29eae-2d4d-4c6e-85c2-9915def01ad4

import Definitions.Def_UnderstandingML_Framework
import Theorems.Thm_UnderstandingML_no_free_lunch
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

namespace UnderstandingML.AllFunctionsAux

variable {X : Type*} [MeasurableSpace X]

/-- The `0–1` risk is at most the (outer) measure of the disagreement set, for any hypothesis. -/
theorem risk_loss01_le (D : Measure (X × Bool)) [IsFiniteMeasure D] (h : X → Bool) :
    risk loss01 D h ≤ (D {z | h z.1 ≠ z.2}).toReal := by
  set V := {z : X × Bool | h z.1 ≠ z.2}
  set T := toMeasurable D V
  have hT : MeasurableSet T := measurableSet_toMeasurable D V
  have hle : ∀ z, loss01 h z ≤ T.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    unfold loss01
    split_ifs with hz
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) z
    · rw [Set.indicator_of_mem (subset_toMeasurable D V hz)]
  have hnn : ∀ z, 0 ≤ loss01 h z := by intro z; unfold loss01; split_ifs <;> norm_num
  calc risk loss01 D h ≤ ∫ z, T.indicator (fun _ => (1 : ℝ)) z ∂D :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn)
          ((integrable_const (1 : ℝ)).indicator hT) (Filter.Eventually.of_forall hle)
    _ = (D V).toReal := by
        rw [integral_indicator hT, setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
          measure_toMeasurable]

/-- The disagreement set of a measurable labeling function is measurable. -/
theorem measurableSet_disagree {f : X → Bool} (hf : Measurable f) :
    MeasurableSet {z : X × Bool | f z.1 ≠ z.2} := by
  have hd : MeasurableSet {p : Bool × Bool | p.1 ≠ p.2} := (Set.toFinite _).measurableSet
  exact hd.preimage ((hf.comp measurable_fst).prodMk measurable_snd)

/-- If the measurable `f` has zero `0–1` risk, its disagreement set is null. -/
theorem measure_disagree_eq_zero {D : Measure (X × Bool)} [IsProbabilityMeasure D] {f : X → Bool}
    (hf : Measurable f) (h0 : risk loss01 D f = 0) : D {z : X × Bool | f z.1 ≠ z.2} = 0 := by
  have hU := measurableSet_disagree hf
  have hloss : loss01 f = {z : X × Bool | f z.1 ≠ z.2}.indicator (fun _ => (1 : ℝ)) := by
    funext z
    unfold loss01
    by_cases hz : f z.1 = z.2
    · rw [if_pos hz, Set.indicator_of_notMem (by simpa using hz)]
    · rw [if_neg hz, Set.indicator_of_mem (by simpa using hz)]
  have : (D {z : X × Bool | f z.1 ≠ z.2}).toReal = 0 := by
    rw [← h0, risk, hloss, integral_indicator hU, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def]
  rcases (ENNReal.toReal_eq_zero_iff _).mp this with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

/-- A distribution under which the measurable `f` has zero `0–1` risk is the law of `(x, f x)`
with `x` drawn from its first marginal. -/
theorem labeledLaw_map_fst {D : Measure (X × Bool)} [IsProbabilityMeasure D] {f : X → Bool}
    (hf : Measurable f) (h0 : risk loss01 D f = 0) : labeledLaw (D.map Prod.fst) f = D := by
  have hDU := measure_disagree_eq_zero hf h0
  have hψ : Measurable (fun x : X => (x, f x)) := measurable_id.prodMk hf
  rw [labeledLaw, Measure.map_map hψ measurable_fst]
  have hae : (fun x : X => (x, f x)) ∘ Prod.fst =ᵐ[D] id := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun z hz => ?_) hDU
    simp only [Function.comp_apply, id_eq, Set.mem_setOf_eq] at hz ⊢
    intro hfz
    exact hz (Prod.ext rfl hfz)
  rw [Measure.map_congr hae, Measure.map_id]

end UnderstandingML.AllFunctionsAux

open UnderstandingML UnderstandingML.AllFunctionsAux

theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Infinite X] :
    ¬ PACLearnable (Set.univ : Set (X → Bool)) := by
  rintro ⟨mH, A, hPAC⟩
  set m := mH (1 / 9) (1 / 8) with hmdef
  have hm : (2 * m : ℕ∞) < ENat.card X := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.coe_lt_top _
  obtain ⟨D, hD, ⟨f, hfm, hf0⟩, E, -, hEsub, hEμ⟩ := no_free_lunch A m hm
  set D' := D.map Prod.fst with hD'
  haveI : IsProbabilityMeasure D' := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hDeq : labeledLaw D' f = D := labeledLaw_map_fst hfm hf0
  have hreal : Realizable (Set.univ : Set (X → Bool)) D' f :=
    ⟨f, Set.mem_univ _, by simp [trueError]⟩
  have hpac := hPAC (1 / 9) (1 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    D' inferInstance f hfm hreal m le_rfl
  rw [hDeq] at hpac
  -- on `E` the true error of the output exceeds `1/9`
  have hsub : E ⊆ {S | 1 / 9 < trueError D' f (A m S)} := by
    intro S hS
    have h1 : 1 / 8 ≤ risk loss01 D (A m S) := hEsub hS
    have h2 := risk_loss01_le D (A m S)
    have h3 : D {z : X × Bool | A m S z.1 ≠ z.2} ≤ D' {x | A m S x ≠ f x} := by
      calc D {z : X × Bool | A m S z.1 ≠ z.2}
          ≤ D (Prod.fst ⁻¹' {x | A m S x ≠ f x} ∪ {z : X × Bool | f z.1 ≠ z.2}) := by
            refine measure_mono (fun z hz => ?_)
            simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_preimage] at hz ⊢
            by_cases hfz : f z.1 = z.2
            · left; rw [hfz]; exact hz
            · right; exact hfz
        _ ≤ D (Prod.fst ⁻¹' {x | A m S x ≠ f x}) + D {z : X × Bool | f z.1 ≠ z.2} :=
            measure_union_le _ _
        _ = D (Prod.fst ⁻¹' {x | A m S x ≠ f x}) := by
            rw [measure_disagree_eq_zero hfm hf0, add_zero]
        _ ≤ D' {x | A m S x ≠ f x} := Measure.le_map_apply measurable_fst.aemeasurable _
    have h4 : (D {z : X × Bool | A m S z.1 ≠ z.2}).toReal ≤ trueError D' f (A m S) :=
      ENNReal.toReal_mono (measure_ne_top _ _) h3
    show 1 / 9 < trueError D' f (A m S)
    linarith
  have hlt : ENNReal.ofReal (1 / 8) < ENNReal.ofReal (1 / 7) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have := (hEμ.trans (measure_mono hsub)).trans hpac
  exact absurd (lt_of_lt_of_le hlt this) (lt_irrefl _)
