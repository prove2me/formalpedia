-- Prove2me | solution 1 for QuantileMDP.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-14T02:32:41.724045+00:00
-- url     : https://prove2.me/submissions/7c75ecdb-5ad9-4d90-8209-b0a8ff8e29df

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Definitions.Def_QuantileMDP_quantile

open MeasureTheory Set QuantileMDP
open scoped ENNReal

namespace QuantileMDP

/-- An almost-sure additive bound on real rewards gives the same bound on
their extended-real quantiles, at both endpoints as well. -/
theorem quantile_le_add_of_ae_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (c τ : ℝ)
    (hXY : ∀ᵐ ω ∂P, X ω ≤ Y ω + c) :
    quantile (P.map X) τ ≤ quantile (P.map Y) τ + (c : EReal) := by
  let e : EReal ≃o EReal :=
    { toFun := fun x => x + (c : EReal)
      invFun := fun x => x - (c : EReal)
      left_inv := fun _ => EReal.add_sub_cancel_right
      right_inv := fun _ => EReal.sub_add_cancel
      map_rel_iff' := (EReal.addLECancellable_coe c).add_le_add_iff_right }
  have hclosed (x : ℝ) : (P.map Y) (Iic x) ≤ (P.map X) (Iic (x + c)) := by
    rw [Measure.map_apply hX measurableSet_Iic, Measure.map_apply hY measurableSet_Iic]
    refine measure_mono_ae ?_
    filter_upwards [hXY] with ω hω hx
    exact mem_Iic.mpr (hω.trans (add_le_add_left hx c))
  have hupper (x : ℝ) : (P.map X) (Ici x) ≤ (P.map Y) (Ici (x - c)) := by
    rw [Measure.map_apply hX measurableSet_Ici, Measure.map_apply hY measurableSet_Ici]
    refine measure_mono_ae ?_
    filter_upwards [hXY] with ω hω hx
    exact mem_Ici.mpr (sub_le_iff_le_add.mpr (hx.trans hω))
  have he (x : ℝ) : e (x : EReal) = ((x + c : ℝ) : EReal) :=
    (EReal.coe_add _ _).symm
  change _ ≤ e (quantile (P.map Y) τ)
  simp only [quantile]
  split_ifs with h0 h1
  · rw [e.map_sSup]
    apply sSup_le
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : (P.map X) (Ici x) = 1 := hx
    let := Measure.isProbabilityMeasure_map (μ := P) hY.aemeasurable
    have hy1 : (P.map Y) (Ici (x - c)) = 1 :=
      le_antisymm prob_le_one (hx1 ▸ hupper x)
    have hx' : (x : EReal) = e ((x - c : ℝ) : EReal) := by rw [he, sub_add_cancel]
    change (x : EReal) ≤ _
    rw [hx']
    apply le_iSup_of_le ((x - c : ℝ) : EReal)
    exact le_iSup_of_le ⟨x - c, hy1, rfl⟩ le_rfl
  · rw [e.map_sInf]
    refine le_iInf fun y => le_iInf fun hy => ?_
    obtain ⟨y, hy, rfl⟩ := hy
    rw [he]
    let := Measure.isProbabilityMeasure_map (μ := P) hX.aemeasurable
    have hx1 : (P.map X) (Iic (y + c)) = 1 :=
      le_antisymm prob_le_one ((show (P.map Y) (Iic y) = 1 from hy) ▸ hclosed y)
    exact sInf_le ⟨y + c, hx1, rfl⟩
  · rw [e.map_sInf]
    refine le_iInf fun y => le_iInf fun hy => ?_
    obtain ⟨y, hy, rfl⟩ := hy
    rw [he]
    exact sInf_le ⟨y + c,
      (show ENNReal.ofReal τ ≤ (P.map Y) (Iic y) from hy).trans (hclosed y), rfl⟩

end QuantileMDP

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace QuantileMDP

private theorem quantile_dirac_interior (c τ : ℝ) (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    quantile (Measure.dirac c) τ = (c : EReal) := by
  rw [quantile, if_neg hτ.1.ne', if_neg hτ.2.ne]
  apply le_antisymm
  · refine sInf_le ⟨c, ?_, rfl⟩
    change ENNReal.ofReal τ ≤ Measure.dirac c (Iic c)
    rw [Measure.dirac_apply_of_mem (mem_Iic.mpr le_rfl)]
    exact ENNReal.ofReal_le_one.mpr hτ.2.le
  · apply le_sInf
    rintro _ ⟨x, hx, rfl⟩
    apply EReal.coe_le_coe_iff.mpr
    by_contra! h
    have hz : Measure.dirac c (Iic x) = 0 := by
      rw [Measure.dirac_apply, indicator_of_notMem (show c ∉ Iic x from h.not_ge)]
    have hl : ENNReal.ofReal τ ≤ Measure.dirac c (Iic x) := hx
    rw [hz] at hl
    exact (ENNReal.ofReal_pos.mpr hτ.1).not_ge hl

/-- Conditioning on a finite full joint history makes both total rewards
deterministic. Thus a single interior conditional comparison suffices
for the unconditional comparison at every level. -/
theorem theorem_5_full_history {Ω H : Type*} [MeasurableSpace Ω] [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (P : Measure Ω) [IsProbabilityMeasure P] (history : Ω → H) (hh : Measurable history)
    (x y : H → ℝ) (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1)
    (h : ∀ j : H, P (history ⁻¹' {j}) ≠ 0 →
      quantile ((cond P (history ⁻¹' {j})).map (y ∘ history)) u ≤
      quantile ((cond P (history ⁻¹' {j})).map (x ∘ history)) u)
    (τ : ℝ) :
    quantile (P.map (y ∘ history)) τ ≤ quantile (P.map (x ∘ history)) τ := by
  classical
  have hl (f : H → ℝ) (j : H) (hp : P (history ⁻¹' {j}) ≠ 0) :
      (cond P (history ⁻¹' {j})).map (f ∘ history) = Measure.dirac (f j) := by
    let fiber : Set Ω := history ⁻¹' {j}
    have hmeas : MeasurableSet fiber := hh (measurableSet_singleton j)
    let _ : IsProbabilityMeasure (cond P fiber) := cond_isProbabilityMeasure hp
    have hmem : ∀ᵐ w ∂cond P fiber, w ∈ fiber :=
      Measure.ae_smul_measure (ae_restrict_mem hmeas) _
    have hconst : (f ∘ history) =ᵐ[cond P fiber] (fun _ => f j) :=
      hmem.mono fun w hw => congrArg f (mem_singleton_iff.mp (mem_preimage.mp hw))
    rw [Measure.map_congr hconst, Measure.map_const, measure_univ, one_smul]
  have hxy : ∀ᵐ w ∂P, y (history w) ≤ x (history w) := by
    have hlocal (j : H) : ∀ᵐ w ∂P, history w = j → y j ≤ x j := by
      by_cases hp : P (history ⁻¹' {j}) = 0
      · have hne : ∀ᵐ w ∂P, history w ≠ j := by
          rw [ae_iff]
          simpa only [not_ne_iff, Set.preimage, mem_singleton_iff] using hp
        exact hne.mono fun _ hw hj => (hw hj).elim
      · have hj := h j hp
        rw [hl y j hp, hl x j hp, quantile_dirac_interior _ u hu,
          quantile_dirac_interior _ u hu, EReal.coe_le_coe_iff] at hj
        exact ae_of_all _ fun _ _ => hj
    filter_upwards [ae_all_iff.mpr hlocal] with w hw
    exact hw (history w) rfl
  simpa using quantile_le_add_of_ae_le P (y ∘ history) (x ∘ history)
    ((measurable_of_countable y).comp hh) ((measurable_of_countable x).comp hh) 0 τ
    (hxy.mono fun _ hw => by simpa using hw)

end QuantileMDP

namespace QuantileMDP

/-- Theorem 5 for finite-state chains with a common initial marginal. For
horizons longer than one, (12) at the final time conditions on the whole joint
history. For a one-step horizon the initial marginal gives equality. -/
theorem verified_theorem_5 {Ω S : Type*} [MeasurableSpace Ω] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (X Y : Fin T → Ω → S) (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (r : S → ℝ) (hstart : ∀ hT : 0 < T, P.map (X ⟨0, hT⟩) = P.map (Y ⟨0, hT⟩))
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1)
    (h : 1 < T → ∀ j : (Fin T → S × S), P {w | (fun t => (X t w, Y t w)) = j} ≠ 0 →
      quantile ((cond P {w | (fun t => (X t w, Y t w)) = j}).map
        (fun w => ∑ t, r (Y t w))) u ≤
      quantile ((cond P {w | (fun t => (X t w, Y t w)) = j}).map
        (fun w => ∑ t, r (X t w))) u)
    (τ : ℝ) :
    quantile (P.map (fun w => ∑ t, r (Y t w))) τ ≤
      quantile (P.map (fun w => ∑ t, r (X t w))) τ := by
  match T with
  | 0 => simp
  | 1 =>
    have hr : Measurable r := measurable_of_countable r
    simp only [Fin.sum_univ_one]
    change quantile (P.map (r ∘ Y 0)) τ ≤ quantile (P.map (r ∘ X 0)) τ
    have h0 : P.map (X 0) = P.map (Y 0) := hstart (by decide)
    rw [← Measure.map_map hr (hY 0), ← Measure.map_map hr (hX 0), h0]
  | n + 2 =>
    let history (w : Ω) (t : Fin (n + 2)) := (X t w, Y t w)
    have hh : Measurable history := measurable_pi_lambda _ fun t => (hX t).prodMk (hY t)
    exact theorem_5_full_history P history hh (fun j => ∑ t, r (j t).1)
      (fun j => ∑ t, r (j t).2) u hu (h (by omega)) τ

end QuantileMDP

open QuantileMDP

theorem solution {Ω S : Type*} [MeasurableSpace Ω] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (X Y : Fin T → Ω → S) (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (r : S → ℝ) (hstart : ∀ hT : 0 < T, P.map (X ⟨0, hT⟩) = P.map (Y ⟨0, hT⟩))
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1)
    (h : 1 < T → ∀ j : (Fin T → S × S), P {w | (fun t => (X t w, Y t w)) = j} ≠ 0 →
      quantile ((cond P {w | (fun t => (X t w, Y t w)) = j}).map
        (fun w => ∑ t, r (Y t w))) u ≤
      quantile ((cond P {w | (fun t => (X t w, Y t w)) = j}).map
        (fun w => ∑ t, r (X t w))) u)
    (τ : ℝ) :
    quantile (P.map (fun w => ∑ t, r (Y t w))) τ ≤
      quantile (P.map (fun w => ∑ t, r (X t w))) τ := QuantileMDP.verified_theorem_5 P T X Y hX hY r hstart u hu h τ
