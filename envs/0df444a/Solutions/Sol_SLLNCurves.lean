-- Prove2me | solution 1 for SLLNCurves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:11.350222+00:00
-- url     : https://prove2.me/submissions/62e516f0-88a7-4769-a76e-cf7e4f3e72ad

import Definitions.Def_Tablet_SamplingRealizesAverages
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveCurrentMeasurable
import Definitions.Def_Tablet_CurveCurrentBound
import Definitions.Def_Tablet_ThetaL
import Definitions.Def_Tablet_SLLNCurves
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveCurrentMeasurable
import Theorems.Thm_CurveLenMeasurable
import Theorems.Thm_SamplingRealizesAverages


set_option autoImplicit false
open MeasureTheory Filter Finset ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T) (l : ℕ) (hl : 1 ≤ l)
    (hne : F.eta l Set.univ ≠ 0)
    (om : ℕ → Form1 E)
    (g : ℕ → Curve E → ℝ) (hgm : ∀ j, Measurable (g j))
    (hgi : ∀ j, Integrable (g j) (F.eta l)) :
    ∃ γ : ℕ → Curve E,
      (∀ i, (γ i).len = (l : ℝ)) ∧
      (∀ i, massOfFunctional (curveCurrent (γ i)) = (l : ℝ≥0∞)) ∧
      (∀ k, Tendsto (fun n : ℕ =>
          (F.eta l Set.univ).toReal / (n * l) * ∑ i ∈ Finset.range n, curveCurrent (γ i) (om k))
          atTop (nhds (T (om k)))) ∧
      (∀ j, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, g j (γ i)) / n) atTop
        (nhds ((F.eta l Set.univ).toReal⁻¹ * ∫ c, g j c ∂(F.eta l)))) := by
-- BODY
  classical
  have := F.finite l
  set M : ℝ≥0∞ := F.eta l Set.univ with hM
  have hMtop : M ≠ ⊤ := measure_ne_top _ _
  have hMinvtop : M⁻¹ ≠ ⊤ := by simpa using (ENNReal.inv_ne_top).2 hne
  have hMR : M.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hne, hMtop⟩
  have hlR : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- integrability of the current family
  have hcm : ∀ k, Measurable (fun c : Curve E => curveCurrent c (om k)) := fun k =>
    CurveCurrentMeasurable (om k)
  have hci : ∀ k, Integrable (fun c : Curve E => curveCurrent c (om k)) (F.eta l) := by
    intro k
    refine Integrable.mono'
      (integrable_const (((om k).fBound : ℝ) * ((om k).piLip : ℝ) * (l : ℝ)))
      (hcm k).aestronglyMeasurable ?_
    filter_upwards [F.lengthExactly l hl] with c hc
    have := CurveCurrentBound c (om k)
    rw [hc] at this
    simpa [Real.norm_eq_abs] using this
  -- merged countable family
  set h : ℕ → Curve E → ℝ :=
    fun j => if j % 2 = 0 then (fun c => curveCurrent c (om (j / 2))) else g (j / 2) with hh
  have hhm : ∀ j, Measurable (h j) := by
    intro j; rw [hh]; dsimp only; split
    · exact hcm _
    · exact hgm _
  have hhi : ∀ j, Integrable (h j) (F.eta l) := by
    intro j; rw [hh]; dsimp only; split
    · exact hci _
    · exact hgi _
  -- normalized probability measure
  set mu : Measure (Curve E) := M⁻¹ • F.eta l with hmu
  have hmuuniv : mu Set.univ = 1 := by
    rw [hmu, Measure.smul_apply, smul_eq_mul, ← hM, ENNReal.inv_mul_cancel hne hMtop]
  have : IsProbabilityMeasure mu := ⟨hmuuniv⟩
  obtain ⟨U, hUsup, hUm, hU0⟩ := exists_measurable_superset_of_null (F.supported l hl)
  have hlenm : MeasurableSet {γ : Curve E | γ.len = (l : ℝ)} :=
    CurveLenMeasurable (measurableSet_singleton ((l : ℝ)))
  set S : Set (Curve E) := Uᶜ ∩ {γ : Curve E | γ.len = (l : ℝ)} with hS
  have hSm : MeasurableSet S := hUm.compl.inter hlenm
  have hlen0 : F.eta l {γ : Curve E | ¬ (γ.len = (l : ℝ))} = 0 := F.lengthExactly l hl
  have hSc : F.eta l Sᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hU0 hlen0)
    rw [hS] at hx
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq, not_and_or, not_not] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  have hmuSc : mu Sᶜ = 0 := by rw [hmu, Measure.smul_apply, smul_eq_mul, hSc, mul_zero]
  have hhi' : ∀ j, Integrable (h j) mu := fun j => by
    rw [hmu]; exact (hhi j).smul_measure hMinvtop
  obtain ⟨x, hxS, hxlim⟩ := SamplingRealizesAverages mu h hhm hhi' S hSm hmuSc
  have hval : ∀ j, ∫ c, h j c ∂mu = M.toReal⁻¹ * ∫ c, h j c ∂(F.eta l) := by
    intro j; rw [hmu, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
  refine ⟨x, fun i => (hxS i).2, ?_, ?_, ?_⟩
  · intro i
    have hnu : x i ∉ U := (hxS i).1
    have hmem : x i ∈ ThetaL (E := E) l := by
      by_contra hcon; exact hnu (hUsup hcon)
    simpa [ThetaL] using hmem
  · -- the current identity, \eqref{closed1} at fixed l
    intro k
    have h2 : (2 * k) % 2 = 0 := by omega
    have h3 : (2 * k) / 2 = k := by omega
    have hk := hxlim (2 * k)
    rw [hval (2 * k)] at hk
    have he : h (2 * k) = fun c : Curve E => curveCurrent c (om k) := by
      simp [hh, h2, h3]
    rw [he] at hk
    have hw : ∫ c, curveCurrent c (om k) ∂(F.eta l) = (l : ℝ) * T (om k) := by
      have := F.weakLength l hl (om k)
      field_simp at this ⊢
      linarith [this]
    rw [hw] at hk
    have hfin : M.toReal / (l : ℝ) * (M.toReal⁻¹ * ((l : ℝ) * T (om k))) = T (om k) := by
      field_simp
    have hlim := hk.const_mul (M.toReal / (l : ℝ))
    rw [hfin] at hlim
    refine hlim.congr (fun n => ?_)
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · intro j
    have h2 : (2 * j + 1) % 2 = 1 := by omega
    have h3 : (2 * j + 1) / 2 = j := by omega
    have hk := hxlim (2 * j + 1)
    rw [hval (2 * j + 1)] at hk
    have he : h (2 * j + 1) = g j := by
      simp [hh, h2, h3]
    rw [he] at hk
    exact hk
