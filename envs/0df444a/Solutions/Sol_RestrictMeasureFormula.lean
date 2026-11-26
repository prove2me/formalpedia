-- Prove2me | solution 1 for RestrictMeasureFormula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:46.374873+00:00
-- url     : https://prove2.me/submissions/e6ec937e-be59-49e2-bf9b-1391b17ac834

import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_RestrictMeasureFormula
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open MeasureTheory Set
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.len) :
    curveMeasure (curveRestrict γ a b ha hab hb)
      = Measure.map γ.toFun (volume.restrict (Set.Icc a b)) := by
-- BODY
  have hmeas : Measurable γ.toFun := (CurveLipschitz γ).continuous.measurable
  have hEq : Set.EqOn (curveRestrict γ a b ha hab hb).toFun
      (fun u => γ.toFun (a + u)) (Set.Icc 0 (b - a)) := by
    rintro u ⟨hu0, hu1⟩
    show γ.toFun (a + min (b - a) (max 0 u)) = γ.toFun (a + u)
    rw [max_eq_right hu0, min_eq_right hu1]
  have hlen : (curveRestrict γ a b ha hab hb).len = b - a := rfl
  rw [curveMeasure, hlen]
  have hae : (curveRestrict γ a b ha hab hb).toFun
      =ᵐ[volume.restrict (Set.Icc 0 (b - a))] (fun u => γ.toFun (a + u)) :=
    (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hEq)
  rw [Measure.map_congr hae]
  have hcomp : (fun u => γ.toFun (a + u)) = γ.toFun ∘ (fun u : ℝ => a + u) := rfl
  rw [hcomp, ← Measure.map_map hmeas (measurable_const_add a)]
  congr 1
  have himg : (fun u : ℝ => a + u) ⁻¹' (Set.Icc a b) = Set.Icc 0 (b - a) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have hmp : Measure.map (fun x : ℝ => a + x) volume = volume :=
    (measurePreserving_add_left volume a).map_eq
  have hres := Measure.restrict_map (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => a + x) (measurable_const_add a) (measurableSet_Icc (a := a) (b := b))
  rw [himg, hmp] at hres
  exact hres.symm
