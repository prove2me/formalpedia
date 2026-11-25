-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.nuabs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:31:42.728176+00:00
-- url     : https://prove2.me/submissions/0d2882dc-bb33-4312-9402-6e631185da59

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_Nuabs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution : ∀ (G N H T : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace N] [Group H] [MeasurableSpace H] [MeasurableMul H] [CommGroup T] [MeasurableSpace T] [MeasurableMul T] (μN : Measure N) [SFinite μN] (μH : Measure H) [SFinite μH] [μH.IsMulLeftInvariant] (μT : Measure T) [SFinite μT] [μT.IsMulLeftInvariant] (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0), Measurable nn → Measurable ι → Measurable mm → Measurable χ → (∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)) → (∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u) → (∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t) → (∀ u t, mm t * ι u = ι u * mm t) → ∀ (p : N) (u : H) (t : T), ((μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2).map (fun g => nn p * ι u * mm t * g) = (μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2 := by
  intro G N H T _ _ _ _ _ _ _ _ _ _ μN _ μH _ _ μT _ _ nn ι mm χ hn hi hm hχ h1 h2 h3 h4 p u t
  set wd := μT.withDensity fun s => (χ s : ℝ≥0∞) with hwd
  have hΨ : Measurable fun z : N × H × T => nn z.1 * ι z.2.1 * mm z.2.2 :=
    ((hn.comp measurable_fst).mul (hi.comp measurable_snd.fst)).mul (hm.comp measurable_snd.snd)
  have key : ∀ (g : G) (A : N × H × T → N × H × T), MeasurePreserving A (μN.prod (μH.prod wd)) (μN.prod (μH.prod wd)) →
      (∀ z, g * (nn z.1 * ι z.2.1 * mm z.2.2) = nn (A z).1 * ι (A z).2.1 * mm (A z).2.2) →
      MeasurePreserving (fun x => g * x) ((μN.prod (μH.prod wd)).map fun z => nn z.1 * ι z.2.1 * mm z.2.2)
        ((μN.prod (μH.prod wd)).map fun z => nn z.1 * ι z.2.1 * mm z.2.2) := fun g A hA e =>
    ⟨measurable_const_mul g, by
      rw [Measure.map_map (measurable_const_mul g) hΨ]
      conv_rhs => rw [← hA.map_eq, Measure.map_map hΨ hA.measurable]
      exact congrArg (fun f => Measure.map f _) (funext e)⟩
  obtain ⟨L₁, a1, a2⟩ := h1 p
  obtain ⟨L₂, b1, b2⟩ := h2 u
  obtain ⟨L₃, c0, c1, c2⟩ := h3 t
  have hw : (χ t : ℝ≥0∞) • wd.map (fun x => t * x) = wd := by
    ext s hs
    have hχ' : Measurable fun s => (χ s : ℝ≥0∞) := hχ.coe_nnreal_ennreal
    rw [Measure.smul_apply, Measure.map_apply (measurable_const_mul t) hs, hwd,
      withDensity_apply _ (measurable_const_mul t hs), withDensity_apply _ hs, smul_eq_mul, ← lintegral_const_mul _ hχ',
      ← (measurePreserving_mul_left μT t).setLIntegral_comp_preimage hs hχ']
    simp only [map_mul, ENNReal.coe_mul]
  have k1 := key (nn p) _ (a1.prod (MeasurePreserving.id _)) fun z => by simp [← mul_assoc, a2]
  have k2 := key (ι u) _ (b1.prod ((measurePreserving_mul_left μH u).prod (MeasurePreserving.id wd))) fun z => by
    simp [← mul_assoc, b2]
  have k3 := key (mm t) (Prod.map L₃ (Prod.map id fun x => t * x))
    ⟨c0.prodMap (measurable_id.prodMap (measurable_const_mul t)), by
      rw [← Measure.map_prod_map _ _ c0 (measurable_id.prodMap (measurable_const_mul t)),
        ← Measure.map_prod_map _ _ measurable_id (measurable_const_mul t), c1, Measure.map_id, ENNReal.smul_def,
        Measure.prod_smul_left, ← Measure.prod_smul_right, ← Measure.prod_smul_right, hw]⟩ fun z => by
    simp only [Prod.map_fst, Prod.map_snd, id, map_mul, ← mul_assoc, c2]
    rw [mul_assoc _ (mm t), h4, ← mul_assoc]
  simpa only [Function.comp_def, mul_assoc] using (k1.comp (k2.comp k3)).map_eq
end PositivityTheory.PlacePermOperatorBicommutantSpan
