-- Prove2me | solution 1 for SumProduct.volume_le_of_tsum_indicator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:48:27.37837+00:00
-- url     : https://prove2.me/submissions/17f36c9e-5f42-421a-9c73-eed4e0bb47ad

import Mathlib
import Definitions.Def_SumProduct_Blichfeldt

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open MeasureTheory
namespace SumProduct
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [MeasureSpace E]
    {L : Submodule ℤ E} [Countable ↥L] [MeasurableVAdd ↥L E] [VAddInvariantMeasure ↥L E volume]
    {F : Set E} (hF : IsAddFundamentalDomain (↥L) F volume) {S : Set E} (hSmeas : MeasurableSet S)
    {N : ℕ} (hbound : ∀ y : E,
      ∑' l : ↥L, S.indicator (fun _ => (1 : ENNReal)) (l +ᵥ y) ≤ (N : ENNReal)) :
    volume S ≤ (N : ENNReal) * volume F := by
  set f : E → ENNReal := S.indicator (fun _ => 1) with hf
  have hfmeas : Measurable f := measurable_const.indicator hSmeas
  have hint : ∫⁻ y, f y = volume S := by rw [hf, lintegral_indicator hSmeas, setLIntegral_one]
  have hkey : volume S = ∑' l : ↥L, ∫⁻ y in F, f (l +ᵥ y) := by
    rw [← hint]; exact hF.lintegral_eq_tsum'' f
  have hdecomp : volume S = ∫⁻ y in F, ∑' l : ↥L, f (l +ᵥ y) := by
    rw [hkey]
    exact (lintegral_tsum fun l : ↥L => (hfmeas.comp (measurable_const_vadd l)).aemeasurable).symm
  rw [hdecomp]
  calc ∫⁻ y in F, ∑' l : ↥L, f (l +ᵥ y)
      ≤ ∫⁻ _ in F, (N : ENNReal) := lintegral_mono fun y => hbound y
    _ = (N : ENNReal) * volume F := by rw [setLIntegral_const]
end SumProduct
