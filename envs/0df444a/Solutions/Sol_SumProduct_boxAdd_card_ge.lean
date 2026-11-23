-- Prove2me | solution 1 for SumProduct.boxAdd_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:54:52.924738+00:00
-- url     : https://prove2.me/submissions/707e0a42-b95e-4ba7-a791-2310b8cc3700

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
import Theorems.Thm_SumProduct_volume_convexBodyLT_const
import Theorems.Thm_SumProduct_latticeEmbed_apply
import Theorems.Thm_SumProduct_latticeEquiv_coe
import Theorems.Thm_SumProduct_tsum_indicator_le
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult


attribute [local simp] SumProduct.latticeEmbed_apply
attribute [local simp] SumProduct.latticeEquiv_coe

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) (X : ℝ) (hX : 0 ≤ X) :
    X ^ d / Real.sqrt |(NumberField.discr K : ℝ)| ≤ (boxAdd K X).card := by
  set r : NNReal := ⟨X / 2, by positivity⟩ with hr
  have hcoe : (r : ℝ) = X / 2 := by rw [hr]; rfl
  have hr2 : 2 * (r : ℝ) = X := by rw [hcoe]; ring
  set S := convexBodyLT K (fun _ => r) with hS
  set F := ZSpan.fundamentalDomain (latticeBasis K) with hFdef
  have hfund : IsAddFundamentalDomain (mixedEmbedding.integerLattice K) F volume :=
    fundamentalDomain_integerLattice K
  haveI : MeasurableVAdd (mixedEmbedding.integerLattice K) (mixedSpace K) :=
    inferInstanceAs (MeasurableVAdd (mixedEmbedding.integerLattice K).toAddSubgroup _)
  haveI : VAddInvariantMeasure (mixedEmbedding.integerLattice K) (mixedSpace K) volume :=
    inferInstanceAs (VAddInvariantMeasure (mixedEmbedding.integerLattice K).toAddSubgroup _ _)
  have hSmeas : MeasurableSet S := by
    rw [hS, convexBodyLT]
    exact (MeasurableSet.univ_pi fun _ => measurableSet_ball).prod
      (MeasurableSet.univ_pi fun _ => measurableSet_ball)
  set f : mixedSpace K → ENNReal := S.indicator (fun _ => 1) with hf
  have hfmeas : Measurable f := measurable_const.indicator hSmeas
  -- discriminant positivity
  have hsqrtpos : 0 < Real.sqrt |(NumberField.discr K : ℝ)| := by
    rw [Real.sqrt_pos, abs_pos]
    exact_mod_cast NumberField.discr_ne_zero K
  -- covolume = √Δ
  have hFreal : (volume F).toReal = Real.sqrt |(NumberField.discr K : ℝ)| := by
    have hcov : ZLattice.covolume (mixedEmbedding.integerLattice K) volume
        = Real.sqrt |(NumberField.discr K : ℝ)| := by
      rw [mixedEmbedding.covolume_integerLattice, IsTotallyReal.nrComplexPlaces_eq_zero,
        pow_zero, one_mul]
    rw [← hcov, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hfund, Measure.real]
  have hFne : volume F ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hFreal
    exact (ne_of_gt hsqrtpos) hFreal.symm
  -- volume of the box
  have hvolS : volume S = (2 : ENNReal) ^ d * (r : ENNReal) ^ d :=
    volume_convexBodyLT_const hd r
  -- the integral chain: vol S ≤ |B⁺(X)| · vol F
  have hSF : volume S ≤ (↑(boxAdd K X).card : ENNReal) * volume F := by
    have hint : ∫⁻ y, f y = volume S := by
      rw [hf, lintegral_indicator hSmeas, setLIntegral_one]
    have hkey : volume S
        = ∑' l : ↥(mixedEmbedding.integerLattice K), ∫⁻ y in F, f (l +ᵥ y) := by
      rw [← hint]; exact hfund.lintegral_eq_tsum'' f
    have hdecomp : volume S
        = ∫⁻ y in F, ∑' l : ↥(mixedEmbedding.integerLattice K), f (l +ᵥ y) := by
      rw [hkey]
      exact (lintegral_tsum fun l : ↥(mixedEmbedding.integerLattice K) =>
        (hfmeas.comp (measurable_const_vadd l)).aemeasurable).symm
    rw [hdecomp]
    calc ∫⁻ y in F, ∑' l : ↥(mixedEmbedding.integerLattice K), f (l +ᵥ y)
        ≤ ∫⁻ _ in F, (↑(boxAdd K X).card : ENNReal) := by
          refine lintegral_mono fun y => ?_
          have h := tsum_indicator_le y r
          rw [hr2] at h
          exact h
      _ = (↑(boxAdd K X).card : ENNReal) * volume F := by rw [setLIntegral_const]
  -- convert to reals
  have hSne : volume S ≠ ⊤ := by
    rw [hvolS]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hprodne : (↑(boxAdd K X).card : ENNReal) * volume F ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFne
  have hreal := (ENNReal.toReal_le_toReal hSne hprodne).mpr hSF
  rw [hvolS, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, ENNReal.toReal_mul, ENNReal.toReal_natCast, hFreal, hcoe,
    ← mul_pow, show (2 : ℝ) * (X / 2) = X by ring] at hreal
  rw [div_le_iff₀ hsqrtpos]
  exact hreal
end SumProduct
