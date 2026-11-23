-- Prove2me | solution 1 for SumProduct.completedPartialZeta_residue_perIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:07:15.687786+00:00
-- url     : https://prove2.me/submissions/9014e4cb-9db0-478b-b1f5-a1748a61437e

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
import Theorems.Thm_DedekindZeta_ConeMellinBridge_completedPartialZeta_eq_conePolarCorrection_add_tail
import Theorems.Thm_DedekindZeta_ConeMellinBridge_conePolarCorrection_residue_one
import Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_isMellinPair_radialTheta
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_MellinPrinciple_mellinTail_analyticOn
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open SumProduct
variable (K : Type*) [Field K] [NumberField K]
open DedekindZeta DedekindZeta.ConeRadialReduction DedekindZeta.ConeMellinBridge
  DedekindZeta.MellinPrinciple
open scoped nonZeroDivisors
namespace SumProduct
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (surfaceVolume K / (Units.torsionOrder K : ℂ))) := by
  classical
  -- The Mellin pair, for `mellinTail` continuity at `s = 1`.
  obtain ⟨c, α, hpair⟩ := exists_isMellinPair_radialTheta (K := K) 𝔞 hne
  set pf : ℂ → ℂ := fun s => (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ s
      * (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) with hpfdef
  set T : ℂ → ℂ := fun s => mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
      (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s with hTdef
  -- `ofReal : 𝓝[>]1 (real) → 𝓝[≠]1 (complex)`, continuous and avoiding 1.
  have hmap : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhds 1) (nhds ((1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 1
      have h1 : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
          (nhds ((1 : ℝ) : ℂ)) :=
        h0.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
      simpa using h1
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have hs1 : (s : ℝ) = 1 := by exact_mod_cast h
      have : (1 : ℝ) < 1 := by rw [hs1] at hs; exact hs
      exact absurd this (lt_irrefl 1)
  -- `(s-1)·completedPartialZeta = pf(s)·((s-1)·conePolar + (s-1)·T)`, eventually on `𝓝[>]1`.
  have hrw : (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ))
      =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      (fun s : ℝ => pf (s : ℂ)
        * (((s : ℂ) - 1) * conePolarCorrection K 𝔞 (s : ℂ) + ((s : ℂ) - 1) * T (s : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsre : (1 : ℝ) < (s : ℂ).re := by simpa using hs
    rw [completedPartialZeta_eq_conePolarCorrection_add_tail 𝔞 hne hsre]
    ring
  rw [Filter.tendsto_congr' hrw]
  -- Limit of the bracket (along complex `𝓝[≠]1`, then composed with `ofReal`).
  have hcone := conePolarCorrection_residue_one K 𝔞
  have hTail : Filter.Tendsto (fun s : ℂ => (s - 1) * T s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 0) := by
    have hTcont : ContinuousAt T 1 := (mellinTail_analyticOn hpair 1 (Set.mem_univ 1)).continuousAt
    have h1 : Filter.Tendsto (fun s : ℂ => (s - 1) * T s) (nhds 1) (nhds ((1 - 1) * T 1)) :=
      ((continuous_id.sub continuous_const).continuousAt.mul hTcont).tendsto
    simpa using h1.mono_left nhdsWithin_le_nhds
  have hbracketC : Filter.Tendsto
      (fun s : ℂ => (s - 1) * conePolarCorrection K 𝔞 s + (s - 1) * T s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds ((Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K + 0)) := hcone.add hTail
  have hbracket : Filter.Tendsto
      (fun s : ℝ => ((s : ℂ) - 1) * conePolarCorrection K 𝔞 (s : ℂ) + ((s : ℂ) - 1) * T (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K + 0)) := hbracketC.comp hmap
  -- Limit of `pf` at `1`.
  have hNne : (Ideal.absNorm 𝔞 : ℂ) ≠ 0 := by
    have : Ideal.absNorm 𝔞 ≠ 0 :=
      fun h => hne (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast this
  have hDne : (((|NumberField.discr K| : ℤ) : ℂ)) ≠ 0 := by
    have : (|NumberField.discr K| : ℤ) ≠ 0 := by
      simpa using NumberField.discr_ne_zero K
    exact_mod_cast this
  have hpfcont : ContinuousAt pf 1 := by
    rw [hpfdef]
    refine (continuousAt_const.mul ?_).mul ?_
    · exact continuousAt_id.const_cpow (Or.inl hNne)
    · exact (continuousAt_id.div_const 2).const_cpow (Or.inl hDne)
  have hpfC : Filter.Tendsto pf (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (pf 1)) :=
    hpfcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpf1 : Filter.Tendsto (fun s : ℝ => pf (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1)) (nhds (pf 1)) :=
    hpfC.comp hmap
  have hprod := hpf1.mul hbracket
  -- Identify the value `pf(1)·(covolume⁻¹·V) = V/w`.
  have hval : pf 1 * ((Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K + 0)
      = surfaceVolume K / (Units.torsionOrder K : ℂ) := by
    rw [add_zero, hpfdef]
    show (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ (1 : ℂ)
        * (((|NumberField.discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2))
        * ((Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K)
      = surfaceVolume K / (Units.torsionOrder K : ℂ)
    -- pf(1) = (1/w)·𝔑𝔞·|d|^{1/2}; covolume = 𝔑𝔞·√|d|.
    have hN : (Ideal.absNorm 𝔞 : ℂ) ^ (1 : ℂ) = (Ideal.absNorm 𝔞 : ℂ) := by
      rw [Complex.cpow_one]
    have hD : (((|NumberField.discr K| : ℤ) : ℂ)) ^ ((1 : ℂ) / 2)
        = ((Real.sqrt |(NumberField.discr K : ℝ)| : ℝ) : ℂ) := by
      have hdR : ((|NumberField.discr K| : ℤ) : ℝ) = |(NumberField.discr K : ℝ)| := by
        rw [Int.cast_abs]
      rw [show (((|NumberField.discr K| : ℤ) : ℂ)) = ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) by
            rw [← hdR]; norm_cast,
        show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (abs_nonneg _), Real.sqrt_eq_rpow]
    rw [hN, hD, Theta.covolume]
    have hNne : (Ideal.absNorm 𝔞 : ℝ) ≠ 0 := by
      have : Ideal.absNorm 𝔞 ≠ 0 :=
        fun h => hne (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast this
    have hsne : Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 :=
      (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)))).ne'
    have hwne : (Units.torsionOrder K : ℂ) ≠ 0 := by
      exact_mod_cast NumberField.Units.torsionOrder_ne_zero K
    rw [show ((((Ideal.absNorm 𝔞 : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)| : ℝ)) : ℂ)
        = ((Ideal.absNorm 𝔞 : ℝ) : ℂ) * ((Real.sqrt |(NumberField.discr K : ℝ)| : ℝ) : ℂ) by
      push_cast; ring]
    rw [mul_inv]
    have hNC : ((Ideal.absNorm 𝔞 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hNne
    have hsC : ((Real.sqrt |(NumberField.discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsne
    field_simp
    push_cast
    ring
  rw [hval] at hprod
  exact hprod
end SumProduct
