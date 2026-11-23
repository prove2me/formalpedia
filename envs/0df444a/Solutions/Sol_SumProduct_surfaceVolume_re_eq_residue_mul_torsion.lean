-- Prove2me | solution 1 for SumProduct.surfaceVolume_re_eq_residue_mul_torsion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:10:47.999273+00:00
-- url     : https://prove2.me/submissions/6b4390d4-1dbd-4bdc-a4bf-5df9cfa20f0e

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
import Theorems.Thm_SumProduct_zInfty_ofReal
import Theorems.Thm_SumProduct_zInfty_one
import Theorems.Thm_SumProduct_completedDedekindZeta_residue_geometric
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_completedDedekindZeta_eq
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
theorem _root_.solution :
    (surfaceVolume K).re = partialCompletedZetaResidue K * (Units.torsionOrder K : ℝ) := by
  classical
  set h : ℕ := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hhcn : (h : ℝ) = (NumberField.classNumber K : ℝ) := by rw [hh, NumberField.classNumber]
  -- Mathlib analytic residue: `(s-1)·completedDedekindZeta → ZInfty(1)·κ = (√|d|/π^{r₂})·κ`.
  have hZeq : (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedDedekindZeta K (s : ℂ))
      =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      (fun s : ℝ => DedekindZeta.ZInfty K (s : ℂ) * (((s : ℂ) - 1) * NumberField.dedekindZeta K s))
      := by
    have hmem : {s : ℝ | (1 : ℝ) < s} ∈ nhdsWithin (1 : ℝ) (Set.Ioi 1) := self_mem_nhdsWithin
    filter_upwards [hmem] with s hs
    have hsre : (1 : ℝ) < (s : ℂ).re := by simpa using hs
    rw [DedekindZeta.completedDedekindZeta_eq K hsre]
    ring
  -- The Mathlib pieces: `ZInfty (s:ℂ) → ZInfty 1` (continuity) and `(s-1)·ζ_K → κ`.
  have hzinf : Filter.Tendsto (fun s : ℝ => DedekindZeta.ZInfty K (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (DedekindZeta.ZInfty K (1 : ℂ))) := by
    -- Use the explicit real form `zInfty_ofReal`: continuity of the real prefactor for `s > 0`.
    set F : ℝ → ℝ := fun s => |(NumberField.discr K : ℝ)| ^ (s / 2)
        * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ NumberField.InfinitePlace.nrRealPlaces K
        * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s)
            ^ NumberField.InfinitePlace.nrComplexPlaces K with hF
    have hrwF : (fun s : ℝ => DedekindZeta.ZInfty K (s : ℂ)) = (fun s : ℝ => ((F s : ℝ) : ℂ)) := by
      funext s; rw [zInfty_ofReal K s]
    have h1F : DedekindZeta.ZInfty K (1 : ℂ) = ((F 1 : ℝ) : ℂ) := by
      have : ((1 : ℝ) : ℂ) = (1 : ℂ) := by norm_num
      rw [← this, zInfty_ofReal K 1]
    rw [hrwF, h1F]
    -- `F` is continuous at `1` (all factors continuous for `s` near `1 > 0`).
    have hd : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
    have hFcont : ContinuousAt F 1 := by
      rw [hF]
      have hc1 : ContinuousAt (fun s : ℝ => |(NumberField.discr K : ℝ)| ^ (s / 2)) 1 :=
        (Real.continuousAt_const_rpow hd.ne').comp (continuousAt_id.div_const 2)
      have hc2 : ContinuousAt
          (fun s : ℝ => (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2))
            ^ NumberField.InfinitePlace.nrRealPlaces K) 1 := by
        refine ContinuousAt.pow ?_ _
        refine ContinuousAt.mul ?_ ?_
        · exact (Real.continuousAt_const_rpow Real.pi_ne_zero).comp
            ((continuousAt_id.div_const 2).neg)
        · have hG : ContinuousAt Real.Gamma ((1 : ℝ) / 2) :=
            (Real.differentiableAt_Gamma (s := (1 : ℝ) / 2) (fun m => by
              have hm : (-(m : ℝ)) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
              norm_num; linarith)).continuousAt
          have hinner : ContinuousAt (fun s : ℝ => s / 2) 1 := continuousAt_id.div_const 2
          exact ContinuousAt.comp (g := Real.Gamma) (f := fun s : ℝ => s / 2)
            (by simpa using hG) hinner
      have hc3 : ContinuousAt
          (fun s : ℝ => (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s)
            ^ NumberField.InfinitePlace.nrComplexPlaces K) 1 := by
        refine ContinuousAt.pow ?_ _
        refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) ?_
        · exact (Real.continuousAt_const_rpow (by positivity)).comp continuousAt_id.neg
        · exact (Real.differentiableAt_Gamma (s := (1 : ℝ)) (fun m => by
            have hm : (-(m : ℝ)) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
            norm_num; linarith)).continuousAt
      exact (hc1.mul hc2).mul hc3
    have hco : ContinuousAt (fun s : ℝ => ((F s : ℝ) : ℂ)) 1 :=
      Complex.continuous_ofReal.continuousAt.comp hFcont
    exact hco.tendsto.mono_left nhdsWithin_le_nhds
  have hzeta := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hzeta' : Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * NumberField.dedekindZeta K (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((NumberField.dedekindZeta_residue K : ℝ) : ℂ)) := by
    refine hzeta.congr (fun s => ?_)
    ring
  have hmathlib : Filter.Tendsto
      (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedDedekindZeta K (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (DedekindZeta.ZInfty K (1 : ℂ) * ((NumberField.dedekindZeta_residue K : ℝ) : ℂ))) := by
    rw [Filter.tendsto_congr' hZeq]
    exact hzinf.mul hzeta'
  -- Geometric residue.
  have hgeom := completedDedekindZeta_residue_geometric K
  -- The two limits agree (uniqueness of limits along a nontrivial filter).
  have hbot : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := nhdsWithin_Ioi_neBot (le_refl 1)
  have heq := tendsto_nhds_unique hgeom hmathlib
  -- `ZInfty 1 = √|d|/π^{r₂}` and rearrange to a real identity.
  rw [zInfty_one K] at heq
  -- Take real parts: everything is `ofReal`.
  have hsurf : surfaceVolume K = ((surfaceVolume K).re : ℂ) := by rw [surfaceVolume]; simp
  have hwne : (Units.torsionOrder K : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.Units.torsionOrder_ne_zero K
  -- Convert `heq` (complex) into a real equation between residues.
  have hcomplex : (h : ℝ) * ((surfaceVolume K).re / (Units.torsionOrder K : ℝ))
      = (Real.sqrt |(NumberField.discr K : ℝ)|
            / Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K)
        * NumberField.dedekindZeta_residue K := by
    have h0 := heq
    rw [hsurf] at h0
    -- both sides are `ofReal`s; strip.
    have hlhs : (h : ℂ) * (((surfaceVolume K).re : ℂ) / (Units.torsionOrder K : ℂ))
        = (((h : ℝ) * ((surfaceVolume K).re / (Units.torsionOrder K : ℝ)) : ℝ) : ℂ) := by
      push_cast; ring
    have hrhs : ((Real.sqrt |(NumberField.discr K : ℝ)|
            / Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K : ℝ) : ℂ)
          * ((NumberField.dedekindZeta_residue K : ℝ) : ℂ)
        = (((Real.sqrt |(NumberField.discr K : ℝ)|
            / Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K)
            * NumberField.dedekindZeta_residue K : ℝ) : ℂ) := by
      push_cast; ring
    rw [hlhs, hrhs] at h0
    exact Complex.ofReal_injective h0
  -- Elementary residue identity: `(√|d|/π^{r₂})·κ = classNumber·ρ`.
  have hcnf : (Real.sqrt |(NumberField.discr K : ℝ)|
        / Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K)
        * NumberField.dedekindZeta_residue K
      = (NumberField.classNumber K : ℝ) * partialCompletedZetaResidue K := by
    have hΔ0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
    have hsq : Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 := (Real.sqrt_pos.mpr hΔ0).ne'
    have hpi : Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 :=
      pow_ne_zero _ Real.pi_ne_zero
    have hw : (Units.torsionOrder K : ℝ) ≠ 0 := by
      exact_mod_cast NumberField.Units.torsionOrder_ne_zero K
    rw [NumberField.dedekindZeta_residue_def]
    unfold partialCompletedZetaResidue
    field_simp
    rw [pow_add, mul_pow]
    ring
  -- Combine and cancel `classNumber > 0`.
  rw [hcnf, ← hhcn] at hcomplex
  have hhpos : (0 : ℝ) < (h : ℝ) := by
    rw [hh]; exact_mod_cast Fintype.card_pos
  have hcancel : (surfaceVolume K).re / (Units.torsionOrder K : ℝ) = partialCompletedZetaResidue K :=
    mul_left_cancel₀ (ne_of_gt hhpos) hcomplex
  have hw : (Units.torsionOrder K : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.Units.torsionOrder_ne_zero K
  field_simp [hw] at hcancel
  linarith [hcancel]
end SumProduct
