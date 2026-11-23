-- Prove2me | solution 1 for SumProduct.partialCompletedZetaResidue_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:13:32.594539+00:00
-- url     : https://prove2.me/submissions/757ad374-d548-433c-9f1c-83560b9ee777

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
import Theorems.Thm_SumProduct_orbitTheta_re_nonneg
import Theorems.Thm_SumProduct_orbitThetaFrac_re_nonneg
import Theorems.Thm_SumProduct_completedPartialZeta_real_decomp
import Theorems.Thm_SumProduct_surfaceVolume_re_eq_residue_mul_torsion
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_orbitTheta
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_orbitThetaFrac
import Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_isMellinPair_radialTheta
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialTheta_inversion
import Theorems.Thm_DedekindZeta_MellinPrinciple_mellinTail_integrable_left
import Theorems.Thm_DedekindZeta_MellinPrinciple_mellinTail_integrable_right
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply


section
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
namespace SumProduct
variable (K : Type*) [Field K] [NumberField K]
open DedekindZeta DedekindZeta.ConeRadialReduction DedekindZeta.ConeMellinBridge
  DedekindZeta.MellinPrinciple
open scoped nonZeroDivisors
variable {K} in
/-- A complex number with vanishing imaginary part equals the `ofReal` of its real part. -/
private theorem ofReal_re_of_im_zero {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (Complex.ofReal_re _).symm (h.trans (Complex.ofReal_im _).symm)
private theorem reflectionCore_head_cov (X s : ℝ) (hX : 0 < X) (OT : ℝ → ℝ) :
    (∫ u in Set.Ioi X, OT (u / X) * u ^ (s - 1))
      = X ^ s * ∫ y in Set.Ioi (1 : ℝ), OT y * y ^ (s - 1) := by
  have hcov := integral_comp_mul_left_Ioi
    (fun x : ℝ => OT (x / X) * x ^ (s - 1)) 1 hX
  simp only [mul_one, smul_eq_mul] at hcov
  -- LHS of `hcov` : `∫_{x>1} OT(X·x/X)·(X·x)^{s-1} = X^{s-1}·∫_{x>1} OT(x)·x^{s-1}`.
  have hlhs : (∫ x in Set.Ioi (1 : ℝ), OT (X * x / X) * (X * x) ^ (s - 1))
      = X ^ (s - 1) * ∫ y in Set.Ioi (1 : ℝ), OT y * y ^ (s - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    rw [mul_div_cancel_left₀ y hX.ne', Real.mul_rpow hX.le hy0.le]
    ring
  rw [hlhs] at hcov
  -- `hcov : X^{s-1}·I1 = X⁻¹·H` with `H = ∫_{u>X} OT(u/X)·u^{s-1}`.  So `H = X·X^{s-1}·I1 = X^s·I1`.
  have hXs : X ^ s = X * X ^ (s - 1) := by
    rw [show s = 1 + (s - 1) by ring, Real.rpow_add hX, Real.rpow_one]
    ring_nf
  rw [hXs, mul_assoc, hcov, ← mul_assoc, mul_inv_cancel₀ hX.ne', one_mul]
private theorem reflectionCore_dual_cov (X s : ℝ) (hX : 0 < X) (OTD : ℝ → ℝ) :
    (∫ u in Set.Ioi (1 : ℝ), OTD (X * u) * u ^ (-s))
      = X ^ (s - 1) * ∫ y in Set.Ioi X, OTD y * y ^ (-s) := by
  have hcov := integral_comp_mul_left_Ioi
    (fun x : ℝ => OTD x * (x / X) ^ (-s)) 1 hX
  simp only [mul_one, smul_eq_mul] at hcov
  -- LHS of `hcov`: `∫_{x>1} OTD(X·x)·(X·x/X)^{-s} = ∫_{x>1} OTD(X·x)·x^{-s}`.
  have hlhs : (∫ x in Set.Ioi (1 : ℝ), OTD (X * x) * (X * x / X) ^ (-s))
      = ∫ u in Set.Ioi (1 : ℝ), OTD (X * u) * u ^ (-s) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    rw [mul_div_cancel_left₀ y hX.ne']
  -- RHS of `hcov`: `X⁻¹·∫_{y>X} OTD(y)·(y/X)^{-s} = X⁻¹·X^s·∫_{y>X} OTD(y)·y^{-s}`.
  have hrhs : (X⁻¹ * ∫ y in Set.Ioi X, OTD y * (y / X) ^ (-s))
      = X ^ (s - 1) * ∫ y in Set.Ioi X, OTD y * y ^ (-s) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans hX hy
    have hdr : (y / X) ^ (-s) = y ^ (-s) * X ^ s := by
      rw [Real.div_rpow hy0.le hX.le, Real.rpow_neg hX.le s, div_inv_eq_mul]
    rw [hdr, show s - 1 = s + (-1) by ring, Real.rpow_add hX, Real.rpow_neg_one]
    ring
  rw [hlhs, hrhs] at hcov
  exact hcov
private theorem reflectionCore_inv_cov (X : ℝ) (hX : 1 < X) (H : ℝ → ℝ) :
    (∫ y in Set.Ioo (1 : ℝ) X, H y)
      = ∫ r in Set.Ioo (1 / X) (1 : ℝ), (1 / r ^ 2) * H (1 / r) := by
  have hX0 : (0 : ℝ) < X := lt_trans one_pos hX
  -- The reflection `f r = 1/r` is an injective `C¹` bijection `Ioo (1/X) 1 → Ioo 1 X`,
  -- with derivative `f' r = -1/r²`.
  have hderiv : ∀ r ∈ Set.Ioo (1 / X) (1 : ℝ),
      HasDerivWithinAt (fun r : ℝ => 1 / r) (-1 / r ^ 2) (Set.Ioo (1 / X) (1 : ℝ)) r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := lt_trans (by positivity) hr.1
    have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr0.ne'
    have h2 : HasDerivAt (fun r : ℝ => 1 / r) (-1 / r ^ 2) r := by
      simp only [one_div]
      exact h1.congr_deriv (by rw [neg_div, one_div])
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (fun r : ℝ => 1 / r) (Set.Ioo (1 / X) (1 : ℝ)) := by
    intro a ha b hb hab
    have ha0 : (0 : ℝ) < a := lt_trans (by positivity) ha.1
    have hb0 : (0 : ℝ) < b := lt_trans (by positivity) hb.1
    field_simp at hab
    linarith
  have himg : (fun r : ℝ => 1 / r) '' (Set.Ioo (1 / X) (1 : ℝ)) = Set.Ioo (1 : ℝ) X := by
    ext z
    simp only [Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨r, ⟨hr1, hr2⟩, rfl⟩
      have hr0 : (0 : ℝ) < r := lt_trans (by positivity) hr1
      constructor
      · rw [lt_div_iff₀ hr0, one_mul]; exact hr2
      · rw [div_lt_iff₀ hr0]
        rw [div_lt_iff₀ hX0] at hr1; linarith [hr1]
    · rintro ⟨hz1, hz2⟩
      have hz0 : (0 : ℝ) < z := lt_trans one_pos hz1
      refine ⟨1 / z, ⟨?_, ?_⟩, by rw [one_div_one_div]⟩
      · rw [div_lt_div_iff₀ hX0 hz0, one_mul, one_mul]; exact hz2
      · rw [div_lt_one hz0]; exact hz1
  have key := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv hinj H
  rw [himg] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := lt_trans (by positivity) hr.1
  have habs : |(-1 : ℝ) / r ^ 2| = 1 / r ^ 2 := by
    rw [abs_div, abs_neg, abs_one, abs_of_nonneg (by positivity : (0:ℝ) ≤ r^2)]
  rw [habs, smul_eq_mul]
private theorem reflectionCore_head_integrable (X s : ℝ) (hX : 0 < X) (OT : ℝ → ℝ)
    (hI1 : IntegrableOn (fun y => OT y * y ^ (s - 1)) (Set.Ioi (1 : ℝ))) :
    IntegrableOn (fun u => OT (u / X) * u ^ (s - 1)) (Set.Ioi X) := by
  rw [show X = X * 1 by ring, ← integrableOn_Ioi_comp_mul_left_iff _ 1 hX]
  have hc : IntegrableOn (fun y => X ^ (s - 1) * (OT y * y ^ (s - 1))) (Set.Ioi (1 : ℝ)) :=
    Integrable.const_mul hI1 (X ^ (s - 1))
  refine hc.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  show X ^ (s - 1) * (OT y * y ^ (s - 1)) = OT (X * y / (X * 1)) * (X * y) ^ (s - 1)
  rw [mul_one, mul_div_cancel_left₀ y hX.ne', Real.mul_rpow hX.le hy0.le]
  ring
private theorem reflectionCore_slice (X V s : ℝ) (hX1 : 1 < X) (hs : 1 < s) (OT OTD : ℝ → ℝ)
    (hinv : ∀ r, 0 < r → OTD (1 / r) = X * r * (OT r + V) - V)
    (hOTcont : ContinuousOn OT (Set.Ioi (0 : ℝ))) :
    X ^ (s - 1) * (∫ y in Set.Ioo (1 : ℝ) X, OTD y * y ^ (-s))
        - (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
      = X ^ s * V * ((1 - (1 / X) ^ s) / s)
        - X ^ (s - 1) * V * ((1 - (1 / X) ^ (s - 1)) / (s - 1)) := by
  have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
  have hXinv : (0 : ℝ) < 1 / X := by positivity
  have hXinv1 : 1 / X < 1 := by rw [div_lt_one hX0]; exact hX1
  -- Integrabilities on the bounded slices (continuity on compacts away from 0).
  have hcont_pow1 : ContinuousOn (fun r : ℝ => r ^ (s - 1)) (Set.Icc (1 / X) 1) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro r hr; left
    have : (0 : ℝ) < r := lt_of_lt_of_le hXinv hr.1
    exact this.ne'
  have hcont_pow2 : ContinuousOn (fun r : ℝ => r ^ (s - 2)) (Set.Icc (1 / X) 1) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro r hr; left
    have : (0 : ℝ) < r := lt_of_lt_of_le hXinv hr.1
    exact this.ne'
  have hOT_icc : ContinuousOn (fun r : ℝ => OT r * r ^ (s - 1)) (Set.Icc (1 / X) 1) := by
    refine (hOTcont.mono ?_).mul hcont_pow1
    intro r hr; exact lt_of_lt_of_le hXinv hr.1
  have hint_pow1 : IntegrableOn (fun r : ℝ => r ^ (s - 1)) (Set.Ioo (1 / X) 1) :=
    (hcont_pow1.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hint_pow2 : IntegrableOn (fun r : ℝ => r ^ (s - 2)) (Set.Ioo (1 / X) 1) :=
    (hcont_pow2.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hint_OT : IntegrableOn (fun r : ℝ => OT r * r ^ (s - 1)) (Set.Ioo (1 / X) 1) :=
    (hOT_icc.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  -- Reflect the dual slice integral.
  have hP2 : (∫ y in Set.Ioo (1 : ℝ) X, OTD y * y ^ (-s))
      = ∫ r in Set.Ioo (1 / X) (1 : ℝ), (1 / r ^ 2) * (OTD (1 / r) * (1 / r) ^ (-s)) :=
    reflectionCore_inv_cov X hX1 (fun y => OTD y * y ^ (-s))
  -- Rewrite the reflected integrand to `X·OT(r)·r^{s-1} + X·V·r^{s-1} − V·r^{s-2}`.
  have hP2' : (∫ r in Set.Ioo (1 / X) (1 : ℝ), (1 / r ^ 2) * (OTD (1 / r) * (1 / r) ^ (-s)))
      = ∫ r in Set.Ioo (1 / X) (1 : ℝ),
          (X * (OT r * r ^ (s - 1)) + X * V * r ^ (s - 1) - V * r ^ (s - 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hXinv hr.1.le
    rw [hinv r hr0]
    -- `(1/r)^{-s} = r^s`
    have hpr : (1 / r) ^ (-s) = r ^ s := by
      rw [one_div, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le, neg_neg]
    rw [hpr]
    -- `1/r^2 = r^{-2}`, then collect powers
    have e1 : (1 / r ^ 2) * r ^ s = r ^ (s - 2) := by
      have h2 : (r : ℝ) ^ (2 : ℕ) = r ^ (2 : ℝ) := by
        rw [← Real.rpow_natCast r 2]; norm_num
      rw [div_mul_eq_mul_div, one_mul, show (r ^ 2 : ℝ) = r ^ (2 : ℕ) by norm_num, h2,
        ← Real.rpow_sub hr0]
    have e2 : r ^ (s - 2) * r = r ^ (s - 1) := by
      rw [show (s - 1) = (s - 2) + 1 by ring, Real.rpow_add hr0, Real.rpow_one]
    -- expand
    have : (1 / r ^ 2) * ((X * r * (OT r + V) - V) * r ^ s)
        = X * (r ^ (s - 2) * r) * (OT r + V) - V * (r ^ (s - 2)) := by
      rw [show (X * r * (OT r + V) - V) * r ^ s
          = X * r * (OT r + V) * r ^ s - V * r ^ s by ring]
      rw [mul_sub]
      congr 1
      · rw [show (1 / r ^ 2) * (X * r * (OT r + V) * r ^ s)
            = X * r * (OT r + V) * ((1 / r ^ 2) * r ^ s) by ring, e1]; ring
      · rw [show (1 / r ^ 2) * (V * r ^ s) = V * ((1 / r ^ 2) * r ^ s) by ring, e1]
    rw [this, e2]; ring
  -- Reflect the `OT(u/X)·u^{s-1}` slice via `u = X·r` to `X^s·∫_{(1/X,1)} OT(r)·r^{s-1}`.
  have hP1 : (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
      = X ^ s * ∫ r in Set.Ioo (1 / X) (1 : ℝ), OT r * r ^ (s - 1) := by
    -- `u = X·r` maps `(1/X,1) → (1,X)` with derivative `X`.
    have hderiv : ∀ r ∈ Set.Ioo (1 / X) (1 : ℝ),
        HasDerivWithinAt (fun r : ℝ => X * r) X (Set.Ioo (1 / X) (1 : ℝ)) r := by
      intro r _
      simpa using ((hasDerivAt_id r).const_mul X).hasDerivWithinAt
    have hinj : Set.InjOn (fun r : ℝ => X * r) (Set.Ioo (1 / X) (1 : ℝ)) := by
      intro a _ b _ hab; exact mul_left_cancel₀ hX0.ne' hab
    have himg : (fun r : ℝ => X * r) '' (Set.Ioo (1 / X) (1 : ℝ)) = Set.Ioo (1 : ℝ) X := by
      ext z
      simp only [Set.mem_image, Set.mem_Ioo]
      constructor
      · rintro ⟨r, ⟨hr1, hr2⟩, rfl⟩
        have hr0 : (0 : ℝ) < r := lt_trans hXinv hr1
        rw [div_lt_iff₀ hX0] at hr1
        constructor
        · nlinarith [hr1]
        · nlinarith [hr2]
      · rintro ⟨hz1, hz2⟩
        have hz0 : (0 : ℝ) < z := lt_trans one_pos hz1
        refine ⟨z / X, ⟨?_, ?_⟩, by rw [mul_div_cancel₀ z hX0.ne']⟩
        · rw [lt_div_iff₀ hX0, div_mul_cancel₀ 1 hX0.ne']; exact hz1
        · rw [div_lt_one hX0]; exact hz2
    have key := integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioo hderiv hinj (fun u => OT (u / X) * u ^ (s - 1))
    rw [himg] at key
    rw [key, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hXinv hr.1.le
    have hXs : X * X ^ (s - 1) = X ^ s := by
      have : X ^ (1 : ℝ) * X ^ (s - 1) = X ^ (1 + (s - 1)) := (Real.rpow_add hX0 _ _).symm
      rw [Real.rpow_one] at this; rw [this]; congr 1; ring
    rw [abs_of_pos hX0, smul_eq_mul, mul_div_cancel_left₀ r hX0.ne',
      Real.mul_rpow hX0.le hr0.le]
    rw [show X * (OT r * (X ^ (s - 1) * r ^ (s - 1)))
        = (X * X ^ (s - 1)) * (OT r * r ^ (s - 1)) by ring, hXs]
  -- Pure-power interval integrals over `(1/X, 1)`.
  have hA : (∫ r in Set.Ioo (1 / X) (1 : ℝ), r ^ (s - 1)) = (1 - (1 / X) ^ s) / s := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hXinv1.le,
      integral_rpow (Or.inl (by linarith))]
    rw [show s - 1 + 1 = s by ring, Real.one_rpow]
  have hB : (∫ r in Set.Ioo (1 / X) (1 : ℝ), r ^ (s - 2)) = (1 - (1 / X) ^ (s - 1)) / (s - 1) := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hXinv1.le,
      integral_rpow (Or.inl (by linarith))]
    rw [show s - 2 + 1 = s - 1 by ring, Real.one_rpow]
  -- Assemble: split the reflected integral by linearity, substitute, and cancel the `OT`-piece.
  have hsplit : (∫ r in Set.Ioo (1 / X) (1 : ℝ),
        (X * (OT r * r ^ (s - 1)) + X * V * r ^ (s - 1) - V * r ^ (s - 2)))
      = X * (∫ r in Set.Ioo (1 / X) (1 : ℝ), OT r * r ^ (s - 1))
        + X * V * (∫ r in Set.Ioo (1 / X) (1 : ℝ), r ^ (s - 1))
        - V * (∫ r in Set.Ioo (1 / X) (1 : ℝ), r ^ (s - 2)) := by
    have hsub : (∫ r in Set.Ioo (1 / X) (1 : ℝ),
          ((X * (OT r * r ^ (s - 1)) + X * V * r ^ (s - 1)) - V * r ^ (s - 2)))
        = (∫ r in Set.Ioo (1 / X) (1 : ℝ), (X * (OT r * r ^ (s - 1)) + X * V * r ^ (s - 1)))
          - ∫ r in Set.Ioo (1 / X) (1 : ℝ), V * r ^ (s - 2) :=
      MeasureTheory.integral_sub
        ((hint_OT.const_mul X).add (hint_pow1.const_mul (X * V))) (hint_pow2.const_mul V)
    have hadd : (∫ r in Set.Ioo (1 / X) (1 : ℝ), (X * (OT r * r ^ (s - 1)) + X * V * r ^ (s - 1)))
        = (∫ r in Set.Ioo (1 / X) (1 : ℝ), X * (OT r * r ^ (s - 1)))
          + ∫ r in Set.Ioo (1 / X) (1 : ℝ), X * V * r ^ (s - 1) :=
      MeasureTheory.integral_add (hint_OT.const_mul X) (hint_pow1.const_mul (X * V))
    rw [hsub, hadd, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hP2, hP2', hsplit, hP1, hA, hB]
  -- Now everything is in closed form; the `X^s·∫OT` pieces cancel after `X^{s-1}·X = X^s`.
  have hXpow : X ^ s = X ^ (s - 1) * X := by
    have : X ^ (s - 1) * X ^ (1 : ℝ) = X ^ (s - 1 + 1) := (Real.rpow_add hX0 _ _).symm
    rw [Real.rpow_one] at this
    rw [this]; congr 1; ring
  rw [hXpow]
  ring
private theorem reflectionCore_main (X V a s : ℝ) (hX1le : 1 ≤ X) (hs : 1 < s) (OT OTD : ℝ → ℝ)
    (hinv : ∀ r, 0 < r → OTD (1 / r) = X * r * (OT r + V) - V)
    (hI1 : IntegrableOn (fun y => OT y * y ^ (s - 1)) (Set.Ioi (1 : ℝ)))
    (hI2 : IntegrableOn (fun y => OTD y * y ^ (-s)) (Set.Ioi (1 : ℝ)))
    (hOTcont : ContinuousOn OT (Set.Ioi (0 : ℝ)))
    (hOTDcont : ContinuousOn OTD (Set.Ioi (0 : ℝ))) :
    a * X ^ s * (-V / s + (V / X) / (s - 1))
        + a * X ^ s * (∫ y in Set.Ioi (1 : ℝ), OT y * y ^ (s - 1))
        + a * X ^ (s - 1) * (∫ y in Set.Ioi (1 : ℝ), OTD y * y ^ (-s))
      = a * V / (s * (s - 1))
        + a * (∫ u in Set.Ioi (1 : ℝ), OT (u / X) * u ^ (s - 1))
        + a * (∫ u in Set.Ioi (1 : ℝ), OTD (X * u) * u ^ (-s)) := by
  rcases eq_or_lt_of_le hX1le with hXeq | hX1
  · -- `X = 1`: the slice integrals are over the empty interval; pure pole algebra.
    subst hXeq
    have hs0 : s ≠ 0 := by linarith
    have hs10 : s - 1 ≠ 0 := by linarith
    simp only [Real.one_rpow, one_mul, div_one, mul_one]
    field_simp
    ring
  have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
  have hXinv : (0 : ℝ) < 1 / X := by positivity
  -- Bounded-slice integrabilities (continuity on `[1,X] ⊂ Ioi 0`).
  have hcont_pow1 : ContinuousOn (fun u : ℝ => u ^ (s - 1)) (Set.Icc (1 : ℝ) X) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro u hu; left; exact (lt_of_lt_of_le one_pos hu.1).ne'
  have hcont_pownegs : ContinuousOn (fun u : ℝ => u ^ (-s)) (Set.Icc (1 : ℝ) X) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro u hu; left; exact (lt_of_lt_of_le one_pos hu.1).ne'
  have hOTcomp : ContinuousOn (fun u : ℝ => OT (u / X)) (Set.Icc (1 : ℝ) X) := by
    apply hOTcont.comp (continuousOn_id.div_const X)
    intro u hu
    have : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu.1
    simp only [Set.mem_Ioi]; positivity
  have hint_P1 : IntegrableOn (fun u => OT (u / X) * u ^ (s - 1)) (Set.Ioo (1 : ℝ) X) :=
    ((hOTcomp.mul hcont_pow1).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hint_P2 : IntegrableOn (fun y => OTD y * y ^ (-s)) (Set.Ioo (1 : ℝ) X) :=
    (((hOTDcont.mono (fun u hu => lt_of_lt_of_le one_pos hu.1)).mul
      hcont_pownegs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  -- Split `J1` and `I2` at `X`:  `Ioi 1 = Ioo 1 X ∪ Ici X`.
  have hunion : Set.Ioo (1 : ℝ) X ∪ Set.Ici X = Set.Ioi (1 : ℝ) := Set.Ioo_union_Ici_eq_Ioi hX1
  have hdisj : Disjoint (Set.Ioo (1 : ℝ) X) (Set.Ici X) := by
    rw [Set.disjoint_left]
    rintro u hu hu'
    exact absurd hu.2 (not_lt.mpr hu')
  -- `∫_{Ici X} = ∫_{Ioi X}` (the single point `X` is null).
  have hIciX_OT : (∫ u in Set.Ici X, OT (u / X) * u ^ (s - 1))
      = ∫ u in Set.Ioi X, OT (u / X) * u ^ (s - 1) :=
    setIntegral_congr_set (Ioi_ae_eq_Ici).symm
  have hIciX_OTD : (∫ y in Set.Ici X, OTD y * y ^ (-s))
      = ∫ y in Set.Ioi X, OTD y * y ^ (-s) :=
    setIntegral_congr_set (Ioi_ae_eq_Ici).symm
  -- `J1 = ∫_{Ioo 1 X} + ∫_{Ioi X}`, and `∫_{Ioi X} OT(u/X)u^{s-1} = X^s·I1`.
  have hint_headX : IntegrableOn (fun u => OT (u / X) * u ^ (s - 1)) (Set.Ioi X) :=
    reflectionCore_head_integrable X s hX0 OT hI1
  have hint_headXci : IntegrableOn (fun u => OT (u / X) * u ^ (s - 1)) (Set.Ici X) :=
    hint_headX.congr_set_ae (Ioi_ae_eq_Ici).symm
  have hint_I2Xci : IntegrableOn (fun y => OTD y * y ^ (-s)) (Set.Ici X) :=
    (hI2.mono_set (Set.Ioi_subset_Ioi hX1.le)).congr_set_ae (Ioi_ae_eq_Ici).symm
  have hJ1 : (∫ u in Set.Ioi (1 : ℝ), OT (u / X) * u ^ (s - 1))
      = (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
        + X ^ s * ∫ y in Set.Ioi (1 : ℝ), OT y * y ^ (s - 1) := by
    have hu : (∫ u in Set.Ioi (1 : ℝ), OT (u / X) * u ^ (s - 1))
        = (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
          + ∫ u in Set.Ici X, OT (u / X) * u ^ (s - 1) := by
      rw [← setIntegral_union hdisj measurableSet_Ici hint_P1 hint_headXci, hunion]
    rw [hu, hIciX_OT, reflectionCore_head_cov X s hX0 OT]
  -- `I2 = ∫_{Ioo 1 X} OTD y^{-s} + ∫_{Ioi X} OTD y^{-s}`, and `J2 = X^{s-1}·∫_{Ioi X} OTD y^{-s}`.
  have hI2split : (∫ y in Set.Ioi (1 : ℝ), OTD y * y ^ (-s))
      = (∫ y in Set.Ioo (1 : ℝ) X, OTD y * y ^ (-s))
        + ∫ y in Set.Ioi X, OTD y * y ^ (-s) := by
    rw [← hIciX_OTD, ← setIntegral_union hdisj measurableSet_Ici hint_P2 hint_I2Xci, hunion]
  have hJ2 : (∫ u in Set.Ioi (1 : ℝ), OTD (X * u) * u ^ (-s))
      = X ^ (s - 1) * ∫ y in Set.Ioi X, OTD y * y ^ (-s) :=
    reflectionCore_dual_cov X s hX0 OTD
  -- The slice identity.
  have hslice := reflectionCore_slice X V s hX1 hs OT OTD hinv hOTcont
  -- `X^s·(1/X)^s = 1` and `X^{s-1}·(1/X)^{s-1} = 1` (clears the pole bookkeeping).
  have hpow_s : X ^ s * (1 / X) ^ s = 1 := by
    rw [one_div, Real.inv_rpow hX0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hX0 s).ne']
  have hpow_s1 : X ^ (s - 1) * (1 / X) ^ (s - 1) = 1 := by
    rw [one_div, Real.inv_rpow hX0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hX0 (s - 1)).ne']
  -- Assemble: substitute `J1`, `I2`-split, `J2` into the goal, then use `hslice`.
  rw [hJ1, hI2split, hJ2]
  -- The remaining identity is purely algebraic given `hslice`, `hpow_s`, `hpow_s1`.
  -- `hslice : X^{s-1}·P2 − P1 = X^s·V·A − X^{s-1}·V·B` with `A = (1−(1/X)^s)/s`, `B = ...`.
  have key : X ^ (s - 1) * (∫ y in Set.Ioo (1 : ℝ) X, OTD y * y ^ (-s))
      - (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
      = X ^ s * V * ((1 - (1 / X) ^ s) / s)
        - X ^ (s - 1) * V * ((1 - (1 / X) ^ (s - 1)) / (s - 1)) := hslice
  -- Now everything is closed-form.  Expand `(1/X)^s`, `(1/X)^{s-1}` via the cancellation facts.
  have hXspos : (0 : ℝ) < X ^ s := Real.rpow_pos_of_pos hX0 s
  have hXs1pos : (0 : ℝ) < X ^ (s - 1) := Real.rpow_pos_of_pos hX0 (s - 1)
  have hinvA : (1 / X) ^ s = (X ^ s)⁻¹ := by
    rw [eq_comm, inv_eq_of_mul_eq_one_left]; rw [mul_comm]; exact hpow_s
  have hinvB : (1 / X) ^ (s - 1) = (X ^ (s - 1))⁻¹ := by
    rw [eq_comm, inv_eq_of_mul_eq_one_left]; rw [mul_comm]; exact hpow_s1
  have hAexp : X ^ s * V * ((1 - (1 / X) ^ s) / s) = V * (X ^ s - 1) / s := by
    rw [hinvA]; field_simp
  have hBexp : X ^ (s - 1) * V * ((1 - (1 / X) ^ (s - 1)) / (s - 1))
      = V * (X ^ (s - 1) - 1) / (s - 1) := by
    rw [hinvB]; field_simp
  rw [hAexp, hBexp] at key
  -- Final algebra:  use `key` to eliminate the slice integrals; `s ≠ 0`, `s − 1 ≠ 0`.
  have hs0 : s ≠ 0 := by linarith
  have hs10 : s - 1 ≠ 0 := by linarith
  -- Substitute the slice integrals via `key` (treated as `A_int = B_int + closed`).
  have hP1eq : (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
      = X ^ (s - 1) * (∫ y in Set.Ioo (1 : ℝ) X, OTD y * y ^ (-s))
        - (V * (X ^ s - 1) / s - V * (X ^ (s - 1) - 1) / (s - 1)) := by
    linarith [key]
  rw [hP1eq]
  have hXpow : X ^ s = X ^ (s - 1) * X := by
    have h := (Real.rpow_add hX0 (s - 1) 1).symm
    rw [Real.rpow_one] at h
    rw [h]; congr 1; ring
  rw [hXpow]
  field_simp
  ring
end SumProduct
end

set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open SumProduct
variable (K : Type*) [Field K] [NumberField K]
open DedekindZeta DedekindZeta.ConeRadialReduction DedekindZeta.ConeMellinBridge
  DedekindZeta.MellinPrinciple
open scoped nonZeroDivisors
variable {K}
namespace SumProduct
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) {s : ℝ} (hs : 1 < s) :
    partialCompletedZetaResidue K ≤
      s * (s - 1) * (DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ)).re := by
  set X : ℝ := Theta.covolume K 𝔞 with hX
  set a : ℝ := 1 / (Units.torsionOrder K : ℝ) with ha
  set ρ : ℝ := partialCompletedZetaResidue K with hρ
  set OT : ℝ → ℝ := fun u => (orbitTheta K 𝔞 u).re with hOT
  set OTD : ℝ → ℝ := fun u => (orbitThetaFrac K (Theta.dualIdeal K 𝔞) u).re with hOTD
  -- Positivity facts on `X` (covolume = 𝔑(𝔞)·√|d| > 0).
  have hXpos : 0 < X := by
    rw [hX, Theta.covolume]
    have hNpos : (0 : ℝ) < (Ideal.absNorm 𝔞 : ℝ) := by
      have : Ideal.absNorm 𝔞 ≠ 0 := fun h =>
        hne (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
      positivity
    have hd : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
    have : (0 : ℝ) < Real.sqrt |(NumberField.discr K : ℝ)| := Real.sqrt_pos.mpr hd
    positivity
  set V : ℝ := (surfaceVolume K).re with hV
  -- `ρ = a·V` (residue identity `V = ρ·w` and `a = 1/w`).
  have hρaV : ρ = a * V := by
    rw [hρ, hV, ha, surfaceVolume_re_eq_residue_mul_torsion K]
    have hw : (Units.torsionOrder K : ℝ) ≠ 0 := by
      exact_mod_cast NumberField.Units.torsionOrder_ne_zero K
    field_simp
  -- The `IsMellinPair` packaging (continuity, decay/integrability, inversion).
  obtain ⟨_c, _α, hpair⟩ := exists_isMellinPair_radialTheta (K := K) 𝔞 hne
  -- Real inversion law: `OTD (1/r) = X·r·(OT r + V) − V`.
  have hsurf : surfaceVolume K = ((surfaceVolume K).re : ℂ) := by rw [surfaceVolume]; simp
  have hcovC : (Theta.covolume K 𝔞 : ℂ)⁻¹ = ((1 / X : ℝ) : ℂ) := by
    rw [hX]; push_cast; ring
  have hinv : ∀ r, 0 < r → OTD (1 / r) = X * r * (OT r + V) - V := by
    intro r hr
    have hrinv : (0 : ℝ) < 1 / r := by positivity
    -- Apply the complex inversion at `1/r` (so `1/(1/r) = r`).
    have hI := radialTheta_inversion (K := K) 𝔞 hne (1 / r) hrinv
    rw [one_div_one_div] at hI
    obtain ⟨ho1, _⟩ := orbitTheta_re_nonneg 𝔞 r
    obtain ⟨ho2, _⟩ := orbitThetaFrac_re_nonneg (Theta.dualIdeal K 𝔞) (1 / r)
    -- Express both sides of `hI` as `ofReal`s, then strip via injectivity.
    have hOTr : orbitTheta K 𝔞 r = ((OT r : ℝ) : ℂ) := by
      rw [hOT]; exact ofReal_re_of_im_zero ho1
    have hOTDr : orbitThetaFrac K (Theta.dualIdeal K 𝔞) (1 / r) = ((OTD (1 / r) : ℝ) : ℂ) := by
      rw [hOTD]; exact ofReal_re_of_im_zero ho2
    have hRT : radialTheta K 𝔞 r = ((OT r + V : ℝ) : ℂ) := by
      rw [radialTheta, hOTr, hsurf, ← Complex.ofReal_add]
    have hRTD : radialThetaDual K 𝔞 (1 / r) = ((OTD (1 / r) + V : ℝ) : ℂ) := by
      rw [radialThetaDual, hOTDr, hsurf, ← Complex.ofReal_add]
    rw [hRT, hRTD, hcovC, Real.rpow_one] at hI
    -- `hI : (OT r + V : ℂ) = (1/X : ℂ)·(1/r : ℂ)·(OTD(1/r) + V : ℂ)`
    have hIr : (OT r + V) = (1 / X) * (1 / r) * (OTD (1 / r) + V) := by
      have h := hI
      push_cast at h
      exact_mod_cast h
    -- Solve for `OTD (1/r)`:  multiply by `X·r` and rearrange.
    have hmul : X * r * (OT r + V) = OTD (1 / r) + V := by
      rw [hIr]; field_simp
    linarith [hmul]
  -- Real tail integrabilities, from the complex `mellinTail_integrable_left/right` via `.re`.
  have hI1 : IntegrableOn (fun y => OT y * y ^ (s - 1)) (Set.Ioi (1 : ℝ)) := by
    have hC := mellinTail_integrable_left hpair (s := (s : ℂ))
    have hre : IntegrableOn (fun y => (((radialTheta K 𝔞 y - surfaceVolume K)
        * (y : ℂ) ^ ((s : ℂ) - 1)).re)) (Set.Ioi (1 : ℝ)) := hC.re
    refine hre.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    obtain ⟨ho1, _⟩ := orbitTheta_re_nonneg 𝔞 y
    have hfa : radialTheta K 𝔞 y - surfaceVolume K = ((OT y : ℝ) : ℂ) := by
      rw [radialTheta, add_sub_cancel_right, hOT]; exact ofReal_re_of_im_zero ho1
    have hpw : (y : ℂ) ^ ((s : ℂ) - 1) = ((y ^ (s - 1) : ℝ) : ℂ) := by
      rw [show ((s : ℂ) - 1) = (((s - 1 : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hy0.le]
    show (((radialTheta K 𝔞 y - surfaceVolume K) * (y : ℂ) ^ ((s : ℂ) - 1)).re) = OT y * y ^ (s - 1)
    rw [hfa, hpw, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hI2 : IntegrableOn (fun y => OTD y * y ^ (-s)) (Set.Ioi (1 : ℝ)) := by
    have hC := mellinTail_integrable_right hpair (s := (s : ℂ))
    have hre : IntegrableOn (fun y => (((Theta.covolume K 𝔞 : ℂ)⁻¹
        * (radialThetaDual K 𝔞 y - surfaceVolume K)
        * (y : ℂ) ^ ((1 : ℂ) - (s : ℂ) - 1)).re)) (Set.Ioi (1 : ℝ)) := hC.re
    -- `hre` is integrability of `(1/X)·OTD y·y^{-s}`; scale by `X`.
    have hreX : IntegrableOn (fun y => X * (((Theta.covolume K 𝔞 : ℂ)⁻¹
        * (radialThetaDual K 𝔞 y - surfaceVolume K)
        * (y : ℂ) ^ ((1 : ℂ) - (s : ℂ) - 1)).re)) (Set.Ioi (1 : ℝ)) :=
      Integrable.const_mul hre X
    refine hreX.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    obtain ⟨ho2, _⟩ := orbitThetaFrac_re_nonneg (Theta.dualIdeal K 𝔞) y
    have hga : radialThetaDual K 𝔞 y - surfaceVolume K = ((OTD y : ℝ) : ℂ) := by
      rw [radialThetaDual, add_sub_cancel_right, hOTD]; exact ofReal_re_of_im_zero ho2
    have hpw : (y : ℂ) ^ (((1 : ℝ) : ℂ) - (s : ℂ) - 1) = ((y ^ (-s) : ℝ) : ℂ) := by
      rw [show ((1 : ℝ) : ℂ) - (s : ℂ) - 1 = ((-s : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hy0.le]
    show X * (((Theta.covolume K 𝔞 : ℂ)⁻¹ * (radialThetaDual K 𝔞 y - surfaceVolume K)
        * (y : ℂ) ^ ((1 : ℂ) - (s : ℂ) - 1)).re) = OTD y * y ^ (-s)
    rw [show ((1 : ℂ) - (s : ℂ) - 1) = (((1 : ℝ) : ℂ) - (s : ℂ) - 1) by push_cast; ring,
      hga, hpw, hcovC]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re, hX]
    have hcovne : Theta.covolume K 𝔞 ≠ 0 := by rw [← hX]; exact hXpos.ne'
    field_simp [hcovne]
  -- Continuity of `OT`, `OTD` on `Ioi 0`, from the continuity of `orbitTheta`/`orbitThetaFrac`.
  have hOTcont : ContinuousOn OT (Set.Ioi (0 : ℝ)) := by
    rw [hOT]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_orbitTheta K 𝔞)
  have hOTDcont : ContinuousOn OTD (Set.Ioi (0 : ℝ)) := by
    rw [hOTD]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_orbitThetaFrac K (Theta.dualIdeal K 𝔞))
  -- `X ≥ 1`:  `X = 𝔑(𝔞)·√|d|`, both factors `≥ 1`.
  have hX1le : (1 : ℝ) ≤ X := by
    rw [hX, Theta.covolume]
    have hN1 : (1 : ℝ) ≤ (Ideal.absNorm 𝔞 : ℝ) := by
      have hpos : 0 < Ideal.absNorm 𝔞 := by
        rcases Nat.eq_zero_or_pos (Ideal.absNorm 𝔞) with h0 | hp
        · exact absurd (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h0) hne
        · exact hp
      exact_mod_cast hpos
    have hd1 : (1 : ℝ) ≤ Real.sqrt |(NumberField.discr K : ℝ)| := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      apply Real.sqrt_le_sqrt
      have hz : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs (NumberField.discr_ne_zero K)
      have hr : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast hz
      rw [Int.cast_abs] at hr; simpa using hr
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (Ideal.absNorm 𝔞 : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)| :=
          mul_le_mul hN1 hd1 (by norm_num) (by positivity)
  -- Assemble a clean `u`-tail decomposition, but do not package the tails as `Φ, Ψ`.
  set I1 : ℝ := ∫ y in Set.Ioi (1 : ℝ), OT y * y ^ (s - 1) with hI1def
  set I2 : ℝ := ∫ y in Set.Ioi (1 : ℝ), OTD y * y ^ (-s) with hI2def
  set J1 : ℝ := ∫ u in Set.Ioi (1 : ℝ), OT (u / X) * u ^ (s - 1) with hJ1def
  set J2 : ℝ := ∫ u in Set.Ioi (1 : ℝ), OTD (X * u) * u ^ (-s) with hJ2def
  -- `pf = a·X^s` (the prefactor matches, using `X = 𝔑·√|d|`, `a = 1/w`).
  have hpf : (1 / (Units.torsionOrder K : ℝ)) * (Ideal.absNorm 𝔞 : ℝ) ^ s
      * (|(NumberField.discr K : ℝ)|) ^ (s / 2) = a * X ^ s := by
    rw [ha, hX, Theta.covolume, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)]
    have hsqrt : (Real.sqrt |(NumberField.discr K : ℝ)|) ^ s = |(NumberField.discr K : ℝ)| ^ (s / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
      congr 1; ring
    rw [hsqrt]; ring
  -- `T.re = I1 + (1/X)·I2` (the real tail form of `mellinTail`).
  have hTre : (mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
        (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 (s : ℂ)).re
      = I1 + (1 / X) * I2 := by
    have htailReal : mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
        (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 (s : ℂ)
        = ((∫ y in Set.Ioi (1 : ℝ),
            ((orbitTheta K 𝔞 y).re * y ^ (s - 1)
              + (1 / Theta.covolume K 𝔞)
                * (orbitThetaFrac K (Theta.dualIdeal K 𝔞) y).re * y ^ (-s))) : ℝ) := by
      rw [mellinTail, ← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
      have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
      obtain ⟨ho1, _⟩ := orbitTheta_re_nonneg 𝔞 y
      obtain ⟨ho2, _⟩ := orbitThetaFrac_re_nonneg (Theta.dualIdeal K 𝔞) y
      have hfa : radialTheta K 𝔞 y - surfaceVolume K = ((orbitTheta K 𝔞 y).re : ℂ) := by
        rw [radialTheta, add_sub_cancel_right]; exact ofReal_re_of_im_zero ho1
      have hga : radialThetaDual K 𝔞 y - surfaceVolume K
          = ((orbitThetaFrac K (Theta.dualIdeal K 𝔞) y).re : ℂ) := by
        rw [radialThetaDual, add_sub_cancel_right]; exact ofReal_re_of_im_zero ho2
      rw [hfa, hga]
      have hpow1 : (y : ℂ) ^ ((s : ℂ) - 1) = ((y ^ (s - 1) : ℝ) : ℂ) := by
        rw [show ((s : ℂ) - 1) = (((s - 1 : ℝ)) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow hy0.le]
      have hpow2 : (y : ℂ) ^ (((1 : ℝ) : ℂ) - (s : ℂ) - 1) = ((y ^ (-s) : ℝ) : ℂ) := by
        rw [show ((1 : ℝ) : ℂ) - (s : ℂ) - 1 = ((-s : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow hy0.le]
      rw [hpow1, hpow2, hcovC]
      push_cast; ring
    rw [htailReal, Complex.ofReal_re]
    -- Split the integral by linearity into `I1 + (1/X)·I2`.
    have hsplit : (∫ y in Set.Ioi (1 : ℝ),
          ((orbitTheta K 𝔞 y).re * y ^ (s - 1)
            + (1 / Theta.covolume K 𝔞)
              * (orbitThetaFrac K (Theta.dualIdeal K 𝔞) y).re * y ^ (-s)))
        = I1 + (1 / X) * I2 := by
      rw [hI1def, hI2def, hX]
      have hint_a : IntegrableOn (fun y => (orbitTheta K 𝔞 y).re * y ^ (s - 1))
          (Set.Ioi (1 : ℝ)) :=
        IntegrableOn.congr_fun hI1 (fun y _ => by rw [hOT]) measurableSet_Ioi
      have hint_b : IntegrableOn (fun y => 1 / Theta.covolume K 𝔞
          * (orbitThetaFrac K (Theta.dualIdeal K 𝔞) y).re * y ^ (-s)) (Set.Ioi (1 : ℝ)) := by
        have : IntegrableOn (fun y => (1 / Theta.covolume K 𝔞) * (OTD y * y ^ (-s)))
            (Set.Ioi (1 : ℝ)) := Integrable.const_mul hI2 _
        exact IntegrableOn.congr_fun this (fun y _ => by rw [hOTD]; ring) measurableSet_Ioi
      rw [MeasureTheory.integral_add hint_a hint_b]
      congr 1
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
      rw [hOTD]; ring
    rw [hsplit]
  have hclean : (DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ)).re
      = a * V / (s * (s - 1)) + a * J1 + a * J2 := by
    have hmain := reflectionCore_main X V a s hX1le hs OT OTD hinv hI1 hI2 hOTcont hOTDcont
    rw [completedPartialZeta_real_decomp 𝔞 hne hs, hpf, hTre]
    rw [← hV, ← hX]
    rw [show a * X ^ s * ((-V / s + 1 / X * V / (s - 1)) + (I1 + 1 / X * I2))
        = a * X ^ s * (-V / s + (V / X) / (s - 1)) + a * X ^ s * I1
          + a * X ^ s * (1 / X) * I2 by ring]
    rw [show a * X ^ s * (1 / X) = a * X ^ (s - 1) by
      rw [show X ^ s = X ^ (s - 1) * X by
        have h := (Real.rpow_add hXpos (s - 1) 1).symm
        rw [Real.rpow_one] at h; rw [h]; congr 1; ring]
      field_simp]
    rw [hI1def, hI2def, hJ1def, hJ2def]
    exact hmain
  -- The clean `u`-tails are nonnegative, so multiplying the clean decomposition by `s*(s-1)`
  -- dominates the residue.
  have ha_nonneg : 0 ≤ a := by rw [ha]; positivity
  have hJ1_nonneg : 0 ≤ J1 := by
    rw [hJ1def]
    refine setIntegral_nonneg measurableSet_Ioi (fun u hu => ?_)
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (lt_trans one_pos hu)
    have hOTnn : 0 ≤ OT (u / X) := by
      rw [hOT]
      exact (orbitTheta_re_nonneg 𝔞 (u / X)).2
    exact mul_nonneg hOTnn (Real.rpow_nonneg hu0 _)
  have hJ2_nonneg : 0 ≤ J2 := by
    rw [hJ2def]
    refine setIntegral_nonneg measurableSet_Ioi (fun u hu => ?_)
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (lt_trans one_pos hu)
    have hOTDnn : 0 ≤ OTD (X * u) := by
      rw [hOTD]
      exact (orbitThetaFrac_re_nonneg (Theta.dualIdeal K 𝔞) (X * u)).2
    exact mul_nonneg hOTDnn (Real.rpow_nonneg hu0 _)
  have htail_nonneg : 0 ≤ a * J1 + a * J2 :=
    add_nonneg (mul_nonneg ha_nonneg hJ1_nonneg) (mul_nonneg ha_nonneg hJ2_nonneg)
  rw [hclean]
  change ρ ≤ s * (s - 1) * (a * V / (s * (s - 1)) + a * J1 + a * J2)
  rw [hρaV]
  have hssne : s * (s - 1) ≠ 0 := by positivity
  have hss_nonneg : 0 ≤ s * (s - 1) := by positivity
  have htail_scaled : 0 ≤ s * (s - 1) * (a * J1 + a * J2) :=
    mul_nonneg hss_nonneg htail_nonneg
  have heq : s * (s - 1) * (a * V / (s * (s - 1)) + a * J1 + a * J2)
      = a * V + s * (s - 1) * (a * J1 + a * J2) := by
    rw [show a * V / (s * (s - 1)) + a * J1 + a * J2
        = a * V / (s * (s - 1)) + (a * J1 + a * J2) by ring,
      mul_add, mul_div_cancel₀ _ hssne]
  rw [heq]
  linarith
end SumProduct
