-- Prove2me | solution 1 for SNumbers.piLp_norm_le_of_exponent_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:25:13.147162+00:00
-- url     : https://prove2.me/submissions/af57b7e7-30ac-470e-817c-4fc7f7b1cf03

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_DiagonalMatrices
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_idEmbed_apply
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SNumbers_toReal_pos_of_ne_top
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.idEmbed_apply
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
namespace SNumbers
theorem _root_.solution [Nonempty (Fin m)] (hqp : q ≤ p) (f : Fin m → 𝕜) :
    ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜))‖
      ≤ ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜))‖ := by
  have hfp : ∀ i, (WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜)) i = f i := fun _ => rfl
  have hfq : ∀ i, (WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜)) i = f i := fun _ => rfl
  rcases p.dichotomy with rfl | hp
  · -- `p = ∞`: the sup is dominated by any `ℓ^q`-norm.
    rw [PiLp.norm_eq_ciSup]
    rcases q.dichotomy with rfl | hq
    · rw [PiLp.norm_eq_ciSup]
    · have hQ : 0 < q.toReal := zero_lt_one.trans_le hq
      rw [PiLp.norm_eq_sum hQ]
      refine ciSup_le fun j => ?_
      rw [hfp j]
      calc ‖f j‖ = (‖f j‖ ^ q.toReal) ^ (1 / q.toReal) := by
            rw [← Real.rpow_mul (norm_nonneg _), mul_one_div, div_self hQ.ne', Real.rpow_one]
        _ ≤ (∑ i, ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜)) i‖ ^ q.toReal) ^ (1 / q.toReal) := by
            refine Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) ?_ (by positivity)
            rw [← hfq j]
            exact Finset.single_le_sum
              (fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ j)
  · -- `p` finite, hence `q` finite with `q.toReal ≤ p.toReal`.
    have hP : 0 < p.toReal := zero_lt_one.trans_le hp
    have hpt : p ≠ ∞ := by intro h; rw [h, ENNReal.toReal_top] at hp; norm_num at hp
    have hqt : q ≠ ∞ := ne_top_of_le_ne_top hpt hqp
    have hQ : 0 < q.toReal := toReal_pos_of_ne_top hqt
    have hQP : q.toReal ≤ p.toReal := ENNReal.toReal_mono hpt hqp
    have esum_p : ∑ i, ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜)) i‖ ^ p.toReal
        = ∑ i, ‖f i‖ ^ p.toReal := rfl
    have esum_q : ∑ i, ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜)) i‖ ^ q.toReal
        = ∑ i, ‖f i‖ ^ q.toReal := rfl
    rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hQ, esum_p, esum_q]
    set SQ : ℝ := ∑ i, ‖f i‖ ^ q.toReal with hSQ
    have hSQnn : 0 ≤ SQ := Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
    -- `∑ ‖f i‖^p ≤ SQ^{p/q}`.
    have hkey : ∑ i, ‖f i‖ ^ p.toReal ≤ SQ ^ (p.toReal / q.toReal) := by
      have hterm : ∀ i, ‖f i‖ ^ p.toReal
          ≤ ‖f i‖ ^ q.toReal * SQ ^ ((p.toReal - q.toReal) / q.toReal) := by
        intro i
        rcases eq_or_ne ‖f i‖ 0 with h0 | h0
        · rw [h0]; simp [Real.zero_rpow hP.ne', Real.zero_rpow hQ.ne']
        · have hpos : 0 < ‖f i‖ := (norm_nonneg _).lt_of_ne (Ne.symm h0)
          have hsingle : ‖f i‖ ^ q.toReal ≤ SQ :=
            Finset.single_le_sum (fun j _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ i)
          have hle : ‖f i‖ ^ (p.toReal - q.toReal)
              ≤ SQ ^ ((p.toReal - q.toReal) / q.toReal) := by
            have heq : ‖f i‖ ^ (p.toReal - q.toReal)
                = (‖f i‖ ^ q.toReal) ^ ((p.toReal - q.toReal) / q.toReal) := by
              rw [← Real.rpow_mul (norm_nonneg _)]
              congr 1
              field_simp
            rw [heq]
            exact Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hsingle
              (div_nonneg (by linarith) hQ.le)
          calc ‖f i‖ ^ p.toReal
              = ‖f i‖ ^ q.toReal * ‖f i‖ ^ (p.toReal - q.toReal) := by
                rw [← Real.rpow_add hpos]; congr 1; ring
            _ ≤ ‖f i‖ ^ q.toReal * SQ ^ ((p.toReal - q.toReal) / q.toReal) :=
                mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (norm_nonneg _) _)
      have hcombine : SQ * SQ ^ ((p.toReal - q.toReal) / q.toReal) = SQ ^ (p.toReal / q.toReal) := by
        rcases eq_or_lt_of_le hSQnn with h0 | hpos
        · rw [← h0, zero_mul, Real.zero_rpow (by positivity : (0:ℝ) < p.toReal / q.toReal).ne']
        · have hstep : SQ * SQ ^ ((p.toReal - q.toReal) / q.toReal)
              = SQ ^ (1 + (p.toReal - q.toReal) / q.toReal) := by
            rw [Real.rpow_add hpos, Real.rpow_one]
          rw [hstep]; congr 1; field_simp; ring
      calc ∑ i, ‖f i‖ ^ p.toReal
          ≤ ∑ i, ‖f i‖ ^ q.toReal * SQ ^ ((p.toReal - q.toReal) / q.toReal) :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = SQ * SQ ^ ((p.toReal - q.toReal) / q.toReal) := by rw [← Finset.sum_mul, ← hSQ]
        _ = SQ ^ (p.toReal / q.toReal) := hcombine
    calc (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
        ≤ (SQ ^ (p.toReal / q.toReal)) ^ (1 / p.toReal) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
            hkey (by positivity)
      _ = SQ ^ (1 / q.toReal) := by
          rw [← Real.rpow_mul hSQnn]; congr 1; field_simp
end SNumbers
