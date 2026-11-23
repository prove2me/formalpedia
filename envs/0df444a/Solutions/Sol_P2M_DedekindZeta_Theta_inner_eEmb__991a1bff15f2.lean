-- Prove2me | solution 1 for P2M_DedekindZeta_Theta_inner_eEmb__991a1bff15f2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:08:29.312736+00:00
-- url     : https://prove2.me/submissions/a29ca2fb-7e64-471e-9037-32e288a24431

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (ξ : mixedSpace K) (y : K) :
    (inner ℝ (eEmbℝ K ξ) (eEmb K y) : ℝ) =
      (∑ w : {w : InfinitePlace K // w.IsReal},
          ξ.1 w * (mixedEmbedding K y).1 w) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
          (starRingEnd ℂ (ξ.2 w) * (mixedEmbedding K y).2 w).re := by
  classical
  rw [WithLp.prod_inner_apply,
      show (WithLp.ofLp (eEmbℝ K ξ)).fst
          = WithLp.toLp 2 (scaleMixed K ξ).1 from rfl,
      show (WithLp.ofLp (eEmb K y)).fst
          = WithLp.toLp 2 (scaleMixed K (mixedEmbedding K y)).1 from rfl,
      show (WithLp.ofLp (eEmbℝ K ξ)).snd
          = WithLp.toLp 2 (scaleMixed K ξ).2 from rfl,
      show (WithLp.ofLp (eEmb K y)).snd
          = WithLp.toLp 2 (scaleMixed K (mixedEmbedding K y)).2 from rfl]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, scaleMixed,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.coe_refl', id_eq,
    ContinuousLinearEquiv.smulLeft_apply_apply, real_inner_eq_re_inner ℂ]
  rw [Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl (fun w _ => mul_comm _ _)
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    have key : (sqrtTwo • (mixedEmbedding K y).2) w *
        (starRingEnd ℂ) ((sqrtTwo • ξ.2) w)
        = ((2 : ℝ) : ℂ) *
          ((starRingEnd ℂ) (ξ.2 w) * (mixedEmbedding K y).2 w) := by
      simp only [Pi.smul_apply, Units.smul_def, sqrtTwo, Units.val_mk0, Complex.real_smul,
        map_mul, Complex.conj_ofReal]
      rw [← hsq]; ring
    rw [key]; exact Complex.re_ofReal_mul _ _
end DedekindZeta.Theta
