-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.kraw_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:50:54.053719+00:00
-- url     : https://prove2.me/submissions/7194d7a0-af55-4dbd-9f60-3b12c78285dd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_gauss_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ≠ 0) (u : E n) :
    (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      (((|t| / (2 * Real.sqrt ε)) ^ (n ^ 2) * gK ((|t| / (2 * Real.sqrt ε)) • u) : ℝ) : ℂ) := by
  set lam : ℝ := |t| / (2 * Real.sqrt ε) with hlam
  have hε' : 0 < (ε : ℂ).re := by simpa using hε

  have hprod : ∀ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      ∏ a, ∏ b, (Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ)) *
        Complex.exp (-(ε : ℂ) * ((y a b : ℝ) : ℂ) ^ 2)) := by
    intro y
    simp_rw [Finset.prod_mul_distrib, ← gauss_prod, ← Complex.exp_sum]
    rw [mul_comm]
    congr 2
    unfold ip
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hint : ∫ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      ∏ a, ∏ b, ((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) * Complex.exp (-((t * u a b : ℝ) : ℂ) ^ 2 / (4 * ε)) := by
    simp_rw [hprod]
    rw [integral_fintype_prod_volume_eq_prod (f := fun a (w : Fin n → ℝ) =>
      ∏ b, (Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * ((w b : ℝ) : ℂ)) *
        Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2)))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [integral_fintype_prod_volume_eq_prod (f := fun b (s : ℝ) =>
      Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * (s : ℂ)) * Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2))]
    refine Finset.prod_congr rfl fun b _ => ?_
    exact fourierIntegral_gaussian hε' _

  have hsq : ((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi / Real.sqrt ε : ℝ) : ℂ) := by
    rw [← Real.sqrt_div' _ hε.le, Real.sqrt_eq_rpow, Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hε.le)]
    push_cast
    ring_nf
  have hcoord : ∀ s : ℝ, (((|t| / (2 * Real.pi)) : ℝ) : ℂ) * (((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) *
      Complex.exp (-((t * s : ℝ) : ℂ) ^ 2 / (4 * ε))) =
      ((lam * ((Real.sqrt Real.pi)⁻¹ * Real.exp (-(lam * s) ^ 2)) : ℝ) : ℂ) := by
    intro s
    have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hee : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
    have hpp : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    rw [hsq]
    have hexp : (-((t * s : ℝ) : ℂ) ^ 2 / (4 * ε)) = ((-(lam * s) ^ 2 : ℝ) : ℂ) := by
      rw [hlam]
      push_cast
      have : ((|t| : ℝ) : ℂ) ^ 2 = (t : ℂ) ^ 2 := by
        rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
      have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
      have hs0 : ((Real.sqrt ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hse.ne'
      have hee' : ((Real.sqrt ε : ℝ) : ℂ) ^ 2 = (ε : ℂ) := by exact_mod_cast hee
      field_simp
      rw [this, hee']
      ring
    rw [hexp, ← Complex.ofReal_exp]
    push_cast
    rw [hlam]
    have hpi0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    have hs0 : ((Real.sqrt ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hse.ne'
    have hpp' : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by exact_mod_cast hpp
    have hpi1 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    push_cast
    field_simp
    rw [← hpp']
  rw [hint]
  have hC : (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) = ∏ _a : Fin n, ∏ _b : Fin n, (((|t| / (2 * Real.pi)) : ℝ) : ℂ) := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rw [← pow_mul, sq]
  rw [hC, ← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib, hcoord]
  push_cast
  unfold gK
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [show ((lam : ℂ)) ^ (n ^ 2) = ∏ _a : Fin n, ∏ _b : Fin n, (lam : ℂ) by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, sq]]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib]
end PositivityTheory.Rg.Sw.WR.D.Moll
