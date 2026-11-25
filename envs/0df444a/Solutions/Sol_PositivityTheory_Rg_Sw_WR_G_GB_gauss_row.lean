-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GB.gauss_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:48.995454+00:00
-- url     : https://prove2.me/submissions/e600b4e3-bb62-4dad-ad0c-54fdfa647e27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GB_integral_unitary
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GB_gauss_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GB
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.G.GB
theorem _root_.solution (c τ : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ∫ r : Fin n → ℂ, cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * τ * ∑ i, ∑ j, star (r i) * H i j * r j) =
      (Real.pi : ℂ) ^ n / ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H).det := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ := (hH.eigenvectorUnitary).2
  set lam : Fin n → ℂ := RCLike.ofReal ∘ hH.eigenvalues with hlam
  have hspec : H = U * Matrix.diagonal lam * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hV : star U ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact h2)

  set G : (Fin n → ℂ) → ℂ := fun r' => cexp (-∑ k, ((c : ℂ) - Complex.I * τ * lam k) * ((‖r' k‖ ^ 2 : ℝ) : ℂ))
    with hG
  have hpt : ∀ r : Fin n → ℂ, cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
      Complex.I * τ * ∑ i, ∑ j, star (r i) * H i j * r j) = G (star U *ᵥ r) := by
    intro r
    simp only [hG]
    congr 1
    have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := fun z => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]; rfl
    have e1 : ∑ i, ∑ j, star (r i) * H i j * r j = star r ⬝ᵥ (H *ᵥ r) := by
      simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
    have e2 : star r ⬝ᵥ (H *ᵥ r) = star (star U *ᵥ r) ⬝ᵥ (Matrix.diagonal lam *ᵥ (star U *ᵥ r)) := by
      rw [hspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
      congr 1
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    have e3 : star r ⬝ᵥ r = star (star U *ᵥ r) ⬝ᵥ (star U *ᵥ r) := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mulVec]
    have hn' : ∀ z : ℂ, ((‖z‖ : ℂ)) ^ 2 = star z * z := fun z => by rw [← hn z]; push_cast; ring
    have e4 : (((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) = (c : ℂ) * (star r ⬝ᵥ r) := by
      push_cast
      simp only [dotProduct, Pi.star_apply, hn']
    rw [e4, e1, e2, e3]
    simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal, hn, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_unitary (star U) hV G]
  simp only [hG]
  rw [gauss_diag (fun k => (c : ℂ) - Complex.I * τ * lam k) (fun k => by simp [hlam, hc])]
  have hdet : ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H).det =
      ∏ k, ((c : ℂ) - Complex.I * τ * lam k) := by
    have : (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H =
        U * Matrix.diagonal (fun k => (c : ℂ) - Complex.I * τ * lam k) * star U := by
      rw [hspec]
      have hd : Matrix.diagonal (fun k => (c : ℂ) - Complex.I * τ * lam k) =
          (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • Matrix.diagonal lam := by
        ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
      rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h1,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hdu : U.det * (star U).det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
    calc (U.det * ∏ k, ((c : ℂ) - Complex.I * τ * lam k)) * (star U).det
        = (U.det * (star U).det) * ∏ k, ((c : ℂ) - Complex.I * τ * lam k) := by ring
      _ = _ := by rw [hdu, one_mul]
  rw [hdet, Finset.prod_div_distrib]
  simp
end PositivityTheory.Rg.Sw.WR.G.GB
