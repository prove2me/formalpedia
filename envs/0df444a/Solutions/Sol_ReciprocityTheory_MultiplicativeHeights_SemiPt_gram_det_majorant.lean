-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.gram_det_majorant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:01:17.103916+00:00
-- url     : https://prove2.me/submissions/aae24e01-71ff-4f73-a9a2-508e715388fd

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
import Definitions.Def_Lemmata_GeneralBFactSecondAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_det_map_hom
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_gramC_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_hGram_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (M : Majorant S) (hG : S.G.det ≠ 0) (σ : K →+* ℂ) (b : Fin r → Fin r → K) :
    (gramC (M.H σ) σ b).det.re = ‖σ (hGram S b).det‖ := by
  have hσG : (S.G.map σ).det ≠ 0 := by
    rw [det_map_hom]
    exact fun h => hG (σ.injective (by rw [h, map_zero]))
  have hdet2 : (M.H σ).det * (M.H σ).det = (S.G.map σ).det * (S.G.map σ).det := by
    have h1 := congr_arg Matrix.det (M.major σ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h1
    field_simp at h1
    linear_combination h1
  have hpos := (M.posDef σ).det_pos
  rw [Complex.lt_def] at hpos
  set x : ℝ := (M.H σ).det.re with hx
  have hxH : (M.H σ).det = (x : ℂ) := by
    apply Complex.ext
    · simp [hx]
    · simp [← hpos.2]
  have hx0 : 0 < x := by simpa using hpos.1
  have hxn : x = ‖(S.G.map σ).det‖ := by
    have h1 := congr_arg (‖·‖) hdet2
    simp only [norm_mul, hxH, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at h1
    nlinarith [norm_nonneg (S.G.map σ).det]
  rw [gramC_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hxH, hGram_eq,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hE : embMat σ b = (colMat b).map σ := rfl
  rw [det_map_hom, hE, det_map_hom, map_mul, map_mul, S.c_emb]
  rw [det_map_hom] at hxn
  set z := σ (colMat b).det
  rw [Complex.star_def, norm_mul, norm_mul, Complex.norm_conj]
  rw [show (starRingEnd ℂ) z * (x : ℂ) * z = (x : ℂ) * ((starRingEnd ℂ) z * z) by ring,
    Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hxn]
  ring
end ReciprocityTheory.MultiplicativeHeights.SemiPt
