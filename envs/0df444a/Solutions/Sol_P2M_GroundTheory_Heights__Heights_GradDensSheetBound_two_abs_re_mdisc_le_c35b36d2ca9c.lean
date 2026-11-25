-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradDensSheetBound_two_abs_re_mdisc_le_c35b36d2ca9c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:39.603608+00:00
-- url     : https://prove2.me/submissions/bd176afc-992c-4817-92b9-ed1eb37b73d6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGradDensSheetBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_mdisc_cons_smul_tail_e30b329eeb60
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_add
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_mdisc_le_of_abs_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_re_mdisc_cons_conjTranspose


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.GradDensSheetBound
namespace GroundTheory.Heights₂.Heights.GradDensSheetBound
theorem _root_.solution {n : ℕ} (x y : Fin (n + 1) → ℂ)
    (A W : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℝ) (hc : 0 < c)
    (hle : ∀ i, ((c : ℂ) • W i - A i).PosSemidef) (hge : ∀ i, (A i + (c : ℂ) • W i).PosSemidef) :
    2 * |(mdisc (Fin.cons (vecMulVec x (star y)) A :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re| ≤
      3 ^ (n + 1) * c ^ n *
        ((mdisc (Fin.cons (vecMulVec x (star x)) W :
            Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re +
          (mdisc (Fin.cons (vecMulVec y (star y)) W :
            Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re) := by
  have hA : ∀ i, (A i).IsHermitian := fun i => by
    refine IsHermitian.ext fun j k => ?_
    have e1 := (hle i).1.apply j k
    have e2 := (hge i).1.apply j k
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_sub, star_add] at e1 e2
    linear_combination (e2 - e1) / 2
  have hNM : vecMulVec x (star x) + vecMulVec y (star y) -
      (vecMulVec x (star y) + vecMulVec y (star x)) = vecMulVec (x - y) (star (x - y)) := by
    ext j k; simp [vecMulVec_apply]; ring
  have hMN : vecMulVec x (star y) + vecMulVec y (star x) +
      (vecMulVec x (star x) + vecMulVec y (star y)) = vecMulVec (x + y) (star (x + y)) := by
    ext j k; simp [vecMulVec_apply]; ring
  have hB := norm_mdisc_le_of_abs_le
    (Fin.cons (vecMulVec x (star y) + vecMulVec y (star x)) A :
      Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (Fin.cons (vecMulVec x (star x) + vecMulVec y (star y)) (fun i => (c : ℂ) • W i))
    (fun k => by
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Fin.cons_zero]; rw [hNM]; exact posSemidef_vecMulVec_self_star _
      · simpa using hle i)
    (fun k => by
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Fin.cons_zero]; rw [hMN]; exact posSemidef_vecMulVec_self_star _
      · simpa using hge i)
  have hM : (mdisc (Fin.cons (vecMulVec x (star y) + vecMulVec y (star x)) A :
      Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re =
      2 * (mdisc (Fin.cons (vecMulVec x (star y)) A :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re := by
    have e := mdisc_cons_smul_add 1 1 (vecMulVec x (star y)) (vecMulVec y (star x)) A
    simp only [one_smul, one_mul] at e
    have hsw : vecMulVec y (star x) = (vecMulVec x (star y))ᴴ := by
      rw [conjTranspose_vecMulVec, star_star]
    rw [e, Complex.add_re, hsw, re_mdisc_cons_conjTranspose _ _ hA]
    ring
  have hN : (mdisc (Fin.cons (vecMulVec x (star x) + vecMulVec y (star y)) (fun i => (c : ℂ) • W i) :
      Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re =
      c ^ n * ((mdisc (Fin.cons (vecMulVec x (star x)) W :
            Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re +
          (mdisc (Fin.cons (vecMulVec y (star y)) W :
            Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re) := by
    have e := mdisc_cons_smul_add 1 1 (vecMulVec x (star x)) (vecMulVec y (star y)) W
    simp only [one_smul, one_mul] at e
    rw [mdisc_cons_smul_tail _ (Complex.ofReal_ne_zero.2 hc.ne'), e, ← Complex.ofReal_pow,
      Complex.re_ofReal_mul, Complex.add_re]
  have h1 := Complex.abs_re_le_norm (mdisc (Fin.cons (vecMulVec x (star y) + vecMulVec y (star x)) A :
      Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
  rw [hM, abs_mul, abs_two] at h1
  rw [hN] at hB
  linarith
end GroundTheory.Heights₂.Heights.GradDensSheetBound
