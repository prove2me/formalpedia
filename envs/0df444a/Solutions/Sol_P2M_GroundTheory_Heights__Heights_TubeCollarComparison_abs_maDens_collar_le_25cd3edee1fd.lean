-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeCollarComparison_abs_maDens_collar_le_25cd3edee1fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:09:17.797423+00:00
-- url     : https://prove2.me/submissions/49b1610b-b98e-4b41-a937-135824e67289

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeCollarCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeCollarCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_euclPot_8b94f23095e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_multilinearMap_eq_mdisc
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_comp
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_mdisc_le_of_abs_le


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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeCollarComparison
namespace GroundTheory.Heights₂.Heights.TubeCollarComparison
theorem _root_.solution {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y) (hg : ContDiffAt ℝ 2 g (s y)) {c : ℝ}
    (hb : (hessC g (s y) + (c : ℂ) • 1).PosSemidef ∧ (-hessC g (s y) + (c : ℂ) • 1).PosSemidef) :
    |maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) y| ≤
      3 ^ (d + 1) * c * maDens (fun _ : Fin (d + 1) => euclPot ∘ s) y := by
  set Jc := ReciprocityTheory.AnForm.A.jacC s y with hJc
  set B := Jc.map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = Jcᵀ := by
    ext a b
    simp [hB]
  have hE2 : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hH : hessC (g ∘ s) y = Bᴴ * hessC g (s y) * B := by
    rw [hBJ]
    exact ReciprocityTheory.AnForm.A.hessC_comp _ s y hs hg
  have hG : hessC (euclPot ∘ s) y = Bᴴ * B := by
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ s y hs hE2, TubeFormComparison.hessC_euclPot, hBJ, Matrix.mul_one]
  have hGp : (Bᴴ * B).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  set Av : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    fun k => hessC (vecCons g (fun _ => euclPot) k ∘ s) y with hAv
  set a : Fin (d + 1) → ℂ := Fin.cons (c : ℂ) (fun _ => 1) with ha
  set Bv : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun k => a k • (Bᴴ * B) with hBv
  have hle : ∀ k, (Bv k - Av k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, ha, Fin.cons_zero, Matrix.cons_val_zero, hH]
      have e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC g (s y) * B = Bᴴ * (-hessC g (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one]
        abel
      rw [e]
      exact hb.2.conjTranspose_mul_mul_same B
    · simp only [hAv, hBv, ha, Fin.cons_succ, Matrix.cons_val_succ, hG, one_smul, sub_self]
      exact Matrix.PosSemidef.zero
  have hge : ∀ k, (Av k + Bv k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, ha, Fin.cons_zero, Matrix.cons_val_zero, hH]
      have e : Bᴴ * hessC g (s y) * B + (c : ℂ) • (Bᴴ * B) = Bᴴ * (hessC g (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [e]
      exact hb.1.conjTranspose_mul_mul_same B
    · simp only [hAv, hBv, ha, Fin.cons_succ, Matrix.cons_val_succ, hG, one_smul]
      exact hGp.add hGp
  have hmain := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le Av Bv hle hge
  have hscale : mdisc Bv = (c : ℂ) * mdisc (fun _ : Fin (d + 1) => hessC (euclPot ∘ s) y) := by
    obtain ⟨L, hL⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := d + 1)
    rw [hG, ← hL, hBv, L.map_smul_univ, smul_eq_mul, Fin.prod_univ_succ]
    simp [ha]
  rw [hscale, Complex.re_ofReal_mul] at hmain
  have hm : ∀ Φ : Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ, maDens Φ y =
      ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * (mdisc fun k => hessC (Φ k) y).re :=
    fun Φ => rfl
  rw [hm, hm, abs_mul]
  have hK0 : 0 ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) := by positivity
  rw [abs_of_nonneg hK0]
  calc ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * |(mdisc Av).re|
      ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * ‖mdisc Av‖ := by
        gcongr
        exact Complex.abs_re_le_norm _
    _ ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) *
        (3 ^ (d + 1) * (c * (mdisc fun _ : Fin (d + 1) => hessC (euclPot ∘ s) y).re)) := by
        gcongr
    _ = _ := by ring
end GroundTheory.Heights₂.Heights.TubeCollarComparison
