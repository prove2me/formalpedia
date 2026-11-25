-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeFormComparison_abs_maDens_cons_le_50c543526b9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:58.875499+00:00
-- url     : https://prove2.me/submissions/14c13d4f-3e93-4e65-ad09-038d1b2503f5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
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
open GroundTheory.Heights₂.Heights.TubeFormComparison
namespace GroundTheory.Heights₂.Heights.TubeFormComparison
theorem _root_.solution {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y)
    (hφ : ∀ i, ContDiffAt ℝ 2 (φ i) (s y)) {c : ℝ}
    (hb : ∀ i, (hessC (φ i) (s y) + (c : ℂ) • 1).PosSemidef ∧
      (-hessC (φ i) (s y) + (c : ℂ) • 1).PosSemidef)
    (hM : (hessC (g ∘ s) y).PosSemidef) :
    |maDens (fun k => vecCons g φ k ∘ s) y| ≤
      3 ^ (d + 1) * c ^ d * maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) y := by
  set Jc := ReciprocityTheory.AnForm.A.jacC s y with hJc
  set B := Jc.map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = Jcᵀ := by
    ext a b
    simp [hB]
  have hE2 : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hA : ∀ i, hessC (φ i ∘ s) y = Bᴴ * hessC (φ i) (s y) * B := fun i => by
    rw [hBJ]
    exact ReciprocityTheory.AnForm.A.hessC_comp _ s y hs (hφ i)
  have hG : hessC (euclPot ∘ s) y = Bᴴ * B := by
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ s y hs hE2, hessC_euclPot, hBJ, Matrix.mul_one]
  set M := hessC (g ∘ s) y with hMdef
  set Av : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    fun k => hessC (vecCons g φ k ∘ s) y with hAv
  set Bv : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    Fin.cons M (fun _ => (c : ℂ) • (Bᴴ * B)) with hBv
  have hle : ∀ k, (Bv k - Av k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, Fin.cons_zero, Matrix.cons_val_zero, ← hMdef, sub_self]
      exact Matrix.PosSemidef.zero
    · simp only [hAv, hBv, Fin.cons_succ, Matrix.cons_val_succ, hA]
      have e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC (φ i) (s y) * B =
          Bᴴ * (-hessC (φ i) (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
        abel
      rw [e]
      exact (hb i).2.conjTranspose_mul_mul_same B
  have hge : ∀ k, (Av k + Bv k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, Fin.cons_zero, Matrix.cons_val_zero, ← hMdef]
      exact hM.add hM
    · simp only [hAv, hBv, Fin.cons_succ, Matrix.cons_val_succ, hA]
      have e : Bᴴ * hessC (φ i) (s y) * B + (c : ℂ) • (Bᴴ * B) =
          Bᴴ * (hessC (φ i) (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [e]
      exact (hb i).1.conjTranspose_mul_mul_same B
  have hmain := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le Av Bv hle hge
  have hscale : mdisc Bv =
      (c : ℂ) ^ d * mdisc (fun k => hessC (vecCons g (fun _ => euclPot) k ∘ s) y) := by
    obtain ⟨L, hL⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := d + 1)
    have e : Bv = fun k => (Fin.cons (1 : ℂ) (fun _ => (c : ℂ)) : Fin (d + 1) → ℂ) k •
        hessC (vecCons g (fun _ => euclPot) k ∘ s) y := by
      funext k
      refine Fin.cases ?_ (fun i => ?_) k
      · simp [hBv, hMdef]
      · simp [hBv, hG]
    rw [e, ← hL, L.map_smul_univ, smul_eq_mul, Fin.prod_univ_succ]
    simp
  rw [hscale, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmain
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
        (3 ^ (d + 1) * (c ^ d * (mdisc fun k => hessC (vecCons g (fun _ => euclPot) k ∘ s) y).re)) := by
        gcongr
    _ = _ := by ring
end GroundTheory.Heights₂.Heights.TubeFormComparison
