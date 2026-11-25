-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_integral_chosenSheet_eq_6c401d343d67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:39.921047+00:00
-- url     : https://prove2.me/submissions/01b9044d-cad2-4f0b-9a2d-e181d3e99eb8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_indicator_ball_norm_pow_269848d30fd3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre mcPts)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n e : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (P : Ideal (MRing (PBlk n))) (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (g : (Fin n → ℂ) → ℝ) (hg : ∀ (c : ℂ) (z : Fin n → ℂ), c ≠ 0 → g (c • z) = g z)
    (x : Fin e → ℂ) (w : ((k : Unit) → PBlk n k) → ℂ) :
    ∫ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y))
          (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
        (‖t‖ ^ (2 * e) * gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) * chartGramDensity P Ψ S g x w := by
  classical
  by_cases hγ : ∃ γ, IsSheet P Ψ x w γ
  · have hc : chosenSheet P Ψ x w = hγ.choose := by
      simp only [chosenSheet, dif_pos hγ]
    have hd : chartGramDensity P Ψ S g x w = g (fun i => hγ.choose x ⟨(), i⟩) *
        ((e.factorial : ℝ) / Real.pi ^ e *
            gramVol (fun y' => S *ᵥ fun i => hγ.choose y' ⟨(), i⟩) x /
          ‖WithLp.toLp 2 (S *ᵥ fun i => hγ.choose x ⟨(), i⟩)‖ ^ (2 * (e + 1))) := by
      simp only [chartGramDensity, dif_pos hγ]
    rw [hc, hd]
    set u : Fin n → ℂ := fun i => hγ.choose x ⟨(), i⟩ with hu_def
    set G := gramVol (fun y' => S *ᵥ fun i => hγ.choose y' ⟨(), i⟩) x with hG_def
    have hmem : hγ.choose x ∈ mcPts P := (hγ.choose_spec.2.self_of_nhds).2.1
    have hu : u ≠ 0 := by
      obtain ⟨i, hi⟩ := hmem.1 ()
      intro h
      exact hi (congrFun h i)
    have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
    have hinv : S⁻¹ *ᵥ (S *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S hdet, Matrix.one_mulVec]
    have hSu : S *ᵥ u ≠ 0 := by
      intro h
      apply hu
      rw [← hinv, h, Matrix.mulVec_zero]
    set ρ := ‖WithLp.toLp 2 (S *ᵥ u)‖ with hρ_def
    have hρ : 0 < ρ := by
      rw [hρ_def, norm_pos_iff]
      intro h
      exact hSu (by simpa using congrArg WithLp.ofLp h)
    have hpt : ∀ t : ℂ, (ObjectsHeight.ofPointMatrix S hS).pointOf (t • WithLp.toLp 2 (S *ᵥ u)) =
        t • u := by
      intro t
      have : (fun i => (t • WithLp.toLp 2 (S *ᵥ u)) i) = t • (S *ᵥ u) := by
        ext i
        simp
      simp only [HermNorm.pointOf, ObjectsHeight.ofPointMatrix, transpose_transpose, this,
        Matrix.mulVec_smul, hinv]
    have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y))
          (t • WithLp.toLp 2 (S *ᵥ u)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
        fun t => (g u * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
      have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
        rw [ae_iff]
        simp
      filter_upwards [h0] with t ht
      have hiff : ‖t • WithLp.toLp 2 (S *ᵥ u)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
        rw [norm_smul, lt_div_iff₀ hρ]
      by_cases hb : ‖t‖ < 1 / ρ
      · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
          indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hg t u ht]
        ring
      · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
          indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
        ring
    rw [integral_congr_ae hae, integral_const_mul,
      integral_indicator_ball_norm_pow e (by positivity)]
    rw [one_div, inv_pow, Nat.factorial_succ]
    have hρ' : ρ ^ (2 * (e + 1)) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have hc : chosenSheet P Ψ x w = 0 := by
      simp only [chosenSheet, dif_neg hγ]
    have hd : chartGramDensity P Ψ S g x w = 0 := by
      simp only [chartGramDensity, dif_neg hγ]
    have hG : gramVol (fun x' => S *ᵥ fun i =>
        (0 : (Fin e → ℂ) → (Σ k, PBlk n k) → ℂ) x' ⟨(), i⟩) x = 0 := by
      have hz : (S *ᵥ fun _ : Fin n => (0 : ℂ)) = 0 := Matrix.mulVec_zero S
      have hw : ∀ a : Fin (e + 1), (Fin.cons (0 : Fin n → ℂ) (fun _ : Fin e => (0 : Fin n → ℂ)) :
          Fin (e + 1) → Fin n → ℂ) a = 0 := fun a => Fin.cases rfl (fun _ => rfl) a
      simp [gramVol, hz, hw]
      rw [show (Matrix.of fun _ _ => (0 : ℂ) : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) = 0 from rfl,
        Matrix.det_zero, Complex.zero_re]
    rw [hc, hd, hG]
    simp
end GroundTheory.Heights₂.Heights
