-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.squared_l2_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:31:27.354214+00:00
-- url     : https://prove2.me/submissions/a335e4ff-c8b1-4da2-a23a-1962939a9c2c

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P04
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF pp.10–11, (G.2)–(G.4): selective-monotonicity failure, with null branches allowed. -/
theorem gk_off3 (M : CoherenceMatrix 3) : squaredOffDiagonal M =
    ‖M 0 1‖^2 + ‖M 0 2‖^2 + ‖M 1 0‖^2 + ‖M 1 2‖^2 + ‖M 2 0‖^2 + ‖M 2 1‖^2 := by
  unfold squaredOffDiagonal
  simp only [Finset.sum_filter, Fin.sum_univ_three]
  simp
  ring

theorem solution (alpha beta : ℂ)
    (hnorm : ‖alpha‖^2+‖beta‖^2 = 1) (hbeta : 1/3 < ‖beta‖^2) :
    IsDensityMatrix hsCounterexample ∧
    IncoherentInstrument (fun _ : Fin 2 => 3) (hsCounterKraus alpha beta) ∧
    squaredOffDiagonal hsCounterexample = 1/8 ∧
    (∑ i, selectiveContribution (fun _ => squaredOffDiagonal)
      (hsCounterKraus alpha beta i) hsCounterexample) = ‖beta‖^2/(2*(1+‖beta‖^2)) ∧
    squaredOffDiagonal hsCounterexample < ∑ i, selectiveContribution (fun _ => squaredOffDiagonal)
      (hsCounterKraus alpha beta i) hsCounterexample := by
  have hab : ((‖alpha‖^2 : ℝ) : ℂ) + ((‖beta‖^2 : ℝ) : ℂ) = 1 := by exact_mod_cast hnorm
  have hm : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖^2 : ℝ) : ℂ) := by
    intro z; rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hm' : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖^2 : ℝ) : ℂ) := by
    intro z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hmc : ∀ z : ℂ, z * (starRingEnd ℂ) z = (‖z‖:ℂ)^2 := by
    intro z; rw [hm' z]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have e : hsCounterexample = (!![1/2,0,1/2; 0,0,0; 0,0,0] : CoherenceMatrix 3)ᴴ *
          !![1/2,0,1/2; 0,0,0; 0,0,0] + Matrix.diagonal ![0,1/2,0] := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [hsCounterexample, Matrix.mul_apply, Fin.sum_univ_three, map_ofNat] <;> norm_num
      rw [e]
      refine (Matrix.posSemidef_conjTranspose_mul_self _).add (Matrix.PosSemidef.diagonal ?_)
      intro i; fin_cases i <;> simp
    · simp [hsCounterexample, Matrix.trace, Fin.sum_univ_three]; norm_num
  · refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hsCounterKraus, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hm]
      push_cast at hab; linear_combination hab
    · intro k X _ hX
      have hXd : X = Matrix.diagonal (fun i => X i i) := by
        ext i j
        by_cases h : i = j
        · subst h; simp
        · rw [hX i j h]; simp [Matrix.diagonal_apply_ne _ h]
      rw [hXd]
      intro i j hij
      fin_cases k <;> fin_cases i <;> fin_cases j <;>
        simp [conjSuperop, hsCounterKraus, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul,
          dotProduct, Matrix.diagonal_apply] at hij ⊢
  · rw [gk_off3]; simp [hsCounterexample]; norm_num
  · have hM0 : conjSuperop (hsCounterKraus alpha beta 0) hsCounterexample =
        !![1/2,0,0; 0,0,0; 0,0,((‖alpha‖^2:ℝ):ℂ)/4] := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [conjSuperop, hsCounterKraus, hsCounterexample, Matrix.mul_apply, Fin.sum_univ_three,
          map_ofNat] <;> first | ring1 | linear_combination (1/4:ℂ) * hmc alpha
    have hM1 : conjSuperop (hsCounterKraus alpha beta 1) hsCounterexample =
        !![1/4,(starRingEnd ℂ) beta/4,0; beta/4,((‖beta‖^2:ℝ):ℂ)/4,0; 0,0,0] := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [conjSuperop, hsCounterKraus, hsCounterexample, Matrix.mul_apply, Fin.sum_univ_three,
          map_ofNat] <;> first | ring1 | linear_combination (1/4:ℂ) * hmc beta
    have ht0 : (Matrix.trace (!![1/2,0,0; 0,0,0; 0,0,((‖alpha‖^2:ℝ):ℂ)/4] :
        CoherenceMatrix 3)).re = 1/2 + ‖alpha‖^2/4 := by
      simp [Matrix.trace_fin_three]; norm_cast
    have ht1 : (Matrix.trace (!![1/4,(starRingEnd ℂ) beta/4,0; beta/4,((‖beta‖^2:ℝ):ℂ)/4,0;
        0,0,0] : CoherenceMatrix 3)).re = 1/4 + ‖beta‖^2/4 := by
      simp [Matrix.trace_fin_three]; norm_cast
    have hsum : (∑ i, selectiveContribution (fun _ => squaredOffDiagonal)
        (hsCounterKraus alpha beta i) hsCounterexample) = ‖beta‖^2/(2*(1+‖beta‖^2)) := by
      rw [Fin.sum_univ_two]
      unfold selectiveContribution branchProbability
      simp only [hM0, hM1]
      rw [ht0, ht1, if_pos (by positivity), if_pos (by positivity), gk_off3, gk_off3]
      have hn : ‖(4⁻¹ : ℂ) + (‖beta‖:ℂ)^2 / 4‖ = 4⁻¹ + ‖beta‖^2/4 := by
        have : (4⁻¹ : ℂ) + (‖beta‖:ℂ)^2 / 4 = ((4⁻¹ + ‖beta‖^2/4 : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      simp [Matrix.smul_apply, norm_mul]
      rw [hn]
      have hp : (0:ℝ) < 4⁻¹ + ‖beta‖^2/4 := by positivity
      have h1 : (0:ℝ) < 1 + ‖beta‖^2 := by positivity
      rw [eq_div_iff (by positivity)]
      field_simp
      ring
    refine ⟨hsum, ?_⟩
    rw [hsum, gk_off3]
    simp [hsCounterexample]
    rw [lt_div_iff₀ (by positivity)]
    norm_num
    linarith

