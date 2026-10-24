-- Prove2me | solution 1 for SKAlgorithm.Qudit.log_near_identity
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:49:18.98899+00:00
-- url     : https://prove2.me/submissions/20587555-c089-4d22-a806-73675c39c5d9

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open Matrix Complex NormedSpace Filter
open scoped Matrix.Norms.L2Operator Topology
open QAlgorithms

namespace SKAlgorithm.Qudit.LogProof

lemma exp_diagonal {d : ℕ} (z : Fin d → ℂ) :
    NormedSpace.exp (Matrix.diagonal z) = Matrix.diagonal (fun i => Complex.exp (z i)) := by
  have h := NormedSpace.map_exp (Matrix.diagonalRingHom (Fin d) ℂ)
    (by change Continuous (Matrix.diagonal : (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ); fun_prop) z
  simpa only [Matrix.diagonalRingHom_apply, Pi.exp_def, Complex.exp_eq_exp_ℂ] using h.symm

lemma det_conj_unitary {d : ℕ} (V : Matrix.unitaryGroup (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    ((V : Matrix (Fin d) (Fin d) ℂ) * A * star (V : Matrix (Fin d) (Fin d) ℂ)).det = A.det := by
  have hv := congrArg Matrix.det (Unitary.coe_mul_star_self V)
  rw [Matrix.det_mul, Matrix.det_one] at hv
  change (V : Matrix (Fin d) (Fin d) ℂ).det * (star (V : Matrix (Fin d) (Fin d) ℂ)).det = 1 at hv
  rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hv, one_mul]

set_option backward.isDefEq.respectTransparency false in
lemma det_exp_smul_I {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    (NormedSpace.exp (Complex.I • H)).det = Complex.exp (Complex.I * H.trace) := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let V := hH.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) V
  let z : Fin d → ℂ := fun j => Complex.I * (hH.eigenvalues j : ℂ)
  have hs : Complex.I • H = φ (Matrix.diagonal z) := by
    rw [hH.spectral_theorem]
    change Complex.I • φ (Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ))) = _
    rw [← map_smul]
    congr 1
    ext i j
    simp [z, Matrix.diagonal, mul_ite]
  have hc : Continuous φ := by
    change Continuous (fun A : Matrix (Fin d) (Fin d) ℂ =>
      (V : Matrix (Fin d) (Fin d) ℂ) * A * star (V : Matrix (Fin d) (Fin d) ℂ))
    fun_prop
  rw [hs, ← NormedSpace.map_exp φ hc, exp_diagonal]
  change ((V : Matrix (Fin d) (Fin d) ℂ) * _ * star (V : Matrix (Fin d) (Fin d) ℂ)).det = _
  rw [det_conj_unitary, Matrix.det_diagonal, ← Complex.exp_sum,
    hH.trace_eq_sum_eigenvalues, Finset.mul_sum]
  rfl

lemma arg_one {d : ℕ} :
    Unitary.argSelfAdjoint (1 : Matrix.unitaryGroup (Fin d) ℂ) = 0 := by
  simpa using (argSelfAdjoint_expUnitary (x := (0 : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)))
    (by simpa using Real.pi_pos))

lemma exists_small_arg_radius (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : Matrix.unitaryGroup (Fin d) ℂ,
      ‖(u : Matrix (Fin d) (Fin d) ℂ) - 1‖ < ε →
      ‖Unitary.argSelfAdjoint u‖ < 1 ∧
      ‖Matrix.trace (Unitary.argSelfAdjoint u : Matrix (Fin d) (Fin d) ℂ)‖ < 1 := by
  have hc : ContinuousAt (Unitary.argSelfAdjoint :
      Matrix.unitaryGroup (Fin d) ℂ → selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) 1 :=
    Unitary.continuousOn_argSelfAdjoint.continuousAt
      (Metric.isOpen_ball.mem_nhds (by simp))
  have ht : ContinuousAt (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      Matrix.trace (Unitary.argSelfAdjoint u : Matrix (Fin d) (Fin d) ℂ)) 1 := by
    have hc' : ContinuousAt (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
        (Unitary.argSelfAdjoint u : Matrix (Fin d) (Fin d) ℂ)) 1 :=
      continuous_subtype_val.continuousAt.comp hc
    have ht' : Continuous (Matrix.trace : Matrix (Fin d) (Fin d) ℂ → ℂ) := by
      unfold Matrix.trace Matrix.diag
      fun_prop
    exact ht'.continuousAt.comp hc' 
  have hn : ∀ᶠ u : Matrix.unitaryGroup (Fin d) ℂ in 𝓝 1,
      ‖Unitary.argSelfAdjoint u‖ < 1 :=
    hc.norm.eventually (gt_mem_nhds (by simp [arg_one]))
  have htn : ∀ᶠ u : Matrix.unitaryGroup (Fin d) ℂ in 𝓝 1,
      ‖Matrix.trace (Unitary.argSelfAdjoint u : Matrix (Fin d) (Fin d) ℂ)‖ < 1 :=
    ht.norm.eventually (gt_mem_nhds (by simp [arg_one]))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (hn.and htn)
  refine ⟨ε, hε, fun u hu => he ?_⟩
  simpa only [Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm] using hu

lemma trace_zero_of_exp_det_one {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (ht : ‖H.trace‖ < 1)
    (he : (NormedSpace.exp (Complex.I • H)).det = 1) : H.trace = 0 := by
  rw [det_exp_smul_I H hH] at he
  have him : |(Complex.I * H.trace).im| < Real.pi := by
    calc
      _ ≤ ‖Complex.I * H.trace‖ := Complex.abs_im_le_norm _
      _ = ‖H.trace‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ < 1 := ht
      _ < Real.pi := by linarith [Real.pi_gt_three]
  have hz : Complex.I * H.trace = 0 :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi (abs_lt.mp him).1 (abs_lt.mp him).2.le
      (by simpa using neg_neg_of_pos Real.pi_pos) (by simpa using Real.pi_pos.le)
      (by simpa only [Complex.exp_zero] using he)
  exact (mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero

lemma exists_local_chart (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U : SU d, opDist 1 U < ε →
      ∃ H : Matrix (Fin d) (Fin d) ℂ, H.IsHermitian ∧ H.trace = 0 ∧ specNorm H < 1 ∧
        (U : Matrix (Fin d) (Fin d) ℂ) = NormedSpace.exp (Complex.I • H) ∧
        (opDist 1 U)^2 = 2 * (1 - Real.cos (specNorm H)) := by
  obtain ⟨ε, hε, he⟩ := exists_small_arg_radius d
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro U hU
  let u : Matrix.unitaryGroup (Fin d) ℂ := ⟨U, U.property.1⟩
  have hdist : ‖(u : Matrix (Fin d) (Fin d) ℂ) - 1‖ = opDist 1 U := by
    change ‖(U : Matrix (Fin d) (Fin d) ℂ) - 1‖ = ‖1 - (U : Matrix (Fin d) (Fin d) ℂ)‖
    exact norm_sub_rev _ _
  have hu : ‖(u : Matrix (Fin d) (Fin d) ℂ) - 1‖ < 2 := by
    rw [hdist]
    exact (hU.trans_le (min_le_right _ _)).trans (by norm_num)
  obtain ⟨hn, ht⟩ := he u (by rw [hdist]; exact hU.trans_le (min_le_left _ _))
  let H : Matrix (Fin d) (Fin d) ℂ := Unitary.argSelfAdjoint u
  have hH : H.IsHermitian := (Unitary.argSelfAdjoint u).property.isHermitian
  have hexp : (U : Matrix (Fin d) (Fin d) ℂ) = NormedSpace.exp (Complex.I • H) := by
    have h := congrArg Subtype.val (expUnitary_argSelfAdjoint hu)
    exact h.symm
  refine ⟨H, hH, trace_zero_of_exp_det_one H hH ht ?_, hn, hexp, ?_⟩
  · rw [← hexp]
    exact U.property.2
  · have hc := Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint hu
    rw [hdist] at hc
    exact hc.symm

end SKAlgorithm.Qudit.LogProof

/- Scalar sine estimates copied from the checked SK10 helper. -/

namespace SKAlgorithm.Qudit.ScalarProof

/-- The nonnegative chord length is twice the sine of the half-angle. -/
theorem chord_eq_two_sin_half {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hsq : s ^ 2 = 2 * (1 - Real.cos t)) :
    s = 2 * Real.sin (t / 2) := by
  have hsin : 0 ≤ Real.sin (t / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_gt_three])
  apply (sq_eq_sq₀ hs (mul_nonneg (by norm_num) hsin)).mp
  have hhalf := Real.sin_sq_eq_half_sub (x := t / 2)
  rw [show 2 * (t / 2) = t by ring] at hhalf
  nlinarith

/-- A quantitative angle/chord comparison with the Taylor constant `1/24`. -/
theorem chord_cubic_bound {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hsq : s ^ 2 = 2 * (1 - Real.cos t)) :
    |s - t| ≤ t ^ 3 / 24 := by
  have heq := chord_eq_two_sin_half ht ht1 hs hsq
  have hb := Real.abs_sub_sin_le (t / 2)
  rw [abs_of_nonneg (show 0 ≤ t / 2 by linarith)] at hb
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The same comparison in the square-root formulation. -/
theorem sqrt_chord_cubic_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |Real.sqrt (2 * (1 - Real.cos t)) - t| ≤ t ^ 3 / 24 :=
  chord_cubic_bound ht ht1 (Real.sqrt_nonneg _)
    (Real.sq_sqrt (by nlinarith [Real.cos_le_one t]))

/-- A convenient linear inverse estimate on the same chart. -/
theorem angle_le_twice_chord {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hsq : s ^ 2 = 2 * (1 - Real.cos t)) :
    t ≤ 2 * s := by
  have hb := (abs_le.mp (chord_cubic_bound ht ht1 hs hsq)).1
  have hcube : t ^ 3 ≤ t := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1),
      mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
  nlinarith

end SKAlgorithm.Qudit.ScalarProof

namespace SKAlgorithm.Qudit.LogProof

/-- The local special-unitary logarithm, including the linear norm control used by Eq. (33). -/
lemma exists_local_chart_bounds (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U : SU d, opDist 1 U < ε →
      ∃ H : Matrix (Fin d) (Fin d) ℂ, H.IsHermitian ∧ H.trace = 0 ∧ specNorm H < 1 ∧
        (U : Matrix (Fin d) (Fin d) ℂ) = NormedSpace.exp (Complex.I • H) ∧
        specNorm H ≤ 2 * opDist 1 U ∧
        |opDist 1 U - specNorm H| ≤ specNorm H ^ 3 / 24 := by
  obtain ⟨ε, hε, he⟩ := exists_local_chart d
  refine ⟨ε, hε, ?_⟩
  intro U hU
  obtain ⟨H, hH, htr, hn, hexp, hcos⟩ := he U hU
  have ht : 0 ≤ specNorm H := norm_nonneg H
  have hs : 0 ≤ opDist 1 U := norm_nonneg _
  exact ⟨H, hH, htr, hn, hexp,
    ScalarProof.angle_le_twice_chord ht hn.le hs hcos,
    ScalarProof.chord_cubic_bound ht hn.le hs hcos⟩

end SKAlgorithm.Qudit.LogProof

open SKAlgorithm.Qudit

/-- The original near-identity special-unitary logarithm milestone. -/
theorem solution (d : ℕ) :
    ∃ ε₁ K : ℝ, 0 < ε₁ ∧ 0 < K ∧ ∀ U : SU d, opDist 1 U < ε₁ →
      ∃ H : Matrix (Fin d) (Fin d) ℂ, H.IsHermitian ∧ H.trace = 0 ∧ specNorm H < Real.pi ∧
        (U : Matrix (Fin d) (Fin d) ℂ) = NormedSpace.exp (Complex.I • H) ∧
        |opDist 1 U - specNorm H| ≤ K * specNorm H ^ 3 := by
  obtain ⟨ε, hε, he⟩ := LogProof.exists_local_chart_bounds d
  refine ⟨ε, 1 / 24, hε, by norm_num, ?_⟩
  intro U hU
  obtain ⟨H, hH, htr, hn, hexp, _, herr⟩ := he U hU
  refine ⟨H, hH, htr, hn.trans (by linarith [Real.pi_gt_three]), hexp, ?_⟩
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using herr
