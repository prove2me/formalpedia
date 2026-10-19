-- Prove2me | solution 1 for QAlgorithms.Nannicini.amplitudeAmplification_overlap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T00:35:59.707447+00:00
-- url     : https://prove2.me/submissions/12cae44b-8fbe-42da-8c8c-7524e5cbe3ad

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Theorems.Thm_QAlgorithms_DeWolf_amplitudeAmplification

open QAlgorithms
open scoped ComplexConjugate

private lemma mask_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : EuclideanSpace ℂ ι) (P : ι → Prop) [DecidablePred P] :
    ‖(WithLp.toLp 2 fun j => if P j then α j else 0 : EuclideanSpace ℂ ι)‖ ^ 2 =
      probEvent α P := by
  simp [EuclideanSpace.norm_sq_eq, probEvent, prob, ket,
    EuclideanSpace.inner_single_left, Finset.sum_filter, apply_ite]

private lemma event_compl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : EuclideanSpace ℂ ι) (P : ι → Prop) [DecidablePred P]
    (hα : IsState α) : probEvent α (fun j => ¬P j) = 1 - probEvent α P := by
  have hsum : probEvent α P + probEvent α (fun j => ¬P j) = 1 := by
    simp only [probEvent, Finset.sum_filter_add_sum_filter_not]
    rw [show (∑ z, prob α z) = ‖α‖ ^ 2 by
      simp [prob, ket, EuclideanSpace.inner_single_left, EuclideanSpace.norm_sq_eq]]
    rw [hα]; norm_num
  linarith

private lemma normalized_mask {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : EuclideanSpace ℂ ι) (P : ι → Prop) [DecidablePred P]
    (h : 0 < probEvent α P) :
    IsState (((Real.sqrt (probEvent α P))⁻¹ : ℂ) •
      (WithLp.toLp 2 fun j => if P j then α j else 0 : EuclideanSpace ℂ ι)) := by
  have hn : ‖(WithLp.toLp 2 fun j => if P j then α j else 0 : EuclideanSpace ℂ ι)‖ =
      Real.sqrt (probEvent α P) := by
    rw [← mask_sq α P, Real.sqrt_sq (norm_nonneg _)]
  dsimp [IsState]
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), hn]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr h))

private lemma components {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : EuclideanSpace ℂ ι) (M : Finset ι) (hα : IsState α)
    (hp : 0 < probEvent α (fun j => j ∈ M)) (hp1 : probEvent α (fun j => j ∈ M) < 1) :
    IsState (ampGoodState α M) ∧ IsState (ampBadState α M) ∧
      inner ℂ (ampGoodState α M) (ampBadState α M) = 0 ∧
      α = (Real.sqrt (probEvent α (fun j => j ∈ M)) : ℂ) • ampGoodState α M +
        (Real.sqrt (1 - probEvent α (fun j => j ∈ M)) : ℂ) • ampBadState α M := by
  have hc := event_compl α (fun j => j ∈ M) hα
  have hg := normalized_mask α (fun j => j ∈ M) hp
  have hb := normalized_mask α (fun j => j ∉ M) (by linarith : 0 < probEvent α (fun j => j ∉ M))
  refine ⟨hg, ?_, ?_, ?_⟩
  · simpa only [ampBadState, hc, ite_not] using hb
  · rw [ampGoodState, ampBadState, inner_smul_left, inner_smul_right]
    have hz : inner ℂ
        (WithLp.toLp 2 fun j => if j ∈ M then α j else 0 : EuclideanSpace ℂ ι)
        (WithLp.toLp 2 fun j => if j ∈ M then 0 else α j : EuclideanSpace ℂ ι) = 0 := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j ∈ M <;> simp [hj]
    rw [hz]; ring
  · have hs : (Real.sqrt (probEvent α (fun j => j ∈ M)) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hp)
    have ht : (Real.sqrt (1 - probEvent α (fun j => j ∈ M)) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by linarith : 0 < 1 - probEvent α (fun j => j ∈ M)))
    ext j
    simp only [ampGoodState, ampBadState, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    by_cases hj : j ∈ M <;> simp [hj, hs, ht]

private lemma rounded_iterations (p : ℝ) (hp : 0 < p) :
    ∃ k : ℕ, |(k : ℝ) - (Real.pi / (4 * Real.arcsin (Real.sqrt p)) - 1 / 2)| ≤ 1 / 2 := by
  let x := Real.pi / (4 * Real.arcsin (Real.sqrt p))
  have hx : 0 ≤ x := by
    dsimp [x]
    exact le_of_lt (div_pos Real.pi_pos (mul_pos (by norm_num) (Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hp))))
  refine ⟨⌊x⌋₊, abs_le.mpr ⟨?_, ?_⟩⟩
  · have := Nat.lt_floor_add_one x
    dsimp [x] at *
    linarith
  · have := Nat.floor_le hx
    dsimp [x] at *
    linarith

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (S R : Matrix (Qubits n) (Qubits n) ℂ) (M : Finset (Qubits n)),
      S ∈ Matrix.unitaryGroup (Qubits n) ℂ → R ∈ Matrix.unitaryGroup (Qubits n) ℂ →
      0 < probEvent (act S (zeroKet n)) (fun j => j ∈ M) →
      probEvent (act S (zeroKet n)) (fun j => j ∈ M) < 1 →
      act R (ampGoodState (act S (zeroKet n)) M) = -ampGoodState (act S (zeroKet n)) M →
      act R (ampBadState (act S (zeroKet n)) M) = ampBadState (act S (zeroKet n)) M →
      ∃ k : ℕ,
        (2 * (k : ℝ) + 1) ≤ C / Real.sqrt (probEvent (act S (zeroKet n)) (fun j => j ∈ M)) ∧
        2 / 3 ≤ ‖inner ℂ (ampGoodState (act S (zeroKet n)) M)
          (act (ampAmpIterate S R 0 ^ k) (act S (zeroKet n)))‖ := by
  refine ⟨Real.pi / 2 + 1, by positivity, ?_⟩
  intro n S R M hS hR hp hp1 hRG hRB
  let α := act S (zeroKet n)
  let p := probEvent α (fun j => j ∈ M)
  have hα : IsState α := by
    dsimp [α, IsState]
    rw [act_norm_of_mem_unitaryGroup hS]
    simp [zeroKet, ket]
  obtain ⟨hG, hB, horth, hprep⟩ := components α M hα hp hp1
  have haa := QAlgorithms.DeWolf.amplitudeAmplification n S R hS hR
    (ampGoodState α M) (ampBadState α M) hG hB horth p hp hp1.le hprep hRG hRB
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hsqrt1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp1.le
  have hself : inner ℂ (ampGoodState α M) (ampGoodState α M) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hG]; norm_num
  by_cases hlarge : (4 : ℝ) / 9 ≤ p
  · refine ⟨0, ?_, ?_⟩
    · dsimp [p, α] at hsqrt hsqrt1 ⊢
      rw [le_div_iff₀ hsqrt]
      simpa using (show Real.sqrt p ≤ Real.pi / 2 + 1 by linarith [Real.pi_pos])
    · change 2 / 3 ≤ ‖inner ℂ (ampGoodState α M) (act (ampAmpIterate S R 0 ^ 0) α)‖
      rw [haa.1 0]
      simp only [Nat.cast_zero, mul_zero, zero_add, one_mul, inner_add_right,
        inner_smul_right, hself, horth, mul_one, mul_zero, add_zero]
      rw [Real.sin_arcsin (by linarith : -1 ≤ Real.sqrt p) hsqrt1,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt]
      nlinarith [Real.sq_sqrt hp.le]
  · obtain ⟨k, hk⟩ := rounded_iterations p hp
    obtain ⟨hkθ, hθp, hsucc⟩ := haa.2 k hk
    refine ⟨k, ?_, ?_⟩
    · change 2 * (k : ℝ) + 1 ≤ (Real.pi / 2 + 1) / Real.sqrt p
      rw [le_div_iff₀ hsqrt]
      have hbound : (k : ℝ) * Real.sqrt p ≤ Real.pi / 4 := by
        have hh := hkθ.trans hθp
        have hh' := (le_div_iff₀ (show 0 < 4 * Real.sqrt p by positivity)).mp hh
        nlinarith
      nlinarith
    · have hn := norm_nonneg (inner ℂ (ampGoodState α M)
        (act (ampAmpIterate S R 0 ^ k) α))
      change 2 / 3 ≤ ‖inner ℂ (ampGoodState α M) (act (ampAmpIterate S R 0 ^ k) α)‖
      nlinarith
