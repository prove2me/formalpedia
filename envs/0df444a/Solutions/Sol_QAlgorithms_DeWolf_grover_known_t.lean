-- Prove2me | solution 1 for QAlgorithms.DeWolf.grover_known_t
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:18:46.924596+00:00
-- url     : https://prove2.me/submissions/7f245ac3-a8e6-4f68-9788-b6f03c218b01

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Theorems.Thm_QAlgorithms_DeWolf_amplitudeAmplification

open QAlgorithms
open scoped ComplexConjugate

private def sgn (b : Bool) : ℂ := if b then -1 else 1

private lemma sgn_add (a b : Bool) : sgn (a + b) = sgn a * sgn b := by
  cases a <;> cases b <;> norm_num [sgn, Bool.add_eq_xor, Bool.zero_eq_false]

private lemma sgn_sum {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn, Bool.zero_eq_false]
  | @insert a s ha ih => simp [ha, sgn_add, ih]

private lemma char_orth (n : ℕ) (a b : Qubits n) :
    (∑ i : Qubits n, sgn (dotBits a i) * sgn (dotBits b i)) =
      if a = b then (2 : ℂ)^n else 0 := by
  classical
  simp_rw [dotBits, sgn_sum, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k v => sgn (a k && v) * sgn (b k && v))]
  have h (k : Fin n) :
      (∑ v : Bool, sgn (a k && v) * sgn (b k && v)) =
        if a k = b k then (2 : ℂ) else 0 := by
    cases a k <;> cases b k <;> norm_num [sgn, Bool.add_eq_xor, Bool.zero_eq_false]
  simp_rw [h]
  by_cases hab : a = b
  · subst b; simp
  · rw [if_neg hab]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

private lemma normalization (n : ℕ) :
    ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)) ^ 2 * (2 : ℂ)^n = 1 := by
  have h : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 2 * 2 = 1 := by
    have hsq : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have : ((Real.sqrt (2 : ℝ))⁻¹)^2 * 2 = 1 := by field_simp; nlinarith
    exact_mod_cast this
  push_cast at h ⊢
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow, h, one_pow]

private lemma hadamard_involutive (n : ℕ) : hadamardN n * hadamardN n = 1 := by
  classical
  have he (a b : Qubits n) : hadamardN n a b =
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * sgn (dotBits a b) := by
    have hc : dotBits b a = dotBits a b := by simp [dotBits, Bool.and_comm]
    simp only [hadamardN, Matrix.of_apply, hc, sgn]
    split_ifs <;> ring
  ext a b
  simp_rw [Matrix.mul_apply, he]
  have hc (i : Qubits n) : dotBits i b = dotBits b i := by simp [dotBits, Bool.and_comm]
  simp_rw [hc]
  simp_rw [show ∀ u v : ℂ, (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * u *
    ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * v) =
      ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ))^2 * (u * v) by intros; ring]
  rw [← Finset.mul_sum, char_orth]
  by_cases h : a = b
  · subst b
    simpa only [ite_true, Matrix.one_apply_eq] using normalization n
  · simp [h]


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


private lemma aa_round (p θ : ℝ) (hp : 0 < p) (hθ : 0 < θ)
    (hθtop : θ ≤ Real.pi / 2) (hsin : Real.sin θ = Real.sqrt p)
    (k : ℕ) (hk : |(k : ℝ) - (Real.pi / (4 * θ) - 1 / 2)| ≤ 1 / 2) :
    (k : ℝ) ≤ Real.pi / (4 * θ) ∧
    Real.pi / (4 * θ) ≤ Real.pi / (4 * Real.sqrt p) ∧
    1 - p ≤ Real.sin ((2 * k + 1) * θ) ^ 2 := by
  have hkp := (abs_le.mp hk).2
  have hlo := (abs_le.mp hk).1
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hsmall : Real.sqrt p ≤ θ := by rw [← hsin]; exact Real.sin_le hθ.le
  refine ⟨by linarith, div_le_div_of_nonneg_left Real.pi_pos.le
    (by positivity) (by linarith), ?_⟩
  let d := (k : ℝ) - (Real.pi / (4 * θ) - 1 / 2)
  let e := 2 * d * θ
  have he : |e| ≤ θ := by
    dsimp [e]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos hθ]
    dsimp [d]
    nlinarith
  have ht : (2 * (k : ℝ) + 1) * θ = Real.pi / 2 + e := by
    dsimp [e, d]
    field_simp
    <;> ring
  have hse : |Real.sin e| ≤ Real.sin θ := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (he.trans (by linarith [Real.pi_pos]))]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) (abs_nonneg e)) hθtop he
  have hsquare : Real.sin e ^ 2 ≤ p := by
    have hs := Real.sq_sqrt hp.le
    rw [hsin] at hse
    calc
      Real.sin e ^ 2 = |Real.sin e| ^ 2 := (sq_abs _).symm
      _ ≤ Real.sqrt p ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hse 2
      _ = p := hs
  rw [ht, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
  simp only [one_mul, zero_mul, add_zero]
  nlinarith [Real.sin_sq_add_cos_sq e]

private lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) : act (A * B) ψ = act A (act B ψ) := by
  exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec _ _ _).symm

private lemma act_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (c : ℂ) (ψ : EuclideanSpace ℂ ι) : act A (c • ψ) = c • act A ψ := by
  ext j
  simp [act, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]

private lemma had_unitary (n : ℕ) : hadamardN n ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [hadamardN_star, hadamard_involutive]

private lemma phase_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → Bool) :
    phaseOracle x ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  by_cases hij : i = j
  · subst j
    cases hx : x i <;> simp [phaseOracle, hx]
  · simp [phaseOracle, hij, Ne.symm hij]

private lemma phase_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → Bool)
    (ψ : EuclideanSpace ℂ ι) (j : ι) :
    act (phaseOracle x) ψ j = (if x j then -1 else 1) * ψ j := by
  simp [act, phaseOracle, Matrix.mulVec_diagonal]

private lemma initial_apply (n : ℕ) (j : Qubits n) :
    act (hadamardN n) (zeroKet n) j = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) := by
  have hz : dotBits (fun _ : Fin n => false) j = false := by
    simp only [dotBits, Bool.false_and]
    change (∑ _ : Fin n, (0 : Bool)) = false
    simp only [Finset.sum_const_zero]
    rfl
  simp [act, zeroKet, ket, hadamardN, hz]

private lemma initial_state (n : ℕ) : IsState (act (hadamardN n) (zeroKet n)) := by
  rw [IsState, act_norm_of_mem_unitaryGroup (had_unitary n)]
  simp [zeroKet, ket]

private lemma initial_prob (n : ℕ) (x : Qubits n → Bool) :
    probEvent (act (hadamardN n) (zeroKet n)) (fun j => x j = true) =
      (hammingWeight x : ℝ) / (2 ^ n : ℕ) := by
  have hn : (((Real.sqrt 2)⁻¹ ^ n : ℝ)) ^ 2 * (2 : ℝ)^n = 1 := by
    exact_mod_cast normalization n
  have hp : (0 : ℝ) < 2^n := by positivity
  simp only [probEvent, prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul, initial_apply,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Finset.sum_const, nsmul_eq_mul]
  rw [show (((Real.sqrt 2)⁻¹ ^ n : ℝ)) ^ 2 = 1 / (2:ℝ)^n by
    apply (eq_div_iff (ne_of_gt hp)).mpr; simpa using hn]
  simp [hammingWeight, div_eq_mul_inv]

private lemma event_amplified {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : EuclideanSpace ℂ ι) (M : Finset ι) (hp : 0 < probEvent α (fun j => j ∈ M))
    (s c : ℝ) :
    probEvent ((s : ℂ) • ampGoodState α M + (c : ℂ) • ampBadState α M)
      (fun j => j ∈ M) = s^2 := by
  have hs : Real.sqrt (probEvent α fun j => j ∈ M) ≠ 0 :=
    (Real.sqrt_pos.mpr hp).ne'
  simp only [probEvent, prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul]
  have hc (j : ι) (hj : j ∈ Finset.univ.filter (fun j => j ∈ M)) :
      ‖((s : ℂ) • ampGoodState α M + (c : ℂ) • ampBadState α M) j‖^2 =
        (s^2 / probEvent α (fun j => j ∈ M)) * ‖α j‖^2 := by
    have hjM := (Finset.mem_filter.mp hj).2
    simp only [ampGoodState, ampBadState, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, hjM, if_true, mul_zero, add_zero]
    rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt hp.le]
    ring
  rw [Finset.sum_congr rfl hc, ← Finset.mul_sum]
  have he : (∑ j ∈ Finset.univ.filter (fun j => j ∈ M), ‖α j‖^2) =
      probEvent α (fun j => j ∈ M) := by
    simp [probEvent, prob, ket, EuclideanSpace.inner_single_left]
  rw [he, div_mul_cancel₀ _ hp.ne']
private lemma reflection_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι) :
    reflAt z ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = z <;> simp [reflAt, hi]
  · simp [reflAt, hij, Ne.symm hij]

private lemma all_marked_prob (n : ℕ) (x : Qubits n → Bool) (hx : ∀ j, x j = true)
    (k : ℕ) : groverSuccessProb x k = 1 := by
  have hG : groverIterate x ∈ Matrix.unitaryGroup (Qubits n) ℂ :=
    mul_mem (mul_mem (mul_mem (had_unitary n) (reflection_unitary 0)) (had_unitary n))
      (phase_unitary x)
  have hnorm : ‖act (groverIterate x ^ k) (act (hadamardN n) (zeroKet n))‖ = 1 := by
    rw [act_norm_of_mem_unitaryGroup (pow_mem hG k)]
    exact initial_state n
  unfold groverSuccessProb probEvent
  simp only [hx, Finset.filter_true]
  simp only [prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [← EuclideanSpace.norm_sq_eq, hnorm]
  norm_num

private lemma grover_formula (n : ℕ) (x : Qubits n → Bool) (ht : 1 ≤ hammingWeight x) :
    ∀ k : ℕ, groverSuccessProb x k =
      Real.sin ((2 * k + 1) * groverAngle (hammingWeight x) (2^n)) ^ 2 := by
  classical
  let α := act (hadamardN n) (zeroKet n)
  let M := Finset.univ.filter (fun j => x j = true)
  let p : ℝ := (hammingWeight x : ℝ) / (2 ^ n : ℕ)
  have hp : 0 < p := div_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)) (by positivity)
  have htN : hammingWeight x ≤ 2^n := by
    calc hammingWeight x ≤ Fintype.card (Qubits n) := Finset.card_filter_le _ _
         _ = 2^n := by simp [Qubits]
  have hpN : p ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast htN)
  have hprob : probEvent α (fun j => j ∈ M) = p := by
    simpa only [α, M, Finset.mem_filter, Finset.mem_univ, true_and] using initial_prob n x
  by_cases hp1 : p = 1
  · have hc : hammingWeight x = 2^n := by
      have he := (div_eq_one_iff_eq (by positivity : ((2^n : ℕ) : ℝ) ≠ 0)).mp hp1
      exact_mod_cast he
    have hM : M = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by simpa [M, hammingWeight, Qubits] using hc.ge)
    have hx : ∀ j, x j = true := by
      intro j
      have := show j ∈ M from hM.symm ▸ Finset.mem_univ j
      exact (Finset.mem_filter.mp this).2
    intro k
    rw [all_marked_prob n x hx k]
    have hangle : groverAngle (hammingWeight x) (2^n) = Real.pi / 2 := by
      simp [groverAngle, hc]
    rw [hangle, show (2 * (k : ℝ) + 1) * (Real.pi / 2) =
      k * Real.pi + Real.pi / 2 by ring, Real.sin_add]
    simp only [Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, Real.sin_pi_div_two,
      Real.cos_pi_div_two, mul_one, mul_zero, zero_add]
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  · obtain ⟨hG,hB,horth,hprep⟩ := components α M (initial_state n)
      (hprob.symm ▸ hp) (hprob.symm ▸ lt_of_le_of_ne hpN hp1)
    have hRG : act (phaseOracle x) (ampGoodState α M) = -ampGoodState α M := by
      ext j
      rw [phase_apply]
      cases hj : x j <;> simp [ampGoodState, M, hj]
    have hRB : act (phaseOracle x) (ampBadState α M) = ampBadState α M := by
      ext j
      rw [phase_apply]
      cases hj : x j <;> simp [ampBadState, M, hj]
    have haa := QAlgorithms.DeWolf.amplitudeAmplification n (hadamardN n) (phaseOracle x)
      (had_unitary n) (phase_unitary x) (ampGoodState α M) (ampBadState α M)
      hG hB horth p hp hpN (by simpa only [hprob] using hprep) hRG hRB
    intro k
    have heq : ampAmpIterate (hadamardN n) (phaseOracle x) 0 = groverIterate x := by
      simp [ampAmpIterate, groverIterate, hadamardN_star]
    have ht := haa.1 k
    rw [heq] at ht
    change probEvent (act (groverIterate x ^ k) α) (fun j => x j = true) = _
    rw [ht]
    simpa only [M, Finset.mem_filter, Finset.mem_univ, true_and, groverAngle, p]
      using event_amplified α M (hprob.symm ▸ hp)
        (Real.sin ((2 * k + 1) * Real.arcsin (Real.sqrt p)))
        (Real.cos ((2 * k + 1) * Real.arcsin (Real.sqrt p)))
theorem solution (n : ℕ) (x : Qubits n → Bool) (ht : 1 ≤ hammingWeight x) :
    (∀ k : ℕ, groverSuccessProb x k =
        Real.sin ((2 * k + 1) * groverAngle (hammingWeight x) (2 ^ n)) ^ 2) ∧
    ∀ k : ℕ, |(k : ℝ) - (Real.pi / (4 * groverAngle (hammingWeight x) (2 ^ n)) - 1 / 2)| ≤ 1 / 2 →
      1 - (hammingWeight x : ℝ) / ((2 ^ n : ℕ) : ℝ) ≤ groverSuccessProb x k ∧
      (k : ℝ) ≤ Real.pi / (4 * groverAngle (hammingWeight x) (2 ^ n)) ∧
      Real.pi / (4 * groverAngle (hammingWeight x) (2 ^ n)) ≤
        Real.pi / 4 * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (hammingWeight x : ℝ)) := by
  have hf := grover_formula n x ht
  refine ⟨hf, ?_⟩
  intro k hk
  let p : ℝ := (hammingWeight x : ℝ) / ((2^n : ℕ) : ℝ)
  let θ := groverAngle (hammingWeight x) (2^n)
  have hp : 0 < p := div_pos
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)) (by positivity)
  have hp1 : p ≤ 1 := by
    have hw : hammingWeight x ≤ 2^n := by
      calc hammingWeight x ≤ Fintype.card (Qubits n) := Finset.card_filter_le _ _
           _ = 2^n := by simp [Qubits]
    exact (div_le_one (by positivity)).mpr (by exact_mod_cast hw)
  have hθ : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hp)
  have hθtop : θ ≤ Real.pi/2 := Real.arcsin_le_pi_div_two _
  have hsin : Real.sin θ = Real.sqrt p :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg p]) (Real.sqrt_le_one.mpr hp1)
  obtain ⟨hkθ,hθp,hsucc⟩ := aa_round p θ hp hθ hθtop hsin k hk
  refine ⟨by rw [hf]; exact hsucc, hkθ, ?_⟩
  have hrecip : Real.sqrt (((2^n : ℕ) : ℝ) / (hammingWeight x : ℝ)) = (Real.sqrt p)⁻¹ := by
    dsimp [p]
    rw [Real.sqrt_div, Real.sqrt_div, inv_div] <;> positivity
  calc
    Real.pi / (4 * θ) ≤ Real.pi / (4 * Real.sqrt p) := hθp
    _ = Real.pi / 4 * Real.sqrt (((2^n : ℕ) : ℝ) / (hammingWeight x : ℝ)) := by
      rw [hrecip]; ring
