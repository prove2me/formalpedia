-- Prove2me | solution 1 for QAlgorithms.Nannicini.search_knownCount
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:28:11.588601+00:00
-- url     : https://prove2.me/submissions/7394eaf5-a213-4f0b-969d-9b3b16d3f454

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation

open QAlgorithms
open scoped ComplexConjugate

private lemma aa_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) : act (A * B) v = act A (act B v) := by
  ext i
  exact (congrFun (Matrix.mulVec_mulVec (WithLp.ofLp v) A B) i).symm

private lemma aa_add {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (u v : EuclideanSpace ℂ ι) : act A (u + v) = act A u + act A v := by
  ext i
  simp [act, Matrix.mulVec_add]

private lemma aa_sub {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (u v : EuclideanSpace ℂ ι) : act A (u - v) = act A u - act A v := by
  ext i
  simp [act, Matrix.mulVec_sub]

private lemma aa_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (c : ℂ) (v : EuclideanSpace ℂ ι) : act A (c • v) = c • act A v := by
  ext i
  simp [act, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

private lemma aa_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) : act (1 : Matrix ι ι ℂ) v = v := by
  ext i
  simp [act]

private lemma aa_ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z : ι) : act A (ket z) = WithLp.toLp 2 (fun i => A i z) := by
  ext i
  simp [act, ket, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]


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

private def reflection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.of fun i j => 2 * α i * conj (α j) - (1 : Matrix ι ι ℂ) i j

private lemma reflection_act {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α v : EuclideanSpace ℂ ι) :
    act (reflection α) v = (2 * inner ℂ α v) • α - v := by
  ext i
  simp only [act, reflection, Matrix.of_apply, Matrix.mulVec, dotProduct,
    sub_mul, Finset.sum_sub_distrib, PiLp.toLp_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct,
    Pi.star_apply]
  rw [show (∑ j, (1 : Matrix ι ι ℂ) i j * v j) = v i by
    simpa only [Matrix.mulVec, dotProduct] using congrFun (Matrix.one_mulVec (WithLp.ofLp v)) i]
  congr 1
  simp only [starRingEnd_apply]
  simp_rw [show ∀ j, 2 * α i * star (α j) * v j = (2 * α i) * (star (α j) * v j) by intros; ring]
  rw [← Finset.mul_sum]
  simp_rw [show ∀ j, star (α j) * v j = v j * star (α j) by intros; ring]
  ring

private lemma reflection_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : EuclideanSpace ℂ ι) (hα : IsState α) :
    reflection α ∈ Matrix.unitaryGroup ι ℂ := by
  have hi : inner ℂ α α = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hα]; norm_num
  have hstar : star (reflection α) = reflection α := by
    ext i j
    change conj (2 * α j * conj (α i) - (1 : Matrix ι ι ℂ) j i) =
      2 * α i * conj (α j) - (1 : Matrix ι ι ℂ) i j
    simp only [map_sub, map_mul, map_ofNat, starRingEnd_self_apply]
    have hs : conj ((1 : Matrix ι ι ℂ) j i) = (1 : Matrix ι ι ℂ) i j := by
      simp [Matrix.one_apply, eq_comm]
    rw [hs]; ring
  rw [Matrix.mem_unitaryGroup_iff, hstar]
  ext i j
  have h := congrArg (fun v : EuclideanSpace ℂ ι => v i)
    (show act (reflection α * reflection α) (ket j) = ket j from by
      rw [aa_mul, reflection_act, reflection_act]
      simp only [inner_sub_right, inner_smul_right, hi, mul_one]
      module)
  change (act (reflection α * reflection α) (ket j)) i = (ket j) i at h
  rw [aa_ket] at h
  simpa only [PiLp.toLp_apply, ket, EuclideanSpace.single_apply, Matrix.one_apply] using h


private lemma rotation_step {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α u v : EuclideanSpace ℂ ι) (R : Matrix ι ι ℂ)
    (hu : IsState u) (hv : IsState v) (huv : inner ℂ u v = 0)
    (θ t : ℝ) (hw : α = (Real.sin θ : ℂ) • u + (Real.cos θ : ℂ) • v)
    (hRu : act R u = -u) (hRv : act R v = v) :
    act (reflection α * R) ((Real.sin t : ℂ) • u + (Real.cos t : ℂ) • v) =
      (Real.sin (t + 2 * θ) : ℂ) • u + (Real.cos (t + 2 * θ) : ℂ) • v := by
  have huu : inner ℂ u u = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hvv : inner ℂ v v = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; norm_num
  have hvu : inner ℂ v u = 0 := by rw [← inner_conj_symm, huv, map_zero]
  have trig : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  rw [aa_mul, aa_add, aa_smul, aa_smul, hRu, hRv, reflection_act, hw]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_neg_right, huu, hvv, huv, hvu, map_add, map_mul, map_ofNat,
    Complex.conj_ofReal, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.neg_apply, Real.sin_add, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  linear_combination -2 * (Real.sin t : ℂ) * u i * trig

private abbrev Register (n : ℕ) := (Qubits n × Bool) × Fin 4

private noncomputable def startState (n : ℕ) : EuclideanSpace ℂ (Register n) :=
  WithLp.toLp 2 fun z =>
    if z.2 = 0 ∧ z.1.2 = true then -((Real.sqrt (8 * (2 : ℝ)^n))⁻¹ : ℂ)
    else ((Real.sqrt (8 * (2 : ℝ)^n))⁻¹ : ℂ)

private lemma start_coord (n : ℕ) (z : Register n) :
    ‖startState n z‖ ^ 2 = (8 * (2 : ℝ)^n)⁻¹ := by
  have hp : 0 < 8 * (2 : ℝ)^n := by positivity
  simp only [startState, PiLp.toLp_apply]
  split_ifs <;> simp only [norm_neg, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt hp.le]

private lemma start_unit (n : ℕ) : IsState (startState n) := by
  have h : ‖startState n‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [start_coord]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
    <;> ring
  dsimp [IsState]
  nlinarith [norm_nonneg (startState n)]

private def marked {n : ℕ} (f : Qubits n → Bool) : Finset (Register n) :=
  Finset.univ.filter fun z => z.2 = 0 ∧ f z.1.1 = true

private lemma marked_prob {n t : ℕ} (f : Qubits n → Bool)
    (ht : (Finset.univ.filter fun j => f j = true).card = t) :
    probEvent (startState n) (fun z => z ∈ marked f) = (t : ℝ) / (4 * (2 : ℝ)^n) := by
  simp only [probEvent, prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul]
  simp_rw [start_coord]
  have hcard : (marked f).card = 2 * t := by
    simp only [marked, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Fin.sum_univ_succ]
    norm_num [Fin.ext_iff]
    rw [Finset.sum_add_distrib]
    simpa only [Finset.card_eq_sum_ones, Finset.sum_filter, two_mul] using congrArg (fun k : ℕ => 2 * k) ht
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hfilter : (Finset.univ.filter fun z => z ∈ marked f) = marked f := by ext; simp
  rw [hfilter, hcard]
  push_cast
  field_simp
  <;> ring

private lemma oracle_coord {n : ℕ} (f : Qubits n → Bool)
    (v : EuclideanSpace ℂ (Register n)) (j : Qubits n) (b : Bool) (w : Fin 4) :
    act (Matrix.kronecker (xorOracle f) (1 : Matrix (Fin 4) (Fin 4) ℂ)) v ((j,b),w) =
      v ((j,b + f j),w) := by
  classical
  simp only [act, PiLp.toLp_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kroneckerMap_apply, xorOracle, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single j]
  · simp only [true_and]
    cases hb : b <;> cases hf : f j <;>
      simp [hb, hf, Fintype.sum_bool, Bool.add_eq_xor]
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

private lemma oracle_good {n : ℕ} (f : Qubits n → Bool) :
    act (Matrix.kronecker (xorOracle f) (1 : Matrix (Fin 4) (Fin 4) ℂ))
      (ampGoodState (startState n) (marked f)) =
        -ampGoodState (startState n) (marked f) := by
  ext ⟨⟨j,b⟩,w⟩
  rw [oracle_coord]
  simp only [ampGoodState, PiLp.smul_apply, PiLp.neg_apply, PiLp.toLp_apply,
    smul_eq_mul, marked, Finset.mem_filter, Finset.mem_univ, true_and,
    startState]
  by_cases hw : w = 0 <;> cases hb : b <;> cases hf : f j <;>
    simp [hw, hb, hf, Bool.add_eq_xor]

private lemma oracle_bad {n : ℕ} (f : Qubits n → Bool) :
    act (Matrix.kronecker (xorOracle f) (1 : Matrix (Fin 4) (Fin 4) ℂ))
      (ampBadState (startState n) (marked f)) =
        ampBadState (startState n) (marked f) := by
  ext ⟨⟨j,b⟩,w⟩
  rw [oracle_coord]
  simp only [ampBadState, PiLp.smul_apply, PiLp.toLp_apply,
    smul_eq_mul, marked, Finset.mem_filter, Finset.mem_univ, true_and,
    startState]
  by_cases hw : w = 0 <;> cases hb : b <;> cases hf : f j <;>
    simp [hw, hb, hf, Bool.add_eq_xor]

private noncomputable def searchAlg (n T : ℕ) : QueryAlg (Qubits n) Bool (Fin 4) T where
  start := startState n
  start_unit := start_unit n
  U := fun i => if i.val = 0 then 1 else ⟨reflection (startState n), reflection_unitary _ (start_unit n)⟩

private lemma search_state (n T : ℕ) (f : Qubits n → Bool) :
    (searchAlg n T).finalState (xorOracle f) =
      act ((reflection (startState n) *
        Matrix.kronecker (xorOracle f) (1 : Matrix (Fin 4) (Fin 4) ℂ)) ^ T) (startState n) := by
  have h : ∀ i : Fin (T+1), (searchAlg n T).stateAt (xorOracle f) i =
      act ((reflection (startState n) *
        Matrix.kronecker (xorOracle f) (1 : Matrix (Fin 4) (Fin 4) ℂ)) ^ i.val) (startState n) := by
    intro i
    induction i using Fin.induction with
    | zero => simp [QueryAlg.stateAt, searchAlg, aa_one]
    | succ i ih =>
      simp only [QueryAlg.stateAt, Fin.induction_succ] at ih ⊢
      change act (reflection (startState n))
        (act (Matrix.kronecker (xorOracle f) (1 : Matrix (Fin 4) (Fin 4) ℂ)) _) = _
      rw [ih]
      simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', aa_mul]
  exact h (Fin.last T)

private lemma rotation_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α u v : EuclideanSpace ℂ ι) (R : Matrix ι ι ℂ)
    (hu : IsState u) (hv : IsState v) (huv : inner ℂ u v = 0)
    (θ : ℝ) (hw : α = (Real.sin θ : ℂ) • u + (Real.cos θ : ℂ) • v)
    (hRu : act R u = -u) (hRv : act R v = v) (k : ℕ) :
    act ((reflection α * R) ^ k) α =
      (Real.sin ((2*k+1)*θ) : ℂ) • u + (Real.cos ((2*k+1)*θ) : ℂ) • v := by
  induction k with
  | zero => simpa [aa_one] using hw
  | succ k ih =>
    rw [pow_succ', aa_mul, ih, rotation_step α u v R hu hv huv θ _ hw hRu hRv]
    have he : ((2 : ℝ) * k + 1) * θ + 2 * θ = (2 * (k + 1) + 1) * θ := by ring
    simpa only [Nat.cast_add, Nat.cast_one, he]

private lemma good_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : EuclideanSpace ℂ ι) (M : Finset ι) (hp : 0 < probEvent α (fun z => z ∈ M))
    (a b : ℝ) :
    probEvent ((a : ℂ) • ampGoodState α M + (b : ℂ) • ampBadState α M)
      (fun z => z ∈ M) = a ^ 2 := by
  have hcoord (z : ι) (hz : z ∈ M) :
      prob ((a : ℂ) • ampGoodState α M + (b : ℂ) • ampBadState α M) z =
        (a ^ 2 / probEvent α (fun z => z ∈ M)) * prob α z := by
    have hs : (Real.sqrt (probEvent α (fun z => z ∈ M))) ^ 2 =
        probEvent α (fun z => z ∈ M) := Real.sq_sqrt hp.le
    simp only [prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul,
      PiLp.add_apply, PiLp.smul_apply, ampGoodState, ampBadState, smul_eq_mul,
      PiLp.toLp_apply, if_pos hz, mul_zero, add_zero, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simp only [map_one, norm_one, one_mul, mul_pow, sq_abs, inv_pow, hs]
    ring
  simp only [probEvent]
  rw [Finset.sum_congr rfl (fun z hz => hcoord z (Finset.mem_filter.mp hz).2),
    ← Finset.mul_sum]
  change a ^ 2 / probEvent α (fun z => z ∈ M) * probEvent α (fun z => z ∈ M) = _
  exact div_mul_cancel₀ _ hp.ne'

private lemma event_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ z, P z → Q z) : probEvent v P ≤ probEvent v Q := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact h z hz
  · intro z _ _
    exact sq_nonneg _

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n t : ℕ, 1 ≤ t → t ≤ 2 ^ n →
      ∃ (w T : ℕ) (A : QueryAlg (Qubits n) Bool (Fin w) T)
        (out : (Qubits n × Bool) × Fin w → Qubits n),
        (T : ℝ) ≤ C * Real.sqrt ((2 : ℝ) ^ n / (t : ℝ)) ∧
        ∀ f : Qubits n → Bool, (Finset.univ.filter fun j => f j = true).card = t →
          2 / 3 ≤ probEvent (A.finalState (xorOracle f)) fun z => f (out z) = true := by
  classical
  refine ⟨Real.pi / 2, by positivity, ?_⟩
  intro n t ht htop
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hN : 0 < (2 : ℝ)^n := by positivity
  have htN : (t : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast htop
  let p := (t : ℝ) / (4 * (2 : ℝ)^n)
  have hp : 0 < p := div_pos ht0 (by positivity)
  have hpquarter : p ≤ 1/4 := by
    dsimp [p]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (2 : ℝ)^n)).mpr
    linarith
  let θ := Real.arcsin (Real.sqrt p)
  have hθ : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hp)
  have hθtop : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hs : Real.sin θ = Real.sqrt p := Real.sin_arcsin
    (by linarith [Real.sqrt_nonneg p]) (Real.sqrt_le_one.mpr (by linarith))
  have hc : Real.cos θ = Real.sqrt (1-p) := by
    dsimp [θ]
    rw [Real.cos_arcsin, Real.sq_sqrt hp.le]
  obtain ⟨k, hk⟩ := rounded_iterations p hp
  have hr := aa_round p θ hp hθ hθtop hs k hk
  refine ⟨4, k, searchAlg n k, fun z => z.1.1, ?_, ?_⟩
  · have hroot : Real.sqrt p * Real.sqrt ((2 : ℝ)^n / t) = 1/2 := by
      rw [← Real.sqrt_mul hp.le]
      have he : p * ((2 : ℝ)^n / t) = (1/2 : ℝ)^2 := by
        dsimp [p]
        field_simp
        <;> ring
      rw [he, Real.sqrt_sq (by norm_num)]
    calc
      (k : ℝ) ≤ Real.pi / (4 * Real.sqrt p) := hr.1.trans hr.2.1
      _ = Real.pi / 2 * Real.sqrt ((2 : ℝ)^n / t) := by
        apply (div_eq_iff (by positivity : 4 * Real.sqrt p ≠ 0)).mpr
        symm
        calc
          _ = 2 * Real.pi * (Real.sqrt p * Real.sqrt ((2 : ℝ)^n / t)) := by ring
          _ = Real.pi := by rw [hroot]; ring
  · intro f hf
    have hprob : probEvent (startState n) (fun z => z ∈ marked f) = p := marked_prob f hf
    obtain ⟨hu, hv, huv, hw⟩ := components (startState n) (marked f) (start_unit n)
      (by rw [hprob]; exact hp) (by rw [hprob]; linarith)
    have hwθ : startState n =
        (Real.sin θ : ℂ) • ampGoodState (startState n) (marked f) +
          (Real.cos θ : ℂ) • ampBadState (startState n) (marked f) := by
      simpa only [hprob, hs, hc] using hw
    have hstate := rotation_power (startState n)
      (ampGoodState (startState n) (marked f)) (ampBadState (startState n) (marked f))
      (Matrix.kronecker (xorOracle f) (1 : Matrix (Fin 4) (Fin 4) ℂ))
      hu hv huv θ hwθ (oracle_good f) (oracle_bad f) k
    have hsuccess : probEvent ((searchAlg n k).finalState (xorOracle f))
        (fun z => z ∈ marked f) = Real.sin ((2*k+1)*θ)^2 := by
      rw [search_state, hstate]
      exact good_probability (startState n) (marked f) (by rw [hprob]; exact hp) _ _
    calc
      2/3 ≤ 1-p := by linarith
      _ ≤ Real.sin ((2*k+1)*θ)^2 := hr.2.2
      _ = probEvent ((searchAlg n k).finalState (xorOracle f))
          (fun z => z ∈ marked f) := hsuccess.symm
      _ ≤ probEvent ((searchAlg n k).finalState (xorOracle f))
          (fun z => f z.1.1 = true) := event_mono _ _ _ (by
            intro z hz
            exact (Finset.mem_filter.mp hz).2.2)
