-- Prove2me | solution 1 for QAlgorithms.DeWolf.amplitudeAmplification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:44:51.853814+00:00
-- url     : https://prove2.me/submissions/8181d220-7f92-4623-946f-3e6d0b83bc4f

import Definitions.Def_QAlgorithms_Defs_Search

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

private lemma aa_refl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι) (v : EuclideanSpace ℂ ι) :
    act (reflAt z) v = (2 * v z) • ket z - v := by
  ext i
  simp only [act, reflAt, Matrix.mulVec_diagonal, PiLp.toLp_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ket, EuclideanSpace.single_apply]
  by_cases h : i = z
  · subst i; simp; ring
  · simp [h]

private lemma aa_reflect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (z : ι)
    (v : EuclideanSpace ℂ ι) :
    act (A * reflAt z * star A) v =
      (2 * inner ℂ (act A (ket z)) v) • act A (ket z) - v := by
  have hc : (act (star A) v) z = inner ℂ (act A (ket z)) v := by
    rw [aa_ket]
    simp [act, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec, dotProduct,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, mul_comm]
  rw [aa_mul, aa_mul, aa_refl, aa_sub, aa_smul, hc, ← aa_mul,
    Matrix.mem_unitaryGroup_iff.mp hA, aa_one]

private lemma aa_plane {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A RG : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (z : ι)
    (u v : EuclideanSpace ℂ ι) (hu : IsState u) (hv : IsState v)
    (huv : inner ℂ u v = 0) (θ t : ℝ)
    (hw : act A (ket z) = (Real.sin θ : ℂ) • u + (Real.cos θ : ℂ) • v)
    (hRu : act RG u = -u) (hRv : act RG v = v) :
    act (ampAmpIterate A RG z) ((Real.sin t : ℂ) • u + (Real.cos t : ℂ) • v) =
      (Real.sin (t + 2 * θ) : ℂ) • u + (Real.cos (t + 2 * θ) : ℂ) • v := by
  have huu : inner ℂ u u = 1 := by simp [inner_self_eq_norm_sq_to_K, IsState] at hu ⊢; rw [hu]; norm_num
  have hvv : inner ℂ v v = 1 := by simp [inner_self_eq_norm_sq_to_K, IsState] at hv ⊢; rw [hv]; norm_num
  have hvu : inner ℂ v u = 0 := by rw [← inner_conj_symm, huv, map_zero]
  have trig : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  rw [ampAmpIterate, aa_mul, aa_add, aa_smul, aa_smul, hRu, hRv, aa_reflect A hA, hw]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_neg_right, huu, hvv, huv, hvu, map_add, map_mul, map_ofNat,
    Complex.conj_ofReal, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.neg_apply, Real.sin_add, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  linear_combination -2 * (Real.sin t : ℂ) * u i * trig

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

theorem solution (m : ℕ) (A RG : Matrix (Qubits m) (Qubits m) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Qubits m) ℂ) (hRG : RG ∈ Matrix.unitaryGroup (Qubits m) ℂ)
    (ψ1 ψ0 : EuclideanSpace ℂ (Qubits m)) (hψ1 : IsState ψ1) (hψ0 : IsState ψ0)
    (horth : inner ℂ ψ1 ψ0 = 0) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hAψ : act A (zeroKet m) =
      (Real.sqrt p : ℂ) • ψ1 + (Real.sqrt (1 - p) : ℂ) • ψ0)
    (hRG1 : act RG ψ1 = -ψ1) (hRG0 : act RG ψ0 = ψ0) :
    (∀ k : ℕ, act (ampAmpIterate A RG (0 : Qubits m) ^ k) (act A (zeroKet m)) =
        (Real.sin ((2 * k + 1) * Real.arcsin (Real.sqrt p)) : ℂ) • ψ1 +
          (Real.cos ((2 * k + 1) * Real.arcsin (Real.sqrt p)) : ℂ) • ψ0) ∧
    ∀ k : ℕ, |(k : ℝ) - (Real.pi / (4 * Real.arcsin (Real.sqrt p)) - 1 / 2)| ≤ 1 / 2 →
      (k : ℝ) ≤ Real.pi / (4 * Real.arcsin (Real.sqrt p)) ∧
      Real.pi / (4 * Real.arcsin (Real.sqrt p)) ≤ Real.pi / (4 * Real.sqrt p) ∧
      1 - p ≤ ‖inner ℂ ψ1 (act (ampAmpIterate A RG (0 : Qubits m) ^ k) (act A (zeroKet m)))‖ ^ 2 := by
  let θ := Real.arcsin (Real.sqrt p)
  have hsq : Real.sqrt p ≤ 1 := (Real.sqrt_le_one).mpr hp1
  have hs : Real.sin θ = Real.sqrt p := Real.sin_arcsin (by linarith [Real.sqrt_nonneg p]) hsq
  have hc : Real.cos θ = Real.sqrt (1 - p) := by
    dsimp [θ]
    rw [Real.cos_arcsin, Real.sq_sqrt hp0.le]
  have hw : act A (ket (0 : Qubits m)) =
      (Real.sin θ : ℂ) • ψ1 + (Real.cos θ : ℂ) • ψ0 := by
    have hz : (0 : Qubits m) = (fun _ => false) := by funext i; rfl
    simpa only [hs, hc, hz, zeroKet] using hAψ
  have hall : ∀ k : ℕ,
      act (ampAmpIterate A RG (0 : Qubits m) ^ k) (act A (zeroKet m)) =
        (Real.sin ((2 * k + 1) * θ) : ℂ) • ψ1 +
          (Real.cos ((2 * k + 1) * θ) : ℂ) • ψ0 := by
    intro k
    induction k with
    | zero => simpa [aa_one, hs, hc] using hAψ
    | succ k ih =>
      rw [pow_succ', aa_mul, ih, aa_plane A RG hA _ ψ1 ψ0 hψ1 hψ0 horth θ _ hw hRG1 hRG0]
      have heq : (2 * (k : ℝ) + 1) * θ + 2 * θ = (2 * ((k + 1 : ℕ) : ℝ) + 1) * θ := by
        push_cast; ring
      rw [heq]
  refine ⟨hall, ?_⟩
  intro k hk
  have hh := aa_round p θ hp0 (Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hp0))
    (Real.arcsin_le_pi_div_two _) hs k hk
  refine ⟨hh.1, hh.2.1, ?_⟩
  have huu : inner ℂ ψ1 ψ1 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ1]; norm_num
  rw [hall]
  simp only [inner_add_right, inner_smul_right, huu, horth, mul_one, mul_zero, add_zero]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact hh.2.2
