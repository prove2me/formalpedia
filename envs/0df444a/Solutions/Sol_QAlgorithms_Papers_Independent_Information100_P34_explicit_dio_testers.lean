-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P34.explicit_dio_testers
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:07:26.063993+00:00
-- url     : https://prove2.me/submissions/238264e9-f9b4-4c83-b8c5-afbc1393b69a

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

section generic

set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

private lemma x8_ch_zero {M : Superop A B} (h : IsChannel M) : M 0 = 0 := by
  obtain ⟨m, E, hK, hM⟩ := h
  rw [hM, krausApply]; simp

private lemma x8_ch_trace {M : Superop A B} (h : IsChannel M)
    (X : Matrix A A ℂ) : (M X).trace = X.trace := by
  obtain ⟨m, E, hK, hM⟩ := h
  rw [hM, krausApply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) X ((E _)ᴴ)]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

private lemma x8_ch_expand {M : Superop A B} (h : IsChannel M) (X : Matrix A A ℂ) (β γ : B) :
    M X β γ = ∑ i, ∑ j, X i j * choi M (i, β) (j, γ) := by
  obtain ⟨m, E, hK, hM⟩ := h
  simp only [choi, hM, krausApply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply]
  simp [ite_and, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

private lemma x8_choi_trB {M : Superop A B} (h : IsChannel M) (i j : A) :
    ∑ β, choi M (i, β) (j, β) = if i = j then 1 else 0 := by
  have := x8_ch_trace h (Matrix.single i j 1)
  simp only [Matrix.trace, Matrix.diag] at this
  simp only [choi]
  rw [this]
  by_cases hij : i = j
  · subst hij; simp [Matrix.single_apply]
  · simp [Matrix.single_apply, hij, Ne.symm hij]

private lemma x8_deph_single (i j : A) :
    dephasing (Matrix.single i j (1 : ℂ)) = if i = j then Matrix.single i j 1 else 0 := by
  ext k l
  by_cases hij : i = j
  · subst hij; by_cases hkl : k = l
    · subst hkl; simp [dephasing, Matrix.single_apply]
    · simp [dephasing, Matrix.single_apply, hkl]
      intro h1 h2; exact hkl (h1.symm.trans h2)
  · simp only [dephasing, hij, if_false, Matrix.diagonal_apply, Matrix.single_apply]
    by_cases hkl : k = l
    · subst hkl; simp; intro h1 h2; exact hij (h1.trans h2.symm)
    · simp [hkl]

private lemma x8_mio_choi {M : Superop A B} (hO : Free .mio M) (i : A) (β γ : B)
    (hβγ : β ≠ γ) : choi M (i, β) (i, γ) = 0 := by
  have := congrFun (congrFun (hO.2 (Matrix.single i i 1)) β) γ
  rw [x8_deph_single, if_pos rfl] at this
  rw [choi, this]
  simp [dephasing, Matrix.diagonal_apply, hβγ]

private lemma x8_di_choi {M : Superop A B} (hO : Free .di M) (i j : A) (β : B)
    (hij : i ≠ j) : choi M (i, β) (j, β) = 0 := by
  have := congrFun (congrFun (hO.2 (Matrix.single i j 1)) β) β
  rw [x8_deph_single, if_neg hij, x8_ch_zero hO.1] at this
  simpa [dephasing, choi] using this

private lemma x8_dio_choi {M : Superop A B} (hO : Free .dio M) :
    (∀ i β γ, β ≠ γ → choi M (i, β) (i, γ) = 0) ∧
    (∀ i j β, i ≠ j → choi M (i, β) (j, β) = 0) := by
  constructor
  · intro i β γ hβγ
    have := congrFun (congrFun (hO.2 (Matrix.single i i 1)) β) γ
    rw [x8_deph_single, if_pos rfl] at this
    rw [choi, ← this]
    simp [dephasing, Matrix.diagonal_apply, hβγ]
  · intro i j β hij
    have := congrFun (congrFun (hO.2 (Matrix.single i j 1)) β) β
    rw [x8_deph_single, if_neg hij, x8_ch_zero hO.1] at this
    simpa [dephasing, choi] using this

private lemma x8_free_of_choi {M : Superop A B} (h : IsChannel M)
    (O : Theory) (hmio : O ≠ .di → ∀ i β γ, β ≠ γ → choi M (i, β) (i, γ) = 0)
    (hdi : O ≠ .mio → ∀ i j β, i ≠ j → choi M (i, β) (j, β) = 0) : Free O M := by
  have hd : ∀ X : Matrix A A ℂ, ∀ β γ, M (Matrix.diagonal fun i => X i i) β γ = ∑ i, X i i * choi M (i, β) (i, γ) := by
    intro X β γ
    rw [x8_ch_expand h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [dephasing, Matrix.diagonal_apply]
  have hM : O ≠ .mio → ∀ X : Matrix A A ℂ, ∀ β, M X β β = ∑ i, X i i * choi M (i, β) (i, β) := by
    intro hO X β
    rw [x8_ch_expand h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · intro j _ hj; rw [hdi hO i j β (Ne.symm hj), mul_zero]
    · simp
  refine ⟨h, ?_⟩
  cases O with
  | mio =>
    intro X; ext β γ
    by_cases hβγ : β = γ
    · subst hβγ; simp [dephasing]
    · simp only [dephasing, Matrix.diagonal_apply, hβγ, if_false]
      rw [hd]; exact Finset.sum_eq_zero fun i _ => by rw [hmio (by decide) i β γ hβγ, mul_zero]
  | di =>
    intro X; ext β γ
    simp only [dephasing, Matrix.diagonal_apply]
    split_ifs with hβγ
    · subst hβγ; rw [hM (by decide), hd]
    · rfl
  | dio =>
    intro X; ext β γ
    simp only [dephasing, Matrix.diagonal_apply]
    split_ifs with hβγ
    · subst hβγ; rw [hM (by decide), hd]
    · rw [hd]
      exact (Finset.sum_eq_zero fun i _ => by rw [hmio (by decide) i β γ hβγ, mul_zero]).symm

end generic

section choiGen

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma x8_choi_fromChoi (J : Matrix (A × B) (A × B) ℂ) : choi (fromChoi J) = J := by
  ext p q
  simp [choi, fromChoi, Matrix.single_apply, ite_and]

lemma x8_fromChoi_channel (J : Matrix (A × B) (A × B) ℂ) (hJ : J.PosSemidef)
    (htr : ∀ a a', ∑ b, J (a, b) (a', b) = if a = a' then 1 else 0) :
    IsChannel (fromChoi J) := by
  obtain ⟨m, w, hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hJ
  have hJe : ∀ p q, J p q = ∑ k, w k p * star (w k q) := by
    intro p q; rw [hw]; simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  refine ⟨m, fun k => Matrix.of fun β i => w k (i, β), ?_, ?_⟩
  · unfold IsKrausFamily
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    have := htr j i
    simp only [hJe] at this
    rw [Finset.sum_comm]
    convert this using 2 with β
    · exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
  · intro ρ
    ext b b'
    simp only [fromChoi, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply, hJe, Finset.mul_sum, Finset.sum_mul]
    symm
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma x8_freeChoi (J : Matrix (A × B) (A × B) ℂ) (hJ : J.PosSemidef)
    (htr : ∀ a a', ∑ b, J (a, b) (a', b) = if a = a' then 1 else 0) (O : Theory)
    (hmio : O ≠ .di → ∀ i β γ, β ≠ γ → J (i, β) (i, γ) = 0)
    (hdi : O ≠ .mio → ∀ i j β, i ≠ j → J (i, β) (j, β) = 0) : FreeChoi O J := by
  have hc := x8_fromChoi_channel J hJ htr
  refine ⟨x8_free_of_choi hc O ?_ ?_, x8_choi_fromChoi J⟩
  · intro hO; rw [x8_choi_fromChoi]; exact hmio hO
  · intro hO; rw [x8_choi_fromChoi]; exact hdi hO

end choiGen

/-- Kronecker delta as a complex number. -/
def x8δ {α : Type*} [DecidableEq α] (x y : α) : ℂ := if x = y then 1 else 0

@[simp] lemma x8δ_star {α : Type*} [DecidableEq α] (x y : α) : star (x8δ x y) = x8δ x y := by
  unfold x8δ; split_ifs <;> simp

lemma x8δ_comm {α : Type*} [DecidableEq α] (x y : α) : x8δ x y = x8δ y x := by
  unfold x8δ; simp [eq_comm]

lemma x8_single_eq {α : Type*} [DecidableEq α] (i j u v : α) :
    Matrix.single i j (1 : ℂ) u v = x8δ u i * x8δ v j := by
  simp only [Matrix.single_apply, x8δ]
  by_cases h1 : i = u <;> by_cases h2 : j = v <;> simp [h1, h2, eq_comm]

@[simp] lemma x8δ_self {α : Type*} [DecidableEq α] (x : α) : x8δ x x = 1 := by simp [x8δ]

lemma x8δ_ne {α : Type*} [DecidableEq α] {x y : α} (h : x ≠ y) : x8δ x y = 0 := by
  simp [x8δ, h]

lemma x8δ_mul_self {α : Type*} [DecidableEq α] (x y : α) : x8δ x y * x8δ x y = x8δ x y := by
  unfold x8δ; split_ifs <;> simp

lemma x8δ_mul_ne {α : Type*} [DecidableEq α] {x y : α} (z : α) (h : x ≠ y) :
    x8δ x z * x8δ y z = 0 := by
  unfold x8δ; split_ifs with h1 h2 <;> simp_all

lemma x8δ_pair {α β : Type*} [DecidableEq α] [DecidableEq β] (a c : α) (b d : β) :
    x8δ (a, b) (c, d) = x8δ a c * x8δ b d := by
  unfold x8δ; by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2]

lemma x8δ_real {α : Type*} [DecidableEq α] (x y : α) :
    x8δ x y = ((if x = y then 1 else 0 : ℝ) : ℂ) := by
  unfold x8δ; split_ifs <;> simp

lemma x8_nonneg {z : ℂ} (r : ℝ) (hr : 0 ≤ r) (h : z = r) : 0 ≤ z := by
  rw [h]; exact Complex.zero_le_real.mpr hr

section testers

set_option linter.unusedSectionVars false

variable {c : ℕ} {R : Type*} [Fintype R] [DecidableEq R] (hc : 2 ≤ c) (kr lr : R)

def x8e0 : Fin c × R := (⟨0, by omega⟩, kr)
def x8e1 : Fin c × R := (⟨1, by omega⟩, lr)

lemma x8e01 : x8e0 hc kr ≠ x8e1 hc lr := by
  simp [x8e0, x8e1, Prod.ext_iff, Fin.ext_iff]

lemma x8_psi (σ : Bool) (x : Fin c × R) :
    testerPsi hc kr lr σ x = (Real.sqrt 2 : ℂ)⁻¹ *
      (x8δ x (x8e0 hc kr) + (if σ then (-1 : ℂ) else 1) * x8δ x (x8e1 hc lr)) := by
  cases σ <;> simp [testerPsi, ket, x8δ, x8e0, x8e1] <;> split_ifs <;> simp_all

lemma x8_s2 : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma x8_H (x y : Fin c × R) :
    pureDensity (testerPsi hc kr lr false) x y + pureDensity (testerPsi hc kr lr true) x y =
      x8δ x (x8e0 hc kr) * x8δ y (x8e0 hc kr) + x8δ x (x8e1 hc lr) * x8δ y (x8e1 hc lr) := by
  simp only [Matrix.add_apply, pureDensity, Matrix.of_apply, x8_psi, map_mul, map_add,
    Complex.conj_ofReal, map_inv₀, ← Complex.star_def, x8δ_star]
  simp
  linear_combination (2 * (x8δ x (x8e0 hc kr) * x8δ y (x8e0 hc kr) +
    x8δ x (x8e1 hc lr) * x8δ y (x8e1 hc lr))) * x8_s2

lemma x8_Z (x y : Fin c × R) :
    pureDensity (testerPsi hc kr lr false) x y - pureDensity (testerPsi hc kr lr true) x y =
      x8δ x (x8e0 hc kr) * x8δ y (x8e1 hc lr) + x8δ x (x8e1 hc lr) * x8δ y (x8e0 hc kr) := by
  simp only [Matrix.sub_apply, pureDensity, Matrix.of_apply, x8_psi, map_mul, map_add,
    Complex.conj_ofReal, map_inv₀, ← Complex.star_def, x8δ_star]
  simp
  linear_combination (2 * (x8δ x (x8e0 hc kr) * x8δ y (x8e1 hc lr) +
    x8δ x (x8e1 hc lr) * x8δ y (x8e0 hc kr))) * x8_s2

lemma x8_Am (x y : Fin c × R) :
    dyad (testerPsi hc kr lr false) (testerPsi hc kr lr true) x y -
      dyad (testerPsi hc kr lr true) (testerPsi hc kr lr false) x y =
      x8δ x (x8e1 hc lr) * x8δ y (x8e0 hc kr) - x8δ x (x8e0 hc kr) * x8δ y (x8e1 hc lr) := by
  simp only [Matrix.sub_apply, dyad, x8_psi, map_mul, map_add,
    Complex.conj_ofReal, map_inv₀, ← Complex.star_def, x8δ_star]
  simp
  linear_combination (2 * (x8δ x (x8e1 hc lr) * x8δ y (x8e0 hc kr) -
    x8δ x (x8e0 hc kr) * x8δ y (x8e1 hc lr))) * x8_s2

variable {a b : ℕ} (k l : Fin a) (n m : Fin b)

lemma x8_tT (σ : Bool) (p q : (Fin a × Fin b) × (Fin c × R)) :
    testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ p q =
      1 / 2 * ((x8δ p.1 (k, n) * x8δ q.1 (k, n) + x8δ p.1 (l, m) * x8δ q.1 (l, m)) *
        (x8δ p.2 (x8e0 hc kr) * x8δ q.2 (x8e0 hc kr) +
          x8δ p.2 (x8e1 hc lr) * x8δ q.2 (x8e1 hc lr))) +
      1 / 2 * (if σ then
        (x8δ p.1 (k, n) * x8δ q.1 (l, m) - x8δ p.1 (l, m) * x8δ q.1 (k, n)) *
          (x8δ p.2 (x8e1 hc lr) * x8δ q.2 (x8e0 hc kr) -
            x8δ p.2 (x8e0 hc kr) * x8δ q.2 (x8e1 hc lr))
      else
        (x8δ p.1 (k, n) * x8δ q.1 (l, m) + x8δ p.1 (l, m) * x8δ q.1 (k, n)) *
          (x8δ p.2 (x8e0 hc kr) * x8δ q.2 (x8e1 hc lr) +
            x8δ p.2 (x8e1 hc lr) * x8δ q.2 (x8e0 hc kr))) := by
  cases σ
  · simp only [testerTerm, Matrix.add_apply, Matrix.smul_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, x8_single_eq, x8_H, x8_Z, smul_eq_mul, Bool.false_eq_true,
      if_false, Matrix.sub_apply]
  · simp only [testerTerm, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, x8_single_eq, smul_eq_mul, if_true]
    rw [← x8_H, ← x8_Am]

lemma x8_one_eq {α : Type*} [DecidableEq α] (i j : α) : (1 : Matrix α α ℂ) i j = x8δ i j := by
  simp [Matrix.one_apply, x8δ]

lemma x8_tD (p q : (Fin a × Fin b) × (Fin c × R)) :
    testerD (b := b) (B := Fin c × R) k l p q =
      (x8δ p.1.1 q.1.1 - x8δ p.1.1 k * x8δ q.1.1 k - x8δ p.1.1 l * x8δ q.1.1 l) *
        ((b : ℂ)⁻¹ * x8δ p.1.2 q.1.2) * ((Fintype.card (Fin c × R) : ℂ)⁻¹ * x8δ p.2 q.2) := by
  simp only [testerD, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply,
    Matrix.smul_apply, x8_one_eq, x8_single_eq, smul_eq_mul]

lemma x8_tQ (p q : (Fin a × Fin b) × (Fin c × R)) :
    testerQ k l (testerPsi hc kr lr false) (testerPsi hc kr lr true) p q =
      (x8δ (p.1.1, p.2) (q.1.1, q.2) - 1 / 2 * ((x8δ p.1.1 k * x8δ q.1.1 k +
        x8δ p.1.1 l * x8δ q.1.1 l) * (x8δ p.2 (x8e0 hc kr) * x8δ q.2 (x8e0 hc kr) +
          x8δ p.2 (x8e1 hc lr) * x8δ q.2 (x8e1 hc lr)))) * ((b : ℂ)⁻¹ * x8δ p.1.2 q.1.2) := by
  simp only [testerQ, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, x8_one_eq, x8_single_eq, smul_eq_mul, x8_H]

lemma x8_T_psd (σ : Bool) :
    (testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ).PosSemidef := by
  set s : ℂ := if σ then -1 else 1
  set w1 : (Fin a × Fin b) × (Fin c × R) → ℂ := fun p =>
    x8δ p.1 (k, n) * x8δ p.2 (x8e0 hc kr) + s * (x8δ p.1 (l, m) * x8δ p.2 (x8e1 hc lr))
  set w2 : (Fin a × Fin b) × (Fin c × R) → ℂ := fun p =>
    x8δ p.1 (k, n) * x8δ p.2 (x8e1 hc lr) + x8δ p.1 (l, m) * x8δ p.2 (x8e0 hc kr)
  have e : testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ =
      (1 / 2 : ℂ) • (Matrix.vecMulVec w1 (star w1) + Matrix.vecMulVec w2 (star w2)) := by
    ext p q
    rw [x8_tT]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.star_apply, w1, w2,
      star_add, star_mul', x8δ_star, smul_eq_mul]
    cases σ
    · simp only [s, Bool.false_eq_true, if_false, star_one]; ring
    · simp only [s, if_true, star_neg, star_one]; ring
  rw [e]
  refine Matrix.PosSemidef.smul ((Matrix.posSemidef_vecMulVec_self_star _).add
    (Matrix.posSemidef_vecMulVec_self_star _)) ?_
  rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.zero_le_real.mpr (by norm_num)

lemma x8_D_psd (hkl : k ≠ l) : (testerD (b := b) (B := Fin c × R) k l).PosSemidef := by
  set f : (Fin a × Fin b) × (Fin c × R) → ℂ := fun p =>
    (1 - x8δ p.1.1 k - x8δ p.1.1 l) * ((b : ℂ)⁻¹ * ((Fintype.card (Fin c × R) : ℂ)⁻¹))
  have e : testerD (b := b) (B := Fin c × R) k l = Matrix.diagonal f := by
    ext ⟨⟨i, n'⟩, x⟩ ⟨⟨j, n''⟩, y⟩
    rw [x8_tD, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      by_cases hn : n' = n''
      · subst hn
        by_cases hx : x = y
        · subst hx; simp only [x8δ_self, x8δ_mul_self, if_true, f]; ring
        · rw [x8δ_ne hx, if_neg (by simp [hx])]; ring
      · rw [x8δ_ne hn, if_neg (by simp [hn])]; ring
    · rw [if_neg (by simp [hij]), x8δ_ne hij, x8δ_mul_ne _ hij, x8δ_mul_ne _ hij]; ring
  rw [e]
  refine Matrix.PosSemidef.diagonal fun p => ?_
  simp only [Pi.zero_apply, f]
  refine x8_nonneg ((1 - (if p.1.1 = k then 1 else 0) - (if p.1.1 = l then 1 else 0)) *
    ((b : ℝ)⁻¹ * (Fintype.card (Fin c × R) : ℝ)⁻¹)) ?_ (by simp only [x8δ_real]; push_cast; ring)
  apply mul_nonneg _ (by positivity)
  by_cases h1 : p.1.1 = k
  · rw [if_pos h1, if_neg (fun h2 => hkl (h1.symm.trans h2))]; norm_num
  · rw [if_neg h1]; split_ifs <;> norm_num

lemma x8_Q_psd :
    (testerQ (b := b) k l (testerPsi hc kr lr false) (testerPsi hc kr lr true)).PosSemidef := by
  set f : (Fin a × Fin b) × (Fin c × R) → ℂ := fun p =>
    (1 - 1 / 2 * ((x8δ p.1.1 k + x8δ p.1.1 l) *
      (x8δ p.2 (x8e0 hc kr) + x8δ p.2 (x8e1 hc lr)))) * (b : ℂ)⁻¹
  have e : testerQ (b := b) k l (testerPsi hc kr lr false) (testerPsi hc kr lr true) =
      Matrix.diagonal f := by
    ext ⟨⟨i, n'⟩, x⟩ ⟨⟨j, n''⟩, y⟩
    rw [x8_tQ, Matrix.diagonal_apply]
    by_cases hn : n' = n''
    · subst hn
      by_cases hij : i = j
      · subst hij
        by_cases hx : x = y
        · subst hx; simp only [x8δ_self, x8δ_mul_self, if_true, f]; ring
        · rw [if_neg (by simp [hx]), x8δ_ne (by simp [hx]), x8δ_mul_ne _ hx, x8δ_mul_ne _ hx]; ring
      · rw [if_neg (by simp [hij]), x8δ_ne (by simp [hij]), x8δ_mul_ne _ hij, x8δ_mul_ne _ hij]; ring
    · rw [x8δ_ne hn, if_neg (by simp [hn])]; ring
  rw [e]
  refine Matrix.PosSemidef.diagonal fun p => ?_
  simp only [Pi.zero_apply, f]
  refine x8_nonneg ((1 - 1 / 2 * (((if p.1.1 = k then 1 else 0) + (if p.1.1 = l then 1 else 0)) *
    ((if p.2 = x8e0 hc kr then 1 else 0) + (if p.2 = x8e1 hc lr then 1 else 0)))) * (b : ℝ)⁻¹) ?_
    (by simp only [x8δ_real]; push_cast; ring)
  apply mul_nonneg _ (by positivity)
  have h01 := x8e01 hc kr lr
  by_cases h0 : p.2 = x8e0 hc kr
  · rw [if_pos h0, if_neg (fun h1 => h01 (h0.symm.trans h1))]
    split_ifs <;> norm_num
  · rw [if_neg h0]; split_ifs <;> norm_num

lemma x8_C_entry (σ : Bool) (i j : Fin a) (n' n'' : Fin b) (x y : Fin c × R) :
    testerAsCreation (testerD (b := b) (B := Fin c × R) k l +
      testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ)
      (i, (n', x)) (j, (n'', y)) =
    (x8δ i j - x8δ i k * x8δ j k - x8δ i l * x8δ j l) *
        ((b : ℂ)⁻¹ * x8δ n' n'') * ((Fintype.card (Fin c × R) : ℂ)⁻¹ * x8δ x y) +
      (1 / 2 * ((x8δ i k * x8δ n' n * (x8δ j k * x8δ n'' n) +
          x8δ i l * x8δ n' m * (x8δ j l * x8δ n'' m)) *
        (x8δ x (x8e0 hc kr) * x8δ y (x8e0 hc kr) + x8δ x (x8e1 hc lr) * x8δ y (x8e1 hc lr))) +
      1 / 2 * (if σ then
        (x8δ i k * x8δ n' n * (x8δ j l * x8δ n'' m) - x8δ i l * x8δ n' m * (x8δ j k * x8δ n'' n)) *
          (x8δ x (x8e1 hc lr) * x8δ y (x8e0 hc kr) - x8δ x (x8e0 hc kr) * x8δ y (x8e1 hc lr))
      else
        (x8δ i k * x8δ n' n * (x8δ j l * x8δ n'' m) + x8δ i l * x8δ n' m * (x8δ j k * x8δ n'' n)) *
          (x8δ x (x8e0 hc kr) * x8δ y (x8e1 hc lr) + x8δ x (x8e1 hc lr) * x8δ y (x8e0 hc kr)))) := by
  simp only [testerAsCreation, Matrix.submatrix_apply, Matrix.add_apply, x8_tD, x8_tT, x8δ_pair]

lemma x8_sum_δ {α : Type*} [Fintype α] [DecidableEq α] (y : α) (f : α → ℂ) :
    ∑ x, x8δ x y * f x = f y := by
  simp [x8δ]

lemma x8δ_sum1 {α : Type*} [Fintype α] [DecidableEq α] (y : α) : ∑ x, x8δ x y = 1 := by
  simp [x8δ]

lemma x8_C_tr (hb : 0 < b) (σ : Bool) (i j : Fin a) :
    ∑ β : Fin b × (Fin c × R), testerAsCreation (testerD (b := b) (B := Fin c × R) k l +
      testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ)
      (i, β) (j, β) = if i = j then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [x8_C_entry, x8δ_self, mul_one]
  have h01 := x8e01 hc kr lr
  have h0 : ∀ x : Fin c × R, x8δ x (x8e0 hc kr) * x8δ x (x8e1 hc lr) = 0 := by
    intro x; unfold x8δ; split_ifs with h1 h2 <;> simp_all
  have h1 : ∀ x : Fin c × R, x8δ x (x8e1 hc lr) * x8δ x (x8e0 hc kr) = 0 := by
    intro x; rw [mul_comm]; exact h0 x
  simp only [x8δ_mul_self, h0, h1, sub_zero, mul_zero, add_zero, ite_self]
  have hs : ∀ n' : Fin b, ∑ x : Fin c × R,
      ((x8δ i j - x8δ i k * x8δ j k - x8δ i l * x8δ j l) * (b : ℂ)⁻¹ *
        (Fintype.card (Fin c × R) : ℂ)⁻¹ +
      1 / 2 * ((x8δ i k * x8δ n' n * (x8δ j k * x8δ n' n) +
          x8δ i l * x8δ n' m * (x8δ j l * x8δ n' m)) *
        (x8δ x (x8e0 hc kr) + x8δ x (x8e1 hc lr)))) =
      (x8δ i j - x8δ i k * x8δ j k - x8δ i l * x8δ j l) * (b : ℂ)⁻¹ +
      (x8δ i k * x8δ j k * x8δ n' n + x8δ i l * x8δ j l * x8δ n' m) := by
    intro n'
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [x8δ_sum1]
    have hC : (Fintype.card (Fin c × R) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Fintype.card_pos_iff.mpr ⟨x8e0 hc kr⟩).ne'
    have hCC := mul_inv_cancel₀ hC
    rw [nsmul_eq_mul]
    linear_combination ((x8δ i j - x8δ i k * x8δ j k - x8δ i l * x8δ j l) * (b : ℂ)⁻¹) * hCC +
      (x8δ i k * x8δ j k) * x8δ_mul_self n' n + (x8δ i l * x8δ j l) * x8δ_mul_self n' m
  simp only [hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, x8δ_sum1]
  have hbb := mul_inv_cancel₀ (Nat.cast_ne_zero.2 hb.ne' : (b : ℂ) ≠ 0)
  rw [show (if i = j then (1 : ℂ) else 0) = x8δ i j from rfl]
  linear_combination (x8δ i j - x8δ i k * x8δ j k - x8δ i l * x8δ j l) * hbb

lemma x8_z1 {p q : ℂ} (h : p * q = 0) (A B : ℂ) : p * A * (q * B) = 0 := by
  rw [show p * A * (q * B) = (p * q) * (A * B) by ring, h, zero_mul]

lemma x8_z2 {p q : ℂ} (h : p * q = 0) (A B : ℂ) : q * A * (p * B) = 0 := by
  rw [show q * A * (p * B) = (p * q) * (A * B) by ring, h, zero_mul]

lemma x8_z3 {p q : ℂ} (h : p * q = 0) (A B : ℂ) : A * p * (B * q) = 0 := by
  rw [show A * p * (B * q) = (p * q) * (A * B) by ring, h, zero_mul]

lemma x8_C_mio (hkl : k ≠ l) (σ : Bool) (i : Fin a) (β γ : Fin b × (Fin c × R)) (h : β ≠ γ) :
    testerAsCreation (testerD (b := b) (B := Fin c × R) k l +
      testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ)
      (i, β) (i, γ) = 0 := by
  obtain ⟨n', x⟩ := β
  obtain ⟨n'', y⟩ := γ
  have h01 := x8e01 hc kr lr
  rw [x8_C_entry]
  have hz : x8δ i k * x8δ i l = 0 := by
    by_cases hik : i = k
    · subst hik; rw [x8δ_ne hkl, mul_zero]
    · rw [x8δ_ne hik, zero_mul]
  by_cases hn : n' = n''
  · subst hn
    have hxy : x ≠ y := fun h' => h (by rw [h'])
    rw [x8δ_ne hxy, x8δ_mul_ne _ hxy, x8δ_mul_ne _ hxy]
    simp only [x8_z1 hz, x8_z2 hz, mul_zero, zero_mul, add_zero, sub_zero, sub_self, ite_self]
  · rw [x8δ_ne hn]
    have hn1 : x8δ n' n * x8δ n'' n = 0 := x8δ_mul_ne _ hn
    have hn2 : x8δ n' m * x8δ n'' m = 0 := x8δ_mul_ne _ hn
    simp only [x8_z1 hz, x8_z2 hz, x8_z3 hn1, x8_z3 hn2, mul_zero, zero_mul, add_zero, sub_zero,
      sub_self, ite_self]

lemma x8_h0 (x : Fin c × R) : x8δ x (x8e0 hc kr) * x8δ x (x8e1 hc lr) = 0 := by
  have h01 := x8e01 hc kr lr
  unfold x8δ; split_ifs with h1 h2 <;> simp_all

lemma x8_h1 (x : Fin c × R) : x8δ x (x8e1 hc lr) * x8δ x (x8e0 hc kr) = 0 := by
  rw [mul_comm]; exact x8_h0 hc kr lr x

lemma x8δ_mul_ne' {α : Type*} [DecidableEq α] (x : α) {z w : α} (h : z ≠ w) :
    x8δ x z * x8δ x w = 0 := by
  unfold x8δ; split_ifs with h1 h2 <;> simp_all

lemma x8_C_di (σ : Bool) (i j : Fin a) (β : Fin b × (Fin c × R)) (hij : i ≠ j) :
    testerAsCreation (testerD (b := b) (B := Fin c × R) k l +
      testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ)
      (i, β) (j, β) = 0 := by
  obtain ⟨n', x⟩ := β
  rw [x8_C_entry]
  simp only [x8δ_ne hij, x8δ_mul_ne _ hij, x8_z1 (x8δ_mul_ne k hij), x8_z1 (x8δ_mul_ne l hij),
    x8_h0 hc kr lr x, x8_h1 hc kr lr x, mul_zero, zero_mul, add_zero, sub_zero, sub_self,
    ite_self]

lemma x8_D_entry (σ : Bool) (i j : Fin a) (n' n'' : Fin b) (x y : Fin c × R) :
    testerAsDetection (testerQ (b := b) k l (testerPsi hc kr lr false) (testerPsi hc kr lr true) +
      testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ)
      ((i, x), n') ((j, y), n'') =
    (x8δ i j * x8δ x y - 1 / 2 * ((x8δ i k * x8δ j k + x8δ i l * x8δ j l) *
        (x8δ x (x8e0 hc kr) * x8δ y (x8e0 hc kr) + x8δ x (x8e1 hc lr) * x8δ y (x8e1 hc lr)))) *
        ((b : ℂ)⁻¹ * x8δ n' n'') +
      (1 / 2 * ((x8δ i k * x8δ n' n * (x8δ j k * x8δ n'' n) +
          x8δ i l * x8δ n' m * (x8δ j l * x8δ n'' m)) *
        (x8δ x (x8e0 hc kr) * x8δ y (x8e0 hc kr) + x8δ x (x8e1 hc lr) * x8δ y (x8e1 hc lr))) +
      1 / 2 * (if σ then
        (x8δ i k * x8δ n' n * (x8δ j l * x8δ n'' m) - x8δ i l * x8δ n' m * (x8δ j k * x8δ n'' n)) *
          (x8δ x (x8e1 hc lr) * x8δ y (x8e0 hc kr) - x8δ x (x8e0 hc kr) * x8δ y (x8e1 hc lr))
      else
        (x8δ i k * x8δ n' n * (x8δ j l * x8δ n'' m) + x8δ i l * x8δ n' m * (x8δ j k * x8δ n'' n)) *
          (x8δ x (x8e0 hc kr) * x8δ y (x8e1 hc lr) + x8δ x (x8e1 hc lr) * x8δ y (x8e0 hc kr)))) := by
  simp only [testerAsDetection, Matrix.submatrix_apply, Matrix.add_apply, x8_tQ, x8_tT, x8δ_pair]

lemma x8_D_mio (σ : Bool) (p : Fin a × (Fin c × R)) (n' n'' : Fin b) (hn : n' ≠ n'') :
    testerAsDetection (testerQ (b := b) k l (testerPsi hc kr lr false) (testerPsi hc kr lr true) +
      testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ)
      (p, n') (p, n'') = 0 := by
  obtain ⟨i, x⟩ := p
  rw [x8_D_entry]
  simp only [x8δ_ne hn, x8_z3 (x8δ_mul_ne n hn), x8_z3 (x8δ_mul_ne m hn),
    x8_h0 hc kr lr x, x8_h1 hc kr lr x, mul_zero, zero_mul, add_zero, sub_zero, sub_self,
    ite_self]

lemma x8_D_di (hnm : n ≠ m) (σ : Bool) (p q : Fin a × (Fin c × R)) (n' : Fin b) (hpq : p ≠ q) :
    testerAsDetection (testerQ (b := b) k l (testerPsi hc kr lr false) (testerPsi hc kr lr true) +
      testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ)
      (p, n') (q, n') = 0 := by
  obtain ⟨i, x⟩ := p
  obtain ⟨j, y⟩ := q
  rw [x8_D_entry]
  have e1 := x8δ_mul_ne' n' hnm
  have e2 := x8δ_mul_ne' n' (Ne.symm hnm)
  simp only [x8_z3 e1, x8_z3 e2, mul_zero, zero_mul, add_zero, sub_zero, sub_self, ite_self]
  by_cases hij : i = j
  · subst hij
    have hxy : x ≠ y := fun h' => hpq (by rw [h'])
    rw [x8δ_ne hxy, x8δ_mul_ne _ hxy, x8δ_mul_ne _ hxy]
    simp
  · simp only [x8δ_ne hij, x8δ_mul_ne _ hij, x8_z1 (x8δ_mul_ne k hij), x8_z1 (x8δ_mul_ne l hij)]
    simp

lemma x8_D_tr (hb : 0 < b) (hnm : n ≠ m) (σ : Bool) (p q : Fin a × (Fin c × R)) :
    ∑ n' : Fin b, testerAsDetection (testerQ (b := b) k l (testerPsi hc kr lr false)
      (testerPsi hc kr lr true) +
      testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ)
      (p, n') (q, n') = if p = q then 1 else 0 := by
  obtain ⟨i, x⟩ := p
  obtain ⟨j, y⟩ := q
  simp only [x8_D_entry, x8δ_self, mul_one]
  have e1 : ∀ (n' : Fin b) (A B : ℂ), A * x8δ n' n * (B * x8δ n' m) = 0 :=
    fun n' => x8_z3 (x8δ_mul_ne' n' hnm)
  have e2 : ∀ (n' : Fin b) (A B : ℂ), A * x8δ n' m * (B * x8δ n' n) = 0 :=
    fun n' => x8_z3 (x8δ_mul_ne' n' (Ne.symm hnm))
  simp only [e1, e2, mul_zero, zero_mul, add_zero, sub_zero, sub_self, ite_self]
  set H := x8δ x (x8e0 hc kr) * x8δ y (x8e0 hc kr) + x8δ x (x8e1 hc lr) * x8δ y (x8e1 hc lr)
  set K := x8δ i j * x8δ x y - 1 / 2 * ((x8δ i k * x8δ j k + x8δ i l * x8δ j l) * H)
  have hs : ∀ n' : Fin b, K * (b : ℂ)⁻¹ + 1 / 2 * ((x8δ i k * x8δ n' n * (x8δ j k * x8δ n' n) +
      x8δ i l * x8δ n' m * (x8δ j l * x8δ n' m)) * H) =
      K * (b : ℂ)⁻¹ + 1 / 2 * (x8δ i k * x8δ j k * H) * x8δ n' n +
        1 / 2 * (x8δ i l * x8δ j l * H) * x8δ n' m := by
    intro n'
    linear_combination (1 / 2 * x8δ i k * x8δ j k * H) * x8δ_mul_self n' n +
      (1 / 2 * x8δ i l * x8δ j l * H) * x8δ_mul_self n' m
  simp only [hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, x8δ_sum1]
  have hbb := mul_inv_cancel₀ (Nat.cast_ne_zero.2 hb.ne' : (b : ℂ) ≠ 0)
  rw [show (if (i, x) = (j, y) then (1 : ℂ) else 0) = x8δ i j * x8δ x y from (x8δ_pair i j x y)]
  linear_combination K * hbb

lemma x8_creation_free (hb : 0 < b) (hkl : k ≠ l) (σ : Bool) (O : Theory) :
    FreeChoi O (testerAsCreation (testerD (b := b) (B := Fin c × R) k l +
      testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ)) :=
  x8_freeChoi _ (((x8_D_psd (c := c) (R := R) k l hkl).add (x8_T_psd hc kr lr k l n m σ)).submatrix _)
    (x8_C_tr hc kr lr k l n m hb σ) O
    (fun _ i β γ h => x8_C_mio hc kr lr k l n m hkl σ i β γ h)
    (fun _ i j β h => x8_C_di hc kr lr k l n m σ i j β h)

lemma x8_detection_free (hb : 0 < b) (hnm : n ≠ m) (σ : Bool) (O : Theory) :
    FreeChoi O (testerAsDetection (testerQ (b := b) k l (testerPsi hc kr lr false)
      (testerPsi hc kr lr true) +
      testerTerm k l n m (testerPsi hc kr lr false) (testerPsi hc kr lr true) σ)) :=
  x8_freeChoi _ (((x8_Q_psd hc kr lr k l).add (x8_T_psd hc kr lr k l n m σ)).submatrix _)
    (x8_D_tr hc kr lr k l n m hb hnm σ) O
    (fun _ p n' n'' h => x8_D_mio hc kr lr k l n m σ p n' n'' h)
    (fun _ p q n' h => x8_D_di hc kr lr k l n m hnm σ p q n' h)

end testers

theorem x8_main {a b c : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] [Nonempty R]
    (ha : 0 < a) (hb : 0 < b) (hc : 2 ≤ c)
    (k l : Fin a) (n m : Fin b) (kr lr : R) :
    let plus := testerPsi hc kr lr false
    let minus := testerPsi hc kr lr true
    let JN := testerAsCreation (testerD k l + testerTerm k l n m plus minus false)
    let JM := testerAsCreation (testerD k l + testerTerm k l n m plus minus true)
    let JK := testerAsDetection (testerQ k l plus minus + testerTerm k l n m plus minus false)
    let JL := testerAsDetection (testerQ k l plus minus + testerTerm k l n m plus minus true)
    (k ≠ l → FreeChoi .dio JN ∧ FreeChoi .mio JN ∧
      FreeChoi .dio JM ∧ FreeChoi .mio JM) ∧
    (n ≠ m → FreeChoi .dio JK ∧ FreeChoi .di JK ∧
      FreeChoi .dio JL ∧ FreeChoi .di JL) := by
  intro plus minus JN JM JK JL
  refine ⟨fun hkl => ⟨?_, ?_, ?_, ?_⟩, fun hnm => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact x8_creation_free hc kr lr k l n m hb hkl false .dio
  · exact x8_creation_free hc kr lr k l n m hb hkl false .mio
  · exact x8_creation_free hc kr lr k l n m hb hkl true .dio
  · exact x8_creation_free hc kr lr k l n m hb hkl true .mio
  · exact x8_detection_free hc kr lr k l n m hb hnm false .dio
  · exact x8_detection_free hc kr lr k l n m hb hnm false .di
  · exact x8_detection_free hc kr lr k l n m hb hnm true .dio
  · exact x8_detection_free hc kr lr k l n m hb hnm true .di

end QAlgorithms.Papers.Independent.Information100.P34

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P34 in
theorem solution {a b c : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] [Nonempty R]
    (ha : 0 < a) (hb : 0 < b) (hc : 2 ≤ c)
    (k l : Fin a) (n m : Fin b) (kr lr : R) :
    let plus := testerPsi hc kr lr false
    let minus := testerPsi hc kr lr true
    let JN := testerAsCreation (testerD k l + testerTerm k l n m plus minus false)
    let JM := testerAsCreation (testerD k l + testerTerm k l n m plus minus true)
    let JK := testerAsDetection (testerQ k l plus minus + testerTerm k l n m plus minus false)
    let JL := testerAsDetection (testerQ k l plus minus + testerTerm k l n m plus minus true)
    (k ≠ l → FreeChoi .dio JN ∧ FreeChoi .mio JN ∧
      FreeChoi .dio JM ∧ FreeChoi .mio JM) ∧
    (n ≠ m → FreeChoi .dio JK ∧ FreeChoi .di JK ∧
      FreeChoi .dio JL ∧ FreeChoi .di JL) :=
  x8_main ha hb hc k l n m kr lr
