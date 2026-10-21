-- Prove2me | solution 1 for SystemicHoldings.FEfficient.remark_EC_1_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T17:33:12.008729+00:00
-- url     : https://prove2.me/submissions/bbc1ecaf-2642-4a0d-9069-41c9dcfa9b08

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model

namespace SystemicHoldings.FEfficient
open Matrix

section core

variable {K N : ℕ}

lemma vmv_mulVec {m n : ℕ} (w : Fin m → ℝ) (v u : Fin n → ℝ) :
    vecMulVec w v *ᵥ u = (v ⬝ᵥ u) • w := by
  rw [vecMulVec_mulVec]; ext; simp [mul_comm]

lemma shM_mulVec (μ σ : Fin K → ℝ) (x : Fin K → ℝ) :
    shockMoment μ σ *ᵥ x = fun k => μ k * (μ ⬝ᵥ x) + σ k ^ 2 * x k := by
  ext k
  simp [shockMoment, add_mulVec, vmv_mulVec, mulVec_diagonal, mul_comm]

lemma shM_bil (μ σ : Fin K → ℝ) (x y : Fin K → ℝ) :
    x ⬝ᵥ (shockMoment μ σ *ᵥ y) = (μ ⬝ᵥ x) * (μ ⬝ᵥ y) + ∑ k, σ k ^ 2 * x k * y k := by
  rw [shM_mulVec]
  simp only [dotProduct]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma shM_symm (μ σ : Fin K → ℝ) (x y : Fin K → ℝ) :
    x ⬝ᵥ (shockMoment μ σ *ᵥ y) = y ⬝ᵥ (shockMoment μ σ *ᵥ x) := by
  rw [shM_bil, shM_bil, mul_comm (μ ⬝ᵥ x)]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma shM_pos (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) (x : Fin K → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (shockMoment μ σ *ᵥ x) := by
  rw [shM_bil]
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra h; push Not at h; exact hx (funext h)
  have h1 : 0 < σ k ^ 2 * x k * x k := by
    rw [mul_assoc]; exact mul_pos (pow_pos (hσ k) 2) (mul_self_pos.mpr hk)
  have h2 : σ k ^ 2 * x k * x k ≤ ∑ j, σ j ^ 2 * x j * x j :=
    Finset.single_le_sum (f := fun j => σ j ^ 2 * x j * x j)
      (fun j _ => by rw [mul_assoc]; exact mul_nonneg (sq_nonneg _) (mul_self_nonneg _)) (Finset.mem_univ k)
  nlinarith [mul_self_nonneg (μ ⬝ᵥ x)]

lemma shM_transpose (μ σ : Fin K → ℝ) : (shockMoment μ σ)ᵀ = shockMoment μ σ := by
  ext i j
  simp only [shockMoment, transpose_apply, Matrix.add_apply, vecMulVec_apply, diagonal_apply]
  by_cases h : i = j
  · subst h; ring
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

lemma shM_posDef (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) : (shockMoment μ σ).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · unfold IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact shM_transpose μ σ
  · intro x hx
    simpa using shM_pos μ σ hσ x hx

lemma shM_det (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) : IsUnit (shockMoment μ σ).det :=
  (isUnit_iff_isUnit_det _).mp (shM_posDef μ σ hσ).isUnit

lemma shM_zVec (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) :
    shockMoment μ σ *ᵥ zVec μ σ = fun _ => (1 : ℝ) := by
  unfold zVec
  rw [mulVec_mulVec, mul_nonsing_inv _ (shM_det μ σ hσ), one_mulVec]

lemma one_dot_zVec_eq (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) :
    (fun _ => (1 : ℝ)) ⬝ᵥ zVec μ σ = zVec μ σ ⬝ᵥ (shockMoment μ σ *ᵥ zVec μ σ) := by
  rw [shM_zVec μ σ hσ, dotProduct_comm]

lemma one_dot_zVec_pos (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) :
    0 < (fun _ => (1 : ℝ)) ⬝ᵥ zVec μ σ := by
  rw [one_dot_zVec_eq μ σ hσ]
  apply shM_pos μ σ hσ
  intro hz
  have h := shM_zVec μ σ hσ
  rw [hz, mulVec_zero] at h
  have := congrFun h ⟨0, hK⟩
  simp at this

lemma shM_yStar (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) (b v : Fin N → ℝ) :
    shockMoment μ σ *ᵥ yStar μ σ b v =
      ((b ⬝ᵥ v) / ((fun _ => (1 : ℝ)) ⬝ᵥ zVec μ σ)) • (fun _ => (1 : ℝ)) := by
  unfold yStar
  rw [mulVec_smul, shM_zVec μ σ hσ]

lemma one_dot_yStar (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) (b v : Fin N → ℝ) :
    (fun _ => (1 : ℝ)) ⬝ᵥ yStar μ σ b v = b ⬝ᵥ v := by
  unfold yStar
  rw [dotProduct_smul, smul_eq_mul]
  have := one_dot_zVec_pos hK μ σ hσ
  field_simp

lemma yStar_quad (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) (b v : Fin N → ℝ) :
    yStar μ σ b v ⬝ᵥ (shockMoment μ σ *ᵥ yStar μ σ b v) =
      (b ⬝ᵥ v) ^ 2 / ((fun _ => (1 : ℝ)) ⬝ᵥ zVec μ σ) := by
  rw [shM_yStar μ σ hσ, dotProduct_smul, smul_eq_mul, dotProduct_comm (yStar μ σ b v),
    one_dot_yStar hK μ σ hσ]
  ring

/-- Key decomposition: for `y` with `1ᵀy = bᵀv`, `yᵀGy = y*ᵀGy* + dᵀGd`, `d = y - y*`. -/
lemma quad_decomp (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) (b v : Fin N → ℝ)
    (y : Fin K → ℝ) (hy : (fun _ => (1 : ℝ)) ⬝ᵥ y = b ⬝ᵥ v) :
    y ⬝ᵥ (shockMoment μ σ *ᵥ y) =
      yStar μ σ b v ⬝ᵥ (shockMoment μ σ *ᵥ yStar μ σ b v) +
        (y - yStar μ σ b v) ⬝ᵥ (shockMoment μ σ *ᵥ (y - yStar μ σ b v)) := by
  set ys := yStar μ σ b v
  set G := shockMoment μ σ
  have hd : (y - ys) ⬝ᵥ (G *ᵥ ys) = 0 := by
    rw [shM_yStar μ σ hσ, dotProduct_smul, smul_eq_mul, dotProduct_comm (y - ys), dotProduct_sub,
      hy, one_dot_yStar hK μ σ hσ, sub_self, mul_zero]
  have hd' : ys ⬝ᵥ (G *ᵥ (y - ys)) = 0 := by rw [shM_symm]; exact hd
  have hy' : y = ys + (y - ys) := by abel
  conv_lhs => rw [hy']
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hd, hd']
  ring

lemma solvesAggregate_yStar (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (b v : Fin N → ℝ) : SolvesAggregate μ σ b v (yStar μ σ b v) := by
  refine ⟨one_dot_yStar hK μ σ hσ b v, fun y' hy' => ?_⟩
  rw [quad_decomp hK μ σ hσ b v y' hy']
  by_cases h : y' - yStar μ σ b v = 0
  · rw [h, mulVec_zero, dotProduct_zero, add_zero]
  · have := shM_pos μ σ hσ _ h; linarith

lemma eq_yStar_of_le (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (b v : Fin N → ℝ) (y : Fin K → ℝ) (hy : (fun _ => (1 : ℝ)) ⬝ᵥ y = b ⬝ᵥ v)
    (hle : y ⬝ᵥ (shockMoment μ σ *ᵥ y) ≤
      yStar μ σ b v ⬝ᵥ (shockMoment μ σ *ᵥ yStar μ σ b v)) : y = yStar μ σ b v := by
  rw [quad_decomp hK μ σ hσ b v y hy] at hle
  by_contra h
  have := shM_pos μ σ hσ _ (sub_ne_zero.mpr h)
  linarith

lemma solvesAggregate_unique (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (b v : Fin N → ℝ) (y : Fin K → ℝ) (hy : SolvesAggregate μ σ b v y) :
    y = yStar μ σ b v :=
  eq_yStar_of_le hK μ σ hσ b v y hy.1 (hy.2 _ (one_dot_yStar hK μ σ hσ b v))

lemma feasible_agg {q : Fin K → ℝ} {b : Fin N → ℝ} (v : Fin N → ℝ)
    {Q : Matrix (Fin K) (Fin N) ℝ} (hQ : Q ∈ feasible q b) :
    (fun _ => (1 : ℝ)) ⬝ᵥ (Q *ᵥ v) = b ⬝ᵥ v := by
  rw [dotProduct_mulVec, hQ.2]

/-- A feasible `Q` with `Qv = y*` is f-efficient. -/
lemma isFEfficient_of_eq (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ) (Q : Matrix (Fin K) (Fin N) ℝ)
    (hQ : Q ∈ feasible q b) (hQv : Q *ᵥ v = yStar μ σ b v) : IsFEfficient μ σ q b v Q := by
  refine ⟨hQ, fun Q' hQ' => ?_⟩
  unfold msd
  rw [hQv]
  exact (solvesAggregate_yStar hK μ σ hσ b v).2 _ (feasible_agg v hQ')

/-- Construction of a feasible `Q` with prescribed `Qv = y`, whenever `1ᵀy = bᵀv`. -/
lemma exists_feasible_mulVec (hK : 1 ≤ K) (q : Fin K → ℝ) (b v : Fin N → ℝ)
    (hT : ∑ k, q k = ∑ i, b i) (hv : ∃ i j, v i ≠ v j) (y : Fin K → ℝ)
    (hy : (fun _ => (1 : ℝ)) ⬝ᵥ y = b ⬝ᵥ v) :
    ∃ Q ∈ feasible q b, Q *ᵥ v = y := by
  obtain ⟨i0, j0, hij⟩ := hv
  set e0 : Fin K → ℝ := Pi.single ⟨0, hK⟩ 1
  set f0 : Fin N → ℝ := Pi.single i0 1
  set one : Fin N → ℝ := fun _ => 1
  set oneK : Fin K → ℝ := fun _ => 1
  set T : ℝ := ∑ i, b i
  set Q0 : Matrix (Fin K) (Fin N) ℝ := vecMulVec q f0 + vecMulVec e0 (b - T • f0)
  set r : Fin K → ℝ := y - Q0 *ᵥ v
  set w : Fin N → ℝ := (1 / (v i0 - v j0)) • (Pi.single i0 1 - Pi.single j0 1)
  have hsub : v i0 - v j0 ≠ 0 := sub_ne_zero.mpr hij
  have hf0one : f0 ⬝ᵥ one = 1 := by simp [f0, one]
  have hbone : b ⬝ᵥ one = T := by simp [one, T, dotProduct]
  have hoq : oneK ⬝ᵥ q = T := by simp [oneK, T, dotProduct, hT]
  have hoe : oneK ⬝ᵥ e0 = 1 := by simp [oneK, e0]
  have hwone : w ⬝ᵥ one = 0 := by
    simp [w, one, sub_dotProduct, smul_dotProduct]
  have hwv : w ⬝ᵥ v = 1 := by
    simp only [w, smul_dotProduct, sub_dotProduct, single_one_dotProduct, smul_eq_mul]
    field_simp
  have hor : oneK ⬝ᵥ r = 0 := by
    simp only [r, dotProduct_sub, oneK, hy, Q0]
    rw [dotProduct_mulVec, vecMul_add, vecMul_vecMulVec, vecMul_vecMulVec, add_dotProduct,
      smul_dotProduct, smul_dotProduct]
    change b ⬝ᵥ v - ((oneK ⬝ᵥ q) • (f0 ⬝ᵥ v) + (oneK ⬝ᵥ e0) • ((b - T • f0) ⬝ᵥ v)) = 0
    rw [hoq, hoe]
    simp [sub_dotProduct, smul_dotProduct]
  refine ⟨Q0 + vecMulVec r w, ⟨?_, ?_⟩, ?_⟩
  · change (Q0 + vecMulVec r w) *ᵥ one = q
    rw [add_mulVec, vmv_mulVec, hwone, zero_smul, add_zero]
    simp only [Q0, add_mulVec, vmv_mulVec, sub_dotProduct, smul_dotProduct, hf0one, hbone]
    simp
  · change oneK ᵥ* (Q0 + vecMulVec r w) = b
    rw [vecMul_add, vecMul_vecMulVec, hor, zero_smul, add_zero]
    simp only [Q0, vecMul_add, vecMul_vecMulVec, hoq, hoe]
    simp
  · rw [add_mulVec, vmv_mulVec, hwv, one_smul]
    simp [r]




lemma eff_mulVec (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ) (hT : ∑ k, q k = ∑ i, b i) (hv : ∃ i j, v i ≠ v j)
    (Q : Matrix (Fin K) (Fin N) ℝ) (hQ : IsFEfficient μ σ q b v Q) :
    Q *ᵥ v = yStar μ σ b v := by
  obtain ⟨Qs, hQs, hQsv⟩ :=
    exists_feasible_mulVec hK q b v hT hv _ (one_dot_yStar hK μ σ hσ b v)
  have hle := hQ.2 Qs hQs
  unfold msd at hle
  rw [hQsv] at hle
  exact eq_yStar_of_le hK μ σ hσ b v _ (feasible_agg v hQ.1) hle

lemma exists_w (hN : 3 ≤ N) (v : Fin N → ℝ) :
    ∃ w : Fin N → ℝ, w ≠ 0 ∧ w ⬝ᵥ (fun _ => (1 : ℝ)) = 0 ∧ w ⬝ᵥ v = 0 := by
  set A : Matrix (Fin 2) (Fin N) ℝ := Matrix.of ![fun _ => (1 : ℝ), v]
  have hlt : Module.finrank ℝ (Fin 2 → ℝ) < Module.finrank ℝ (Fin N → ℝ) := by
    simp; omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := A.mulVecLin) hlt
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hker
  rw [LinearMap.mem_ker, mulVecLin_apply] at hw
  have h0 := congrFun hw 0
  have h1 := congrFun hw 1
  simp [A, mulVec] at h0 h1
  refine ⟨w, hw0, ?_, ?_⟩
  · rw [dotProduct_comm]; exact h0
  · rw [dotProduct_comm]; exact h1

lemma eq_of_N2 (v : Fin 2 → ℝ) (hv : v 0 ≠ v 1) (Q Q' : Matrix (Fin K) (Fin 2) ℝ)
    (h1 : Q *ᵥ (fun _ => (1 : ℝ)) = Q' *ᵥ (fun _ => (1 : ℝ))) (h2 : Q *ᵥ v = Q' *ᵥ v) :
    Q = Q' := by
  ext k i
  have e1 := congrFun h1 k
  have e2 := congrFun h2 k
  simp [mulVec, dotProduct, Fin.sum_univ_two] at e1 e2
  have hs : v 1 - v 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have hk1 : Q k 1 = Q' k 1 := by
    have : (Q k 1 - Q' k 1) * (v 1 - v 0) = 0 := by linear_combination e2 - v 0 * e1
    have := (mul_eq_zero.mp this).resolve_right hs
    linarith
  fin_cases i
  · simp; linarith
  · simpa using hk1

lemma QN2_feasible (q y : Fin K → ℝ) (b v : Fin 2 → ℝ) (hv : v 0 ≠ v 1)
    (hT : ∑ k, q k = ∑ i, b i) (hy : (fun _ => (1 : ℝ)) ⬝ᵥ y = b ⬝ᵥ v) :
    QN2 q y v ∈ feasible q b := by
  have hs : v 1 - v 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  simp only [Fin.sum_univ_two] at hT
  simp only [dotProduct, Fin.sum_univ_two, one_mul] at hy
  constructor
  · ext k
    simp [QN2, mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  · ext i
    simp only [vecMul, dotProduct, one_mul, QN2, Matrix.of_apply]
    fin_cases i
    · simp only [Fin.zero_eta, if_true]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hT, hy]
      field_simp
      ring
    · simp only [Fin.mk_one, one_ne_zero, if_false]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hT, hy]
      field_simp
      ring

lemma QN2_mulVec (q y : Fin K → ℝ) (v : Fin 2 → ℝ) (hv : v 0 ≠ v 1) :
    QN2 q y v *ᵥ v = y := by
  have hs : v 1 - v 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  ext k
  simp [QN2, mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

lemma v01_of (v : Fin 2 → ℝ) (hv : ∃ i j, v i ≠ v j) : v 0 ≠ v 1 := by
  obtain ⟨i, j, h⟩ := hv
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]


-- EXTRA
lemma feasible_sum {K N : ℕ} {q : Fin K → ℝ} {b : Fin N → ℝ}
    {Q : Matrix (Fin K) (Fin N) ℝ} (hQ : Q ∈ feasible q b) : ∑ k, q k = ∑ i, b i := by
  have h := feasible_agg (fun _ => (1 : ℝ)) hQ
  rw [hQ.1] at h
  simpa [dotProduct] using h

lemma Fmat_mulVec {K N : ℕ} (v : Fin N → ℝ) (Q : Matrix (Fin K) (Fin N) ℝ) :
    Fmat v *ᵥ (fun c : Fin K × Fin N => Q c.1 c.2) =
      Sum.elim ((fun _ => (1 : ℝ)) ᵥ* Q) (Sum.elim (Q *ᵥ (fun _ => (1 : ℝ))) (Q *ᵥ v)) := by
  funext r
  rcases r with i | k | k
  · simp [Fmat, mulVec, vecMul, dotProduct, Fintype.sum_prod_type]
  · simp [Fmat, mulVec, dotProduct, Fintype.sum_prod_type]
  · simp [Fmat, mulVec, dotProduct, Fintype.sum_prod_type, mul_comm]

lemma sum_elim3_iff {α β γ : Type} (a a' : α → ℝ) (b b' : β → ℝ) (c c' : γ → ℝ) :
    Sum.elim a (Sum.elim b c) = Sum.elim a' (Sum.elim b' c') ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    refine ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => ?_⟩
    · simpa using congrFun h (Sum.inl x)
    · simpa using congrFun h (Sum.inr (Sum.inl x))
    · simpa using congrFun h (Sum.inr (Sum.inr x))
  · rintro ⟨rfl, rfl, rfl⟩; rfl

end core

end SystemicHoldings.FEfficient

open SystemicHoldings.FEfficient Matrix


theorem solution {K N : ℕ} (hN : 2 ≤ N) (hK : 1 ≤ K)
    (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ) (hv : ∃ i j, v i ≠ v j)
    (Q : Matrix (Fin K) (Fin N) ℝ) :
    IsFEfficient μ σ q b v Q ↔
      Fmat v *ᵥ (fun c : Fin K × Fin N => Q c.1 c.2) =
        Sum.elim b (Sum.elim q (yStar μ σ b v)) := by
  rw [Fmat_mulVec, sum_elim3_iff]
  constructor
  · intro h
    exact ⟨h.1.2, h.1.1, eff_mulVec hK μ σ hσ q b v (feasible_sum h.1) hv Q h⟩
  · rintro ⟨h1, h2, h3⟩
    exact isFEfficient_of_eq hK μ σ hσ q b v Q ⟨h2, h1⟩ h3
