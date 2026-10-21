-- Prove2me | solution 2 for SystemicHoldings.FEfficient.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:34:53.967992+00:00
-- url     : https://prove2.me/submissions/72dcabd2-3c90-48ff-97bd-6d73f46fc575

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model

set_option autoImplicit false
open SystemicHoldings.FEfficient Matrix

namespace ShAux

local notation "𝟙" => (fun _ => (1 : ℝ))

lemma dot_one {ι : Type*} [Fintype ι] (x : ι → ℝ) : x ⬝ᵥ 𝟙 = ∑ k, x k := by
  simp [dotProduct]

lemma one_dot {ι : Type*} [Fintype ι] (x : ι → ℝ) : 𝟙 ⬝ᵥ x = ∑ k, x k := by
  simp [dotProduct]

lemma one_ne {K : ℕ} (hK : 1 ≤ K) : (𝟙 : Fin K → ℝ) ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hK⟩
  simp at this

lemma G_bil {K : ℕ} (μ σ x y : Fin K → ℝ) :
    x ⬝ᵥ (shockMoment μ σ *ᵥ y) = (μ ⬝ᵥ x) * (μ ⬝ᵥ y) + ∑ k, σ k ^ 2 * (x k * y k) := by
  have h1 : x ⬝ᵥ (vecMulVec μ μ *ᵥ y) = (μ ⬝ᵥ x) * (μ ⬝ᵥ y) := by
    rw [vecMulVec_mulVec]
    simp only [op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm x μ]; ring
  have h2 : x ⬝ᵥ (diagonal (fun k => σ k ^ 2) *ᵥ y) = ∑ k, σ k ^ 2 * (x k * y k) := by
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [shockMoment, add_mulVec, dotProduct_add, h1, h2]

lemma G_symm {K : ℕ} (μ σ x y : Fin K → ℝ) :
    x ⬝ᵥ (shockMoment μ σ *ᵥ y) = y ⬝ᵥ (shockMoment μ σ *ᵥ x) := by
  rw [G_bil, G_bil, mul_comm (μ ⬝ᵥ x)]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma G_nonneg {K : ℕ} (μ σ x : Fin K → ℝ) : 0 ≤ x ⬝ᵥ (shockMoment μ σ *ᵥ x) := by
  rw [G_bil]
  exact add_nonneg (mul_self_nonneg _)
    (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (mul_self_nonneg _))

lemma G_pos {K : ℕ} (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) {x : Fin K → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (shockMoment μ σ *ᵥ x) := by
  rw [G_bil]
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have h1 : 0 ≤ (μ ⬝ᵥ x) * (μ ⬝ᵥ x) := mul_self_nonneg _
  have h2 : 0 < ∑ k, σ k ^ 2 * (x k * x k) := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (sq_nonneg _) (mul_self_nonneg _)
    · refine ⟨k, Finset.mem_univ _, ?_⟩
      have := hσ k
      have h3 : 0 < x k * x k := mul_self_pos.mpr hk
      positivity
  linarith

lemma G_herm {K : ℕ} (μ σ : Fin K → ℝ) : (shockMoment μ σ).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  by_cases h : i = j
  · subst h
    simp [shockMoment, conjTranspose_apply, vecMulVec_apply, diagonal_apply]
  · simp [shockMoment, conjTranspose_apply, vecMulVec_apply, diagonal_apply, h, Ne.symm h,
      mul_comm]

lemma G_posdef {K : ℕ} (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) : (shockMoment μ σ).PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos (G_herm μ σ) (fun x hx => by
    simpa using G_pos μ σ hσ hx)

lemma G_mul_inv {K : ℕ} (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) :
    shockMoment μ σ * (shockMoment μ σ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (G_posdef μ σ hσ).isUnit)

lemma G_z {K : ℕ} (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) :
    shockMoment μ σ *ᵥ zVec μ σ = 𝟙 := by
  rw [zVec, mulVec_mulVec, G_mul_inv μ σ hσ]
  exact one_mulVec _

lemma z_pos {K : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) :
    0 < 𝟙 ⬝ᵥ zVec μ σ := by
  have hz : zVec μ σ ≠ 0 := by
    intro h
    have := G_z μ σ hσ
    rw [h, mulVec_zero] at this
    exact one_ne hK this.symm
  have := G_pos μ σ hσ hz
  rw [G_z μ σ hσ] at this
  rwa [dotProduct_comm] at this

lemma ystar_sum {K N : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) (b v : Fin N → ℝ) :
    𝟙 ⬝ᵥ yStar μ σ b v = b ⬝ᵥ v := by
  have hs := (z_pos hK μ σ hσ).ne'
  rw [yStar, dotProduct_smul, smul_eq_mul]
  field_simp

lemma G_ystar {K N : ℕ} (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) (b v : Fin N → ℝ) :
    shockMoment μ σ *ᵥ yStar μ σ b v = ((b ⬝ᵥ v) / (𝟙 ⬝ᵥ zVec μ σ)) • (𝟙 : Fin K → ℝ) := by
  rw [yStar, mulVec_smul, G_z μ σ hσ]

lemma ystar_quad {K N : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) (b v : Fin N → ℝ) :
    yStar μ σ b v ⬝ᵥ (shockMoment μ σ *ᵥ yStar μ σ b v) =
      (b ⬝ᵥ v) ^ 2 / (𝟙 ⬝ᵥ zVec μ σ) := by
  rw [G_ystar μ σ hσ, dotProduct_smul, dotProduct_comm (yStar μ σ b v) 𝟙,
    ystar_sum hK μ σ hσ, smul_eq_mul]
  ring

lemma decomp {K N : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) (b v : Fin N → ℝ)
    (y : Fin K → ℝ) (hy : y ∈ aggFeasible b v) :
    y ⬝ᵥ (shockMoment μ σ *ᵥ y) = yStar μ σ b v ⬝ᵥ (shockMoment μ σ *ᵥ yStar μ σ b v) +
      (y - yStar μ σ b v) ⬝ᵥ (shockMoment μ σ *ᵥ (y - yStar μ σ b v)) := by
  have hy' : 𝟙 ⬝ᵥ y = b ⬝ᵥ v := hy
  have hd : 𝟙 ⬝ᵥ (y - yStar μ σ b v) = 0 := by
    rw [dotProduct_sub, ystar_sum hK μ σ hσ, hy', sub_self]
  have hcross : (y - yStar μ σ b v) ⬝ᵥ (shockMoment μ σ *ᵥ yStar μ σ b v) = 0 := by
    rw [G_ystar μ σ hσ, dotProduct_smul, dotProduct_comm (y - yStar μ σ b v) 𝟙, hd, smul_zero]
  have hsym : yStar μ σ b v ⬝ᵥ (shockMoment μ σ *ᵥ (y - yStar μ σ b v)) =
      (y - yStar μ σ b v) ⬝ᵥ (shockMoment μ σ *ᵥ yStar μ σ b v) := G_symm μ σ _ _
  have e : y = yStar μ σ b v + (y - yStar μ σ b v) := by abel
  conv_lhs => rw [e]
  simp only [mulVec_add, dotProduct_add, add_dotProduct]
  rw [hsym, hcross]
  ring

lemma lemma41 {K N : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) (b v : Fin N → ℝ) :
    SolvesAggregate μ σ b v (yStar μ σ b v) ∧
    ∀ y : Fin K → ℝ, SolvesAggregate μ σ b v y → y = yStar μ σ b v := by
  have hmem : yStar μ σ b v ∈ aggFeasible b v := ystar_sum hK μ σ hσ b v
  have hsolve : SolvesAggregate μ σ b v (yStar μ σ b v) :=
    ⟨hmem, fun y' hy' => by
      rw [decomp hK μ σ hσ b v y' hy']
      linarith [G_nonneg μ σ (y' - yStar μ σ b v)]⟩
  refine ⟨hsolve, fun y hy => ?_⟩
  have h1 := hy.2 _ hmem
  rw [decomp hK μ σ hσ b v y hy.1] at h1
  by_contra hne
  have hd : y - yStar μ σ b v ≠ 0 := sub_ne_zero.mpr hne
  have := G_pos μ σ hσ hd
  linarith

lemma msd_aux {K N : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) (b v : Fin N → ℝ) :
    yStar μ σ b v ⬝ᵥ (shockMoment μ σ *ᵥ yStar μ σ b v) =
      (b ⬝ᵥ v) ^ 2 / ((fun _ => (1 : ℝ)) ⬝ᵥ zVec μ σ) ∧
    ∀ Q : Matrix (Fin K) (Fin N) ℝ, Q *ᵥ v = yStar μ σ b v →
      msd μ σ v Q = (b ⬝ᵥ v) ^ 2 /
        ((fun _ => (1 : ℝ)) ⬝ᵥ ((shockMoment μ σ)⁻¹ *ᵥ (fun _ => (1 : ℝ)))) := by
  refine ⟨ystar_quad hK μ σ hσ b v, fun Q hQ => ?_⟩
  unfold msd
  rw [hQ]
  exact ystar_quad hK μ σ hσ b v

lemma feas_sum {K N : ℕ} {q : Fin K → ℝ} {b : Fin N → ℝ} {Q : Matrix (Fin K) (Fin N) ℝ}
    (hQ : Q ∈ feasible q b) : ∑ k, q k = ∑ n, b n := by
  obtain ⟨h1, h2⟩ := hQ
  calc ∑ k, q k = 𝟙 ⬝ᵥ q := (one_dot q).symm
    _ = 𝟙 ⬝ᵥ (Q *ᵥ 𝟙) := by rw [h1]
    _ = (𝟙 ᵥ* Q) ⬝ᵥ 𝟙 := by rw [dotProduct_mulVec]
    _ = ∑ n, b n := by rw [h2, dot_one]

lemma feas_agg {K N : ℕ} {q : Fin K → ℝ} {b v : Fin N → ℝ} {Q : Matrix (Fin K) (Fin N) ℝ}
    (hQ : Q ∈ feasible q b) : Q *ᵥ v ∈ aggFeasible b v := by
  show 𝟙 ⬝ᵥ (Q *ᵥ v) = b ⬝ᵥ v
  rw [dotProduct_mulVec, hQ.2]

lemma alloc {K N : ℕ} (hK : 1 ≤ K) (q : Fin K → ℝ) (b v : Fin N → ℝ) (y : Fin K → ℝ)
    (i j : Fin N) (hij : v i ≠ v j)
    (hT : ∑ k, q k = ∑ n, b n) (hy : ∑ k, y k = b ⬝ᵥ v) :
    ∃ Q : Matrix (Fin K) (Fin N) ℝ, Q ∈ feasible q b ∧ Q *ᵥ v = y := by
  set T : ℝ := ∑ k, q k with hTdef
  let k0 : Fin K := ⟨0, hK⟩
  let ei : Fin N → ℝ := fun n => if n = i then 1 else 0
  let ej : Fin N → ℝ := fun n => if n = j then 1 else 0
  let ek : Fin K → ℝ := fun k => if k = k0 then 1 else 0
  have hei : ei ⬝ᵥ 𝟙 = 1 := by simp [ei, dotProduct]
  have hek : 𝟙 ⬝ᵥ ek = 1 := by simp [ek, dotProduct]
  have hek' : ek ⬝ᵥ 𝟙 = 1 := by rw [dotProduct_comm]; exact hek
  let Q0 : Matrix (Fin K) (Fin N) ℝ := vecMulVec q ei + vecMulVec ek (b - T • ei)
  have hb0 : (b - T • ei) ⬝ᵥ 𝟙 = 0 := by
    rw [sub_dotProduct, smul_dotProduct, hei, dot_one, ← hT, smul_eq_mul]; ring
  have hQ01 : Q0 *ᵥ 𝟙 = q := by
    simp only [Q0, add_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hei, hb0, one_smul,
      zero_smul, add_zero]
  have hQ02 : 𝟙 ᵥ* Q0 = b := by
    have h1 : 𝟙 ⬝ᵥ q = T := one_dot q
    simp only [Q0, vecMul_add, vecMul_vecMulVec, h1, hek, one_smul]
    abel
  have hd : 𝟙 ⬝ᵥ (y - Q0 *ᵥ v) = 0 := by
    rw [dotProduct_sub, dotProduct_mulVec, hQ02, one_dot, hy, sub_self]
  let w : Fin N → ℝ := fun n => (ei n - ej n) / (v i - v j)
  have hΔ : v i - v j ≠ 0 := sub_ne_zero.mpr hij
  have hw1 : w ⬝ᵥ 𝟙 = 0 := by
    simp only [w, dot_one, ← Finset.sum_div, Finset.sum_sub_distrib]
    simp [ei, ej]
  have hw2 : w ⬝ᵥ v = 1 := by
    simp only [w, dotProduct, div_mul_eq_mul_div, ← Finset.sum_div, sub_mul,
      Finset.sum_sub_distrib, ei, ej, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    exact div_self hΔ
  refine ⟨Q0 + vecMulVec (y - Q0 *ᵥ v) w, ⟨?_, ?_⟩, ?_⟩
  · rw [add_mulVec, vecMulVec_mulVec, hQ01, op_smul_eq_smul, hw1, zero_smul, add_zero]
  · rw [vecMul_add, vecMul_vecMulVec, hQ02, hd, zero_smul, add_zero]
  · rw [add_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hw2, one_smul]
    abel

lemma prop42 {K N : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ) (hT : ∑ k, q k = ∑ i, b i)
    (hv : ∃ i j, v i ≠ v j) :
    ∃ Q ∈ feasible q b, Q *ᵥ v = yStar μ σ b v := by
  obtain ⟨i, j, hij⟩ := hv
  obtain ⟨Q, h1, h2⟩ := alloc hK q b v (yStar μ σ b v) i j hij hT
    (by rw [← one_dot]; exact ystar_sum hK μ σ hσ b v)
  exact ⟨Q, h1, h2⟩

lemma prop41 {K N : ℕ} (hK : 1 ≤ K)
    (μ σ : Fin K → ℝ) (q : Fin K → ℝ) (b v : Fin N → ℝ) (hv : ∃ i j, v i ≠ v j)
    (Q : Matrix (Fin K) (Fin N) ℝ) (hQ : Q ∈ feasible q b) :
    IsFEfficient μ σ q b v Q ↔ SolvesAggregate μ σ b v (Q *ᵥ v) := by
  constructor
  · rintro ⟨_, hmin⟩
    refine ⟨feas_agg hQ, fun y' hy' => ?_⟩
    obtain ⟨i, j, hij⟩ := hv
    have h1 : 𝟙 ⬝ᵥ (Q *ᵥ v) = b ⬝ᵥ v := feas_agg hQ
    have h2 : 𝟙 ⬝ᵥ y' = b ⬝ᵥ v := hy'
    have hd : ∑ k, (y' - Q *ᵥ v) k = (0 : Fin N → ℝ) ⬝ᵥ v := by
      rw [zero_dotProduct, ← one_dot, dotProduct_sub, h1, h2, sub_self]
    obtain ⟨Δ, hΔ, hΔv⟩ := alloc hK (0 : Fin K → ℝ) (0 : Fin N → ℝ) v (y' - Q *ᵥ v) i j hij
      (by simp) hd
    have hfeas : Q + Δ ∈ feasible q b :=
      ⟨by rw [add_mulVec, hQ.1, hΔ.1]; simp, by rw [vecMul_add, hQ.2, hΔ.2]; simp⟩
    have := hmin _ hfeas
    unfold msd at this
    rw [add_mulVec, hΔv] at this
    have e : Q *ᵥ v + (y' - Q *ᵥ v) = y' := by abel
    rw [e] at this
    exact this
  · intro h
    exact ⟨hQ, fun Q' hQ' => h.2 _ (feas_agg hQ')⟩

lemma eff_iff {K N : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ) (hv : ∃ i j, v i ≠ v j)
    (Q : Matrix (Fin K) (Fin N) ℝ) :
    IsFEfficient μ σ q b v Q ↔ Q ∈ feasible q b ∧ Q *ᵥ v = yStar μ σ b v := by
  constructor
  · intro h
    have hQ := h.1
    exact ⟨hQ, (lemma41 hK μ σ hσ b v).2 _ ((prop41 hK μ σ q b v hv Q hQ).mp h)⟩
  · rintro ⟨hQ, hy⟩
    refine (prop41 hK μ σ q b v hv Q hQ).mpr ?_
    rw [hy]
    exact (lemma41 hK μ σ hσ b v).1

lemma Fmat_mulVec {K N : ℕ} (v : Fin N → ℝ) (Q : Matrix (Fin K) (Fin N) ℝ) :
    Fmat v *ᵥ (fun c : Fin K × Fin N => Q c.1 c.2) =
      Sum.elim (𝟙 ᵥ* Q) (Sum.elim (Q *ᵥ 𝟙) (Q *ᵥ v)) := by
  funext r
  rcases r with i | k | k
  · simp [Fmat, mulVec, dotProduct, vecMul, Fintype.sum_prod_type]
  · simp [Fmat, mulVec, dotProduct, Fintype.sum_prod_type_right]
  · simp [Fmat, mulVec, dotProduct, Fintype.sum_prod_type_right, mul_comm]

lemma remark_aux {K N : ℕ} (hK : 1 ≤ K)
    (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ) (hv : ∃ i j, v i ≠ v j)
    (Q : Matrix (Fin K) (Fin N) ℝ) :
    IsFEfficient μ σ q b v Q ↔
      Fmat v *ᵥ (fun c : Fin K × Fin N => Q c.1 c.2) =
        Sum.elim b (Sum.elim q (yStar μ σ b v)) := by
  rw [eff_iff hK μ σ hσ q b v hv Q, Fmat_mulVec]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [h1, h2, h3]
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · funext x
      simpa using congrFun h (Sum.inr (Sum.inl x))
    · funext x
      simpa using congrFun h (Sum.inl x)
    · funext x
      simpa using congrFun h (Sum.inr (Sum.inr x))

end ShAux

theorem solution {K N : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (b v : Fin N → ℝ) :
    SolvesAggregate μ σ b v (yStar μ σ b v) ∧
    ∀ y : Fin K → ℝ, SolvesAggregate μ σ b v y → y = yStar μ σ b v :=
  ShAux.lemma41 hK μ σ hσ b v
