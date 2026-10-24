-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P29.oneKrausTerm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:34:15.909385+00:00
-- url     : https://prove2.me/submissions/b8bcf8c2-3d96-47b9-a219-906e63a172a6

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7P29_lin_expand {I J : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (X : Matrix I I ℂ) :
    L X = ∑ i, ∑ j, X i j • L (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem X7P29_choi_psd {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (h : Entanglement.IsCompletelyPositive L) :
    (Matrix.of fun (p q : I × J) => L (Matrix.single p.1 q.1 1) p.2 q.2).PosSemidef := by
  let e := Fintype.equivFin I
  let Ω : Fin (Fintype.card I) × I → ℂ := fun q => if q.1 = e q.2 then 1 else 0
  have hY := h _ _ (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hE : (Matrix.of fun (p q : I × J) => L (Matrix.single p.1 q.1 1) p.2 q.2) =
      (idTensorSuperop L (Matrix.vecMulVec Ω (star Ω))).submatrix
      (fun q : I × J => (e q.1, q.2)) (fun q => (e q.1, q.2)) := by
    ext ⟨i, o⟩ ⟨i', o'⟩
    rw [Matrix.submatrix_apply, Matrix.of_apply]
    show L (Matrix.single i i' 1) o o' =
      L (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) o o'
    have hX : (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) =
        Matrix.single i i' 1 := by
      ext j j'
      by_cases h1 : i = j <;> by_cases h2 : i' = j' <;>
        simp [Matrix.single_apply, Matrix.vecMulVec_apply, Ω, h1, h2, Ne.symm, eq_comm]
    rw [hX]
  rw [hE]
  exact hY.submatrix _

theorem X7P29_perm3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ l, f a b l = ∑ l, ∑ b, ∑ a, f a b l := by
  calc ∑ a, ∑ b, ∑ l, f a b l = ∑ a, ∑ l, ∑ b, f a b l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, f a b l := Finset.sum_comm
    _ = ∑ l, ∑ b, ∑ a, f a b l := Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem X7P29_kraus {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (h : Entanglement.IsCompletelyPositive L) :
    ∃ m : ℕ, ∃ K : Fin m → Matrix J I ℂ, ∀ X, L X = krausApply K X := by
  obtain ⟨m, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (X7P29_choi_psd L h)
  have hMij : ∀ i j o o', L (Matrix.single i j 1) o o' =
      ∑ l, g l (i, o) * star (g l (j, o')) := by
    intro i j o o'
    have := congrFun (congrFun hg (i, o)) (j, o')
    rw [Matrix.of_apply] at this
    rw [this, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  refine ⟨m, fun l => Matrix.of fun o i => g l (i, o), fun X => ?_⟩
  ext o o'
  rw [X7P29_lin_expand]
  simp only [krausApply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hMij,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [X7P29_perm3]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => ?_
  ring

theorem X7P29_entry {I : Type*} [Fintype I] [DecidableEq I] (K : Matrix I I ℂ) (i j k l : I) :
    (K * (Matrix.single j l (1:ℂ) : Matrix I I ℂ) * Kᴴ) i k = K i j * conj (K k l) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

theorem X7P29_fe {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
    (rho : Matrix I I ℂ) (A : Superop I I) (K : Fin m → Matrix I I ℂ)
    (hA : ∀ X, A X = krausApply K X) :
    fe rho A = ∑ a, Complex.normSq ((K a * rho).trace) := by
  unfold fe
  have h5 : ∀ f : I → I → I → I → Fin m → ℂ, ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, f i j k l a =
      ∑ a, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l a := by
    intro f
    calc _ = ∑ i, ∑ j, ∑ k, ∑ a, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ a, ∑ k, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ k, ∑ l, f i j k l a :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have ht : ∀ a, (K a * rho).trace = ∑ i, ∑ j, K a i j * rho j i := by
    intro a; simp [Matrix.trace, Matrix.mul_apply]
  have key : (∑ i, ∑ j, ∑ k, ∑ l, rho j i * conj (rho l k) * A (Matrix.single j l (1:ℂ)) i k) =
      ∑ a, (K a * rho).trace * conj ((K a * rho).trace) := by
    simp only [hA, krausApply, Matrix.sum_apply, X7P29_entry, Finset.mul_sum]
    rw [h5]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ht, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul]
    ring
  rw [key, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re]

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7P29_rot {I : Type*} [Fintype I] {m : ℕ} (K : Fin m → Matrix I I ℂ) (c : Fin m → ℂ)
    (hc : ∑ a, c a * conj (c a) = 1 ∨ c = 0) (X : Matrix I I ℂ) :
    krausApply (Fin.cons (∑ a, c a • K a) (fun j => K j - conj (c j) • ∑ a, c a • K a) :
      Fin (m + 1) → Matrix I I ℂ) X = krausApply K X := by
  set K0 := ∑ a, c a • K a with hK0
  unfold krausApply
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have expand : ∀ j, (K j - conj (c j) • K0) * X * (K j - conj (c j) • K0)ᴴ =
      K j * X * (K j)ᴴ - c j • (K j * X * K0ᴴ) - conj (c j) • (K0 * X * (K j)ᴴ) +
        (c j * conj (c j)) • (K0 * X * K0ᴴ) := by
    intro j
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul]
    simp only [Complex.star_def, Complex.conj_conj, sub_mul, mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, smul_sub, smul_smul]
    module
  have s1 : ∑ j, c j • (K j * X * K0ᴴ) = K0 * X * K0ᴴ := by
    simp only [hK0, Finset.sum_mul, Matrix.smul_mul]
  have hK0h : K0ᴴ = ∑ j, conj (c j) • (K j)ᴴ := by
    rw [hK0, Matrix.conjTranspose_sum]
    simp [Matrix.conjTranspose_smul]
  have s2 : ∑ j, conj (c j) • (K0 * X * (K j)ᴴ) = K0 * X * K0ᴴ := by
    rw [hK0h, Finset.mul_sum]
    simp only [Matrix.mul_smul]
  have s3 : ∑ j, (c j * conj (c j)) • (K0 * X * K0ᴴ) = (∑ j, c j * conj (c j)) • (K0 * X * K0ᴴ) := by
    rw [Finset.sum_smul]
  rw [Finset.sum_congr rfl (fun j _ => expand j)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [s1, s2, s3]
  rcases hc with h | h
  · rw [h, one_smul]; abel
  · have : K0 = 0 := by simp [hK0, h]
    simp [this]

theorem X7P29_main {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (A : Superop I I) (hA : TraceNonincreasingCPMap A) :
    ∃ m : ℕ, ∃ K : Fin (m + 1) → Matrix I I ℂ,
      Represents K A ∧ fe rho A = operatorFe rho (K 0) := by
  obtain ⟨⟨L, hL, hcp⟩, -⟩ := hA
  obtain ⟨m, K, hK⟩ := X7P29_kraus L hcp
  have hAK : ∀ X, A X = krausApply K X := fun X => by rw [← hL, hK]
  set v : Fin m → ℂ := fun a => (K a * rho).trace with hv
  set S : ℝ := ∑ a, Complex.normSq (v a) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  set s : ℝ := Real.sqrt S with hs
  set c : Fin m → ℂ := fun a => conj (v a) / (s : ℂ) with hc
  have hcv : ∑ a, c a * v a = (S : ℂ) / s := by
    simp only [hc, div_mul_eq_mul_div, ← Finset.sum_div, hS, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm, Complex.mul_conj]
  have hcc : ∑ a, c a * conj (c a) = 1 ∨ c = 0 := by
    by_cases h0 : s = 0
    · right; funext a; simp [hc, h0]
    · left
      have hS' : S ≠ 0 := by intro h; apply h0; rw [hs, h, Real.sqrt_zero]
      have : ∑ a, c a * conj (c a) = (S : ℂ) / (s : ℂ) ^ 2 := by
        simp only [hc, map_div₀, Complex.conj_ofReal, Complex.conj_conj, hS, Complex.ofReal_sum]
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Complex.mul_conj, mul_comm (v a)]
        field_simp
      rw [this]
      have : (s : ℂ) ^ 2 = S := by
        rw [← Complex.ofReal_pow, hs, Real.sq_sqrt hS0]
      rw [this, div_self (by exact_mod_cast hS')]
  refine ⟨m, Fin.cons (∑ a, c a • K a) (fun j => K j - conj (c j) • ∑ a, c a • K a),
    fun X => by rw [hAK, X7P29_rot K c hcc X], ?_⟩
  rw [X7P29_fe rho A K hAK, Fin.cons_zero]
  unfold operatorFe
  have htr : ((∑ a, c a • K a) * rho).trace = ∑ a, c a * v a := by
    simp [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, hv]
  rw [htr, hcv]
  by_cases h0 : s = 0
  · have : S = 0 := by
      have := Real.sq_sqrt hS0
      rw [← hs, h0] at this
      linarith
    simp only [h0, Complex.ofReal_zero, div_zero, map_zero]
    rw [← hS, this]
  · have hss : (S : ℂ) / s = s := by
      have : (s : ℂ) ^ 2 = S := by
        rw [← Complex.ofReal_pow, hs, Real.sq_sqrt hS0]
      rw [← this]
      field_simp [show (s : ℂ) ≠ 0 by exact_mod_cast h0]
    rw [hss, Complex.normSq_ofReal, ← hS, ← sq, hs, Real.sq_sqrt hS0]

end QAlgorithms.Papers.Independent.Gap48.P29

end

open QAlgorithms.Papers.Independent.Gap48.P29 in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho : Matrix I I ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) (A : QAlgorithms.Superop I I)
    (hA : TraceNonincreasingCPMap A) :
    ∃ m : ℕ, ∃ K : Fin (m + 1) → Matrix I I ℂ,
      Represents K A ∧ fe rho A = operatorFe rho (K 0) :=
  QAlgorithms.Papers.Independent.Gap48.P29.X7P29_main rho A hA
