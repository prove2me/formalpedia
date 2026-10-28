-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P29.minimumFidelity_controls_entanglementFidelity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:07:18.623219+00:00
-- url     : https://prove2.me/submissions/db04cb29-c36f-4b81-84d6-8916441315bd

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29
import Mathlib

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

theorem X7P29_fe {I : Type*} [Fintype I] [DecidableEq I] {κ : Type*} [Fintype κ]
    (rho : Matrix I I ℂ) (A : Superop I I) (K : κ → Matrix I I ℂ)
    (hA : ∀ X, A X = krausApply K X) :
    fe rho A = ∑ a, Complex.normSq ((K a * rho).trace) := by
  unfold fe
  have h5 : ∀ f : I → I → I → I → κ → ℂ, ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, f i j k l a =
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

namespace X7mf

open scoped ComplexConjugate

def z {I : Type*} (θ : I → Fin 4) (i : I) : ℂ := Complex.I ^ (θ i).val

theorem Ipow_add (a b : Fin 4) : Complex.I ^ (a + b).val = Complex.I ^ a.val * Complex.I ^ b.val := by
  fin_cases a <;> fin_cases b <;> simp [pow_succ, Complex.I_mul_I]

theorem z_add {I : Type*} (θ v : I → Fin 4) (i : I) : z (θ + v) i = z θ i * z v i := by
  simp [z, Ipow_add]

theorem conj_mul_z {I : Type*} (θ : I → Fin 4) (i : I) : conj (z θ i) * z θ i = 1 := by
  simp only [z, map_pow, ← mul_pow, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg, one_pow]

theorem z_single {I : Type*} [DecidableEq I] (m t : I) :
    z (Pi.single m (1 : Fin 4)) t = if t = m then Complex.I else 1 := by
  by_cases h : t = m
  · subst h; simp [z]
  · simp [z, h]

theorem sum_shift {I : Type*} [Fintype I] [DecidableEq I] (g : (I → Fin 4) → ℂ) (v : I → Fin 4) :
    ∑ θ, g (θ + v) = ∑ θ, g θ :=
  Fintype.sum_equiv (Equiv.addRight v) _ _ (fun _ => rfl)

theorem sum_zero_of_factor {I : Type*} [Fintype I] [DecidableEq I] (g : (I → Fin 4) → ℂ) (v : I → Fin 4)
    (f : ℂ) (hf : f ≠ 1) (hg : ∀ θ, g (θ + v) = f * g θ) : ∑ θ, g θ = 0 := by
  have h := sum_shift g v
  simp only [hg, ← Finset.mul_sum] at h
  have : (f - 1) * ∑ θ, g θ = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hf
  · exact h1

theorem G1 {I : Type*} [Fintype I] [DecidableEq I] (i j : I) (hij : i ≠ j) :
    ∑ θ : I → Fin 4, conj (z θ i) * z θ j = 0 := by
  refine sum_zero_of_factor _ (Pi.single i 1) (-Complex.I) ?_ fun θ => ?_
  · intro h; have := congrArg Complex.re h; simp at this
  · simp only [z_add, z_single, ↓reduceIte, if_neg (Ne.symm hij), map_mul, Complex.conj_I, mul_one]
    ring

theorem G2 {I : Type*} [Fintype I] [DecidableEq I] (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l) :
    ∑ θ : I → Fin 4, conj (z θ i) * z θ j * z θ k * conj (z θ l) =
      if i = k ∧ j = l then (Fintype.card (I → Fin 4) : ℂ) else 0 := by
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩]
    have : ∀ θ : I → Fin 4, conj (z θ i) * z θ j * z θ i * conj (z θ j) = 1 := by
      intro θ
      have h1 := conj_mul_z θ i; have h2 := conj_mul_z θ j
      calc _ = (conj (z θ i) * z θ i) * (conj (z θ j) * z θ j) := by ring
        _ = 1 := by rw [h1, h2, one_mul]
    simp [this]
  · rw [if_neg h]
    by_cases hik : i = k
    · subst hik
      have hjl : j ≠ l := fun e => h ⟨rfl, e⟩
      refine sum_zero_of_factor _ (Pi.single j 1) Complex.I ?_ fun θ => ?_
      · intro e; have := congrArg Complex.im e; simp at this
      · simp only [z_add, z_single, ↓reduceIte, if_neg hij, if_neg (Ne.symm hjl), map_mul, map_one, mul_one]
        ring
    · by_cases hli : l = i
      · subst hli
        refine sum_zero_of_factor _ (Pi.single l 1) (-1) ?_ fun θ => ?_
        · norm_num
        · simp only [z_add, z_single, ↓reduceIte, if_neg (Ne.symm hij), if_neg (Ne.symm hik), map_mul,
            Complex.conj_I, mul_one]
          have : Complex.I * Complex.I = -1 := Complex.I_mul_I
          linear_combination (conj (z θ l) * z θ j * z θ k * conj (z θ l)) * this
      · refine sum_zero_of_factor _ (Pi.single i 1) (-Complex.I) ?_ fun θ => ?_
        · intro e; have := congrArg Complex.re e; simp at this
        · simp only [z_add, z_single, ↓reduceIte, if_neg (Ne.symm hij), if_neg (Ne.symm hik),
            if_neg hli, map_mul, Complex.conj_I, mul_one, map_one]
          ring

end X7mf

end

noncomputable section

namespace X7mf

open scoped ComplexConjugate

theorem sumO_zero {I : Type*} [Fintype I] [DecidableEq I] (o : I → I → ℂ) (ho : ∀ i, o i i = 0) :
    ∑ θ : I → Fin 4, ∑ i, ∑ j, conj (z θ i) * z θ j * o i j = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases h : i = j
  · subst h; simp [ho]
  · rw [← Finset.sum_mul, G1 i j h, zero_mul]

theorem sumOO {I : Type*} [Fintype I] [DecidableEq I] (o : I → I → ℂ) (ho : ∀ i, o i i = 0) :
    ∑ θ : I → Fin 4, (∑ i, ∑ j, conj (z θ i) * z θ j * o i j) *
      conj (∑ k, ∑ l, conj (z θ k) * z θ l * o k l) =
    (Fintype.card (I → Fin 4) : ℂ) * ∑ i, ∑ j, o i j * conj (o i j) := by
  have e : ∀ θ : I → Fin 4, (∑ i, ∑ j, conj (z θ i) * z θ j * o i j) *
      conj (∑ k, ∑ l, conj (z θ k) * z θ l * o k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, (o i j * conj (o k l)) * (conj (z θ i) * z θ j * z θ k * conj (z θ l)) := by
    intro θ
    simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [e]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  have hk : ∀ k, ∑ θ : I → Fin 4, ∑ l, (o i j * conj (o k l)) *
      (conj (z θ i) * z θ j * z θ k * conj (z θ l)) =
      ∑ l, if i = k ∧ j = l then (Fintype.card (I → Fin 4) : ℂ) * (o i j * conj (o i j)) else 0 := by
    intro k
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_sum]
    by_cases hij : i = j
    · subst hij; simp [ho]
    by_cases hkl : k = l
    · subst hkl; simp [ho]; intro h1 h2; exact absurd (h1.trans h2.symm) hij
    rw [G2 i j k l hij hkl]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; ring
    · simp
  simp only [hk]
  simp [ite_and]

theorem avg {I : Type*} [Fintype I] [DecidableEq I] (u : I → I → ℂ) :
    ∑ θ : I → Fin 4, Complex.normSq (∑ i, ∑ j, conj (z θ i) * z θ j * u i j) =
      (Fintype.card (I → Fin 4) : ℝ) * (Complex.normSq (∑ i, u i i) +
        ∑ i, ∑ j, if i = j then 0 else Complex.normSq (u i j)) := by
  set o : I → I → ℂ := fun i j => if i = j then 0 else u i j with hodef
  have ho : ∀ i, o i i = 0 := fun i => by simp [o]
  set D := ∑ i, u i i
  have hX : ∀ θ : I → Fin 4, ∑ i, ∑ j, conj (z θ i) * z θ j * u i j =
      D + ∑ i, ∑ j, conj (z θ i) * z θ j * o i j := by
    intro θ
    have : ∀ i j, conj (z θ i) * z θ j * u i j =
        (if i = j then u i j else 0) + conj (z θ i) * z θ j * o i j := by
      intro i j
      by_cases h : i = j
      · subst h; simp [o, conj_mul_z]
      · simp [o, h]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, D]
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast]
  have hn : ∀ w : ℂ, ((Complex.normSq w : ℝ) : ℂ) = w * conj w := fun w => (Complex.mul_conj w).symm
  simp only [hn, hX]
  let O : (I → Fin 4) → ℂ := fun θ => ∑ i, ∑ j, conj (z θ i) * z θ j * o i j
  have hO : ∀ θ, ∑ i, ∑ j, conj (z θ i) * z θ j * o i j = O θ := fun θ => rfl
  simp only [hO]
  have h1 := sumO_zero o ho
  have h2 := sumOO o ho
  have hexp : ∀ θ, (D + O θ) * conj (D + O θ) = D * conj D + D * conj (O θ) + O θ * conj D +
      O θ * conj (O θ) := fun θ => by rw [map_add]; ring
  simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum]
  rw [show (∑ x, O x) = 0 from h1, show ∑ x, O x * conj (O x) = _ from h2]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, map_mul, map_natCast, map_zero, mul_zero,
    zero_mul, add_zero]
  rw [mul_add]
  congr 1
  · ring
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = j
  · simp [o, h]
  · simp [o, h, Complex.mul_conj]

end X7mf

end

noncomputable section

namespace X7mf

open scoped ComplexConjugate

theorem pmin {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (j0 : I) (hj0 : ∀ i, p i ≤ p j0) :
    ∑ j, p j * min (p j0) (1 - p j) ≤ 1 / 2 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
  have hrest : ∑ j ∈ Finset.univ.erase j0, p j = 1 - p j0 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j0), hp1]
  have h2 : ∑ j ∈ Finset.univ.erase j0, p j * min (p j0) (1 - p j) ≤ p j0 * (1 - p j0) := by
    calc _ ≤ ∑ j ∈ Finset.univ.erase j0, p j * p j0 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hp0 j)
      _ = p j0 * (1 - p j0) := by rw [← Finset.sum_mul, hrest, mul_comm]
  have h1 : p j0 * min (p j0) (1 - p j0) ≤ p j0 * (1 - p j0) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (hp0 j0)
  nlinarith [sq_nonneg (p j0 - 1 / 2)]

theorem pair_le {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (i j : I) (h : i ≠ j) : p i ≤ 1 - p j := by
  have : p i + p j ≤ ∑ k, p k := by
    rw [← Finset.sum_pair h]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => hp0 k
  linarith

theorem core {I κ : Type*} [Fintype I] [DecidableEq I] [Fintype κ] (B : κ → I → I → ℂ) (p : I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hTP : ∀ i, ∑ a, ∑ j, Complex.normSq (B a j i) = 1) (η : ℝ)
    (hmin : ∀ c : I → ℂ, ∑ i, Complex.normSq (c i) = 1 → (∀ i, p i = 0 → c i = 0) →
      1 - η ≤ ∑ a, Complex.normSq (∑ i, ∑ j, conj (c i) * B a i j * c j)) :
    1 - 3 / 2 * η ≤ ∑ a, Complex.normSq (∑ i, (p i : ℂ) * B a i i) := by
  -- step 1: columns
  have hcol : ∀ j, p j ≠ 0 → ∑ a, ∑ i, (if i = j then 0 else Complex.normSq (B a i j)) ≤ η := by
    intro j hj
    have h := hmin (Pi.single j 1) (by simp [Pi.single_apply]) (fun i hi => by
      rw [Pi.single_apply, if_neg]; rintro rfl; exact hj hi)
    have e : ∀ a, ∑ i, ∑ k, conj ((Pi.single j (1 : ℂ) : I → ℂ) i) * B a i k * (Pi.single j (1 : ℂ) : I → ℂ) k
        = B a j j := by
      intro a; simp [Pi.single_apply]
    simp only [e] at h
    have e2 : ∀ a, ∑ i, (if i = j then 0 else Complex.normSq (B a i j)) =
        ∑ i, Complex.normSq (B a i j) - Complex.normSq (B a j j) := by
      intro a
      rw [eq_sub_iff_add_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ j), if_pos rfl, add_zero,
        Finset.sum_ite_of_false (fun i hi => Finset.ne_of_mem_erase hi)]
      exact Finset.sum_erase_add _ _ (Finset.mem_univ j)
    simp only [e2, Finset.sum_sub_distrib, hTP j]
    linarith
  obtain ⟨j1, hj1⟩ : ∃ j, p j ≠ 0 := by
    by_contra h; push Not at h; simp [h] at hp1
  have hη : 0 ≤ η := le_trans (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => by
    split_ifs <;> simp [Complex.normSq_nonneg]) (hcol j1 hj1)
  -- step 2: averaging
  set N : ℝ := (Fintype.card (I → Fin 4) : ℝ)
  have hN : 0 < N := by positivity
  set sq : I → ℂ := fun i => ((Real.sqrt (p i) : ℝ) : ℂ)
  have hsq : ∀ i, sq i * sq i = (p i : ℂ) := fun i => by
    simp only [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (hp0 i)]
  set u : κ → I → I → ℂ := fun a i j => sq i * sq j * B a i j
  have hθ : ∀ θ : I → Fin 4, 1 - η ≤ ∑ a, Complex.normSq (∑ i, ∑ j, conj (z θ i) * z θ j * u a i j) := by
    intro θ
    have := hmin (fun i => sq i * z θ i) ?_ ?_
    · refine le_of_le_of_eq this (Finset.sum_congr rfl fun a _ => ?_)
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [u, sq, map_mul, Complex.conj_ofReal]; ring
    · have : ∀ i, Complex.normSq (sq i * z θ i) = p i := by
        intro i
        rw [map_mul]
        simp [sq, z, Complex.normSq_ofReal, Real.mul_self_sqrt (hp0 i)]
      simp [this, hp1]
    · intro i hi; simp [sq, hi]
  have hsum : N * (1 - η) ≤ ∑ a, N * (Complex.normSq (∑ i, (p i : ℂ) * B a i i) +
      ∑ i, ∑ j, if i = j then 0 else p i * p j * Complex.normSq (B a i j)) := by
    have h1 : ∑ θ : I → Fin 4, (1 - η) ≤ ∑ θ : I → Fin 4, ∑ a,
        Complex.normSq (∑ i, ∑ j, conj (z θ i) * z θ j * u a i j) := Finset.sum_le_sum fun θ _ => hθ θ
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm] at h1
    refine le_of_le_of_eq h1 (Finset.sum_congr rfl fun a _ => ?_)
    rw [avg]
    congr 2
    · congr 1; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [u]; rw [hsq]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs; · rfl
      simp only [u, sq, map_mul, Complex.normSq_ofReal, Real.mul_self_sqrt (hp0 i),
        Real.mul_self_sqrt (hp0 j)]
  rw [← Finset.mul_sum] at hsum
  have hsum' := le_of_mul_le_mul_left hsum hN
  rw [Finset.sum_add_distrib] at hsum'
  have : Nonempty I := ⟨j1⟩
  obtain ⟨j0, hj0⟩ := Finite.exists_max p
  have hoff : ∑ a, ∑ i, ∑ j, (if i = j then 0 else p i * p j * Complex.normSq (B a i j)) ≤ η / 2 := by
    have e : ∑ a, ∑ i, ∑ j, (if i = j then 0 else p i * p j * Complex.normSq (B a i j)) =
        ∑ j, p j * ∑ a, ∑ i, (if i = j then 0 else p i * Complex.normSq (B a i j)) := by
      rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    rw [e]
    have hb : ∀ j, p j * ∑ a, ∑ i, (if i = j then 0 else p i * Complex.normSq (B a i j)) ≤
        η * (p j * min (p j0) (1 - p j)) := by
      intro j
      by_cases hj : p j = 0
      · rw [hj]; simp
      have : ∑ a, ∑ i, (if i = j then 0 else p i * Complex.normSq (B a i j)) ≤
          min (p j0) (1 - p j) * η := by
        refine le_trans ?_ (mul_le_mul_of_nonneg_left (hcol j hj) (le_min (hp0 j0) ?_))
        · rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          split_ifs with hij
          · simp
          · exact mul_le_mul_of_nonneg_right (le_min (hj0 i) (pair_le p hp0 hp1 i j hij))
              (Complex.normSq_nonneg _)
        · have := Finset.single_le_sum (fun k _ => hp0 k) (Finset.mem_univ j)
          linarith
      calc _ ≤ p j * (min (p j0) (1 - p j) * η) := mul_le_mul_of_nonneg_left this (hp0 j)
        _ = _ := by ring
    calc _ ≤ ∑ j, η * (p j * min (p j0) (1 - p j)) := Finset.sum_le_sum fun j _ => hb j
      _ = η * ∑ j, p j * min (p j0) (1 - p j) := by rw [Finset.mul_sum]
      _ ≤ η * (1 / 2) := mul_le_mul_of_nonneg_left (pmin p hp0 hp1 j0 hj0) hη
      _ = η / 2 := by ring
  linarith

end X7mf

end

noncomputable section

namespace X7mf

open QAlgorithms

open scoped Matrix ComplexConjugate

theorem pd_tr {I : Type*} [Fintype I] (v : EuclideanSpace ℂ I) (K : Matrix I I ℂ) :
    (pureDensity v * (K * pureDensity v * Kᴴ)).trace =
      (∑ x, ∑ y, conj (v x) * K x y * v y) * conj (∑ x, ∑ y, conj (v x) * K x y * v y) := by
  have h1 : pureDensity v * (K * pureDensity v * Kᴴ) =
      Matrix.of fun i j => v i * ((∑ x, ∑ y, conj (v x) * K x y * v y) *
        ∑ y, conj (v y) * conj (K j y)) := by
    ext i j
    simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  rw [h1, Matrix.trace]
  simp only [Matrix.diag, Matrix.of_apply, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

end X7mf

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

theorem X7mf_main {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (P rho : Matrix I I ℂ)
    (hP : IsProjection P) (hrho : IsDensityMatrix rho) (hsupport : P * rho = rho)
    (E : Superop I I) (hE : IsChannel E) (eta : ℝ)
    (hminimum : ∀ psi : EuclideanSpace ℂ I, ‖psi‖ = 1 → act P psi = psi →
      1 - eta ≤ effectProb (pureDensity psi) (E (pureDensity psi))) :
    1 - (3 : ℝ) / 2 * eta ≤ fe rho E := by
  obtain ⟨m, K, hK, hEK⟩ := hE
  have hH : rho.IsHermitian := hrho.1.isHermitian
  set U : Matrix I I ℂ := (hH.eigenvectorUnitary : Matrix I I ℂ) with hUdef
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self _
  set p : I → ℝ := hH.eigenvalues with hpdef
  set D : Matrix I I ℂ := Matrix.diagonal (fun i => (p i : ℂ)) with hDdef
  have hspec : rho = U * D * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hp0 : ∀ i, 0 ≤ p i := fun i => hrho.1.eigenvalues_nonneg i
  have hp1 : ∑ i, p i = 1 := by
    have h := hH.trace_eq_sum_eigenvalues
    rw [hrho.2] at h
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_one]
    exact h.symm
  set B : Fin m → Matrix I I ℂ := fun a => star U * K a * U with hBdef
  rw [X7P29_fe rho E K hEK]
  have hfe : ∀ a, (K a * rho).trace = ∑ i, (p i : ℂ) * B a i i := by
    intro a
    rw [hspec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag, hDdef, Matrix.mul_diagonal, hBdef, Matrix.mul_assoc]
    ring
  simp only [hfe]
  have hTP : ∀ i, ∑ a, ∑ j, Complex.normSq (B a j i) = 1 := by
    intro i
    have hsum : ∑ a, star (B a) * B a = 1 := by
      have : ∀ a, star (B a) * B a = star U * (star (K a) * K a) * U := by
        intro a
        simp only [hBdef]
        rw [star_mul, star_mul, star_star]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc U (star U), hU2, Matrix.one_mul]
      have hK' : ∑ j, star (K j) * K j = 1 := hK
      simp only [this, ← Finset.sum_mul, ← Finset.mul_sum]
      rw [hK', Matrix.mul_one, hU1]
    have := congrFun (congrFun hsum i) i
    rw [Matrix.sum_apply, Matrix.one_apply_eq] at this
    apply Complex.ofReal_injective
    push_cast
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.star_apply, ← Complex.mul_conj, mul_comm]
    rfl
  refine X7mf.core (fun a => B a) p hp0 hp1 hTP eta ?_
  intro c hc hsupp
  set v : I → ℂ := U *ᵥ c with hvdef
  have hdot : ∀ M : Matrix I I ℂ, ∑ x, ∑ y, conj (v x) * M x y * v y =
      ∑ i, ∑ j, conj (c i) * (star U * M * U) i j * c j := by
    intro M
    have e1 : ∀ w : I → ℂ, ∀ N : Matrix I I ℂ, ∑ x, ∑ y, conj (w x) * N x y * w y = star w ⬝ᵥ (N *ᵥ w) := by
      intro w N
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e1, e1, hvdef, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hnorm : ∑ x, Complex.normSq (v x) = 1 := by
    have h := hdot 1
    simp only [Matrix.mul_one, hU1] at h
    apply Complex.ofReal_injective
    have e : ∀ w : I → ℂ, ((∑ x, Complex.normSq (w x) : ℝ) : ℂ) = ∑ x, ∑ y, conj (w x) * (1 : Matrix I I ℂ) x y * w y := by
      intro w
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [Matrix.one_apply, Complex.normSq_eq_conj_mul_self]
    rw [e, h, ← e, hc, Complex.ofReal_one]
  set psi : EuclideanSpace ℂ I := WithLp.toLp 2 v with hpsi
  have hpsi1 : ‖psi‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [hpsi, PiLp.toLp_apply, Complex.sq_norm, hnorm, Real.sqrt_one]
  have hact : act P psi = psi := by
    have hv : v = rho *ᵥ (U *ᵥ fun i => c i / (p i : ℂ)) := by
      have hrU : rho * U = U * D := by
        rw [hspec, Matrix.mul_assoc, Matrix.mul_assoc, hU1, Matrix.mul_one]
      rw [Matrix.mulVec_mulVec, hrU, ← Matrix.mulVec_mulVec, hDdef, hvdef]
      congr 1
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases h : p i = 0
      · simp [hsupp i h]
      · field_simp
    show WithLp.toLp 2 (P *ᵥ v) = WithLp.toLp 2 v
    rw [hv, Matrix.mulVec_mulVec, hsupport]
  have h := hminimum psi hpsi1 hact
  refine le_of_le_of_eq h ?_
  rw [effectProb, hEK, krausApply, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [X7mf.pd_tr, Complex.mul_conj, Complex.ofReal_re]
  congr 1
  simp only [hpsi, PiLp.toLp_apply]
  exact hdot (K a)

end QAlgorithms.Papers.Independent.Gap48.P29

end

open QAlgorithms.Papers.Independent.Gap48.P29 QAlgorithms in
open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection) in
theorem solution {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (P rho : Matrix I I ℂ) (hP : IsProjection P)
    (hrho : IsDensityMatrix rho) (hsupport : P * rho = rho)
    (E : Superop I I) (hE : IsChannel E) (eta : ℝ)
    (hminimum : ∀ psi : EuclideanSpace ℂ I, ‖psi‖ = 1 → act P psi = psi →
      1 - eta ≤ effectProb (pureDensity psi) (E (pureDensity psi))) :
    1 - (3 : ℝ) / 2 * eta ≤ fe rho E :=
  X7mf_main P rho hP hrho hsupport E hE eta hminimum
