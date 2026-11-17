-- Prove2me | solution 1 for PermInvCC.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T14:35:37.705343+00:00
-- url     : https://prove2.me/submissions/68d2d767-e643-4e10-a48b-1b08f1944e8b

import Mathlib

theorem solution (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) (u v : Fin n → ZMod 2) (huv : u ≠ v) :
    ((Finset.univ.filter fun H : Matrix (Fin m) (Fin n) (ZMod 2) =>
        H.mulVec u = H.mulVec v).card : ℝ) /
      (Fintype.card (Matrix (Fin m) (Fin n) (ZMod 2)) : ℝ) = 1 / 2 ^ m := by
  classical
  set w : Fin n → ZMod 2 := u - v with hw
  have hwne : w ≠ 0 := by
    rw [hw, sub_ne_zero]
    exact huv
  obtain ⟨j, hj⟩ : ∃ j : Fin n, w j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    exact hwne (funext h)
  have htwo : ∀ t : ZMod 2, (t = 0 ↔ t + 1 ≠ 0) := by decide
  have htwo2 : ∀ t : ZMod 2, (t ≠ 0 ↔ t + 1 = 0) := by decide
  have hz1 : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
  have hj1 : w j = 1 := hz1 (w j) hj
  set e : Fin n → ZMod 2 := fun i => if i = j then 1 else 0 with he
  have hew : e ⬝ᵥ w = 1 := by
    simp only [dotProduct, he]
    rw [Finset.sum_eq_single j]
    · simp [hj1]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hadd : ∀ x : Fin n → ZMod 2, (x + e) ⬝ᵥ w = x ⬝ᵥ w + 1 := by
    intro x
    rw [add_dotProduct, hew]
  have hmem : ∀ x : Fin n → ZMod 2, x ⬝ᵥ w = 0 → (x + e) ⬝ᵥ w ≠ 0 := by
    intro x hx
    rw [hadd, hx]
    exact (htwo 0).mp rfl
  have hmem' : ∀ x : Fin n → ZMod 2, x ⬝ᵥ w ≠ 0 → (x + e) ⬝ᵥ w = 0 := by
    intro x hx
    rw [hadd, hz1 (x ⬝ᵥ w) hx]
    decide
  have hee : e + e = 0 := by
    funext i
    simp only [Pi.add_apply, he, Pi.zero_apply]
    split_ifs with h
    · decide
    · decide
  have hbij : (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ⬝ᵥ w = 0)).card =
      (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ⬝ᵥ w ≠ 0)).card := by
    apply Finset.card_bij' (fun x _ => x + e) (fun x _ => x + e)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hmem x hx
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hmem' x hx
    · intro x _
      show x + e + e = x
      rw [add_assoc, hee, add_zero]
    · intro x _
      show x + e + e = x
      rw [add_assoc, hee, add_zero]
  have hsumK : (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ⬝ᵥ w = 0)).card +
      (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ⬝ᵥ w ≠ 0)).card = 2 ^ n := by
    rw [Finset.card_filter_add_card_filter_not (fun x : Fin n → ZMod 2 => x ⬝ᵥ w = 0),
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hK : (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ⬝ᵥ w = 0)).card = 2 ^ (n - 1) := by
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
      ring
    omega
  have hpred : ∀ H : Matrix (Fin m) (Fin n) (ZMod 2),
      (H.mulVec u = H.mulVec v ↔ H.mulVec w = 0) := by
    intro H
    rw [hw, Matrix.mulVec_sub, sub_eq_zero]
  have hq : ∀ H : Fin m → Fin n → ZMod 2,
      (Matrix.mulVec H w = 0 ↔ ∀ i, H i ⬝ᵥ w = 0) := by
    intro H
    constructor
    · intro h i
      have h2 := congrFun h i
      simpa [Matrix.mulVec] using h2
    · intro h
      funext i
      have h2 := h i
      simpa [Matrix.mulVec] using h2
  have hK' : Fintype.card {x : Fin n → ZMod 2 // x ⬝ᵥ w = 0} = 2 ^ (n - 1) := by
    rw [Fintype.card_subtype]
    exact hK
  have hScard : (Finset.univ.filter (fun H : Matrix (Fin m) (Fin n) (ZMod 2) =>
      H.mulVec u = H.mulVec v)).card = (2 ^ (n - 1)) ^ m := by
    rw [Finset.filter_congr (fun H _ => hpred H)]
    have h1 : (Finset.univ.filter (fun H : Matrix (Fin m) (Fin n) (ZMod 2) =>
        H.mulVec w = 0)).card = (Fintype.card {x : Fin n → ZMod 2 // x ⬝ᵥ w = 0}) ^ m := by
      rw [← Fintype.card_subtype (fun H : Matrix (Fin m) (Fin n) (ZMod 2) => H.mulVec w = 0)]
      change Fintype.card {H : Fin m → Fin n → ZMod 2 // Matrix.mulVec H w = 0} =
        (Fintype.card {x : Fin n → ZMod 2 // x ⬝ᵥ w = 0}) ^ m
      rw [Fintype.card_congr (Equiv.subtypeEquivRight hq)]
      have hcard : Fintype.card {x : Fin m → Fin n → ZMod 2 // ∀ i, x i ⬝ᵥ w = 0} =
          Fintype.card ((i : Fin m) → {x : Fin n → ZMod 2 // x ⬝ᵥ w = 0}) :=
        Fintype.card_congr (Equiv.subtypePiEquivPi
          (β := fun (_ : Fin m) => (Fin n → ZMod 2))
          (p := fun (_ : Fin m) (x : Fin n → ZMod 2) => x ⬝ᵥ w = 0))
      rw [hcard]
      rw [Fintype.card_pi]
      simp [Finset.prod_const, Fintype.card_fin]
    rw [h1, hK']
  have htotal : Fintype.card (Matrix (Fin m) (Fin n) (ZMod 2)) = 2 ^ (m * n) := by
    change Fintype.card (Fin m → Fin n → ZMod 2) = 2 ^ (m * n)
    rw [Fintype.card_fun, Fintype.card_fun]
    simp only [Fintype.card_fin, ZMod.card]
    rw [← pow_mul, Nat.mul_comm]
  rw [hScard, htotal]
  push_cast
  have hexp : m * n = (n - 1) * m + m := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    ring
  rw [← pow_mul, hexp, pow_add]
  field_simp
