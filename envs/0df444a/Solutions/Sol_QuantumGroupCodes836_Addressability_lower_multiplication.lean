-- Prove2me | solution 1 for QuantumGroupCodes836.Addressability.lower_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T18:55:07.048275+00:00
-- url     : https://prove2.me/submissions/52b297cf-1aa3-4079-9086-6060a6cb94fa

import Definitions.Def_QuantumGroupCodes836_Addressability_Linear

set_option autoImplicit false

namespace QuantumGroupCodes836.Addressability

theorem schurPower_eq_span {F : Type} [Field F] {n : ℕ} (C : Code F (Fin n)) (k : ℕ) :
    schurPower C k = Submodule.span F {v | ∃ c : Fin k → C, v = fun j => ∏ a, (c a : Fin n → F) j} := by
  unfold schurPower
  by_cases hk : k = 2
  · subst hk
    simp only [if_true]
    unfold TwoFoldOPI.schurSquare
    congr 1
    ext x
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      refine ⟨![⟨u, hu⟩, ⟨v, hv⟩], ?_⟩
      ext j
      simp [Fin.prod_univ_two]
    · rintro ⟨c, rfl⟩
      refine ⟨c 0, (c 0).2, c 1, (c 1).2, ?_⟩
      ext j
      simp [Fin.prod_univ_two]
  · simp [hk]

theorem schurPower_mono_succ {F : Type} [Field F] {n : ℕ} (C : Code F (Fin n))
    (h1 : (1 : Fin n → F) ∈ C) (k : ℕ) : schurPower C k ≤ schurPower C (k + 1) := by
  rw [schurPower_eq_span, schurPower_eq_span]
  apply Submodule.span_mono
  rintro v ⟨c, rfl⟩
  refine ⟨Fin.snoc c ⟨1, h1⟩, ?_⟩
  ext j
  simp [Fin.prod_univ_castSucc]

theorem schurPower_mono {F : Type} [Field F] {n : ℕ} (C : Code F (Fin n))
    (h1 : (1 : Fin n → F) ∈ C) {a m : ℕ} (h : a ≤ m) : schurPower C a ≤ schurPower C m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (schurPower_mono_succ C h1 _)

end QuantumGroupCodes836.Addressability

open QuantumGroupCodes836.Addressability in
theorem solution {F : Type} [Field F] [Fintype F] {n m : ℕ}
    (C : Code F (Fin n)) (u : Fin n → F)
    (hm : 1 ≤ m) (h : MultiplicationWith C m u) (h1 : (1 : Fin n → F) ∈ C) :
    ∀ a : ℕ, 1 ≤ a → a ≤ m → MultiplicationWith C a u := by
  intro a _ ham
  exact ⟨h.1, fun v hv => h.2 v (QuantumGroupCodes836.Addressability.schurPower_mono C h1 ham hv)⟩
