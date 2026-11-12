-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P30.linear_preimage_sizes
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:48:32.824182+00:00
-- url     : https://prove2.me/submissions/2faa00ff-ae73-48da-a649-43066e9d4ee7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

variable {X Y Z M U V A B C : Type*}

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M]

variable [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C]

attribute [local instance] Classical.propDecidable

theorem solution {K : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (f : U →ₗ[K] V) (honto : Function.Surjective f) (v : V) :
    (Fintype.card {u : U // f u = v} : ℝ) =
      (Fintype.card U : ℝ) / (Fintype.card V : ℝ) := by
  have hker : ∀ w : V, Nat.card {u : U // f u = w} = Nat.card (LinearMap.ker f) := by
    intro w
    obtain ⟨uw, huw⟩ := honto w
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1 - uw, by rw [LinearMap.mem_ker, map_sub, x.2, huw, sub_self]⟩
        invFun := fun y => ⟨y.1 + uw, by rw [map_add, LinearMap.mem_ker.1 y.2, huw, zero_add]⟩
        left_inv := fun x => by ext; simp
        right_inv := fun y => by ext; simp }
  have htot : Nat.card U = Nat.card V * Nat.card (LinearMap.ker f) := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
    simp only [hker]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card (α := V)]
  have hV : (Nat.card V : ℝ) ≠ 0 := by
    have : 0 < Nat.card V := Nat.card_pos (α := V)
    exact_mod_cast this.ne'
  simp only [← Nat.card_eq_fintype_card]
  rw [hker v, htot, Nat.cast_mul, mul_div_cancel_left₀ _ hV]

end
