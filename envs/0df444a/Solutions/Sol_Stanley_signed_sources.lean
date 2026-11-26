-- Prove2me | solution 1 for Stanley.signed_sources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:56.632317+00:00
-- url     : https://prove2.me/submissions/42725c79-eb2e-4435-9862-6e6520dfcab7

module
public import Definitions.Def_Stanley_Convolution
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Stanley_NegOne
public import Theorems.Thm_Stanley_orientationCount_induce_univ
public import Theorems.Thm_Stanley_alternating_independent
public import Theorems.Thm_Stanley_chromaticPolynomial_induce_univ
attribute [local simp] Stanley.chromaticPolynomial_induce_univ


attribute [local simp] Stanley.orientationCount_induce_univ

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
open Classical
namespace Stanley
theorem _root_.solution [Nonempty V] :
    ∑ s : Finset V, (if Independent G (s : Set V) then
      (-1 : ℤ) ^ Fintype.card ↥((s : Set V)ᶜ) *
        orientationCount (G.induce (s : Set V)ᶜ) else 0) = 0 := by
  classical
  have hsign (s : Finset V) :
      (-1 : ℤ) ^ Fintype.card V * (-1 : ℤ) ^ s.card =
        (-1 : ℤ) ^ Fintype.card ↥((s : Set V)ᶜ) := by
    have hc : Fintype.card ↥((s : Set V)ᶜ) + s.card = Fintype.card V := by
      have hcomp : Fintype.card ↥((s : Set V)ᶜ) = Fintype.card V - s.card := by
        calc
          _ = Fintype.card {x : V // x ∉ (s : Set V)} :=
            Fintype.card_congr (Equiv.refl _)
          _ = Fintype.card V - s.card := by
            rw [Fintype.card_subtype_compl]
            congr 1
            exact Fintype.card_coe s
      rw [hcomp]
      exact Nat.sub_add_cancel (Finset.card_le_univ s)
    rw [← pow_add]
    have hn : Fintype.card V + s.card = 2 * s.card +
        Fintype.card ↥((s : Set V)ᶜ) := by omega
    rw [hn, pow_add, pow_mul]
    norm_num
  calc
    _ = (-1 : ℤ) ^ Fintype.card V *
        ∑ s : Finset V, (if Independent G (s : Set V) then
          (-1 : ℤ) ^ s.card * orientationCount (G.induce (s : Set V)ᶜ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : Independent G (s : Set V) <;> simp [hs, ← mul_assoc, hsign]
    _ = 0 := by rw [alternating_independent G, mul_zero]
end Stanley
