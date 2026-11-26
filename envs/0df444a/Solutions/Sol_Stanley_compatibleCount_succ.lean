-- Prove2me | solution 1 for Stanley.compatibleCount_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:38.516276+00:00
-- url     : https://prove2.me/submissions/637dd11d-c519-435c-a3df-e7f05b091fbe

module
public import Definitions.Def_Stanley_NegOne
public import Definitions.Def_Stanley_Compatible
public import Theorems.Thm_Stanley_chromaticPolynomial_induce_univ
public import Theorems.Thm_Stanley_orientationCount_induce_univ
attribute [local simp] Stanley.chromaticPolynomial_induce_univ
attribute [local simp] Stanley.orientationCount_induce_univ



set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset
variable {V : Type*} (G : SimpleGraph V)
open Classical
namespace Stanley
theorem _root_.solution [Fintype V] (k : ℕ) :
    compatibleCount G (k + 1) =
      ∑ s : Finset V, orientationCount (G.induce (s : Set V)) *
        compatibleCount (G.induce (s : Set V)ᶜ) k := by
  classical
  have h := Fintype.card_congr (CompatiblePair.splitEquiv G k)
  rw [Fintype.card_sigma] at h
  simpa [compatibleCount, orientationCount, Nat.card_eq_fintype_card,
    Fintype.card_prod, Nat.cast_sum, Nat.cast_mul] using
    congrArg (fun n : ℕ => (n : ℤ)) h.symm
end Stanley
