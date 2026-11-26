-- Prove2me | solution 1 for Stanley.orientationCount_induce_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:04.8801+00:00
-- url     : https://prove2.me/submissions/30ea2222-8990-4dd9-ba4c-f29d8076d66e

module
public import Definitions.Def_Stanley_Convolution
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Stanley_NegOne
public import Theorems.Thm_Stanley_chromaticPolynomial_induce_univ
attribute [local simp] Stanley.chromaticPolynomial_induce_univ



set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution :
    orientationCount (G.induce Set.univ) = orientationCount G := by
  simp only [orientationCount, Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_congr
    (AcyclicOrientation.mapEquiv (SimpleGraph.induceUnivIso G))
end Stanley
