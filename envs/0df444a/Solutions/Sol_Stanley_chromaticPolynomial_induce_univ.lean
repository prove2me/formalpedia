-- Prove2me | solution 1 for Stanley.chromaticPolynomial_induce_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:29.01137+00:00
-- url     : https://prove2.me/submissions/b1ed9438-d3b9-4644-bc28-cd9d106366a1

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
public import Definitions.Def_Stanley_Convolution
public import Theorems.Thm_Stanley_chromaticPolynomial_iso

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution :
    chromaticPolynomial (G.induce Set.univ) = chromaticPolynomial G :=
  chromaticPolynomial_iso _ _ (SimpleGraph.induceUnivIso G)
end Stanley
