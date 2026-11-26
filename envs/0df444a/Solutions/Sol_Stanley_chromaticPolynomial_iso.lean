-- Prove2me | solution 1 for Stanley.chromaticPolynomial_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:55.12584+00:00
-- url     : https://prove2.me/submissions/690964ff-b56d-4b25-8cc6-4069b57afb27

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
public import Definitions.Def_Stanley_Convolution
public import Theorems.Thm_Stanley_eval_card
public import Theorems.Thm_Stanley_polynomial_ext_nat

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)
open Classical
namespace Stanley
theorem _root_.solution {W : Type*} [Fintype W] (H : SimpleGraph W) (e : G ≃g H) :
    chromaticPolynomial G = chromaticPolynomial H := by
  apply polynomial_ext_nat
  intro n
  have h := Fintype.card_congr (SimpleGraph.coloringCongr e (Equiv.refl (Fin n)))
  simpa [← eval_card] using congrArg (fun k : ℕ => (k : ℤ)) h
end Stanley
