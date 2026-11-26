-- Prove2me | solution 1 for Stanley.eval_one_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:06.727021+00:00
-- url     : https://prove2.me/submissions/abcde812-b8b3-4a3a-afe1-6115856914b7

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
public import Definitions.Def_Stanley_Convolution
public import Theorems.Thm_Stanley_eval_card
public import Theorems.Thm_Stanley_chromaticPolynomial_induce_univ
attribute [local simp] Stanley.chromaticPolynomial_induce_univ

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)
open Classical
omit [Fintype V]
namespace Stanley
theorem _root_.solution (s : Finset V) :
    (chromaticPolynomial (G.induce (s : Set V))).eval 1 =
      if Independent G (s : Set V) then 1 else 0 := by
  classical
  have hc := eval_card (G.induce (s : Set V)) (Fin 1)
  by_cases hs : Independent G (s : Set V)
  · let c : (G.induce (s : Set V)).Coloring (Fin 1) :=
      Coloring.mk (fun _ => 0) (fun {u v} h => (hs u.val u.property v.val v.property h).elim)
    have : Nonempty ((G.induce (s : Set V)).Coloring (Fin 1)) := ⟨c⟩
    let : Unique ((G.induce (s : Set V)).Coloring (Fin 1)) :=
      { default := c, uniq := fun _ => Subsingleton.elim _ _ }
    simpa [hs] using hc
  · have : IsEmpty ((G.induce (s : Set V)).Coloring (Fin 1)) := ⟨fun c => hs (by
      intro u hu v hv h
      exact c.valid (show (G.induce (s : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ from h)
        (Subsingleton.elim _ _))⟩
    simpa [hs] using hc
end Stanley
