-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints.finitePrimeAvoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:22.234199+00:00
-- url     : https://prove2.me/submissions/67cec79b-ebc9-44e8-afd2-0fafad9629d3

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_PolynomialMaximalPoints

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
theorem _root_.solution {R : Type*} [CommRing R] [Nontrivial R]
    (M : Ideal R) [M.IsMaximal] (S : Set (Ideal R)) (hS : S.Finite)
    (hprime : ∀ I ∈ S, I.IsPrime) (houtside : M ∉ S) :
    ∃ g ∈ M, ∀ I ∈ S, g ∉ I := by
  have hn : ¬((M : Set R) ⊆ ⋃ I ∈ S, (I : Set R)) := by
    intro hs
    apply houtside
    exact (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite hS ⊥ ⊥
      (fun I hI _ _ => hprime I hI) bot_ne_top bot_ne_top).mp hs
  obtain ⟨g,hg,hgu⟩ := Set.not_subset.mp hn
  refine ⟨g,hg,fun I hI hgi => hgu ?_⟩
  exact Set.mem_iUnion.mpr ⟨I,Set.mem_iUnion.mpr ⟨hI,hgi⟩⟩
end QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
