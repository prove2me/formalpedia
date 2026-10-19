-- Prove2me | solution 1 for PermanentRollout.blockIncidence_adjoin_column_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/95d1f350-d72e-489b-ab1c-7b85f790dfb7

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (b t s d : ℕ) :
    letI := blockIncidenceBaseAlgebra b t s d
    Algebra.adjoin
      (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)
      (Set.range fun coordinate : BlockIncidenceColumn b t s =>
        Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
          (MvPolynomial.X (coordinate.1, Sum.inr coordinate.2))) =
      (⊤ : Subalgebra
        (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)
        (BlockIncidenceCoordinateRing b t s d)) := by
  classical
  letI := blockIncidenceBaseAlgebra b t s d
  let T : Subalgebra
      (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)
      (BlockIncidenceCoordinateRing b t s d) :=
    Algebra.adjoin _
      (Set.range fun coordinate : BlockIncidenceColumn b t s =>
        Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
          (MvPolynomial.X (coordinate.1, Sum.inr coordinate.2)))
  apply top_unique
  intro a ha
  obtain ⟨f, rfl⟩ :=
    Ideal.Quotient.mk_surjective (I := blockIncidenceIdeal b t s d) a
  clear ha
  change Ideal.Quotient.mk (blockIncidenceIdeal b t s d) f ∈ T
  induction f using MvPolynomial.induction_on with
  | C c =>
      let basec : MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ :=
        MvPolynomial.C c
      have heq : algebraMap
          (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)
          (BlockIncidenceCoordinateRing b t s d) basec =
            Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
              (MvPolynomial.C c) := by
        change blockIncidenceBaseProjection b t s d basec = _
        simpa [basec, blockIncidenceBaseProjection] using
          (Ideal.Quotient.mk_algebraMap (R₁ := ℂ)
            (blockIncidenceIdeal b t s d) c).symm
      rw [← heq]
      exact T.algebraMap_mem basec
  | add f g hf hg =>
      simpa using T.add_mem hf hg
  | mul_X f coordinate hf =>
      rw [map_mul]
      apply T.mul_mem hf
      rcases coordinate with ⟨h, coordinate⟩
      cases coordinate with
      | inl block =>
          let baseblock : MvPolynomial
              (BlockIncidenceBaseIndex b t s d) ℂ :=
            MvPolynomial.X (h, Sum.inl block)
          have heq : algebraMap
              (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)
              (BlockIncidenceCoordinateRing b t s d) baseblock =
                Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
                  (MvPolynomial.X (h, Sum.inl block)) := by
            change blockIncidenceBaseProjection
              b t s d baseblock = _
            simp [baseblock, blockIncidenceBaseProjection]
          rw [← heq]
          exact T.algebraMap_mem baseblock
      | inr coordinate =>
          exact Algebra.subset_adjoin ⟨(h, coordinate), rfl⟩
end PermanentRollout
