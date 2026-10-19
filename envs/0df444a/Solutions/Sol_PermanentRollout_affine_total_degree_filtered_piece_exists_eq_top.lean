-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_filtered_piece_exists_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/59f56778-dbf5-473d-8dcc-bffa5c922bbf

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    [Module.Finite ℂ (MvPolynomial ι ℂ ⧸ I)] :
    ∃ n : ℕ, affineTotalDegreeFilteredPiece I n = ⊤ := by
  classical
  let b := Module.finBasis ℂ (MvPolynomial ι ℂ ⧸ I)
  let p : Fin (Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I)) →
      MvPolynomial ι ℂ := fun i =>
    (Ideal.Quotient.mk_surjective (I := I) (b i)).choose
  have hp (i : Fin (Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I))) :
      Ideal.Quotient.mk I (p i) = b i :=
    (Ideal.Quotient.mk_surjective (I := I) (b i)).choose_spec
  let n : ℕ := Finset.univ.sup fun i => (p i).totalDegree
  refine ⟨n, top_unique ?_⟩
  rw [← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply (affine_total_degree_filtered_piece_mem_iff I n (b i)).mpr
  refine ⟨p i, ?_, hp i⟩
  change (p i).totalDegree ≤
    (Finset.univ : Finset
      (Fin (Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I)))).sup
        (fun j => (p j).totalDegree)
  exact Finset.le_sup
    (s := (Finset.univ : Finset
      (Fin (Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I)))))
    (f := fun j => (p j).totalDegree) (Finset.mem_univ i)
end PermanentRollout
