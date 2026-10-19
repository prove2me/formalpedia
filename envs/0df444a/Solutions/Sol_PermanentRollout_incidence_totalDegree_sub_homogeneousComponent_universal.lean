-- Prove2me | solution 1 for PermanentRollout.incidence_totalDegree_sub_homogeneousComponent_universal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/522fa5a5-0ef5-4c0e-b675-2feb212ed766

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {σ B : Type*} [CommRing B]
    (f : MvPolynomial σ B) {q : ℕ}
    (hf : f.totalDegree ≤ q) :
    (f - MvPolynomial.homogeneousComponent q f).totalDegree ≤ q - 1 := by
  classical
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro m hm
  have hmne :
      MvPolynomial.coeff m
        (f - MvPolynomial.homogeneousComponent q f) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hmq : m.degree ≠ q := by
    intro heq
    apply hmne
    simp [MvPolynomial.coeff_sub,
      MvPolynomial.coeff_homogeneousComponent, heq]
  have hmcoeff : MvPolynomial.coeff m f ≠ 0 := by
    intro hzero
    apply hmne
    simp [MvPolynomial.coeff_sub,
      MvPolynomial.coeff_homogeneousComponent, hmq, hzero]
  have hmle : m.degree ≤ q :=
    (MvPolynomial.le_totalDegree
      (MvPolynomial.mem_support_iff.mpr hmcoeff)).trans hf
  change m.degree ≤ q - 1
  omega
end PermanentRollout
