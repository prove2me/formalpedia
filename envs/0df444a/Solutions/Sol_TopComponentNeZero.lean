-- Prove2me | solution 1 for TopComponentNeZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:35:20.758838+00:00
-- url     : https://prove2.me/submissions/bc729f8a-344c-4557-a8e4-52fdc9a7be4b

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_TopComponentNeZero

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {σ R : Type*} [CommSemiring R]
    {P : MvPolynomial σ R} (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  classical
  have hsupp : P.support.Nonempty := by
    rwa [MvPolynomial.support_nonempty]
  obtain ⟨d, hd, hdeg⟩ :=
    Finset.exists_mem_eq_sup P.support hsupp (fun s => s.sum fun _ e => e)
  have hbridge : Finsupp.degree d = d.sum (fun _ e => e) := rfl
  have hcoeff : (homogeneousComponent P.totalDegree P).coeff d = P.coeff d := by
    rw [MvPolynomial.coeff_homogeneousComponent, if_pos]
    rw [hbridge, MvPolynomial.totalDegree, hdeg]
  intro hzero
  rw [hzero, MvPolynomial.coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.1 hd) hcoeff.symm
