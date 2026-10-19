-- Prove2me | solution 1 for PermanentRollout.homogeneousIdeal_radical_eq_idealOfVars_of_vertex_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/442d3a6f-5dde-4de6-ac44-aac8bd668c36

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousIdeal_minimalPrime_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousPrime_le_idealOfVars

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution {t : ℕ}
    (I : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (hvertex : MvPolynomial.idealOfVars (Fin t) ℂ ∈ I.minimalPrimes) :
    I.radical = MvPolynomial.idealOfVars (Fin t) ℂ := by
  rw [← I.sInf_minimalPrimes]
  apply le_antisymm
  · exact sInf_le hvertex
  · apply le_sInf
    intro P hP
    have hPhomogeneous :=
      homogeneousIdeal_minimalPrime_isHomogeneous I P hI hP
    have hPvertex : P ≤ MvPolynomial.idealOfVars (Fin t) ℂ :=
      homogeneousPrime_le_idealOfVars P hP.isPrime hPhomogeneous
    exact hvertex.2 ⟨hP.isPrime, hP.le⟩ hPvertex
end PermanentRollout
