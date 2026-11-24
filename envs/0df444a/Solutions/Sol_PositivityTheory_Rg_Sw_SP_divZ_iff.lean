-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.divZ_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:41.021976+00:00
-- url     : https://prove2.me/submissions/8c4be46a-6ddf-4031-b3d1-2331b0da3ca5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (i : ℕ) (Q : Fm n) : DivZ i Q ↔ ∃ R : Fm n, Q = R * wz n i := by
  constructor
  · intro h
    have hmem : Q ∈ Ideal.map (MvPolynomial.C : Polynomial ℂ →+* Fm n)
        (Ideal.span {(Polynomial.X ^ i : Polynomial ℂ)}) := by
      rw [MvPolynomial.mem_map_C_iff]
      intro e
      exact Ideal.mem_span_singleton.mpr (h e)
    rw [Ideal.map_span, Set.image_singleton] at hmem
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨a, ha.symm⟩
  · rintro ⟨R, rfl⟩ e
    rw [mul_comm, MvPolynomial.coeff_C_mul]
    exact dvd_mul_right _ _
end PositivityTheory.Rg.Sw.SP
