-- Prove2me | solution 1 for ValuationSubring.eq_zero_of_valuation_eval2_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/05bfe6ac-7262-5e20-9916-223adc258f17

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_eq_zero_of_valuation_eval2_lt_one

set_option autoImplicit false

universe u v

theorem solution
    {k : Type u} {K : Type v} [Field k] [Field K] (c : k →+* K) (O : ValuationSubring K)
    (hc : ∀ x : k, c x ∈ O) {d : ℕ} (g : Fin d → K) (hg : ∀ i, g i ∈ O)
    (hind :
      letI : Algebra k (IsLocalRing.ResidueField O) :=
        ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
      AlgebraicIndependent k (fun i => IsLocalRing.residue O ⟨g i, hg i⟩))
    (Q : MvPolynomial (Fin d) k) (hQ : O.valuation (Q.eval₂ c g) < 1) : Q = 0 := by
  classical
  letI instAlg : Algebra k (IsLocalRing.ResidueField O) :=
    ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
  let cO : k →+* ↥O := c.codRestrict O.toSubring hc
  let gO : Fin d → ↥O := fun j => ⟨g j, hg j⟩
  have hev : Q.eval₂ c g = algebraMap ↥O K (Q.eval₂ cO gO) := by
    rw [MvPolynomial.eval₂_comp_left]
    rfl
  rw [hev] at hQ
  have hmem : Q.eval₂ cO gO ∈ IsLocalRing.maximalIdeal ↥O := (O.valuation_lt_one_iff _).mpr hQ
  have hres : IsLocalRing.residue ↥O (Q.eval₂ cO gO) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [MvPolynomial.eval₂_comp_left] at hres
  rw [algebraicIndependent_iff] at hind
  apply hind Q
  rw [MvPolynomial.aeval_def]
  exact hres

end S_ValuationSubring_eq_zero_of_valuation_eval2_lt_one
end P2MW
export P2MW.S_ValuationSubring_eq_zero_of_valuation_eval2_lt_one (solution)
