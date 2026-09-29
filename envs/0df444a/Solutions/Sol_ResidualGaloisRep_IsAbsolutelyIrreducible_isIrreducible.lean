-- Prove2me | solution 1 for ResidualGaloisRep.IsAbsolutelyIrreducible.isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/005c9f79-166f-5527-9595-333a37ef193b

import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_Representation_isIrreducible_of_span_range_eq_top
import Theorems.Thm_ResidualGaloisRep_isIrreducible_iff_representationIsIrreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_IsAbsolutelyIrreducible_isIrreducible

set_option autoImplicit false

theorem solution {k : Type} [Field k] {ρ : ResidualGaloisRep k}
    (h : ρ.IsAbsolutelyIrreducible) : ρ.IsIrreducible := by
  haveI : Nontrivial ρ.V := Module.nontrivial_of_finrank_eq_succ ρ.finrank_eq
  exact (ResidualGaloisRep.isIrreducible_iff_representationIsIrreducible ρ).mpr
    (Representation.isIrreducible_of_span_range_eq_top ρ.ρ
      ((ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρ).mp h))

#print axioms solution

end S_ResidualGaloisRep_IsAbsolutelyIrreducible_isIrreducible
end P2MW
export P2MW.S_ResidualGaloisRep_IsAbsolutelyIrreducible_isIrreducible (solution)
