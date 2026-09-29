-- Prove2me | solution 1 for ResidualGaloisRep.IsAbsolutelyIrreducible.baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f4da2f22-19e3-5dcc-aa0a-38361e1f7d9f

import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_Representation_span_range_baseChange_eq_top_iff
import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong

open Module LinearMap

theorem solution
    {k k' : Type} [Field k] [Field k'] {ρ : ResidualGaloisRep k}
    (hρ : ρ.IsAbsolutelyIrreducible) (φ : k →+* k') :
    (ρ.baseChangeAlong φ).IsAbsolutelyIrreducible := by
  letI : Algebra k k' := φ.toAlgebra
  have hspan := (ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρ).mp hρ
  have h2 := (Representation.span_range_baseChange_eq_top_iff (K := k') ρ.ρ).mpr hspan
  exact (ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top (ρ.baseChangeAlong φ)).mpr h2

end S_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong
end P2MW
export P2MW.S_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong (solution)
