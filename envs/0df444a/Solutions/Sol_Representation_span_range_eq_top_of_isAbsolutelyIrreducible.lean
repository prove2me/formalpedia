-- Prove2me | solution 1 for Representation.span_range_eq_top_of_isAbsolutelyIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a800fa44-0ff7-57cc-847d-d30df561e59a

import Mathlib
import Definitions.Def_Representation_AbsolutelyIrreducible
import Theorems.Thm_Representation_span_range_eq_top_of_isIrreducible
import Theorems.Thm_Representation_span_range_baseChange_eq_top_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_span_range_eq_top_of_isAbsolutelyIrreducible

open scoped TensorProduct

universe u v

theorem solution {k G V : Type u} [Field k] [Group G] [AddCommGroup V]
  [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [Representation.IsAbsolutelyIrreducible.{u} ρ] :
  Submodule.span k (Set.range ρ) = ⊤ := by
  let K := AlgebraicClosure k
  haveI : (Representation.baseChange K ρ).IsIrreducible :=
    Representation.IsAbsolutelyIrreducible.absolutelyIrreducible K inferInstance inferInstance
  have hK : Submodule.span K (Set.range fun g => (ρ g).baseChange K) = ⊤ :=
    Representation.span_range_eq_top_of_isIrreducible (Representation.baseChange K ρ)
  exact (Representation.span_range_baseChange_eq_top_iff (K := K) ρ).mp hK

end S_Representation_span_range_eq_top_of_isAbsolutelyIrreducible
end P2MW
export P2MW.S_Representation_span_range_eq_top_of_isAbsolutelyIrreducible (solution)
