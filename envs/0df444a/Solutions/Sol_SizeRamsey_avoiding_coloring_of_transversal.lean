-- Prove2me | solution 1 for SizeRamsey.avoiding_coloring_of_transversal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:19.945527+00:00
-- url     : https://prove2.me/submissions/98293318-3bc9-478a-869b-b6cd7614bba0

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_ColoringBase
public import Theorems.Thm_SizeRamsey_Plan_incidentRed_adj
public import Theorems.Thm_SizeRamsey_Plan_matching4_incident_card
public import Theorems.Thm_SizeRamsey_Plan_transversal_no_blue_square

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution {V : Type*}
    (F : SimpleGraph V) (S : Finset V)
    (hS : c4Transversal F S) (hcard : S.card ≤ 3) :
    ∃ R : SimpleGraph V,
      R ≤ F ∧ ¬ HasMatching4 R ∧ ¬ HasC4 (F \ R) := by
  refine ⟨incidentRed F S, fun u v h => ((Plan.incidentRed_adj F S u v).1 h).1,
    fun hm => ?_, Plan.transversal_no_blue_square F S hS⟩
  have := Plan.matching4_incident_card F S hm
  omega
end SizeRamsey
