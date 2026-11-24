-- Prove2me | solution 1 for PI.GreenLabelSurjWork.nontrivial_of_simple
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:44.419807+00:00
-- url     : https://prove2.me/submissions/5a70b3b6-f54e-4ea2-afdd-b367f96d712b

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.GreenLabelSurjWork
variable {G : Type} [Group G] [Fintype G]
namespace PI.GreenLabelSurjWork
theorem _root_.solution (V : FDRep ℂ G) (h : Simple V) : Nontrivial V := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  apply CategoryTheory.id_nonzero V
  first
    | (ext x; exact Subsingleton.elim _ _)
    | (apply Action.Hom.ext; ext x; exact Subsingleton.elim _ _)
    | (ext; exact Subsingleton.elim _ _)
end PI.GreenLabelSurjWork
