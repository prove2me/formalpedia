-- Prove2me | solution 1 for PI.MSC.nablaSpan_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:04.040603+00:00
-- url     : https://prove2.me/submissions/9ca5604a-f0a2-49db-a109-49141e6e782c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinorSpanCompl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ExistsCoeffNeZeroOfMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_RenameInitMinor
import Theorems.Thm_PI_MSC_rename_initMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_gen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC
namespace PI.MSC
theorem _root_.solution (R : Type) [CommRing R] (N : ℕ) (ν : YoungDiagram) :
    PI.nablaSpan R N ν = Submodule.map (rename (phi N (ν.colLen 0))).toLinearMap
      (Submodule.span R (Set.range (gen R N ν))) := by
  rw [Submodule.map_span, ← Set.range_comp]
  unfold PI.nablaSpan
  congr 1
  congr 1
  funext I
  simp only [Function.comp_apply, AlgHom.toLinearMap_apply, gen, bideterminant, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  exact (rename_initMinor R N _ _ _ (I c)).symm
end PI.MSC
