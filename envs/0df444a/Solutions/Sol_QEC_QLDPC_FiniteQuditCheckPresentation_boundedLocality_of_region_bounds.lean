-- Prove2me | solution 1 for QEC.QLDPC.FiniteQuditCheckPresentation.boundedLocality_of_region_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:41:25.712174+00:00
-- url     : https://prove2.me/submissions/42f6071b-5989-469e-82da-0d9ac995e8ef

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_checkSupport_eq_region

set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v
open QEC.QLDPC.FiniteQuditCheckPresentation
variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype κ]
namespace QEC.QLDPC.FiniteQuditCheckPresentation
theorem _root_.solution
    (P : FiniteQuditCheckPresentation ι κ) {bound : Nat}
    (hcheck : ∀ checkIndex,
      (P.checks checkIndex).region.selected.card ≤ bound)
    (hcoordinate : ∀ coordinate,
      (P.incidence.variableSupport coordinate).card ≤ bound) :
    Coding.BoundedLocality P.localityProfile bound := by
  apply P.incidence.boundedLocality_of_row_col_bounds
  · intro checkIndex
    rw [P.checkSupport_eq_region]
    exact hcheck checkIndex
  · exact hcoordinate
end QEC.QLDPC.FiniteQuditCheckPresentation
