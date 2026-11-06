-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.commutes_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:45:10.44928+00:00
-- url     : https://prove2.me/submissions/8eb30dc2-c27c-416f-9fcf-755d6d36cee2

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_isAlt


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution (P Q : Binary ι) : Commutes P Q ↔ Commutes Q P := by
  change FiniteSymplectic.form P.vector Q.vector = 0 ↔
    FiniteSymplectic.form Q.vector P.vector = 0
  exact FiniteSymplectic.form_isAlt.isRefl.eq_iff
end QEC.Coding.PauliSymplectic
