-- Prove2me | solution 1 for PI.KerDetFinW.det_mem_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:05.882855+00:00
-- url     : https://prove2.me/submissions/65667728-0072-4818-bf44-7ba3686866b4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution {K : Type} [Field K] (R : Subring K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (h : ∀ i j, A i j ∈ R) : A.det ∈ R := by
  have hB : R.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, h i j⟩ : R)) = A := by
    ext i j
    rfl
  rw [← hB, ← RingHom.map_det]
  exact SetLike.coe_mem _
end PI.KerDetFinW
