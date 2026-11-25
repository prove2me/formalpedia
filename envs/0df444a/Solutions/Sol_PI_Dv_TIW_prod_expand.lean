-- Prove2me | solution 1 for PI.Dv.TIW.prod_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:54.76122+00:00
-- url     : https://prove2.me/submissions/7dfd4096-963a-4814-be51-962f99435c65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_PerS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GroupDataExists
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.TIW
theorem _root_.solution (c c' : G → K) (g' g : G) :
    (∑ x : G, c x • MonoidAlgebra.of K G x) * MonoidAlgebra.of K G g' *
        ((∑ y : G, c' y • MonoidAlgebra.of K G y) * MonoidAlgebra.of K G g) =
      ∑ x : G, ∑ y : G, (c x * c' y) • MonoidAlgebra.of K G (x * g' * (y * g)) := by
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hof : MonoidAlgebra.of K G x * MonoidAlgebra.of K G g' * (MonoidAlgebra.of K G y * MonoidAlgebra.of K G g) =
      MonoidAlgebra.of K G (x * g' * (y * g)) := by simp only [map_mul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hof, mul_comm (c' y) (c x)]
end PI.Dv.TIW
