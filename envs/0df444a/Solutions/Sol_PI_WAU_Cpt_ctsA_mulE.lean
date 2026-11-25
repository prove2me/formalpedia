-- Prove2me | solution 1 for PI.WAU.Cpt.ctsA_mulE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:59.281822+00:00
-- url     : https://prove2.me/submissions/bbd2dce8-1b9b-49f0-822d-ef66c320d6c8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WAU_ctsA_mul
import Theorems.Thm_PI_WAU_ctsA_sum
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
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution {f g : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (hg : ∀ i j, CtsA (bs I) (fun p => g p i j)) (i j : Fin I.n) :
    CtsA (bs I) (fun p => (f p * g p) i j) := by
  simp only [Matrix.mul_apply]
  exact ctsA_sum _ fun l _ => ctsA_mul (hf i l) (hg l j)
end PI.WAU.Cpt
