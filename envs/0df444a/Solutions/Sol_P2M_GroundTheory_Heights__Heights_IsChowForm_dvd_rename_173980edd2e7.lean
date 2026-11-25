-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsChowForm_dvd_rename_173980edd2e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:08:58.504543+00:00
-- url     : https://prove2.me/submissions/2cb6fada-fb39-4a05-9d82-f7c68dc513ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_comp_mem_incidence_ad714cb5fc19

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace IsChowForm
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) : f ∣ rename (Prod.map τ id) f := by
  refine (hf.2 _).mp fun u hu => ?_
  rw [aeval_rename]
  exact (hf.2 f).mpr dvd_rfl _ (comp_mem_incidence hu τ)
end IsChowForm
end GroundTheory.Heights₂.Heights
