-- Prove2me | solution 1 for UpperTheory.V.cAct_cAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:39:37.234383+00:00
-- url     : https://prove2.me/submissions/4b1a8c01-699d-4132-b414-ee33f7c4e1c8

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_V_galois_action_cohomology_mul
import Theorems.Thm_UpperTheory_V_galois_action_cohomology_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.Top
open UpperTheory UpperTheory.V
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime]
namespace UpperTheory.V
theorem _root_.solution (D : LData E Ω l) (e : ℤ) (x : H1 (qzTw D e)) : cAct D e (cAct D e x) = x := by
  have hc : cE E * cE E = 1 := by
    ext y
    simp [cE, IsCMField.complexConj_apply_apply]
  show galoisActionOnCohomology D e (cE E) (galoisActionOnCohomology D e (cE E) x) = x
  rw [← Module.End.mul_apply, ← galois_action_cohomology_mul, hc, galois_action_cohomology_one, Module.End.one_apply]
end UpperTheory.V
