-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.lvA_mulVec_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:18.919555+00:00
-- url     : https://prove2.me/submissions/66fc162c-bfef-4cc5-8bec-a60073eb00dc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
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
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {R : Type} [CommRing R] (S : Subring R) {n : ℕ}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution {ι κ : Type} [Fintype κ] (M : Matrix ι κ R) (hM : ∀ i j, M i j ∈ S)
    (v : κ → R) (hv : ∀ i, v i ∈ S) : ∀ i, (M *ᵥ v) i ∈ S := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact S.sum_mem fun j _ => S.mul_mem (hM i j) (hv j)
end PI.UnitaryGroupMassFormula.InHHClassFin
