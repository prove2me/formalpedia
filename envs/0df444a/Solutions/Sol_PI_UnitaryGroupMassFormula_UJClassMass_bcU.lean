-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.bcU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:54.1962+00:00
-- url     : https://prove2.me/submissions/6f8dc568-1527-4a2e-af2f-56ebc7ae97ea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermC
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution : BcU := by
  intro F E _ _ _ σ M J R _ _ g hg
  have key : ∀ A : Matrix (Fin M) (Fin M) E,
      PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ R)
          (A.map (PI.UnitaryApproxDefs.inclE (F := F) R)) =
        (PI.UnitaryApproxDefs.cT (σ : E →+* E) A).map (PI.UnitaryApproxDefs.inclE (F := F) R) := by
    intro A
    ext i j
    simp [PI.UnitaryApproxDefs.cT, PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]
  have hg' : PI.UnitaryApproxDefs.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
      (g : Matrix (Fin M) (Fin M) E) = J := hg
  change PI.UnitaryApproxDefs.cT _ _ * _ * _ = _
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    RingHom.mapMatrix_apply]
  rw [key, ← Matrix.map_mul, ← Matrix.map_mul, hg']
end PI.UnitaryGroupMassFormula.UJClassMass
