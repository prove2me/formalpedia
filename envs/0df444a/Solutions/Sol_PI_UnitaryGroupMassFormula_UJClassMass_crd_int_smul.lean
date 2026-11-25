-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.crd_int_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:02.686373+00:00
-- url     : https://prove2.me/submissions/4fd83cd4-7779-47b2-95dc-8928ea350c9e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_int_smul_mem
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
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ} (b : Module.Basis (Fin M) E V)
    (L0 : Submodule (𝓞 E) V) : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ crdOf b L0, e • x ∈ crdOf b L0 := by
  intro e he x hx
  show ∑ i, (e • x) i • b i ∈ L0
  have : ∑ i, (e • x) i • b i = e • ∑ i, x i • b i := by
    rw [Finset.smul_sum]
    simp [smul_smul]
  rw [this]
  exact int_smul_mem L0 he hx
end PI.UnitaryGroupMassFormula.UJClassMass
