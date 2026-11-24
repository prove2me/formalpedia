-- Prove2me | solution 1 for PI.WAU.intC_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:26.675798+00:00
-- url     : https://prove2.me/submissions/88e885f0-bd6c-426f-8b7d-a0041063f964

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatSmulMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WAU_ohat_zero
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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "Af" => FiniteAdeleRing (𝓞 F) F
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.WAU
theorem _root_.solution {b : Module.Basis ι F E} : IntC b (0 : E ⊗[F] Af) := by
  intro k
  simp only [map_zero, Pi.zero_apply]
  exact ohat_zero
end PI.WAU
