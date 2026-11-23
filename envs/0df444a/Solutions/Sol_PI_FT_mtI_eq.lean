-- Prove2me | solution 1 for PI.FT.mtI_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:23.383808+00:00
-- url     : https://prove2.me/submissions/5bafbc29-28ca-4f68-ba70-bc16bb40972d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
local notation "ι" => inclR (F := F) (E := E) (AF F)
namespace PI.FT
theorem _root_.solution {M' : ℕ} {J' : Matrix (Fin M') (Fin M') E}
    {K : Type} [Group K] (e : K ≃* HA (AF F) σ J') (g : K) :
    mtI (e g) = mt (e g⁻¹) := by
  rw [map_inv e g]
  rfl
end PI.FT
