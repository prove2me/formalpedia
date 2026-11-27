-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.natCast_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:21:33.949325+00:00
-- url     : https://prove2.me/submissions/c1fed473-8b14-4170-bb06-387dbaeb49ba

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (m : ℕ) :
    ((m : KV I v) ⊗ₜ[I.F] (1 : I.E)) = (m : RV I v) := by
  have := map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := I.F) (A := KV I v) (B := I.E)) m
  rw [← this]
  rfl
end PI.UnitaryGroupMassFormula.ScXuExists
