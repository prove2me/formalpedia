-- Prove2me | solution 1 for P2M_GlobalTheory_CMVal_Fibre_coord_inv__516d95d00b29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:25.668981+00:00
-- url     : https://prove2.me/submissions/ca8c7461-87da-48cd-9b24-f437063433ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Fibre
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Fibre
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (y : (Af E)ˣ) : coord P y⁻¹ = (coord P y)⁻¹ := Units.ext rfl
end GlobalTheory.CMVal.Fibre
