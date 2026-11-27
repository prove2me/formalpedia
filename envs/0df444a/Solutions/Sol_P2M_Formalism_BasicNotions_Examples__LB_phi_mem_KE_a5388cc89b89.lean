-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_phi_mem_KE_a5388cc89b89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:49:37.577498+00:00
-- url     : https://prove2.me/submissions/04d4d52b-726f-4fac-90a1-7d487cd3376c

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocG
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_phi_mem_26f23f35fb3f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime]
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (φ : F →+* PadicAlgCl l) (x : F) : φ x ∈ KE l F := (le_iSup (fun ψ : F →+* PadicAlgCl l => Kphi ψ) φ) (phi_mem φ x)
end Formalism.BasicNotions.Examples₂.LB
