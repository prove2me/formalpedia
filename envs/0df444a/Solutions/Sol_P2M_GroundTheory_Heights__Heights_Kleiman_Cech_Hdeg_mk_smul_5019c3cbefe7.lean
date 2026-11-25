-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_smul_5019c3cbefe7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:01:43.401805+00:00
-- url     : https://prove2.me/submissions/01d87148-7467-4e0b-a01a-2305998a202b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {deg : ∀ I, Submodule R (G I)}
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} {i : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech
theorem _root_.solution (r : R) (a : cocyDeg G deg ρ i) : Hdeg.mk (r • a) = r • Hdeg.mk a :=
  Submodule.Quotient.mk_smul _ _ _
end GroundTheory.Heights₂.Heights.Kleiman.Cech
