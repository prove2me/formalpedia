-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_X_102517a1af24
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:35.841134+00:00
-- url     : https://prove2.me/submissions/87422294-231e-446b-9d04-034a2c3c73ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_PsiOfIsHomogeneous

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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω)
variable (S : Type u) [CommRing S] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution (j : Fin (r + 1)) : psi η S (X j) = single ((0 : ℤ), (1 : ℤ)) (η j) :=
  aeval_X _ _
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
