-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_cpTwist___apply_d5d2a431117a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:37.276272+00:00
-- url     : https://prove2.me/submissions/c9c782a4-d747-4c2d-b901-5632abf71f4c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open UniformSpace
variable {p : ℕ} [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace GroundTheory.PAdicHodge
theorem _root_.solution (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    (cpTwist K j).ρ σ x = twistScalar K j σ * (σ • x) := rfl
end GroundTheory.PAdicHodge
