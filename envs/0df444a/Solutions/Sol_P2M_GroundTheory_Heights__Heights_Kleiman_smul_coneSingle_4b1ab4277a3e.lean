-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_smul_coneSingle_4b1ab4277a3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:31.297583+00:00
-- url     : https://prove2.me/submissions/1982dca2-5896-4186-8e61-9255d6d3c9d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone

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
universe u w
variable (S : Type u) [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable (x : Fin (N + 1) → Ω)
variable {S x}
variable (S x)
variable {S x}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (c : ℤ) (v : Ω) :
    f • coneSingle S x c v = coneSingle S x (c + e) (aeval x f * v) := by
  change coneLaurent S x f * ConeLaurent.ofLP S x (AddMonoidAlgebra.single c v) =
    ConeLaurent.ofLP S x (AddMonoidAlgebra.single (c + e) (aeval x f * v))
  rw [coneLaurent_of_isHomogeneous hf, ← map_mul, AddMonoidAlgebra.single_mul_single, add_comm]
end GroundTheory.Heights₂.Heights.Kleiman
