-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_coneSingle_20bc626224db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:47.154022+00:00
-- url     : https://prove2.me/submissions/3757cc6c-ce3c-4301-be6e-315cf4372b56

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
theorem _root_.solution (c : ℤ) {a : Ω} (ha : a ≠ 0) : IsUnit (coneSingle S x c a) := by
  refine IsUnit.of_mul_eq_one (coneSingle S x (-c) a⁻¹) ?_
  change ConeLaurent.ofLP S x (AddMonoidAlgebra.single c a) *
    ConeLaurent.ofLP S x (AddMonoidAlgebra.single (-c) a⁻¹) = 1
  rw [← map_mul, AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_inv_cancel₀ ha]
  exact map_one _
end GroundTheory.Heights₂.Heights.Kleiman
