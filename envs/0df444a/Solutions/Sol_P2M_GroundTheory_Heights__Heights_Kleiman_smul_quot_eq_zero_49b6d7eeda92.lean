-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_smul_quot_eq_zero_49b6d7eeda92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:14.230804+00:00
-- url     : https://prove2.me/submissions/e498b4e9-946e-445f-979b-eb4ce7003a3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {q : Poly S N} (hq : q ∈ primeOf (S := S) y)
    (m : Poly S N ⧸ primeOf (S := S) y) : q • m = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective m
  change Ideal.Quotient.mk _ (q * f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right f _ hq
end GroundTheory.Heights₂.Heights.Kleiman
