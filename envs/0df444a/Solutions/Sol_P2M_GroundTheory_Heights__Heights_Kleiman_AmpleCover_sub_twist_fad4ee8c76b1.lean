-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_twist_fad4ee8c76b1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:07.037999+00:00
-- url     : https://prove2.me/submissions/54c59903-f5bf-4f7b-807b-14d8d5d5d32e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleCover

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
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace AmpleCover
theorem _root_.solution (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨y, hy, q, hq, mul_comm _ _⟩
  · rintro ⟨y, hy, q, hq, rfl⟩; exact ⟨q, hq, y, hy, mul_comm _ _⟩
end AmpleCover
end GroundTheory.Heights₂.Heights.Kleiman
