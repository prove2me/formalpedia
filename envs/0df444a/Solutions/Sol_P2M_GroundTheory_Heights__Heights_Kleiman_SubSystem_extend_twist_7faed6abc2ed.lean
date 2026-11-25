-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_extend_twist_7faed6abc2ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:56:20.632454+00:00
-- url     : https://prove2.me/submissions/e6990b8f-d379-4838-8544-319cd6477b5f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist

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
open scoped Pointwise
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
omit [Algebra S F] [IsScalarTower S F Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SubSystem
theorem _root_.solution (Q R : SubSystem S x Ω) :
    (Q.twist R).extend F = (Q.extend F).twist (R.extend F) := by
  refine SubSystem.ext_sub fun I => ?_
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change Submodule.span (chartRing F x I) ((Q.twist R).sub I : Set Ω) =
    Submodule.span (chartRing F x I) (R.sub I : Set Ω) * Submodule.span (chartRing F x I) (Q.sub I : Set Ω)
  rw [SubSystem.twist_sub_eq_mul_of_line, Submodule.span_mul_span]
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.mul_induction_on (C := fun y =>
      y ∈ Submodule.span (chartRing F x I) ((R.sub I : Set Ω) * (Q.sub I : Set Ω))) hy ?_ ?_
    · intro r hr q hq
      exact Submodule.subset_span (Set.mul_mem_mul hr hq)
    · intro a b ha hb; exact Submodule.add_mem _ ha hb
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, hr, q, hq, rfl⟩
    exact Submodule.subset_span (Submodule.mul_mem_mul hr hq)
end SubSystem
end GroundTheory.Heights₂.Heights.Kleiman
