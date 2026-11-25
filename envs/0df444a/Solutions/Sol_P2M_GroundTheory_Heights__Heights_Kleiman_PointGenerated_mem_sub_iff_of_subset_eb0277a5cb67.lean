-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_of_subset_eb0277a5cb67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:26:55.061852+00:00
-- url     : https://prove2.me/submissions/9c60482c-d184-4825-ad06-dbc1734d4012

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPointGenerated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_inv_mem_chartRing_cebcaeb7ef5d

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
open GroundTheory.Heights₂.Heights.Kleiman.PointGenerated
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.PointGenerated
theorem _root_.solution (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) {I J : Chart x}
    (h : I.1 ⊆ J.1) (y : Ω) : y ∈ Q.sub J ↔ y ∈ Q.sub I := by
  refine ⟨fun hy => ?_, Q.mono I J h y⟩
  obtain ⟨a, ha, hay⟩ := (Q.mem_iff I J h y).mp hy
  have ha0 : (a : Ω) ≠ 0 := by
    intro h0
    apply ha.ne_zero
    exact Subtype.ext h0
  have hy' : y = (⟨(a : Ω)⁻¹, inv_mem_chartRing hx I a.2⟩ : chartRing k x I) • ((a : Ω) • y) := by
    rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
  rw [hy']
  exact Submodule.smul_mem _ _ hay
end GroundTheory.Heights₂.Heights.Kleiman.PointGenerated
