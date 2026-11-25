-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_twist_twist_a941cbd44f76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:18:55.711797+00:00
-- url     : https://prove2.me/submissions/41bd6722-bd3b-4ed1-9e86-38edc47a34eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm

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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
theorem _root_.solution (F : SubSystem S x E) (P Q : SubSystem S x Ω) :
    (F.twist P).twist Q = F.twist (P.twist Q) := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, z, hz, rfl⟩
    change z ∈ Submodule.span _ _ at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, hp, y, hy, rfl⟩ := hz
      refine Submodule.subset_span ⟨q * p, Submodule.subset_span ⟨q, hq, p, hp, rfl⟩, y, hy, ?_⟩
      rw [mul_smul]
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul a z _ hz =>
      change q • ((a : Ω) • z) ∈ _
      rw [smul_smul, mul_comm, ← smul_smul]
      exact Submodule.smul_mem _ a hz
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, hr, y, hy, rfl⟩
    change r ∈ Submodule.span _ _ at hr
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨q, hq, p, hp, rfl⟩ := hr
      refine Submodule.subset_span ⟨q, hq, p • y, Submodule.subset_span ⟨p, hp, y, hy, rfl⟩, ?_⟩
      rw [smul_eq_mul, mul_smul]
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [add_smul]; exact Submodule.add_mem _ ha hb
    | smul a r _ hr =>
      change ((a : Ω) * r) • y ∈ _
      rw [mul_smul]
      exact Submodule.smul_mem _ a hr
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
