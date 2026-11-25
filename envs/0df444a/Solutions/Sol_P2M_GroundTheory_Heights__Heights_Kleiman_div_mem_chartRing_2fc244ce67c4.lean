-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_div_mem_chartRing_2fc244ce67c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:00.579746+00:00
-- url     : https://prove2.me/submissions/e660e2a0-1905-41d5-972e-a089986c3d32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimSeq

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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {e : ℕ} (I : Chart x) {o : Ω} (ho : o ∈ twistMod k x e I) {s : Poly k N}
    (hs : s ∈ monos I.1) (hse : s.IsHomogeneous e) : o / aeval x s ∈ chartRing k x I := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at ho
  obtain ⟨a, rfl⟩ := ho
  have hq : x i ^ (e : ℤ) / aeval x s ∈ chartRing k x I :=
    ⟨X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, by rw [map_pow, aeval_X, zpow_natCast]⟩
  rw [chartRing_smul_def, mul_div_assoc]
  exact mul_mem a.2 hq
end GroundTheory.Heights₂.Heights.Kleiman
