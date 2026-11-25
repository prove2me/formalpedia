-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tildeSys_twist_dbe5ec796d37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:36.873315+00:00
-- url     : https://prove2.me/submissions/3620afe8-caed-4ac5-b345-2d1eca2768b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tilde_mem_chartRing_0207599c01f2

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
theorem _root_.solution (X : SubSystem k x Ω) :
    ((coordGraded k x).tildeSys 0).twist X = X := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    have hyA := coordGraded_tilde_mem_chartRing hy
    have hqy : q • y = (⟨y, hyA⟩ : chartRing k x I) • q := by
      rw [smul_eq_mul, chartRing_smul_def, mul_comm]
    rw [SetLike.mem_coe, hqy]
    exact (X.sub I).smul_mem _ hq
  · intro q hq
    refine Submodule.subset_span ⟨q, hq, 1, ?_, by rw [smul_eq_mul, mul_one]⟩
    exact Submodule.subset_span ⟨1, 1, 0, 0, one_mem _, isHomogeneous_one _ _,
      Submodule.subset_span ⟨1, 0, isHomogeneous_one _ _, by simp, by simp⟩, by simp, by simp⟩
end GroundTheory.Heights₂.Heights.Kleiman
