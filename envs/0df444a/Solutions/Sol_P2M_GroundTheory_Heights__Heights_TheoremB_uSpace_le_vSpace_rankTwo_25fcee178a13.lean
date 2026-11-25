-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_uSpace_le_vSpace_rankTwo_25fcee178a13
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:29.491712+00:00
-- url     : https://prove2.me/submissions/4cc50416-bcb0-400a-87a1-578567d6f78a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_antisymDelta_rankTwo_527d49b2cc68
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_invForms_le_homogeneous_72bab69dee43

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
theorem _root_.solution : uSpace d1 ≤ vSpace d1 := by
  intro P hP
  obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hP
  have hl1 : l.IsHomogeneous 1 := (mem_homogeneousSubmodule _ _).1 (invForms_le_homogeneous d1 hl)
  refine ⟨?_, ?_⟩
  · rw [mem_homogeneousSubmodule]
    have hdeg : antisymDegree (Fin d1.f) d1.N + 1 = 1 + 1 := by decide
    rw [hdeg, LinearMap.mulLeft_apply, antisymDelta_rankTwo]
    exact ((isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)).mul hl1
  · rintro σ ⟨τ, a, b, hab, hblk, -⟩
    exfalso
    have ha : a.val < 2 := a.isLt
    have hb : b.val < 2 := b.isLt
    have hblk' : b.val < 1 ∨ 1 ≤ a.val := hblk
    omega
end GroundTheory.Heights₂.Heights.TheoremB
