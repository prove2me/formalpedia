-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_delta_7ff44f6dfd11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:34.664638+00:00
-- url     : https://prove2.me/submissions/a69d07c2-d02d-4c04-bc52-588085512228

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_detE_5c2b3d54bea7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerRelations
variable {D : ℕ} (S : ProjectiveLineBundle D)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerRelations
theorem _root_.solution (i : S.ι) (hi : S.x i ≠ 0) (l : S.ν) (k m : S.κ) :
    ∃ a ∈ chartRing ℤ S.x i, wedgeVal S k m * S.δ l = S.x i ^ 3 * a := by
  suffices h : ∀ y ∈ Submodule.span (chartRing ℤ S.x i)
      {d | ∃ u ∈ S.B.lat i, ∃ w ∈ S.B.lat i, d = S.x i * T.detE S.e u w},
      ∃ a ∈ chartRing ℤ S.x i, wedgeVal S k m * y = S.x i ^ 3 * a from
    h _ ((S.detGen i hi).1 l)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    obtain ⟨a₁, ha₁, e₁⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi k u hu)
    obtain ⟨a₂, ha₂, e₂⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi m w hw)
    obtain ⟨a₃, ha₃, e₃⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi k w hw)
    obtain ⟨a₄, ha₄, e₄⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi m u hu)
    refine ⟨a₁ * a₂ - a₃ * a₄, sub_mem (mul_mem ha₁ ha₂) (mul_mem ha₃ ha₄), ?_⟩
    have h := wedge_mul_detE S k m u w
    rw [← e₁, ← e₂, ← e₃, ← e₄] at h
    linear_combination (S.x i) * h
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hya⟩ := hy
    obtain ⟨b, hb, hzb⟩ := hz
    exact ⟨a + b, add_mem ha hb, by rw [mul_add, hya, hzb, mul_add]⟩
  | smul r y _ hy =>
    obtain ⟨a, ha, hya⟩ := hy
    refine ⟨(r : S.Ω) * a, mul_mem r.2 ha, ?_⟩
    rw [Subalgebra.smul_def, smul_eq_mul]
    linear_combination (r : S.Ω) * hya
end GroundTheory.Heights₂.Heights.Inter.PluckerRelations
