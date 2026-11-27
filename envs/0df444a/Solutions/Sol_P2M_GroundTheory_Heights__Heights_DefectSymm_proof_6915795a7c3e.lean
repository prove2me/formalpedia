-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DefectSymm_proof_6915795a7c3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:01:11.389191+00:00
-- url     : https://prove2.me/submissions/99b21a11-57d6-47b3-8452-9a8685c9d016

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDefectSymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace DefectSymm
theorem _root_.solution (h1 : CycleSectionData.Statement) (h2 : SpecFirstSwapMahler.Statement)
    (h3 : CycleIntegralSection.Statement) (h4 : GreenSymmetry.Statement)
    (h5 : SupportCycleSection.Statement) : DefectSymm.Statement := by
  intro e hIH n δ h Z f u u' hZ hu hu' huu' hu'u

  have A := hIH n δ h (cycleSection Z u) (specFirst f u) u' (h1 n e δ Z f u hZ hu) huu'
  have B := hIH n δ h (cycleSection Z u') (specFirst f u') u (h1 n e δ Z f u' hZ hu') hu'u
  have S := h2 n e h Z f u u' hZ.chow

  obtain ⟨c, -, g, hg, -⟩ := hZ.chow
  have G : ∀ W ∈ Z.support,
      (Z W : ℝ) * (cycleIntegral h (divCycle W u) e (fsLog h u') + coneIntegral h W (e + 1) (fsLog h u)) =
        (Z W : ℝ) * (cycleIntegral h (divCycle W u') e (fsLog h u) +
          coneIntegral h W (e + 1) (fsLog h u')) := by
    intro W hW
    congr 1
    refine h4 n e h W u u' (hZ.prime W hW) ⟨g W, hg W hW⟩ (hu W hW) (hu' W hW) ?_
    intro W' hW'
    exact huu' W' ((h5 n Z u).1 W hW hW')
  have hsum := Finset.sum_congr rfl G
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  have Cu := h3 n h Z u e (fsLog h u')
  have Cu' := h3 n h Z u' e (fsLog h u)
  have Ku : cycleIntegral h Z (e + 1) (fsLog h u) =
      ∑ W ∈ Z.support, (Z W : ℝ) * coneIntegral h W (e + 1) (fsLog h u) := rfl
  have Ku' : cycleIntegral h Z (e + 1) (fsLog h u') =
      ∑ W ∈ Z.support, (Z W : ℝ) * coneIntegral h W (e + 1) (fsLog h u') := rfl
  unfold mahlerDefect
  linarith
end DefectSymm
end GroundTheory.Heights₂.Heights
