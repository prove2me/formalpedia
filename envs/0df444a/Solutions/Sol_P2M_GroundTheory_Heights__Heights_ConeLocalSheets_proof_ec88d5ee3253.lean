-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_proof_ec88d5ee3253
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:32.408394+00:00
-- url     : https://prove2.me/submissions/7d34fd8b-2cc9-48ff-a11f-6d9205bc0ac5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_isHomogeneous_92e68ea8d626
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eval_homogenize_d7a73378accb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_ne_zero_b4aa12b26ec4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_lift_injective_4da4e73bfd03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_of_mem_fibre_91ae637f4033
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_to_mem_fibre_71799e65f6b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_fibre_finite_e6f7d229a02e

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix
namespace GroundTheory.Heights₂.Heights
namespace ConeLocalSheets
theorem _root_.solution (hQ : QuasiFiniteSheets.Statement) : ConeLocalSheets.Statement := by
  intro n e P Ψ hP hΨ
  obtain ⟨c, hc0, hc⟩ := hQ n e (ConeLocalSheets.chartIdeal P Ψ) (ConeLocalSheets.tailMat Ψ)
    (ConeLocalSheets.fibre_finite hP hΨ)
  refine ⟨ConeLocalSheets.homogenize c, c.totalDegree, ConeLocalSheets.homogenize_ne_zero hc0,
    ConeLocalSheets.homogenize_isHomogeneous c, fun x hx => ?_⟩
  rw [ConeLocalSheets.eval_homogenize] at hx
  obtain ⟨U, N, s, hU, hxU, hs, hsy⟩ := hc x hx
  refine ⟨U, N, fun j y => ConeLocalSheets.lift (s j y), hU, hxU, fun j => ?_, fun y hy => ?_⟩
  · rw [differentiableOn_pi]
    intro p
    exact differentiableOn_pi.mp (hs j) p.2
  · obtain ⟨hval, hinj, hfib⟩ := hsy y hy
    refine ⟨fun j => ConeLocalSheets.of_mem_fibre (hval j),
      fun j k h => hinj (ConeLocalSheets.lift_injective h), ?_⟩
    intro w hw
    obtain ⟨z, hz, rfl⟩ := ConeLocalSheets.to_mem_fibre hw
    obtain ⟨j, hj⟩ := hfib hz
    exact ⟨j, by simp only [hj]⟩
end ConeLocalSheets
end GroundTheory.Heights₂.Heights
