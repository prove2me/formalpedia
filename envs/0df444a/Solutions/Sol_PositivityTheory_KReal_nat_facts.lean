-- Prove2me | solution 1 for PositivityTheory.KReal.nat_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:52:45.98567+00:00
-- url     : https://prove2.me/submissions/726b2cb4-5690-4985-8d62-358b233cb6f7

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreComb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {D : RealData} (h : D.Hyp) :
    D.R + D.p + D.q = D.a + D.a' ∧ D.S = D.p + D.q ∧ D.P + D.p = D.a ∧ D.Q = D.p ∧ D.P' = D.q ∧
      D.Q' + D.q = D.a' ∧ 2 * nD D + D.a + D.a' = D.κ + 2 * D.p + 2 * D.q ∧
      2 * mD D + 2 * D.p + 2 * D.q = D.κ + D.a + D.a' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hn2 : 2 * nD D = D.κ + 2 * D.y - D.d := by
    unfold nD
    refine Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ?_)
    simp only [RealData.y, RealData.d]
    omega
  have hm2 : 2 * mD D = D.κ + D.d - 2 * D.y := by
    unfold mD
    refine Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ?_)
    simp only [RealData.y, RealData.d]
    omega
  simp only [RealData.y, RealData.d] at hn2 hm2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [RealData.R, RealData.S, RealData.P, RealData.Q, RealData.P', RealData.Q',
    RealData.y, RealData.d]
  all_goals omega
end PositivityTheory.KReal
