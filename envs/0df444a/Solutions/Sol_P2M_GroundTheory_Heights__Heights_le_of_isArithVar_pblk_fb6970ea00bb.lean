-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_le_of_isArithVar_pblk_fb6970ea00bb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:50.386785+00:00
-- url     : https://prove2.me/submissions/7aa432b5-6f05-48eb-88ae-abc1e1d80981

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea

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
open MvPolynomial MeasureTheory Matrix Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre mcPts)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n d : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P d) :
    d ≤ n := by
  have h := ringKrullDim_quotient_le P
  rw [hP.2.2.2, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField] at h
  have hc : Nat.card (Σ k : Unit, PBlk n k) = n := by
    simp [Nat.card_eq_fintype_card]
  rw [hc, Fintype.card_unit] at h
  have h' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((1 + n : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h
  have h'' : d + 1 ≤ 1 + n := by exact_mod_cast h'
  omega
end GroundTheory.Heights₂.Heights
