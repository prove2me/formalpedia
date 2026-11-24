-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PosPartSplit_proof_e6248afef178
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:04.097986+00:00
-- url     : https://prove2.me/submissions/4cb468e3-e303-4224-a82d-a8358aa9b29b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_finite_20785c71949c


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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PosPartSplit
theorem _root_.solution : PosPartSplit.Statement := by
  classical
  intro n d J A f φ E y hA hE hcov
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartPosDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]

  set T : ((Fin n → ℂ) → ℝ) → (Fin n → ℂ) → ℝ := fun g x =>
    if h : ∃ s, IsSheetAt J A x s then
      max (g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y) 0 else 0 with hT
  have hT0 : ∀ g x, 0 ≤ T g x := fun g x => by
    simp only [hT]; split_ifs <;> simp
  have hpt : ∀ x ∈ hfin.toFinset,
      ENNReal.ofReal (T f x) = ∑' k, ENNReal.ofReal (T ((E k).indicator f) x) := by
    intro x hx
    have hx' : x ∈ fibre J A y := hfin.mem_toFinset.mp hx
    by_cases hs : ∃ s, IsSheetAt J A x s
    · obtain ⟨k₀, hk₀⟩ := hcov x hx' hs
      rw [tsum_eq_single k₀]
      · simp only [hT, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : x ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [hT, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [hT, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 f x), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 _ x)).symm
end PosPartSplit
end GroundTheory.Heights₂.Heights
