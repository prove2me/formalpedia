-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_exists_smooth_bump_of_isCompact_d659e4202a0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:33.782535+00:00
-- url     : https://prove2.me/submissions/ed31b9e5-91e7-440f-b611-a6f048ddc61a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PCutoffs
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_chartPush_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiffOn_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_isCompact_symm_image
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_smooth_chartPush


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Set Filter Topology
open scoped ContDiff Manifold
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (chartPush chartPush_eq_zero isCompact_symm_image smooth_chartPush
  contDiffOn_compat)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K V : Set E} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ 1) ∧ (∀ y ∈ K, g y = 1) ∧
      IsCompact (tsupport g) ∧ tsupport g ⊆ V := by
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  have hd : Disjoint Wᶜ K := Set.disjoint_compl_left_iff_subset.2 hKW
  obtain ⟨f, hf, hrange, h0, h1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed
    (I := 𝓘(ℝ, E)) (n := ⊤) hWo.isClosed_compl hK.isClosed hd
  have hsupp : tsupport f ⊆ closure W := by
    refine closure_mono fun y hy => ?_
    by_contra hyW
    exact hy ((h0 y).1 hyW)
  refine ⟨f, contMDiff_iff_contDiff.1 hf, fun y => hrange ⟨y, rfl⟩, fun y hy => (h1 y).1 hy,
    hWc.of_isClosed_subset (isClosed_tsupport f) hsupp, hsupp.trans hWV⟩
end GroundTheory.Heights₂.Heights.Regular
