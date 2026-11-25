-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_cellMon_homog_9faa70fa300d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:25.9521+00:00
-- url     : https://prove2.me/submissions/4826f3b8-6ee4-4e2d-b146-fae1c12af47d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_mul_0a86f7155eda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_X_a46f864d89cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultiHomog_one_zero_4334cb17c577


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
theorem _root_.solution {I : ∀ k, Finset (ι k)} {u : MRingOver S ι} (hu : u ∈ KH.cellMon S I) :
    ∃ e : K → ℕ, IsMultiHomog u e := by
  induction hu using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, -, rfl⟩ := hf
    exact ⟨_, isMultiHomog_X k i⟩
  | one => exact ⟨0, isMultiHomog_one_zero⟩
  | mul f f' _ _ hf hf' =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hf'
    exact ⟨a + b, isMultiHomog_mul ha hb⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
