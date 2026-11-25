-- Prove2me | solution 1 for PositivityTheory.KCo.locConst_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:28:08.608306+00:00
-- url     : https://prove2.me/submissions/986ca5ce-a935-41b7-acc6-6f603b4e3f5a

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.KCo
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank Matrix Topology
  MeasureTheory
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a : Type} [Fintype a] [DecidableEq a] {κ : ℕ}
namespace PositivityTheory.KCo
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {χ : G →* ℂˣ} (h : IsSmoothChar χ) :
    IsLocallyConstant fun g => (χ g : ℂ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  have : IsOpen ((fun x => g⁻¹ * x) ⁻¹' (χ.ker : Set G)) := h.preimage (continuous_const.mul continuous_id)
  filter_upwards [this.mem_nhds (by simp)] with x hx
  have hx' : χ (g⁻¹ * x) = 1 := hx
  rw [map_mul, map_inv, inv_mul_eq_one] at hx'
  rw [hx']
end PositivityTheory.KCo
