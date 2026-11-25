-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.DC.lie_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:35.565378+00:00
-- url     : https://prove2.me/submissions/b13359b9-cae7-4e5a-88fd-67dfde055eaa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_inLie_proj
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_proj_half
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_continuous_proj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DC
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.SiegelWeilFormula.Krd.DC
theorem _root_.solution {J : Matrix ι ι ℂ} {c d : ℂ} (hc : Jᴴ = c • J) (hcc : c * c = 1) (hd : J * J = d • 1) (hd0 : d ≠ 0)
    (hds : star d = d) {S : Set (Matrix ι ι ℂ)} (hS : Dense S) (hSp : ∀ X ∈ S, proj J d X ∈ S) {Y : Matrix ι ι ℂ}
    (hY : InLie J Y) {U : Set (Matrix ι ι ℂ)} (hU : IsOpen U) (hYU : Y ∈ U) : ∃ X ∈ S, InLie J X ∧ X ∈ U := by
  have hW : IsOpen (proj J d ⁻¹' U) := hU.preimage (continuous_proj J d)
  have hmem : (1 / 2 : ℂ) • Y ∈ proj J d ⁻¹' U := by
    show proj J d ((1 / 2 : ℂ) • Y) ∈ U
    rw [proj_half hd hd0 hY]
    exact hYU
  obtain ⟨X, hXS, hXW⟩ := hS.exists_mem_open hW ⟨_, hmem⟩
  exact ⟨proj J d X, hSp X hXS, inLie_proj hc hcc hd hd0 hds X, hXW⟩
end PositivityTheory.SiegelWeilFormula.Krd.DC
