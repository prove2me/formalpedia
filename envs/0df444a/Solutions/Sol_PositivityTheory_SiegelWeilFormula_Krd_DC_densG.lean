-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.DC.densG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:09.792705+00:00
-- url     : https://prove2.me/submissions/c25f3161-20ed-4ff1-b2d2-764899b40321

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_cay_inU
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_cay_surj
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_isOpen_dom
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_continuousOn_cay
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_lie_dense
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_scalar_avoid
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_inU_smul
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_CP_cay_inU
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_CP_cay_surj
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_CP_scalar_avoid


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
    (hds : star d = d) {S : Set (Matrix ι ι ℂ)} (hS : Dense S) (hSp : ∀ X ∈ S, proj J d X ∈ S)
    (hSc : ∀ X ∈ S, IsUnit (1 - X).det → cay X ∈ S) {V : Set (Matrix ι ι ℂ)} (hV : IsOpen V) {h : Matrix ι ι ℂ}
    (hhV : h ∈ V) (hh : InU J h) : ∃ h' ∈ V, h' ∈ S ∧ InU J h' := by
  obtain ⟨μ, hμ, hμV, hμu⟩ := scalar_avoid hh hV hhV
  obtain ⟨Y, hYL, hYu, hYc⟩ := cay_surj (inU_smul hh hμ) hμu
  have hU : IsOpen ({Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} ∩ cay ⁻¹' V) :=
    continuousOn_cay.isOpen_inter_preimage isOpen_dom hV
  have hYU : Y ∈ {Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} ∩ cay ⁻¹' V := by
    refine ⟨hYu, ?_⟩
    show cay Y ∈ V
    rw [hYc]
    exact hμV
  obtain ⟨X, hXS, hXL, hXU⟩ := lie_dense hc hcc hd hd0 hds hS hSp hYL hU hYU
  exact ⟨cay X, hXU.2, hSc X hXS hXU.1, cay_inU hXL hXU.1⟩
end PositivityTheory.SiegelWeilFormula.Krd.DC
