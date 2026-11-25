-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.an_fQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:53.346335+00:00
-- url     : https://prove2.me/submissions/28f55f89-f8d3-4262-9431-c7072b59b328

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_Bridge
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_clsC
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_eval
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_entAn_X
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_entAn_Y
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_entAn_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s z : ℂ) (m : ℕ) (Q : Fm n) (B₀ : MC n) (hB : B₀ ∈ OmS s) : AnalyticAt ℂ (fQ s z m Q) B₀ := by
  obtain ⟨h1, h2, h3⟩ := hB
  have hu := entAn_inv (entAn_X (Complex.I * s) B₀) h1
  have hv := entAn_inv (entAn_Y (Complex.I * s) B₀) h2
  have hf : ∀ k : Bool × Fin n × Fin n, AnalyticAt ℂ (fun B => vals s B k) B₀ := by
    rintro ⟨_ | _, a, b⟩
    · exact hu a b
    · exact hv a b
  exact (an_clsC s z m 0 1 B₀ ⟨h1, h2, h3⟩).mul (an_eval (fun k B => vals s B k) B₀ hf _)
end PositivityTheory.Rg.Sw.SP
