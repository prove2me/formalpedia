-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KMain.schwartz_polyGauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:31.905384+00:00
-- url     : https://prove2.me/submissions/05024787-1f51-499f-89b5-cdb6535431ef

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSchwartzSums_SchwartzPolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KMain_evX_temperate
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KMain_schwartz_gs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KMain
open PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KMain
theorem _root_.solution {m n : ℕ} (c : ℝ) (hc : 0 < c) (P : PX m n) :
    ∃ φ : 𝓢(Fin m → Fin n → ℂ, ℂ), ⇑φ = fun x => evX P x * gs c x := by
  obtain ⟨g, hg⟩ := schwartz_gs (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x => evX P x) g, ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (evX_temperate P), hg]
  rfl
end PositivityTheory.SiegelWeilFormula.KMain
