-- Prove2me | solution 1 for PositivityTheory.KReal.GoodSideLattices.sd_mem_genG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:26:50.224663+00:00
-- url     : https://prove2.me/submissions/6046a8ed-b8f8-4465-baec-691937d5b093

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreStar
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGen
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSide

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
open PositivityTheory.KReal.GoodSideLattices
variable {p q r s : ℕ}
namespace PositivityTheory.KReal.GoodSideLattices
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (act : Mat r s →ₗ[ℂ] Module.End ℂ M)
    (S : Submodule ℂ M) : S ≤ genG act S ∧ ∀ W, ∀ x ∈ genG act S, act W x ∈ genG act S := by
  refine ⟨fun x hx => ?_, fun W x hx => ?_⟩
  · exact Submodule.mem_sInf.2 (fun N hN => hN.1 hx)
  · rw [genG, Submodule.mem_sInf] at hx ⊢
    intro N hN
    exact hN.2 W x (hx N hN)
end PositivityTheory.KReal.GoodSideLattices
