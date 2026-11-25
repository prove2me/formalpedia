-- Prove2me | solution 1 for PositivityTheory.CW.EigenspaceDecomposition.fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:22:12.04598+00:00
-- url     : https://prove2.me/submissions/af7cad04-e14a-4497-a181-7ad1b51bcc61

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenbasisOfBasic
import Theorems.Thm_PositivityTheory_CW_EigenspaceDecomposition_mem_Es

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenspaceDecomposition
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}
namespace PositivityTheory.CW.EigenspaceDecomposition
theorem _root_.solution (h : Mod ε E) (μ : ℝ) : FiniteDimensional ℂ (Es ε E μ) := by
  haveI := h.fin μ
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {v : V | ∃ μ' ≤ μ, Eig ε E μ' v}) ?_
  intro v hv
  exact Submodule.subset_span ⟨μ, le_rfl, mem_Es.mp hv⟩
end PositivityTheory.CW.EigenspaceDecomposition
