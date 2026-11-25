-- Prove2me | solution 1 for PositivityTheory.CW.AdjointWordFiltration.word_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:35:19.963752+00:00
-- url     : https://prove2.me/submissions/c7df9840-90b7-452e-ab83-8ad3c861a1a4

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirPowerCommute
import Theorems.Thm_PositivityTheory_CW_AdjointWordFiltration_word_mem
import Theorems.Thm_PositivityTheory_CW_AdjointWordFiltration_mul_E_mem
import Theorems.Thm_PositivityTheory_CW_AdjointWordFiltration_adjSign_mul_self

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
open PositivityTheory.CW.AdjointWordFiltration
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.AdjointWordFiltration
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (l : List (Fin n × Fin n)) :
    ∃ u' ∈ U E l.length, ∀ x y, inner ℂ x ((l.map fun p => E p.1 p.2).prod y) = inner ℂ (u' x) y := by
  induction l with
  | nil =>
    refine ⟨1, by simpa using word_mem E [], fun x y => ?_⟩
    simp
  | cons p t ih =>
    obtain ⟨w', hw', hw⟩ := ih
    refine ⟨(starRingEnd ℂ (adjSign ε p.2 p.1)) • (w' * E p.2 p.1), ?_, fun x y => ?_⟩
    · exact Submodule.smul_mem _ _ (by simpa using mul_E_mem E p.2 p.1 hw')
    · have h1 := hu p.2 p.1 x ((t.map fun p => E p.1 p.2).prod y)
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.smul_apply, inner_smul_left,
        Complex.conj_conj, Module.End.mul_apply, ← hw, h1, ← mul_assoc, adjSign_mul_self, one_mul]
end PositivityTheory.CW.AdjointWordFiltration
