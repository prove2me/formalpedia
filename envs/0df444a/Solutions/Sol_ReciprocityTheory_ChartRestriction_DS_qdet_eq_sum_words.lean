-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.qdet_eq_sum_words
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:48.086082+00:00
-- url     : https://prove2.me/submissions/ca020b29-1d07-4f9e-93f1-8a35d1abc871

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_AnyAdj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (u : ℂ) : ∃ l : List (ℂ × List (Fin n × Fin n)),
      Formalism.REAL.qdet E u = (l.map fun c => c.1 • (c.2.map fun p => E p.1 p.2).prod).sum := by
  have hE : ∀ a b : Fin n, E a b ∈ anyAdjWordAlg E := fun a b => ⟨[(1, [(a, b)])], by simp [anyAdjWSum]⟩
  have h : Formalism.REAL.qdet E u ∈ anyAdjWordAlg E := by
    unfold Formalism.REAL.qdet Formalism.REAL.qminor
    refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (intCast_mem _ _) ?_
    refine list_prod_mem fun x hx => ?_
    rw [List.mem_ofFn] at hx
    obtain ⟨k, rfl⟩ := hx
    unfold Formalism.REAL.Tm
    refine Subalgebra.add_mem _ ?_ (hE _ _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _
  obtain ⟨l, hl⟩ := h
  exact ⟨l, hl⟩
end ReciprocityTheory.ChartRestriction.DS
