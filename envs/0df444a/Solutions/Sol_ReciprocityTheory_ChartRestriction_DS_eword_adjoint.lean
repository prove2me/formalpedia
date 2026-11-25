-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.eword_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:43.77614+00:00
-- url     : https://prove2.me/submissions/c6807d60-a2b7-46c4-81c6-8d8f29ace93c

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
theorem _root_.solution {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (w : List (Fin n × Fin n)) (x y : M) :
    inner ℂ ((w.map fun p => E p.1 p.2).prod x) y =
      (w.map fun p => adjSign ε p.1 p.2).prod *
        inner ℂ x (((w.reverse.map Prod.swap).map fun p => E p.1 p.2).prod y) := by
  induction w generalizing y with
  | nil => simp
  | cons p w ih =>
    simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append, List.prod_append,
      Module.End.mul_apply]
    rw [hU p.1 p.2, ih]
    simp only [List.map_nil, List.prod_nil, Prod.fst_swap, Prod.snd_swap, Module.End.one_apply]
    ring
end ReciprocityTheory.ChartRestriction.DS
