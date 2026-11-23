-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.actM_pow_mem_layer_of_inK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:15.104075+00:00
-- url     : https://prove2.me/submissions/97cdb0ce-4851-43f4-90fd-846c800f9a41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ClosureK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_actM_mem_layer_of_inK

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {V : Submodule ℂ D} (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {k : ℕ} {x : D} (hx : x ∈ layer ε E V k) (m : ℕ) :
    ((actM E Z) ^ m) x ∈ layer ε E V k := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact actM_mem_layer_of_inK hE hV hZ ih
end ReciprocityTheory.ChartRestriction.DS
