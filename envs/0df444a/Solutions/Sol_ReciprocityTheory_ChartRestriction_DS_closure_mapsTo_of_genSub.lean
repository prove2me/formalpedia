-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.closure_mapsTo_of_genSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:36.570517+00:00
-- url     : https://prove2.me/submissions/0b7666c5-8c4e-40c7-bb97-de1d54f39f01

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Analytic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ClosureK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ExistsExpEqOfMemKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure

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
theorem _root_.solution {V : Submodule ℂ D} (T : H →L[ℂ] H)
    (hT : ∀ v : D, v ∈ genSub E V → T (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure)
    {x : H} (hx : x ∈ ((genSub E V).map D.subtype).topologicalClosure) :
    T x ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  have hsub : (((genSub E V).map D.subtype : Submodule ℂ H) : Set H) ⊆
      T ⁻¹' ((((genSub E V).map D.subtype).topologicalClosure : Submodule ℂ H) : Set H) := by
    rintro y ⟨v, hv, rfl⟩
    exact hT v hv
  have hcl : IsClosed (T ⁻¹' ((((genSub E V).map D.subtype).topologicalClosure :
      Submodule ℂ H) : Set H)) :=
    ((genSub E V).map D.subtype).isClosed_topologicalClosure.preimage T.continuous
  have hx' : x ∈ closure (((genSub E V).map D.subtype : Submodule ℂ H) : Set H) := by
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx
  exact closure_minimal hsub hcl hx'
end ReciprocityTheory.ChartRestriction.DS
