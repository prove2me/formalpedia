-- Prove2me | solution 1 for QEC.Locality.edgeIncidentVertices_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:12:58.886975+00:00
-- url     : https://prove2.me/submissions/738a56d0-0312-4855-baa3-7b6f7810e4e3

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Theorems.Thm_QEC_Locality_mem_edgeIncidentVertices_iff


set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {edges₁ edges₂ : Finset (ι × ι)}
    (hsubset : edges₁ ⊆ edges₂) :
    edgeIncidentVertices edges₁ ⊆ edgeIncidentVertices edges₂ := by
  intro x hx
  rcases (mem_edgeIncidentVertices_iff _ x).1 hx with ⟨edge, hedge, hendpoint⟩
  exact (mem_edgeIncidentVertices_iff _ x).2 ⟨edge, hsubset hedge, hendpoint⟩
end QEC.Locality
