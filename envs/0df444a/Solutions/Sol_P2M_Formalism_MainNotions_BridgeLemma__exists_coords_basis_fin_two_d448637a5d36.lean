-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__exists_coords_basis_fin_two_d448637a5d36
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:07.173981+00:00
-- url     : https://prove2.me/submissions/21094a5e-b22d-4477-9e18-7e5c972bf899

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Module Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (e : Fin 2 → V) (hli : LinearIndependent K e) (hsp : Submodule.span K (Set.range e) = ⊤) (x : V) :
    ∃ a : Fin 2 → K, x = ∑ i, a i • e i := by
  have hx : x ∈ Submodule.span K (Set.range e) := hsp ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
  exact ⟨a, ha.symm⟩
end Formalism.MainNotions.BridgeLemma₂
