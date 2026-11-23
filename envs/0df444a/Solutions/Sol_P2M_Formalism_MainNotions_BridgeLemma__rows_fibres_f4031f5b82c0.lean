-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__rows_fibres_f4031f5b82c0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:25.46862+00:00
-- url     : https://prove2.me/submissions/4e00768b-ebd6-4aa3-8e5e-1a4bbc1448d5

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsRpowPow
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open Formalism.HermitianLatticeCounting
open Classical
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {Pr κ : Type} (S : Finset Pr) (c₁ c₂ : Pr → κ) (F : Pr → ℝ) :
    ∑ p ∈ S, F p = ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), F p := by
  rw [← Finset.sum_product', ← Finset.sum_fiberwise_of_maps_to (g := fun p => (c₁ p, c₂ p))
    (t := S.image c₁ ×ˢ S.image c₂) (fun p hp => Finset.mem_product.2
      ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩)]
  refine Finset.sum_congr rfl fun z _ => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_congr fun p _ => ?_
  rw [Prod.ext_iff]
end Formalism.MainNotions.BridgeLemma₂
