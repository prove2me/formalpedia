-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_alt_884f3cd2a857
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:30:43.711378+00:00
-- url     : https://prove2.me/submissions/056d3012-f44d-4322-8d71-7448441541fb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__planeMap_apply_alt_8549fdd1aaf1

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
open NumberField Formalism.HermitianLatticesTheory Module
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K)
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (hs : h.IsSymm) (x y x' y' : V) (hxy : h x y = 0) (hxx : h x x ≠ 0) :
    planeMapAlt h x y x' y' x = x' := by
  have hyx : h y x = 0 := by rw [← hs.eq x y, hxy, map_zero]
  rw [planeMap_apply_alt, hyx, div_self hxx, zero_div, one_smul, zero_smul, add_zero]
end Formalism.MainNotions.BridgeLemma₂
