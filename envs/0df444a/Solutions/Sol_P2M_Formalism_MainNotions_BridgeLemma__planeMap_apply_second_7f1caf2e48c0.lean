-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__planeMap_apply_second_7f1caf2e48c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:30:45.328831+00:00
-- url     : https://prove2.me/submissions/a9c70622-6b46-4a2c-972e-a28358a95de5

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
theorem _root_.solution (x y x' y' : V) (hxy : h x y = 0) (hyy : h y y ≠ 0) :
    planeMapAlt h x y x' y' y = y' := by
  rw [planeMap_apply_alt, hxy, div_self hyy, zero_div, one_smul, zero_smul, zero_add]
end Formalism.MainNotions.BridgeLemma₂
