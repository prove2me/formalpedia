-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__inner_comb_orthogonal_pair_4a851b395e83
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:58.890974+00:00
-- url     : https://prove2.me/submissions/53f49e8f-b3b8-45ad-9ca0-d24e184146c0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm

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
theorem _root_.solution (x y : V) (hxy : h x y = 0) (hyx : h y x = 0) (a c a' c' : K) :
    h (a • x + c • y) (a' • x + c' • y) = star a * a' * h x x + star c * c' * h y y := by
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hxy, hyx,
    starRingEnd_apply, RingHom.id_apply, mul_zero, add_zero, zero_add]
  ring
end Formalism.MainNotions.BridgeLemma₂
