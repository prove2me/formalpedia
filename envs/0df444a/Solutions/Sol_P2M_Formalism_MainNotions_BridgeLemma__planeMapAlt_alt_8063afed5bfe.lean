-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_8063afed5bfe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:26.340108+00:00
-- url     : https://prove2.me/submissions/9a820aee-7190-4170-b9f8-b1eb13b566f9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__eq_decomp_orthogonal_pair_6bae56acd115
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
theorem _root_.solution (hs : h.IsSymm) (hfr : finrank K V = 2) (x y x' y' : V) (hxy : h x y = 0) (hxx : h x x ≠ 0)
    (hyy : h y y ≠ 0) (hxy' : h x' y' = 0) (hxx' : h x' x' ≠ 0) (hyy' : h y' y' ≠ 0) (v : V) :
    planeMapAlt h x y x' y' (planeMapAlt h x' y' x y v) = v := by
  have hyx : h y x = 0 := by rw [← hs.eq x y, hxy, map_zero]
  rw [planeMap_apply_alt, planeMap_apply_alt]
  simp only [map_add, map_smul, smul_eq_mul, hxy, hyx, mul_zero, add_zero, zero_add]
  rw [mul_div_assoc, div_self hxx, mul_one, mul_div_assoc, div_self hyy, mul_one]
  exact (eq_decomp_orthogonal_pair h hs hfr x' y' hxy' hxx' hyy' v).symm
end Formalism.MainNotions.BridgeLemma₂
