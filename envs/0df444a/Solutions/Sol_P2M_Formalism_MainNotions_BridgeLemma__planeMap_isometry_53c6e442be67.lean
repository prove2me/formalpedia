-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__planeMap_isometry_53c6e442be67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:30:47.536013+00:00
-- url     : https://prove2.me/submissions/854546d5-ccf0-45f7-a016-8062a40f3cfc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_comb_orthogonal_pair_4a851b395e83
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
    (hyy : h y y ≠ 0) (hxy' : h x' y' = 0) (hα : h x' x' = h x x) (hβ : h y' y' = h y y) (u v : V) :
    h (planeMapAlt h x y x' y' u) (planeMapAlt h x y x' y' v) = h u v := by
  have hyx : h y x = 0 := by rw [← hs.eq x y, hxy, map_zero]
  have hyx' : h y' x' = 0 := by rw [← hs.eq x' y', hxy', map_zero]
  rw [planeMap_apply_alt, planeMap_apply_alt, inner_comb_orthogonal_pair h x' y' hxy' hyx', hα, hβ]
  conv_rhs => rw [eq_decomp_orthogonal_pair h hs hfr x y hxy hxx hyy u, eq_decomp_orthogonal_pair h hs hfr x y hxy hxx hyy v]
  rw [inner_comb_orthogonal_pair h x y hxy hyx]
end Formalism.MainNotions.BridgeLemma₂
