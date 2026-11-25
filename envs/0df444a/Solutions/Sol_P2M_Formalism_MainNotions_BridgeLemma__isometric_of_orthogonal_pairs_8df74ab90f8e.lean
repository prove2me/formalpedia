-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__isometric_of_orthogonal_pairs_8df74ab90f8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:45:13.026336+00:00
-- url     : https://prove2.me/submissions/7fc482ec-a2b4-47b2-8fe6-9b7625d09c4e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_8063afed5bfe
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__planeMap_isometry_53c6e442be67
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__pairCoords_apply_ef037467d414
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__le_range_of_orthogonal_pair_22c644a1ec07
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_alt_884f3cd2a857
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__planeMap_apply_second_7f1caf2e48c0

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
theorem _root_.solution (hs : h.IsSymm) (hfr : finrank K V = 2) (M M' : Submodule (𝓞 K) V)
    (hint : IsIntegralLat h M) (hint' : IsIntegralLat h M') (x y x' y' : V) (hx : x ∈ M) (hy : y ∈ M)
    (hx' : x' ∈ M') (hy' : y' ∈ M') (hxy : h x y = 0) (hxx : h x x ≠ 0) (hyy : h y y ≠ 0) (hxy' : h x' y' = 0)
    (hα : h x' x' = h x x) (hβ : h y' y' = h y y)
    (hN : M.comap (pairCoords (K := K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) =
      M'.comap (pairCoords (K := K) ((h x' x')⁻¹ • x') ((h y' y')⁻¹ • y'))) :
    ∃ g ∈ isom h, gmap g M = M' := by
  have hxx' : h x' x' ≠ 0 := by rw [hα]; exact hxx
  have hyy' : h y' y' ≠ 0 := by rw [hβ]; exact hyy
  let g : V ≃ₗ[K] V := LinearEquiv.ofLinearMap (planeMapAlt h x y x' y') (planeMapAlt h x' y' x y)
    (LinearMap.ext fun v => planeMapAlt_alt h hs hfr x y x' y' hxy hxx hyy hxy' hxx' hyy' v)
    (LinearMap.ext fun v => planeMapAlt_alt h hs hfr x' y' x y hxy' hxx' hyy' hxy hxx hyy v)
  have hg : ∀ v, g v = planeMapAlt h x y x' y' v := fun _ => rfl
  refine ⟨g, ?_, ?_⟩
  · intro u v
    rw [hg, hg]
    exact planeMap_isometry h hs hfr x y x' y' hxy hxx hyy hxy' hα hβ u v
  · have hG : ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) ∘ₗ
        (pairCoords (K := K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) =
        pairCoords (K := K) ((h x' x')⁻¹ • x') ((h y' y')⁻¹ • y') := by
      apply LinearMap.ext; intro p
      rw [LinearMap.comp_apply, pairCoords_apply, pairCoords_apply]
      show g _ = _
      rw [← algebraMap_smul K (p 0), ← algebraMap_smul K (p 1), ← algebraMap_smul K (p 0),
        ← algebraMap_smul K (p 1), map_add, map_smul, map_smul, map_smul, map_smul, hg, hg,
        planeMapAlt_alt_alt h hs x y x' y' hxy hxx, planeMap_apply_second h x y x' y' hxy hyy, hα, hβ]
    unfold gmap
    conv_lhs => rw [← Submodule.map_comap_eq_self (le_range_of_orthogonal_pair h hs hfr M hint x y hx hy hxy hxx hyy)]
    rw [← Submodule.map_comp, hG, hN]
    exact Submodule.map_comap_eq_self (le_range_of_orthogonal_pair h hs hfr M' hint' x' y' hx' hy' hxy' hxx' hyy')
end Formalism.MainNotions.BridgeLemma₂
