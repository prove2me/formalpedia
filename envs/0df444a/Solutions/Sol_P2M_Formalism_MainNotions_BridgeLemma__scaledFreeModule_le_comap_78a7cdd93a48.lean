-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__scaledFreeModule_le_comap_78a7cdd93a48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:30:59.282694+00:00
-- url     : https://prove2.me/submissions/663779fd-ffc0-4fdb-830f-edc732abeaca

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__pairCoords_apply_ef037467d414

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
theorem _root_.solution (M : Submodule (𝓞 K) V) (x y : V) (hx : x ∈ M) (hy : y ∈ M) (a b : 𝓞 K)
    (ha : algebraMap (𝓞 K) K a = h x x) (hb : algebraMap (𝓞 K) K b = h y y) (hxx : h x x ≠ 0) (hyy : h y y ≠ 0) :
    scaledFreeModule K (a * b) ≤ M.comap (pairCoords (K := K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) := by
  rw [Submodule.smul_le]
  intro r hr p _
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  rw [Submodule.mem_comap, map_smul, pairCoords_apply, mul_smul]
  refine M.smul_mem c ?_
  rw [smul_add, smul_comm (a * b) (p 0), smul_comm (a * b) (p 1)]
  refine M.add_mem (M.smul_mem _ ?_) (M.smul_mem _ ?_)
  · have e : (a * b) • ((h x x)⁻¹ • x) = b • x := by
      rw [← algebraMap_smul K (a * b), ← algebraMap_smul K b, map_mul, ha, smul_smul]
      congr 1; field_simp
    rw [e]; exact M.smul_mem _ hx
  · have e : (a * b) • ((h y y)⁻¹ • y) = a • y := by
      rw [← algebraMap_smul K (a * b), ← algebraMap_smul K a, map_mul, hb, smul_smul]
      congr 1; field_simp
    rw [e]; exact M.smul_mem _ hy
end Formalism.MainNotions.BridgeLemma₂
