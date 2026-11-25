-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__le_range_of_orthogonal_pair_22c644a1ec07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:25.544065+00:00
-- url     : https://prove2.me/submissions/64147f75-dbad-4a2d-ba07-69d32867b9ad

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__eq_decomp_orthogonal_pair_6bae56acd115
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
theorem _root_.solution (hs : h.IsSymm) (hfr : finrank K V = 2) (M : Submodule (𝓞 K) V)
    (hint : IsIntegralLat h M) (x y : V) (hx : x ∈ M) (hy : y ∈ M) (hxy : h x y = 0) (hxx : h x x ≠ 0)
    (hyy : h y y ≠ 0) : M ≤ LinearMap.range (pairCoords (K := K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) := by
  intro v hv
  obtain ⟨p0, hp0⟩ := Submodule.mem_one.1 (hint x hx v hv)
  obtain ⟨p1, hp1⟩ := Submodule.mem_one.1 (hint y hy v hv)
  refine ⟨![p0, p1], ?_⟩
  rw [pairCoords_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← algebraMap_smul K p0, ← algebraMap_smul K p1, hp0, hp1, smul_smul, smul_smul, ← div_eq_mul_inv,
    ← div_eq_mul_inv]
  exact (eq_decomp_orthogonal_pair h hs hfr x y hxy hxx hyy v).symm
end Formalism.MainNotions.BridgeLemma₂
