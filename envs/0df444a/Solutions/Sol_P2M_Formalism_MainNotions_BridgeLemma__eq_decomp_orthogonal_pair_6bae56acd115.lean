-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__eq_decomp_orthogonal_pair_6bae56acd115
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:51.321023+00:00
-- url     : https://prove2.me/submissions/adcbf93b-377e-4f3a-affa-f699b732de38

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
theorem _root_.solution (hs : h.IsSymm) (hfr : finrank K V = 2) (x y : V) (hxy : h x y = 0) (hxx : h x x ≠ 0)
    (hyy : h y y ≠ 0) (v : V) : v = (h x v / h x x) • x + (h y v / h y y) • y := by
  have hyx : h y x = 0 := by rw [← hs.eq x y, hxy, map_zero]
  have hli : LinearIndependent K ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (h x) hst
    have h2 := congrArg (h y) hst
    simp only [map_add, map_smul, smul_eq_mul, hxy, hyx, mul_zero, add_zero, zero_add, map_zero] at h1 h2
    exact ⟨(mul_eq_zero.1 h1).resolve_right hxx, (mul_eq_zero.1 h2).resolve_right hyy⟩
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hfr])
  have hv : v ∈ Submodule.span K (Set.range ![x, y]) := by rw [hsp]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
  rw [Fin.sum_univ_two] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  subst hc
  simp only [map_add, map_smul, smul_eq_mul, hxy, hyx, mul_zero, add_zero, zero_add]
  rw [mul_div_assoc, div_self hxx, mul_one, mul_div_assoc, div_self hyy, mul_one]
end Formalism.MainNotions.BridgeLemma₂
