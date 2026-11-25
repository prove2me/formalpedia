-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__integral_of_orthonormal_basis_bf41afc29196
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:03:58.926256+00:00
-- url     : https://prove2.me/submissions/710edb73-50ad-4049-b748-23d761a21d05

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_GenusOrthonormalIntegralUnimodular
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__star_algebraMap_mem_range_608979362cd4
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_sum_orthonormal_bc617198dc85

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
open NumberField Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) :
    IsIntegralLat h L := by
  obtain ⟨e, -, -, rfl, he⟩ := hL
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hx
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hy
  have e1 : ∑ i, a i • e i = ∑ i, (algebraMap (𝓞 K) K (a i)) • e i :=
    Finset.sum_congr rfl fun i _ => (algebraMap_smul K (a i) (e i)).symm
  have e2 : ∑ i, b i • e i = ∑ i, (algebraMap (𝓞 K) K (b i)) • e i :=
    Finset.sum_congr rfl fun i _ => (algebraMap_smul K (b i) (e i)).symm
  rw [e1, e2, inner_sum_orthonormal h e he]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨a', ha'⟩ := star_algebraMap_mem_range (a i)
  rw [← ha', ← map_mul]
  exact Submodule.mem_one.2 ⟨_, rfl⟩
end Formalism.MainNotions.BridgeLemma₂
