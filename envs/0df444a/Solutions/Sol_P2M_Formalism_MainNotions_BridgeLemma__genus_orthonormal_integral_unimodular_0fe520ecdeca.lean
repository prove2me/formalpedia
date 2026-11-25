-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__genus_orthonormal_integral_unimodular_0fe520ecdeca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:30:11.578098+00:00
-- url     : https://prove2.me/submissions/9aa99a1e-f4a6-4931-8fd0-bf0bed3262ee

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_GenusOrthonormalIntegralUnimodular
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__star_algebraMap_mem_range_608979362cd4
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__fg_of_orthonormal_basis_b96de8b44bc5
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__integral_of_orthonormal_basis_bf41afc29196
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__unimodular_of_orthonormal_basis_66c8c2117918
import Theorems.Thm_Formalism_HermitianLatticesTheory_final_genusBasic


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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n)
    (M : Submodule (𝓞 K) V) (hM : M ∈ genus h L) : IsIntegralLat h M ∧ dual h M = M := by
  have hG := (final_genusBasic (𝓞 K) K V h hs star_algebraMap_mem_range).2.2 L M (fg_of_orthonormal_basis h L hL) hM.1.fg hM.2
  exact ⟨hG.2.1 (integral_of_orthonormal_basis h L hL), hG.1.1 (unimodular_of_orthonormal_basis h L hL)⟩
end Formalism.MainNotions.BridgeLemma₂
