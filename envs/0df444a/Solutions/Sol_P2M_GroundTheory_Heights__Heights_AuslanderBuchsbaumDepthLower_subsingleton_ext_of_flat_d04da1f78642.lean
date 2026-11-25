-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_flat_d04da1f78642
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:21.955881+00:00
-- url     : https://prove2.me/submissions/2aa15417-7092-488a-a5dc-5781bca86d0e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAuslanderBuchsbaumDepthLower
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_support_residueModule_5535d1c543f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_maximalIdeal_smul_top_lt_top_3d10a1377dbd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing CategoryTheory Limits Abelian RingTheory.Sequence
universe u
open GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
variable {R : Type u} [CommRing R] [IsLocalRing R]
namespace GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
theorem _root_.solution [IsNoetherianRing R] (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hrs : IsWeaklyRegular R rs) (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Flat R P] :
    ∀ i < rs.length, Subsingleton (Ext (residueModule R) P i) := by
  intro i hi
  rcases subsingleton_or_nontrivial P with hP | hP
  · have hZ : IsZero P := ModuleCat.isZero_of_subsingleton P
    have : Injective P := hZ.injective
    cases i with
    | zero => exact Ext.addEquiv₀.subsingleton_congr.mpr ⟨fun a b => hZ.eq_of_tgt a b⟩
    | succ j => exact Ext.subsingleton_of_injective _ _ j
  · have hreg : IsWeaklyRegular P rs :=
      (LinearEquiv.isWeaklyRegular_congr (TensorProduct.rid R P) rs).mp
        (hrs.isWeaklyRegular_lTensor (M₂ := P))
    have hreg' : IsRegular P rs :=
      (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hreg
    exact ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) (residueModule R)
      support_residueModule.le P (maximalIdeal_smul_top_lt_top P) rs hmem hreg' i hi
end GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
