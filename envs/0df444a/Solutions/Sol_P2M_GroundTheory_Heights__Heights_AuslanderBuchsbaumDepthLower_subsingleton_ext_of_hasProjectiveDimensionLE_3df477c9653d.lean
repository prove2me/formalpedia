-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_hasProjectiveDimensionLE_3df477c9653d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:15.632854+00:00
-- url     : https://prove2.me/submissions/3c8903a5-bc59-4e39-bc55-d9bdbd8dc8e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAuslanderBuchsbaumDepthLower
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_flat_d04da1f78642

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
theorem _root_.solution [IsNoetherianRing R] (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : IsWeaklyRegular R rs) (ℓ : ℕ) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M], HasProjectiveDimensionLE M ℓ →
      ∀ i, i + ℓ < rs.length → Subsingleton (Ext (residueModule R) M i) := by
  induction ℓ with
  | zero =>
    intro M _ hM i hi
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr hM
    exact subsingleton_ext_of_flat rs hmem hrs M i (by omega)
  | succ ℓ ih =>
    intro M _ hM i hi
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    have hS : f.shortComplexKer.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have h₂ : HasProjectiveDimensionLT f.shortComplexKer.X₂ (ℓ + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (ℓ + 1) (by omega)
    have hK : HasProjectiveDimensionLE f.shortComplexKer.X₁ ℓ :=
      hS.hasProjectiveDimensionLT_X₁ (ℓ + 1) h₂ hM
    have e₂ : Subsingleton (Ext (residueModule R) f.shortComplexKer.X₂ i) :=
      subsingleton_ext_of_flat rs hmem hrs _ i (by omega)
    have e₁ : Subsingleton (Ext (residueModule R) f.shortComplexKer.X₁ (i + 1)) :=
      ih _ hK (i + 1) (by omega)
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      ((Ext.covariant_sequence_exact₃' (residueModule R) hS) i (i + 1) rfl)
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr e₂).eq_zero_of_src _)
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr e₁).eq_zero_of_tgt _)
end GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
