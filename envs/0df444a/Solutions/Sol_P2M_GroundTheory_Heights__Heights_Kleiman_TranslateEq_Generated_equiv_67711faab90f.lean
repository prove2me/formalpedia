-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:05.987349+00:00
-- url     : https://prove2.me/submissions/c7da3302-4ed4-4db2-9201-13c00f0e583c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedMod_equiv_bab59235570c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_polyGraded_equiv_07714b7c3c16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRingI_equiv_6c221ab935ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRing_equiv_3295007ad279
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_dimCl_equiv_c39cbd206b03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lineX_equiv_6acfbe997019
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_image2_eq_67f8a4da0bc8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace Generated
theorem _root_.solution (F : Kleiman.SubFamily S x E) :
    IndefiniteRowSideFullHecke.Kleiman.IsGenerated S x (toIndefiniteRowSideFullHecke F.toSubSystem) ↔ F.toSubSystem.Generated := by
  have key : ∀ {i : Fin (N + 1)} (h : x i ≠ 0),
      Submodule.span S (Set.image2 (· • ·) (ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i : Set Ω)
        (IndefiniteRowSideFullHecke.Kleiman.secs S x (toIndefiniteRowSideFullHecke F.toSubSystem) : Set E)) =
      (Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart h)) (F.secs : Set E)).restrictScalars S := by
    intro i h
    rw [secs.equiv, chartRing.equiv S x h]
    exact span_image2_eq _ _
  constructor
  · intro hg I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
    have hsub : {i} ⊆ I.1 := Finset.singleton_subset_iff.mpr hi
    have hi' : F.sub (Kleiman.singleChart hxi) =
        Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hxi)) (F.secs : Set E) := by
      have := hg i hxi
      rw [key hxi, chartModule_of_ne_zero _ hxi] at this
      exact Submodule.restrictScalars_injective S _ _ this
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      rw [Kleiman.SubSystem.secs, SetLike.mem_coe, Submodule.mem_iInf] at hy
      exact hy I
    · intro y hy
      obtain ⟨a, ⟨u, hu⟩, hay⟩ := (F.mem_iff (Kleiman.singleChart hxi) I hsub y).mp hy
      rw [hi'] at hay
      have hmono : ∀ w ∈ Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hxi)) (F.secs : Set E),
          w ∈ Submodule.span (Kleiman.chartRing S x I) (F.secs : Set E) := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem z hz => exact Submodule.subset_span hz
        | zero => exact zero_mem _
        | add u v _ _ hu hv => exact add_mem hu hv
        | smul b w _ hw =>
          have : b • w = (Kleiman.chartIncl hsub b) • w := rfl
          rw [this]
          exact Submodule.smul_mem _ _ hw
      have hay' := hmono _ hay
      have hinv : ((↑u⁻¹ : Kleiman.chartRing S x I) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy' : y = (↑u⁻¹ : Kleiman.chartRing S x I) • ((a : Ω) • y) := by
        rw [Subalgebra.smul_def, ← mul_smul, hinv, one_smul]
      rw [hy']
      exact Submodule.smul_mem _ _ hay'
  · intro hg i hxi
    rw [key hxi, chartModule_of_ne_zero _ hxi, hg]
end Generated
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
