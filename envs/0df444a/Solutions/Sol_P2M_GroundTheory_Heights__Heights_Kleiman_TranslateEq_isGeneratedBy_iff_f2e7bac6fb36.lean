-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_isGeneratedBy_iff_f2e7bac6fb36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:10:47.418188+00:00
-- url     : https://prove2.me/submissions/3836706d-fe77-4a7d-b054-f51f96bd6c7f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_congr_dddc775e54fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedMod_equiv_bab59235570c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_PrimeFiltration_equiv_055a468f012b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_bundleA_equiv_9a6f65d8882f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRingI_equiv_6c221ab935ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRing_equiv_3295007ad279
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_dimCl_equiv_c39cbd206b03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lineX_equiv_6acfbe997019
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lmul_equiv_a9ac80d74948
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lpow_equiv_da141a3f94b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_polyGraded_equiv_07714b7c3c16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_image2_eq_67f8a4da0bc8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9


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
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (B : Kleiman.SubFamily S x Ω) (B' : Fin (N + 1) → Submodule S Ω)
    (hB : ∀ i, x i ≠ 0 → B' i = toIndefiniteRowSideFullHecke B.toSubSystem i) {r : ℕ} (η : Fin (r + 1) → Ω) :
    IndefiniteRowSideFullHecke.Kleiman.IsGeneratedBy S x B' η ↔
      (∀ j, η j ∈ B.secs) ∧ ∀ I, Submodule.span (Kleiman.chartRing S x I) (Set.range η) = B.sub I := by
  have hsecs : IndefiniteRowSideFullHecke.Kleiman.secs S x B' = B.secs := by
    rw [← secs.equiv]
    exact secs_congr hB
  have key : ∀ {i : Fin (N + 1)} (h : x i ≠ 0),
      Submodule.span S (Set.image2 (· • ·) (ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i : Set Ω) (Set.range η)) =
      (Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart h)) (Set.range η)).restrictScalars S := by
    intro i h
    rw [chartRing.equiv S x h]
    exact span_image2_eq _ _
  unfold IndefiniteRowSideFullHecke.Kleiman.IsGeneratedBy
  rw [hsecs]
  constructor
  · rintro ⟨hη, hg⟩
    refine ⟨hη, fun I => ?_⟩
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
    have hsub : {i} ⊆ I.1 := Finset.singleton_subset_iff.mpr hi
    have hi' : B.sub (Kleiman.singleChart hxi) =
        Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hxi)) (Set.range η) := by
      have := hg i hxi
      rw [key hxi, hB i hxi, chartModule_of_ne_zero _ hxi] at this
      exact Submodule.restrictScalars_injective S _ _ this
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have := hη j
      rw [Kleiman.SubSystem.secs, Submodule.mem_iInf] at this
      exact this I
    · intro y hy
      obtain ⟨a, ⟨u, hu⟩, hay⟩ := (B.mem_iff (Kleiman.singleChart hxi) I hsub y).mp hy
      rw [hi'] at hay
      have hmono : ∀ w ∈ Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hxi)) (Set.range η),
          w ∈ Submodule.span (Kleiman.chartRing S x I) (Set.range η) := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem z hz => exact Submodule.subset_span hz
        | zero => exact zero_mem _
        | add p q _ _ hp hq => exact add_mem hp hq
        | smul c w _ hw =>
          have : c • w = (Kleiman.chartIncl hsub c) • w := rfl
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
  · rintro ⟨hη, hg⟩
    refine ⟨hη, fun i hxi => ?_⟩
    rw [key hxi, hB i hxi, chartModule_of_ne_zero _ hxi, hg]
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
