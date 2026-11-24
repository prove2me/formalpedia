-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHomogenise_proof_a08065262b6f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:43.712691+00:00
-- url     : https://prove2.me/submissions/c7f2fbd8-2718-4a50-a8ab-bf9f3555cd78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHomogenise_exists_homogeneous_sub_mem_span_2f27af3c3435
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_7a22acaba460


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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHomogenise
attribute [local instance] MvPolynomial.gradedAlgebra
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartHomogenise
theorem _root_.solution : ChartHomogenise.Statement := by
  intro F _ n Q t hQ ht
  set 𝒜 := homogeneousSubmodule (Fin n) F
  set W : Ideal (MvPolynomial (Fin n) F) := (Q.homogeneousCore 𝒜).toIdeal with hW
  have hWQ : W ≤ Q := Ideal.toIdeal_homogeneousCore_le _ _
  have hWprime : W.IsPrime := hQ.homogeneousCore
  have hWhom : IsHomogIdeal W := (isHomogIdeal_iff W).mpr (Q.homogeneousCore 𝒜).isHomogeneous
  have hℓ : (linForm t).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _
  have hℓQ : linForm t ∉ Q := by
    intro h
    apply hQ.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using Q.sub_mem h ht
  have hℓW : linForm t ∉ W := fun h => hℓQ (hWQ h)
  have hrel : IsRelevant W := by
    by_contra h
    simp only [IsRelevant, not_exists, not_not] at h
    exact hℓW (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (h j))
  refine ⟨W, ⟨hWprime, hWhom, hrel⟩, hℓW, le_antisymm ?_ ?_, ?_⟩
  · exact sup_le hWQ ((Ideal.span_singleton_le_iff_mem _).mpr ht)
  · intro g hg
    obtain ⟨G, D, hG, hGg⟩ := exists_homogeneous_sub_mem_span (linForm t) g hℓ
    have hspan : Ideal.span {linForm t - 1} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr ht
    have hGQ : G ∈ Q := by simpa using Q.add_mem (hspan hGg) hg
    have hGW : G ∈ W :=
      Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨D, (mem_homogeneousSubmodule D G).mpr hG⟩ hGQ
    have : g = G - (G - g) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)
  · intro J hJ hJQ
    have hJh := (isHomogIdeal_iff J).mp hJ
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hJQ
end GroundTheory.Heights₂.Heights.ChartHomogenise
