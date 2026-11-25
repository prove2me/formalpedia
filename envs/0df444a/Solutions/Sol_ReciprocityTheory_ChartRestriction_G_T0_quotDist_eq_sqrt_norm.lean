-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.quotDist_eq_sqrt_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:48:47.845047+00:00
-- url     : https://prove2.me/submissions/09c6d08e-756b-4812-ab05-3f87b7ae4426

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsSmallSaturatingVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_normSqSum_add_of_orthogonal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_orthogonal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (q : Fin r → K) : hQdist σ b q = Real.sqrt (hns (hPm σ b *ᵥ fun i => σ (q i))) := by
  set v : Fin r → ℂ := fun i => σ (q i) with hv
  set G := (hBm σ b)ᴴ * hBm σ b with hG
  have hterm : ∀ z : Fin k → ℂ,
      (∑ i, ‖σ (q i) + ∑ j, z j * σ (b j i)‖ ^ 2) = hns (v + hBm σ b *ᵥ z) := by
    intro z
    simp only [hns]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [v, hBm, mulVec, dotProduct, mul_comm]
  have hdec : ∀ z, v + hBm σ b *ᵥ z =
      hPm σ b *ᵥ v + hBm σ b *ᵥ (z + G⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ v)) := by
    intro z
    simp only [hPm, sub_mulVec, one_mulVec, mulVec_add, ← mulVec_mulVec]
    abel
  have hmin : ∀ z, hns (hPm σ b *ᵥ v) ≤ hns (v + hBm σ b *ᵥ z) := by
    intro z
    rw [hdec z, normSqSum_add_of_orthogonal _ _ (orthogonalProjector_orthogonal σ hb _ _)]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
  have hat : v + hBm σ b *ᵥ (-(G⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ v))) = hPm σ b *ᵥ v := by
    rw [hdec, neg_add_cancel, mulVec_zero, add_zero]
  unfold hQdist
  simp_rw [hterm]
  apply le_antisymm
  · exact (ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact Real.sqrt_nonneg _⟩ _).trans_eq (by rw [hat])
  · exact le_ciInf fun z => Real.sqrt_le_sqrt (hmin z)
end ReciprocityTheory.ChartRestriction.G.T0
