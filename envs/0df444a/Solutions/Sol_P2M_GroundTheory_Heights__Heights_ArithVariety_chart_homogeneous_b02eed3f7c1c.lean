-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_chart_homogeneous_b02eed3f7c1c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:16.268233+00:00
-- url     : https://prove2.me/submissions/cbfcde9c-6ae3-4cef-bea5-cac826db6203

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval__scale_of_isWeightedHomogeneous_6a2760d9d5f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.ArithVariety
variable (P : ArithVariety n)
variable (c : (k : ι) → Fin (n k + 1))
namespace GroundTheory.Heights₂.Heights.ArithVariety
theorem _root_.solution (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    (∏ k, P.mkF (X ⟨k, c k⟩) ^ δ k) * eval₂ (Int.castRingHom _) (P.chartCoord c) f = P.mkF f := by
  rw [← eval₂_scale_of_isWeightedHomogeneous _ _ hf]
  have hne : ∀ k, P.mkF (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)
  have : (fun v : Coord n ↦ P.mkF (X ⟨v.1, c v.1⟩) * P.chartCoord c v) = fun v ↦ P.mkF (X v) := by
    funext v
    rw [chartCoord, mul_div_cancel₀ _ (hne v.1)]
  rw [this]
  conv_rhs => rw [← eval₂_eta f]
  rw [eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _
end GroundTheory.Heights₂.Heights.ArithVariety
