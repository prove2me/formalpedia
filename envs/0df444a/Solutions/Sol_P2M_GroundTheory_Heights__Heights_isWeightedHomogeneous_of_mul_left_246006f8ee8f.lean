-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_of_mul_left_246006f8ee8f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:07:16.58848+00:00
-- url     : https://prove2.me/submissions/95d85628-82b2-4c03-9803-b6dc6d8e9474

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_weightSet_ae282eab400e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_component_ne_zero_of_mem_31fa3e9616ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_component_mul_of_unique_5016b9b31e21
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_weightSet_nonempty_9935efbea46e

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
variable {R σ : Type*} [CommRing R] {w : σ → ℕ}
variable [IsDomain R]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {p q : MvPolynomial σ R} {m : ℕ}
    (hpq : IsWeightedHomogeneous w (p * q) m) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ a, IsWeightedHomogeneous w p a := by
  classical
  have hPn := weightSet_nonempty (w := w) hp
  have hQn := weightSet_nonempty (w := w) hq
  set A := (weightSet w p).max' hPn
  set a₀ := (weightSet w p).min' hPn
  set B := (weightSet w q).max' hQn
  set b₀ := (weightSet w q).min' hQn
  have htop : weightedHomogeneousComponent w (A + B) (p * q) ≠ 0 := by
    rw [component_mul_of_unique p q A B]
    · exact mul_ne_zero (component_ne_zero_of_mem (Finset.max'_mem _ _))
        (component_ne_zero_of_mem (Finset.max'_mem _ _))
    · intro a' ha' b' hb' hs
      have h1 := Finset.le_max' _ _ ha'
      have h2 := Finset.le_max' _ _ hb'
      constructor <;> omega
  have hbot : weightedHomogeneousComponent w (a₀ + b₀) (p * q) ≠ 0 := by
    rw [component_mul_of_unique p q a₀ b₀]
    · exact mul_ne_zero (component_ne_zero_of_mem (Finset.min'_mem _ _))
        (component_ne_zero_of_mem (Finset.min'_mem _ _))
    · intro a' ha' b' hb' hs
      have h1 := Finset.min'_le _ _ ha'
      have h2 := Finset.min'_le _ _ hb'
      constructor <;> omega
  have e1 : A + B = m := by
    by_contra hne
    exact htop (hpq.weightedHomogeneousComponent_ne _ hne)
  have e2 : a₀ + b₀ = m := by
    by_contra hne
    exact hbot (hpq.weightedHomogeneousComponent_ne _ hne)
  have hA : a₀ ≤ A := Finset.min'_le _ _ (Finset.max'_mem _ _)
  have hB : b₀ ≤ B := Finset.min'_le _ _ (Finset.max'_mem _ _)
  refine ⟨A, fun d hd => ?_⟩
  have hmem : Finsupp.weight w d ∈ weightSet w p := mem_weightSet.mpr ⟨d, mem_support_iff.mpr hd, rfl⟩
  have h1 := Finset.le_max' _ _ hmem
  have h2 := Finset.min'_le _ _ hmem
  show Finsupp.weight w d = A
  omega
end GroundTheory.Heights₂.Heights
