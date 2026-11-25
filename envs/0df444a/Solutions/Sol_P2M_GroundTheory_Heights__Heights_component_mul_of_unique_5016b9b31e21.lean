-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_component_mul_of_unique_5016b9b31e21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:32.993082+00:00
-- url     : https://prove2.me/submissions/e8717984-ede1-40df-9117-291a96f8cd55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_weightSet_component_481e5721c867
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_weightSet_ae282eab400e

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (p q : MvPolynomial σ R) (a b : ℕ)
    (h : ∀ a' ∈ weightSet w p, ∀ b' ∈ weightSet w q, a' + b' = a + b → a' = a ∧ b' = b) :
    weightedHomogeneousComponent w (a + b) (p * q) =
      weightedHomogeneousComponent w a p * weightedHomogeneousComponent w b q := by
  classical
  conv_lhs => rw [← sum_weightSet_component (w := w) p, ← sum_weightSet_component (w := w) q,
    Finset.sum_mul_sum]
  rw [map_sum]
  have hterm : ∀ a' ∈ weightSet w p, ∀ b' ∈ weightSet w q,
      weightedHomogeneousComponent w (a + b)
        (weightedHomogeneousComponent w a' p * weightedHomogeneousComponent w b' q) =
      if a' = a ∧ b' = b then weightedHomogeneousComponent w a p * weightedHomogeneousComponent w b q
        else 0 := by
    intro a' ha' b' hb'
    have hh := (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) a' p).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) b' q)
    by_cases hs : a' + b' = a + b
    · obtain ⟨rfl, rfl⟩ := h a' ha' b' hb' hs
      rw [if_pos ⟨rfl, rfl⟩, hh.weightedHomogeneousComponent_same]
    · rw [hh.weightedHomogeneousComponent_ne _ (Ne.symm hs)]
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact hs rfl
  rw [Finset.sum_congr rfl fun a' ha' => map_sum _ _ _]
  rw [Finset.sum_congr rfl fun a' ha' => Finset.sum_congr rfl fun b' hb' => hterm a' ha' b' hb']
  by_cases ha : a ∈ weightSet w p
  · by_cases hb : b ∈ weightSet w q
    · rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · rw [if_pos ⟨rfl, rfl⟩]
        · intro b' _ hb'
          rw [if_neg fun h => hb' h.2]
        · intro hb'
          exact absurd hb hb'
      · intro a' _ ha'
        exact Finset.sum_eq_zero fun b' _ => if_neg fun h => ha' h.1
      · intro ha'
        exact absurd ha ha'
    · have : weightedHomogeneousComponent w b q = 0 := by
        apply weightedHomogeneousComponent_eq_zero'
        intro d hd hdb
        exact hb (mem_weightSet.mpr ⟨d, hd, hdb⟩)
      rw [this, mul_zero]
      exact Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => by
        split_ifs <;> simp
  · have : weightedHomogeneousComponent w a p = 0 := by
      apply weightedHomogeneousComponent_eq_zero'
      intro d hd hda
      exact ha (mem_weightSet.mpr ⟨d, hd, hda⟩)
    rw [this, zero_mul]
    exact Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => by
      split_ifs <;> simp
end GroundTheory.Heights₂.Heights
