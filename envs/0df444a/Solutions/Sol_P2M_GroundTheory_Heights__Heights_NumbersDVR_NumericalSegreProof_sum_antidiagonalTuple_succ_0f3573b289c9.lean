-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_sum_antidiagonalTuple_succ_0f3573b289c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:40:40.056071+00:00
-- url     : https://prove2.me/submissions/14596d68-70ad-491f-b46b-28cc9ab08dab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
theorem _root_.solution {A : Type*} [AddCommMonoid A] (i c : ℕ)
    (f : (Fin (i + 1) → ℕ) → A) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple (i + 1) (c + 1), f α =
      ∑ α ∈ Finset.Nat.antidiagonalTuple i (c + 1), f (Fin.snoc α 0) +
        ∑ β ∈ Finset.Nat.antidiagonalTuple (i + 1) c,
          f (Function.update β (Fin.last i) (β (Fin.last i) + 1)) := by
  have hsum : ∀ (α : Fin (i + 1) → ℕ) (v : ℕ),
      ∑ j, Function.update α (Fin.last i) v j = ∑ j : Fin i, α (Fin.castSucc j) + v := by
    intro α v
    rw [Fin.sum_univ_castSucc]
    simp
  have hsum' : ∀ α : Fin (i + 1) → ℕ,
      ∑ j, α j = ∑ j : Fin i, α (Fin.castSucc j) + α (Fin.last i) := fun α =>
    Fin.sum_univ_castSucc α
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun α : Fin (i + 1) → ℕ => α (Fin.last i) = 0)]
  congr 1
  · refine Finset.sum_nbij' Fin.init (fun α => Fin.snoc α 0) ?_ ?_ ?_ ?_ ?_
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      rw [hsum'] at hα
      simpa [Fin.init, hα.2] using hα.1
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      refine ⟨?_, by simp⟩
      rw [hsum']
      simpa using hα
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [← hα.2, Fin.snoc_init_self]
    · intro α _
      exact Fin.init_snoc _ _
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [← hα.2, Fin.snoc_init_self]
  · have linv : ∀ α : Fin (i + 1) → ℕ, α (Fin.last i) ≠ 0 →
        Function.update (Function.update α (Fin.last i) (α (Fin.last i) - 1)) (Fin.last i)
          (Function.update α (Fin.last i) (α (Fin.last i) - 1) (Fin.last i) + 1) = α := by
      intro α hα
      rw [Function.update_self, Function.update_idem, Nat.sub_add_cancel (Nat.pos_of_ne_zero hα),
        Function.update_eq_self]
    refine Finset.sum_nbij' (fun α => Function.update α (Fin.last i) (α (Fin.last i) - 1))
      (fun β => Function.update β (Fin.last i) (β (Fin.last i) + 1)) ?_ ?_ ?_ ?_ ?_
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      rw [hsum]
      rw [hsum'] at hα
      omega
    · intro β hβ
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
      rw [hsum, Function.update_self]
      rw [hsum'] at hβ
      refine ⟨by omega, by omega⟩
    · intro α hα
      simp only [Finset.mem_filter] at hα
      exact linv α hα.2
    · intro β _
      simp
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [linv α hα.2]
end GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
