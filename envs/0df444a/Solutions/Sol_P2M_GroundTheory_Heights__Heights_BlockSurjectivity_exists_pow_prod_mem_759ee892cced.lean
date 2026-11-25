-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_pow_prod_mem_759ee892cced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:45:09.944793+00:00
-- url     : https://prove2.me/submissions/55057dbd-856c-4e3e-9c23-9ddb05fd7d0c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_self_90c3898f7ac0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_of_ne_12930e8adeee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_972328f14a36

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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ)
    (hw0 : w () ≠ 0) (hno : ∀ z ∈ P.points ℂ, z k₀ ≠ w ()) :
    ∃ N : ℕ, ∀ c : (k : ι) → Fin (n k + 1),
      (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ^ N ∈ fibreIdeal P k₀ w := by
  classical
  have hprod : ∀ c : (k : ι) → Fin (n k + 1), ∃ N : ℕ,
      (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ^ N ∈ fibreIdeal P k₀ w := by
    intro c
    have hmem : (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ∈
        vanishingIdeal ℂ (zeroLocus ℂ (fibreIdeal P k₀ w)) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [aeval_eq_eval, eval_prod]
      by_contra hne
      rw [Finset.prod_eq_zero_iff] at hne
      push Not at hne
      refine hno (withBlock k₀ (w ()) x) ⟨fun k ↦ ?_, fun f hf ↦ ?_⟩ (withBlock_self _ _ _)
      · by_cases h : k = k₀
        · subst h
          rw [withBlock_self]
          exact hw0
        · rw [withBlock_of_ne h]
          intro h0
          exact hne k (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩) (by simpa using congrFun h0 (c k))
      · have h0 := (mem_zeroLocus_iff.mp hx) _ (Ideal.subset_span ⟨f, hf, rfl⟩)
        rw [aeval_eq_eval, eval_atBlock] at h0
        exact h0
    rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
    exact hmem
  choose Nc hNc using hprod
  refine ⟨∑ c, Nc c, fun c ↦ ?_⟩
  have hle : Nc c ≤ ∑ c, Nc c := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c)
  rw [← Nat.sub_add_cancel hle, pow_add]
  exact Ideal.mul_mem_left _ _ (hNc c)
end GroundTheory.Heights₂.Heights.BlockSurjectivity
