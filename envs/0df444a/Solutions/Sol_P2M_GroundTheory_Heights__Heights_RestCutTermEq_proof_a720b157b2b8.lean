-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTermEq_proof_a720b157b2b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:32.956671+00:00
-- url     : https://prove2.me/submissions/85f92d75-0b62-48ed-beb9-3abe514cb316

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTermEq

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
namespace GroundTheory.Heights₂.Heights
namespace RestCutTermEq
theorem _root_.solution (h₁ : RestCutRealSyzygy.Statement) (h₂ : RestCutPsiFlag.Statement)
    (h₃ : RestCutTransportPsum.Statement) : RestCutTermEq.Statement := by
  intro f j k N e I c hcomp F Q₀ hQ₀ hQ₀h Q hQ m hm1 hmN τ G hG
  have hNjk : N = j + k := by simpa using Fintype.card_congr e
  subst hNjk
  have hf : 0 < f := Fin.pos τ
  set E' : Fin f × (Fin j ⊕ Fin k) → Fin f × Fin (j + k) := fun p => (p.1, e.symm p.2) with hE'
  have hpr : ∀ x : RootPoly f j k, restRename f j k (j + k) e (rename E' x) = x := by
    intro x
    rw [restRename, rename_rename]
    convert rename_id_apply x
    funext p
    simp [hE']
  have hrp : ∀ x : MvPolynomial (Fin f × Fin (j + k)) ℝ, rename E' (restRename f j k (j + k) e x) = x := by
    intro x
    rw [restRename, rename_rename]
    convert rename_id_apply x
    funext p
    simp [hE']
  have hpsum : ∀ l σ, rename E' (rootPsum f j k l σ) =
      map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) := by
    intro l σ
    rw [← h₃ f j k (j + k) e l σ]
    exact hrp _
  set R : ℕ → Fin f → MvPolynomial (Fin f × Fin (j + k)) ℝ :=
    fun l σ => rename E' (Q σ l) - map (algebraMap ℚ ℝ) (Q₀ l σ) with hR
  have hsyz : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f,
      map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) * R l σ = 0 := by
    simp only [hR, mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    have h1 : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f,
        map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) * rename E' (Q σ l) =
        rename E' (restTransport f j k (j + k) e F) := by
      rw [hQ.2, map_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [map_mul, hpsum]
    have h2 : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f,
        map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) *
          map (algebraMap ℚ ℝ) (Q₀ l σ) = map (algebraMap ℚ ℝ) F := by
      rw [hQ₀]
      simp only [map_sum, map_mul]
    rw [h1, h2]
    exact hrp _
  have hzero := h₁ f (j + k) R hsyz m hm1 hmN τ G hG
  have hDle : j + k ≤ flagDim f j k + 1 := by
    have h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1) := by
      rcases Nat.lt_or_ge (j + k) 2 with h | h
      · interval_cases h : (j + k) <;> simp
      · rw [mul_comm]; exact Nat.mul_le_mul_right _ h
    have h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 h1
    have h3 : (j + k) * (j + k - 1) / 2 ≤ flagDim f j k := by
      unfold flagDim; exact Nat.le_mul_of_pos_left _ hf
    omega
  have hdeg : m - 1 + (flagDim f j k + 1 - m) = flagDim f j k := by omega
  have hQh : (rename E' (Q τ m)).IsHomogeneous (flagDim f j k + 1 - m) :=
    (hQ.1 τ m hm1 hmN).rename_isHomogeneous
  have hQ₀m := hQ₀h m τ hm1 hmN
  have hsplit : restTransport f j k (j + k) e G * Q τ m =
      restRename f j k (j + k) e (map (algebraMap ℚ ℝ) G * R m τ) +
        restRename f j k (j + k) e (map (algebraMap ℚ ℝ) (G * Q₀ m τ)) := by
    rw [← map_add, hR]
    simp only
    rw [map_mul (map (algebraMap ℚ ℝ)) G, ← mul_add, sub_add_cancel, map_mul, hpr]
    rfl
  rw [hsplit, map_add, hcomp _ ?_, hcomp _ ?_, hzero, (h₂ f (j + k)).1]
  · ring
  · rw [← hdeg]; exact ((hG.mul hQ₀m).map _)
  · rw [← hdeg]
    exact (hG.map _).mul (hQh.sub (hQ₀m.map _))
end RestCutTermEq
end GroundTheory.Heights₂.Heights
