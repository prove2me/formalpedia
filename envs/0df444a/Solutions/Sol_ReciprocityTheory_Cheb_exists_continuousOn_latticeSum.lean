-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_continuousOn_latticeSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:06.109789+00:00
-- url     : https://prove2.me/submissions/9e0468c8-20bd-4b9b-91b4-65a238a72420

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_LatSum
import Theorems.Thm_ReciprocityTheory_Cheb_tsum_latSum_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set
open ReciprocityTheory ReciprocityTheory.Cheb
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (Λ₀ Λ' : Submodule ℤ V) [DiscreteTopology Λ₀] (hle : Λ' ≤ Λ₀)
    (reps : Finset V) (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂)
    (c' : V → ℂ) (hper : ∀ l ∈ Λ', ∀ β ∈ reps, c' (l + β) = c' β) (hmean : ∑ β ∈ reps, c' β = 0)
    (G : ℝ → V → ℂ) (r : ℝ) (hr : r < -(Module.finrank ℤ Λ₀ : ℝ))
    (hdiff : ∃ R₀ C : ℝ, ∀ s ∈ Icc (1 : ℝ) 2, ∀ β ∈ reps, ∀ x ∈ Λ', R₀ ≤ ‖x‖ →
      ‖G s (x + β) - G s x‖ ≤ C * ‖x‖ ^ r)
    (K : ℝ) (hbound : ∀ s ∈ Icc (1 : ℝ) 2, ∀ x ∈ Λ₀, ‖G s x‖ ≤ K)
    (hsum : ∀ s ∈ Ioc (1 : ℝ) 2, Summable fun α : Λ₀ => G s α)
    (hcont : ∀ x ∈ Λ₀, ContinuousOn (fun s => G s x) (Icc 1 2)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2, F s = ∑' α : Λ₀, c' α * G s α := by
  classical
  obtain ⟨R₀, C, hRC⟩ := hdiff
  set R := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  set A := ∑ β ∈ reps, ‖c' β‖ with hAdef
  have hr0 : r < 0 := lt_of_lt_of_le hr (neg_nonpos.mpr (Nat.cast_nonneg _))
  set X := |C| + 2 * |K| * R ^ (-r) with hXdef
  have hX : 0 ≤ X := by positivity
  let u : Λ' → ℝ := fun l => A * X * ‖(l : V)‖ ^ r + if (l : V) = 0 then A * (2 * |K|) else 0
  have hu : Summable u := by
    refine Summable.add ?_ ?_
    · refine Summable.mul_left (A * X) ?_
      have h0 := ZLattice.summable_norm_rpow Λ₀ r hr
      have h1 := h0.comp_injective (i := fun l : Λ' => (⟨l, hle l.2⟩ : Λ₀))
        (fun a b h => Subtype.ext (congrArg Subtype.val h :))
      exact h1
    · apply summable_of_ne_finset_zero (s := {0})
      intro l hl
      have : (l : V) ≠ 0 := by simpa using hl
      simp [this]
  refine ⟨fun s => ∑' l : Λ', ∑ β ∈ reps, c' β * (G s (l + β) - G s l), ?_, ?_⟩
  · refine continuousOn_tsum (u := u) (fun l => ?_) hu (fun l s hs => ?_)
    · refine continuousOn_finsetSum _ fun β hβ => ?_
      exact continuousOn_const.mul
        ((hcont _ (Λ₀.add_mem (hle l.2) (hmem β hβ))).sub (hcont _ (hle l.2)))
    · have key : ∀ β ∈ reps, ‖G s (l + β) - G s l‖ ≤
          X * ‖(l : V)‖ ^ r + if (l : V) = 0 then 2 * |K| else 0 := by
        intro β hβ
        have h2K : ‖G s (l + β) - G s l‖ ≤ 2 * |K| := by
          refine (norm_sub_le _ _).trans ?_
          have := hbound s hs _ (Λ₀.add_mem (hle l.2) (hmem β hβ))
          have := hbound s hs _ (hle l.2)
          have := le_abs_self K
          linarith
        have hpow : 0 ≤ ‖(l : V)‖ ^ r := Real.rpow_nonneg (norm_nonneg _) _
        by_cases hl0 : (l : V) = 0
        · rw [if_pos hl0]
          nlinarith
        rw [if_neg hl0, add_zero]
        by_cases hR : R ≤ ‖(l : V)‖
        · have := hRC s hs β hβ l l.2 ((le_max_left _ _).trans hR)
          have hC : C * ‖(l : V)‖ ^ r ≤ |C| * ‖(l : V)‖ ^ r :=
            mul_le_mul_of_nonneg_right (le_abs_self C) hpow
          have : 0 ≤ 2 * |K| * R ^ (-r) * ‖(l : V)‖ ^ r := by positivity
          nlinarith
        · rw [not_le] at hR
          have hlpos : 0 < ‖(l : V)‖ := norm_pos_iff.mpr hl0
          have hRr : R ^ r ≤ ‖(l : V)‖ ^ r := Real.rpow_le_rpow_of_nonpos hlpos hR.le hr0.le
          have hone : R ^ (-r) * R ^ r = 1 := by
            rw [Real.rpow_neg hRpos.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hRpos r).ne']
          have hRn : 0 ≤ R ^ (-r) := Real.rpow_nonneg hRpos.le _
          have h3 : 2 * |K| ≤ 2 * |K| * R ^ (-r) * ‖(l : V)‖ ^ r := by
            calc 2 * |K| = 2 * |K| * (R ^ (-r) * R ^ r) := by rw [hone, mul_one]
              _ ≤ 2 * |K| * (R ^ (-r) * ‖(l : V)‖ ^ r) := by gcongr
              _ = _ := by ring
          have : 0 ≤ |C| * ‖(l : V)‖ ^ r := by positivity
          nlinarith
      calc ‖∑ β ∈ reps, c' β * (G s (l + β) - G s l)‖
          ≤ ∑ β ∈ reps, ‖c' β‖ * ‖G s (l + β) - G s l‖ := by
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp only [norm_mul]
        _ ≤ ∑ β ∈ reps, ‖c' β‖ * (X * ‖(l : V)‖ ^ r + if (l : V) = 0 then 2 * |K| else 0) :=
            Finset.sum_le_sum fun β hβ => mul_le_mul_of_nonneg_left (key β hβ) (norm_nonneg _)
        _ = u l := by
            rw [← Finset.sum_mul]
            simp only [u]
            split_ifs <;> ring
  · intro s hs
    exact (tsum_latSum_eq Λ₀ Λ' hle reps hmem hcover huniq c' hper hmean (G s) (hsum s hs)).symm
end ReciprocityTheory.Cheb
