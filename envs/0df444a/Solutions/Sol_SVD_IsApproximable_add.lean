-- Prove2me | solution 1 for SVD.IsApproximable.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:46.240692+00:00
-- url     : https://prove2.me/submissions/4b3b13dd-14e6-4f3f-bb05-999f035a9b54

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
public import Theorems.Thm_SVD_isApproximable_iff_existsLimit
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open Filter Topology
open SVD
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SVD
namespace IsApproximable
theorem _root_.solution {S T : X →L[𝕜] Y}
    (hS : IsApproximable S) (hT : IsApproximable T) :
    IsApproximable (S + T) := by
  rw [isApproximable_iff_existsLimit] at hS hT ⊢
  obtain ⟨L, hL_rank, hL_lim⟩ := hS
  obtain ⟨K, hK_rank, hK_lim⟩ := hT
  refine ⟨fun n => L (n / 2) + K (n - n / 2), ?_, ?_⟩
  · -- rank `Lₙ/₂ + Kₙ₋ₙ/₂` ≤ n/2 + (n - n/2) = n.
    intro n
    have h_split : n / 2 + (n - n / 2) = n :=
      Nat.add_sub_cancel' (Nat.div_le_self n 2)
    have h_rank_add :
        (L (n / 2) + K (n - n / 2)).rank ≤
          (L (n / 2)).rank + (K (n - n / 2)).rank :=
      LinearMap.rank_add_le _ _
    calc (L (n / 2) + K (n - n / 2)).rank
        ≤ (L (n / 2)).rank + (K (n - n / 2)).rank := h_rank_add
      _ ≤ ((n / 2 : ℕ) : Cardinal) + ((n - n / 2 : ℕ) : Cardinal) :=
          add_le_add (hL_rank _) (hK_rank _)
      _ = ((n / 2 + (n - n / 2) : ℕ) : Cardinal) := by push_cast; rfl
      _ = (n : Cardinal) := by rw [h_split]
  · -- ‖(S+T) - (Lₙ/₂ + Kₙ₋ₙ/₂)‖ ≤ ‖S - Lₙ/₂‖ + ‖T - Kₙ₋ₙ/₂‖ → 0.
    have h_norm_bd : ∀ n, ‖(S + T) - (L (n / 2) + K (n - n / 2))‖ ≤
                            ‖S - L (n / 2)‖ + ‖T - K (n - n / 2)‖ := by
      intro n
      have h_eq : (S + T) - (L (n / 2) + K (n - n / 2)) =
                    (S - L (n / 2)) + (T - K (n - n / 2)) := by abel
      rw [h_eq]; exact norm_add_le _ _
    -- Both subsequences `n/2` and `n - n/2` diverge to ∞.
    have h_div : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
      Nat.tendsto_div_const_atTop (by norm_num)
    have h_sub : Tendsto (fun n : ℕ => n - n / 2) atTop atTop := by
      have h_dom : ∀ n : ℕ, n / 2 ≤ n - n / 2 := fun n => by omega
      exact tendsto_atTop_mono h_dom h_div
    have h_lim_L : Tendsto (fun n => ‖S - L (n / 2)‖) atTop (𝓝 0) :=
      hL_lim.comp h_div
    have h_lim_K : Tendsto (fun n => ‖T - K (n - n / 2)‖) atTop (𝓝 0) :=
      hK_lim.comp h_sub
    have h_lim_sum :
        Tendsto (fun n => ‖S - L (n / 2)‖ + ‖T - K (n - n / 2)‖)
          atTop (𝓝 0) := by simpa using h_lim_L.add h_lim_K
    exact squeeze_zero (fun _ => norm_nonneg _) h_norm_bd h_lim_sum
end IsApproximable
end SVD
