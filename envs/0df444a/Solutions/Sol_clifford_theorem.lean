-- Prove2me | solution 1 for clifford_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:57:54.786171+00:00
-- url     : https://prove2.me/submissions/6f021cbf-0409-4556-95d8-3dfdc9e00999

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
public import Theorems.Thm_riemann_roch_for_graphs
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_degree_of_canonical_divisor
public import Theorems.Thm_effective_divisor_decomposition
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_rank_geq_iff
public import Theorems.Thm_winnable_add_winnable
public import Theorems.Thm_zero_divisor_rank
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
universe u
open Multiset Finset
private lemma rank_subadditive (G : CFGraph) (D D' : CFDiv G)
    (h_D : rank G D ≥ 0) (h_D' : rank G D' ≥ 0) :
    rank G (D+D') ≥ rank G D + rank G D' := by
  -- Express the two (nonnegative) ranks as natural numbers
  obtain ⟨k₁, h_k₁⟩ : ∃ k : ℕ, (k : ℤ) = rank G D := ⟨_, Int.toNat_of_nonneg h_D⟩
  obtain ⟨k₂, h_k₂⟩ : ∃ k : ℕ, (k : ℤ) = rank G D' := ⟨_, Int.toNat_of_nonneg h_D'⟩

  -- Show rank is ≥ k₁ + k₂ by proving rank_geq
  have h_rank_geq : rank_geq G (D + D') (k₁ + k₂) := by
    -- Take any effective divisor E'' of degree k₁ + k₂
    rintro E'' ⟨h_eff, h_deg⟩

    -- Decompose E'' into E₁ and E₂ of degrees k₁ and k₂
    obtain ⟨E₁, E₂, h_E₁_eff, h_E₂_eff, h_E₁_deg, h_E₂_deg, h_sum⟩ :=
      effective_divisor_decomposition G E'' k₁ k₂ h_eff h_deg

    -- Apply rank_geq to get winnability for both parts
    have h_D_win := (rank_geq_iff G D k₁).mpr (le_of_eq h_k₁) E₁ ⟨h_E₁_eff, h_E₁_deg⟩
    have h_D'_win := (rank_geq_iff G D' k₂).mpr (le_of_eq h_k₂) E₂ ⟨h_E₂_eff, h_E₂_deg⟩

    -- Show winnability of sum
    rw [h_sum]
    have h := winnable_add_winnable G (D-E₁) (D'-E₂) h_D_win h_D'_win
    rw [show D - E₁ + (D' - E₂) = (D + D') - (E₁ + E₂) by abel] at h
    exact h

  have h_final := (rank_geq_iff G (D+D') (k₁+k₂)).mp h_rank_geq
  linarith
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset
theorem _root_.solution
    {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G)
    (h_D : rank G D ≥ 0)
    (h_KD : rank G (canonical_divisor G - D) ≥ 0) :
    (rank G D : ℚ) ≤ (deg D : ℚ) / 2 := by
  -- Get canonical divisor K's rank using Riemann-Roch
  have h_K_rank : rank G (canonical_divisor G) = genus G - 1 := by
    -- Apply Riemann-Roch with D = K
    have h_rr := riemann_roch_for_graphs h_conn (canonical_divisor G)
    -- For K-K = 0, rank is 0
    have h_K_minus_K : rank G (canonical_divisor G - canonical_divisor G) = 0 := by
      -- Show that this divisor is the zero divisor
      have h1 : (canonical_divisor G - canonical_divisor G) = 0 := by
        simp only [sub_self]
      -- Show that the zero divisor has rank 0
      have h2 : rank G 0 = 0 := zero_divisor_rank G
      -- Substitute back
      rw [h1, h2]
    -- Substitute into Riemann-Roch
    rw [h_K_minus_K] at h_rr
    -- Use degree_of_canonical_divisor
    rw [degree_of_canonical_divisor] at h_rr
    -- Solve for rank G K
    linarith

  -- Apply rank subadditivity
  have h_subadd := rank_subadditive G D (canonical_divisor G - D) h_D h_KD
  -- The sum D + (K-D) = K
  have h_sum : (D + (canonical_divisor G - D)) = canonical_divisor G := by
    funext v
    simp only [Pi.add_apply, Pi.sub_apply, add_sub_cancel]
  rw [h_sum] at h_subadd
  rw [h_K_rank] at h_subadd

  -- Use Riemann-Roch to get r(K-D) in terms of r(D)
  have h_rr := riemann_roch_for_graphs h_conn D

  -- Combining subadditivity and Riemann-Roch gives 2 r(D) ≤ deg D; conclude in ℚ
  have h_two : 2 * rank G D ≤ deg D := by linarith
  have h_two' : (2 : ℚ) * (rank G D : ℚ) ≤ (deg D : ℚ) := by exact_mod_cast h_two
  linarith
