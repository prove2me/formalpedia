-- Prove2me | solution 1 for PlankProblem.exists_point_outside_normalized_planks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:11:36.500304+00:00
-- url     : https://prove2.me/submissions/31c2d84c-a377-40e0-b0c5-cb771761cf91

module
public import Definitions.Def_BallPlank_ShiftedPlanks
public import Definitions.Def_BallPlank_BallPlankFinal
public import Theorems.Thm_PlankProblem_sum_smul_mem_of_abs_sum_le
public import Theorems.Thm_PlankProblem_exists_nat_near_grid
public import Theorems.Thm_PlankProblem_sum_abs_le_card_of_norm_le
public import Theorems.Thm_Planks_exists_point_outside_shifted_planks


set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped BigOperators InnerProductSpace Pointwise
noncomputable section
open PlankProblem
variable {n : ℕ}
local notation "Rn" => EuclideanSpace ℝ (Fin n)
namespace PlankProblem
theorem _root_.solution {m : ℕ} {K0 : Set Rn} (hconv : Convex ℝ K0)
    (h0 : (0 : Rn) ∈ K0) (hneg : ∀ x ∈ K0, -x ∈ K0)
    (φ : Fin m → (Rn →ₗ[ℝ] ℝ)) (v : Fin m → Rn) (hv : ∀ i, v i ∈ K0)
    (hφv : ∀ i, φ i (v i) = 1)
    (α β : Fin m → ℝ) (hαβ : ∀ i, α i ≤ β i) (hsum : ∑ i, (β i - α i) / 2 < 1) :
    ∃ y ∈ K0, ∀ i, φ i y < α i ∨ β i < φ i y := by
  classical
  set w : Fin m → ℝ := fun i => (β i - α i) / 2 with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => by simp only [w]; linarith [hαβ i]
  set W := ∑ i, w i with hW
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (m : ℝ) ≤ N * (1 - W) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ((m : ℝ) / (1 - W))
    exact ⟨N, by rwa [div_le_iff₀ (by linarith)] at hN⟩
  set k : Fin m → ℕ := fun i => ⌊w i * N⌋₊ + 1 with hk
  have hkpos : ∀ i, 1 ≤ k i := fun i => by simp [k]
  have hkgt : ∀ i, w i * N < k i := fun i => by
    simp only [k]; push_cast; exact Nat.lt_floor_add_one _
  let ι := Σ i : Fin m, Fin (k i)
  have hcard : ((Fintype.card ι : ℕ) : ℝ) ≤ N := by
    simp only [ι, Fintype.card_sigma, Fintype.card_fin]
    push_cast
    have : ∀ i, ((k i : ℕ) : ℝ) ≤ w i * N + 1 := fun i => by
      simp only [k]; push_cast
      linarith [Nat.floor_le (mul_nonneg (hw0 i) (Nat.cast_nonneg N))]
    calc ∑ i, (k i : ℝ) ≤ ∑ i, (w i * N + 1) := Finset.sum_le_sum fun i _ => this i
      _ = W * N + m := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hW]; simp
      _ ≤ N := by linarith
  set M : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hM
  have hMpos : ∀ _ : ι, 0 < M := fun j => Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨j⟩)
  let s : Fin m → ℝ := fun i => 2 * w i / k i
  let γ : ι → ℝ := fun j => α j.1 + (((j.2 : ℕ) : ℝ) + 1 / 2) * s j.1
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] Rn :=
    ∑ j, (EuclideanSpace.proj j : EuclideanSpace ℝ ι →L[ℝ] ℝ).toLinearMap.smulRight (v j.1)
  have hT : ∀ z, T z = ∑ j, z j • v j.1 := fun z => by simp [T]
  let ℓ : ι → (EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
    fun j => LinearMap.toContinuousLinearMap ((φ j.1).comp T)
  have hℓ : ∀ j, ℓ j (EuclideanSpace.basisFun ι ℝ j) = 1 := fun j => by
    simp only [ℓ, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply, hT,
      EuclideanSpace.basisFun_apply, PiLp.single_apply]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp [hφv]
  obtain ⟨z, hz, hzℓ⟩ := Planks.exists_point_outside_shifted_planks ℓ (fun j => M * γ j)
    (EuclideanSpace.basisFun ι ℝ) (EuclideanSpace.basisFun ι ℝ).orthonormal hℓ
  have hzsum := sum_abs_le_card_of_norm_le z hz
  refine ⟨M⁻¹ • T z, ?_, ?_⟩
  · rw [hT, Finset.smul_sum]
    simp_rw [smul_smul]
    apply sum_smul_mem_of_abs_sum_le hconv h0 hneg _ (fun j => hv _)
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨j⟩⟩
    · simp
    · simp only [abs_mul, ← Finset.mul_sum]
      rw [abs_of_pos (inv_pos.mpr (hMpos j)), inv_mul_le_iff₀ (hMpos j)]
      simpa using hzsum
  · intro i
    by_contra hcon
    push Not at hcon
    rw [map_smul, smul_eq_mul] at hcon
    have hs0 : 0 ≤ s i := by
      simp only [s]; exact div_nonneg (by linarith [hw0 i]) (Nat.cast_nonneg _)
    have hks : α i + (k i : ℝ) * s i = β i := by
      have : (k i : ℝ) ≠ 0 := by have := hkpos i; positivity
      simp only [s, w]; field_simp; ring
    obtain ⟨t, htk, ht⟩ := exists_nat_near_grid (hkpos i) hs0 hcon.1 (hks ▸ hcon.2)
    let j : ι := ⟨i, ⟨t, htk⟩⟩
    have h1 : 1 ≤ |φ i (T z) - M * γ j| := hzℓ j
    have hMj := hMpos j
    have e : φ i (T z) - M * γ j = M * (M⁻¹ * φ i (T z) - γ j) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hMj] at h1
    have hγ : γ j = α i + ((t : ℝ) + 1 / 2) * s i := rfl
    rw [hγ] at h1
    -- M * (s i / 2) < 1
    have hkpos' : (0 : ℝ) < k i := by have := hkpos i; positivity
    have hlt : M * (s i / 2) < 1 := by
      have : M * (s i / 2) = M * w i / k i := by simp only [s]; ring
      rw [this, div_lt_one hkpos']
      nlinarith [hkgt i, hw0 i]
    nlinarith [mul_le_mul_of_nonneg_left ht hMj.le]
end PlankProblem
