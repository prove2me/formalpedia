-- Prove2me | solution 1 for SampleRemoval.gram_posDef_iff_card_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:34:47.306031+00:00
-- url     : https://prove2.me/submissions/2c9c4c8f-6aae-43db-bbd4-35665bcff1c8

import Mathlib
import Definitions.Def_SampleRemoval_gram
import Definitions.Def_SampleRemoval_GeneralPosition

section
set_option autoImplicit false

open Matrix

namespace SampleRemoval
namespace Dev
namespace GramPD

theorem gram_mulVec {n d : ℕ} (x : Fin n → Fin d → ℝ) (w : Fin n → ℝ) (v : Fin d → ℝ) :
    gram x w *ᵥ v = ∑ i, (w i * (x i ⬝ᵥ v)) • x i := by
  ext j
  simp only [gram, Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.smul_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem quad {n d : ℕ} (x : Fin n → Fin d → ℝ) (w : Fin n → ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ (gram x w *ᵥ v) = ∑ i, w i * (x i ⬝ᵥ v) ^ 2 := by
  rw [gram_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, dotProduct_comm v (x i), smul_eq_mul]
  ring

theorem herm {n d : ℕ} (x : Fin n → Fin d → ℝ) (w : Fin n → ℝ) : (gram x w).IsHermitian := by
  ext a b
  simp only [gram, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, star_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem posDef_iff {n d : ℕ} (x : Fin n → Fin d → ℝ) (w : Fin n → ℝ) :
    (gram x w).PosDef ↔ ∀ v : Fin d → ℝ, v ≠ 0 → 0 < ∑ i, w i * (x i ⬝ᵥ v) ^ 2 := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  simp only [star_trivial, quad]
  exact ⟨fun h v hv => h.2 hv, fun h => ⟨herm x w, fun v hv => h v hv⟩⟩

theorem main {n d : ℕ} (x : Fin n → Fin d → ℝ)
    (hGP : GeneralPosition x) (w : Fin n → ℝ) (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) :
    (gram x w).PosDef ↔ d ≤ (Finset.univ.filter (fun i => w i ≠ 0)).card := by
  rw [posDef_iff]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    set T := Finset.univ.filter (fun i => w i ≠ 0) with hT
    let ψ : (Fin d → ℝ) →ₗ[ℝ] (T → ℝ) :=
      { toFun := fun v i => x i ⬝ᵥ v
        map_add' := fun a b => by ext i; simp [dotProduct_add]
        map_smul' := fun c a => by ext i; simp [dotProduct_smul] }
    have hker : LinearMap.ker ψ ≠ ⊥ := by
      apply LinearMap.ker_ne_bot_of_finrank_lt
      simpa using hlt
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have h1 := h v hv0
    have h2 : ∑ i, w i * (x i ⬝ᵥ v) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : w i = 0
      · simp [hi]
      · have : x i ⬝ᵥ v = 0 := by
          have := congrFun (LinearMap.mem_ker.mp hv) ⟨i, by simp [hT, hi]⟩
          simpa [ψ] using this
        simp [this]
    linarith
  · intro hcard v hv
    obtain ⟨s, hsT, hs⟩ := Finset.exists_subset_card_eq hcard
    have hli := hGP s hs
    have hspan : Submodule.span ℝ (Set.range (fun i : s => x i)) = ⊤ := by
      exact hli.span_eq_top_of_card_eq_finrank' (by simp [hs])
    have hnn : ∀ i, 0 ≤ w i * (x i ⬝ᵥ v) ^ 2 := fun i => mul_nonneg (hw i).1 (sq_nonneg _)
    by_contra hnot
    have hz : ∑ i, w i * (x i ⬝ᵥ v) ^ 2 ≤ 0 := not_lt.mp hnot
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp
      (le_antisymm hz (Finset.sum_nonneg fun i _ => hnn i))
    have horth : ∀ i ∈ s, x i ⬝ᵥ v = 0 := by
      intro i hi
      have hwi : w i ≠ 0 := by simpa using hsT hi
      have := hzero i (Finset.mem_univ _)
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hwi
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    let φ : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun u => u ⬝ᵥ v
        map_add' := fun a b => add_dotProduct a b v
        map_smul' := fun c a => by simp [smul_dotProduct] }
    have hle : Submodule.span ℝ (Set.range (fun i : s => x i)) ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact horth i i.2
    rw [hspan] at hle
    have hvv : v ⬝ᵥ v = 0 := LinearMap.mem_ker.mp (hle Submodule.mem_top)
    exact hv (dotProduct_self_eq_zero.mp hvv)

end GramPD
end Dev

theorem chk_gram_posDef_iff_card_support {n d : ℕ} (x : Fin n → Fin d → ℝ)
    (hGP : GeneralPosition x) (w : Fin n → ℝ) (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) :
    (gram x w).PosDef ↔ d ≤ (Finset.univ.filter (fun i => w i ≠ 0)).card :=
  Dev.GramPD.main x hGP w hw

end SampleRemoval

end

theorem solution : type_of% @SampleRemoval.chk_gram_posDef_iff_card_support := @SampleRemoval.chk_gram_posDef_iff_card_support
