-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.inv_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:49.106222+00:00
-- url     : https://prove2.me/submissions/eb90fc7b-cb7a-4bfb-a90a-316c9902c9a0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_SpanUnitaryMatrix
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_CompactCayleyBlocks_span_unitary_matrix
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_CompactCayleyBlocks_pm_conj
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_CompactCayleyBlocks_pm_unit
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_CompactCayleyBlocks_dph_unit
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_CompactCayleyBlocks_dph_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
theorem _root_.solution (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ U X : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → Xᴴ * X = 1 → L (U * X * Uᴴ) = L X) :
    ∀ X, L X = L 1 / n * X.trace := by

  have h' : ∀ U X : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → L (U * X * Uᴴ) = L X := by
    intro U X hU
    let C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      L.comp ((LinearMap.mulLeft ℂ U).comp (LinearMap.mulRight ℂ Uᴴ)) - L
    have hC : Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set _) ≤ LinearMap.ker C := by
      rw [Submodule.span_le]
      intro Y hY
      have hY' : Yᴴ * Y = 1 := hY.1
      simp only [SetLike.mem_coe, LinearMap.mem_ker, C, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← Matrix.mul_assoc]
      rw [h U Y hU hY', sub_self]
    have hX : X ∈ LinearMap.ker C := hC (by rw [span_unitary_matrix]; trivial)
    simpa [C, sub_eq_zero, ← Matrix.mul_assoc] using hX

  have hoff : ∀ a b : Fin n, a ≠ b → L (Matrix.single a b 1) = 0 := by
    intro a b hab
    have e := h' (dph a) (Matrix.single a b 1) (dph_unit a)
    rw [dph_conj hab, L.map_smul, smul_eq_mul] at e
    have : (Complex.I - 1) * L (Matrix.single a b 1) = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (by simp [sub_eq_zero, Complex.ext_iff])
    · exact h0

  have hdiag : ∀ a b : Fin n, L (Matrix.single a a 1) = L (Matrix.single b b 1) := by
    intro a b
    have e := h' (pm (Equiv.swap a b)) (Matrix.single a a 1) (pm_unit _)
    rw [pm_conj] at e
    have : (Matrix.single a a (1 : ℂ)).submatrix (Equiv.swap a b) (Equiv.swap a b) = Matrix.single b b 1 := by
      have key : ∀ x, a = (Equiv.swap a b) x ↔ b = x := by
        intro x; rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, eq_comm]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.single_apply, key]
    rw [this] at e
    exact e.symm
  intro X
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : X = 0 := Subsingleton.elim _ _
    simp [this]
  set κ := L (Matrix.single (⟨0, hn⟩ : Fin n) ⟨0, hn⟩ 1)
  have hsum : ∀ Y : Matrix (Fin n) (Fin n) ℂ, L Y = κ * Y.trace := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [map_sum]
    rw [Matrix.trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [show Matrix.single a a (Y a a) = Y a a • Matrix.single a a (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
        L.map_smul, smul_eq_mul, hdiag a ⟨0, hn⟩, Matrix.diag_apply]; ring
    · intro b _ hb
      rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
        L.map_smul, hoff a b (Ne.symm hb), smul_zero]
    · simp
  have h1 : L 1 = κ * n := by rw [hsum, trace_one, Fintype.card_fin]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hsum X, h1]; field_simp
end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
