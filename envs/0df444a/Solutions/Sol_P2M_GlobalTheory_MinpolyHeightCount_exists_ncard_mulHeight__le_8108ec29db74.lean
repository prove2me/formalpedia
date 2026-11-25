-- Prove2me | solution 1 for P2M_GlobalTheory_MinpolyHeightCount_exists_ncard_mulHeight__le_8108ec29db74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:02.298813+00:00
-- url     : https://prove2.me/submissions/d4d80e00-7ec6-4b16-9a50-5f79e57c7dff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe
import Theorems.Thm_GlobalTheory_MinpolyHeightCount_finite_and_ncard_integral_le
import Theorems.Thm_P2M_GlobalTheory_MinpolyHeightCount_norm_embedding_le_mulHeight__593896cf91ef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount
variable {K : Type} [Field K] [NumberField K]
variable (K)
namespace GlobalTheory.MinpolyHeightCount
theorem _root_.solution : ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B →
    {c : K | Height.mulHeight₁ c ≤ B}.Finite ∧
      (({c : K | Height.mulHeight₁ c ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k := by
  classical
  set d := Module.finrank ℚ K with hd
  refine ⟨d * (2 * (d.choose (d / 2) : ℝ) + 3) ^ (d + 1), 1 + 2 * d * (d + 1), fun B hB => ?_⟩
  refine ⟨finite_setOfPred_mulHeight₁_le K B, ?_⟩
  choose n hn0 hnle hint using fun c : K => exists_nat_le_mulHeight₁ c
  set A := {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B ^ 2} with hAdef
  obtain ⟨hAfin, hAcard⟩ := finite_and_ncard_integral_le K (B ^ 2)
  set P : Set (ℕ × K) := (↑(Finset.Icc 1 ⌊B⌋₊) : Set ℕ) ×ˢ A with hPdef
  have hP : P.Finite := (Finset.finite_toSet _).prod hAfin
  have hle : {c : K | Height.mulHeight₁ c ≤ B}.ncard ≤ P.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun c => (n c, (n c : K) * c)) ?_ ?_ hP
    · intro c hc
      have hc' : Height.mulHeight₁ c ≤ B := hc
      refine Set.mk_mem_prod ?_ ⟨hint c, fun φ => ?_⟩
      · rw [Finset.mem_coe, Finset.mem_Icc]
        exact ⟨Nat.one_le_iff_ne_zero.mpr (hn0 c), Nat.le_floor ((hnle c).trans hc')⟩
      · rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast, sq]
        exact mul_le_mul ((hnle c).trans hc') ((norm_embedding_le_mulHeight₁ φ c).trans hc')
          (norm_nonneg _) (by linarith)
    · intro c _ c' _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1] at h2
      exact mul_left_cancel₀ (by exact_mod_cast hn0 c') h2
  have hPcard : P.ncard = ⌊B⌋₊ * A.ncard := by
    rw [hPdef, Set.ncard_prod, Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel]
  have hfl : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hmax : max (B ^ 2) 1 = B ^ 2 := max_eq_left (by nlinarith)
  rw [hmax] at hAcard
  have hX : 1 ≤ B ^ (2 * d) := one_le_pow₀ hB
  have hch : (0 : ℝ) ≤ (d.choose (d / 2) : ℝ) := Nat.cast_nonneg _
  have hstep : 2 * ((B ^ 2) ^ d * (d.choose (d / 2) : ℝ)) + 3 ≤
      (2 * (d.choose (d / 2) : ℝ) + 3) * B ^ (2 * d) := by
    rw [← pow_mul]; nlinarith
  calc (({c : K | Height.mulHeight₁ c ≤ B}.ncard : ℕ) : ℝ) ≤ (P.ncard : ℝ) := by
        exact_mod_cast hle
    _ = (⌊B⌋₊ : ℝ) * (A.ncard : ℝ) := by rw [hPcard]; push_cast; ring
    _ ≤ B * (d * (2 * ((B ^ 2) ^ d * (d.choose (d / 2) : ℝ)) + 3) ^ (d + 1)) :=
        mul_le_mul hfl hAcard (Nat.cast_nonneg _) (by linarith)
    _ ≤ B * (d * ((2 * (d.choose (d / 2) : ℝ) + 3) * B ^ (2 * d)) ^ (d + 1)) := by
        gcongr
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add B 1, pow_one]; ring
end GlobalTheory.MinpolyHeightCount
