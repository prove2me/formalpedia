-- Prove2me | solution 1 for TeschlQM.KatoRellich.relativeBound_linear_comb
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T21:10:39.558475+00:00
-- url     : https://prove2.me/submissions/a199143c-db28-4398-b577-41e7f78cf278

import Mathlib
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded

set_option autoImplicit false

namespace TeschlQM.KatoRellich.P470d9745

open scoped ENNReal
open TeschlQM.KatoRellich

theorem combWith {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B₁ B₂ : H →ₗ.[ℂ] H) (α₁ α₂ : ℂ) (a₁ b₁ a₂ b₂ : ℝ)
    (h₁ : IsRelativelyBoundedWith A B₁ a₁ b₁) (h₂ : IsRelativelyBoundedWith A B₂ a₂ b₂) :
    IsRelativelyBoundedWith A (α₁ • B₁ + α₂ • B₂)
      (‖α₁‖ * a₁ + ‖α₂‖ * a₂) (‖α₁‖ * b₁ + ‖α₂‖ * b₂) := by
  obtain ⟨hd₁, ha₁, hb₁, hn₁⟩ := h₁
  obtain ⟨hd₂, ha₂, hb₂, hn₂⟩ := h₂
  refine ⟨?_, by positivity, by positivity, ?_⟩
  · intro x hx
    exact ⟨hd₁ hx, hd₂ hx⟩
  · intro ψ hA hB
    have e : (α₁ • B₁ + α₂ • B₂) ⟨ψ, hB⟩ = α₁ • B₁ ⟨ψ, hd₁ hA⟩ + α₂ • B₂ ⟨ψ, hd₂ hA⟩ := rfl
    rw [e]
    have k₁ := hn₁ ψ hA (hd₁ hA)
    have k₂ := hn₂ ψ hA (hd₂ hA)
    have n₁ : 0 ≤ ‖α₁‖ := norm_nonneg _
    have n₂ : 0 ≤ ‖α₂‖ := norm_nonneg _
    calc ‖α₁ • B₁ ⟨ψ, hd₁ hA⟩ + α₂ • B₂ ⟨ψ, hd₂ hA⟩‖
        ≤ ‖α₁‖ * ‖B₁ ⟨ψ, hd₁ hA⟩‖ + ‖α₂‖ * ‖B₂ ⟨ψ, hd₂ hA⟩‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
      _ ≤ ‖α₁‖ * (a₁ * ‖A ⟨ψ, hA⟩‖ + b₁ * ‖ψ‖) + ‖α₂‖ * (a₂ * ‖A ⟨ψ, hA⟩‖ + b₂ * ‖ψ‖) := by
          gcongr
      _ = (‖α₁‖ * a₁ + ‖α₂‖ * a₂) * ‖A ⟨ψ, hA⟩‖ + (‖α₁‖ * b₁ + ‖α₂‖ * b₂) * ‖ψ‖ := by ring

end TeschlQM.KatoRellich.P470d9745

open scoped ENNReal in
open TeschlQM.KatoRellich in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B₁ B₂ : H →ₗ.[ℂ] H) (h₁ : IsRelativelyBounded A B₁) (h₂ : IsRelativelyBounded A B₂)
    (α₁ α₂ : ℂ) :
    IsRelativelyBounded A (α₁ • B₁ + α₂ • B₂) ∧
      relativeBound A (α₁ • B₁ + α₂ • B₂) ≤
        ENNReal.ofReal ‖α₁‖ * relativeBound A B₁ + ENNReal.ofReal ‖α₂‖ * relativeBound A B₂ := by
  obtain ⟨a₁, b₁, w₁⟩ := h₁
  obtain ⟨a₂, b₂, w₂⟩ := h₂
  refine ⟨⟨_, _, P470d9745.combWith A B₁ B₂ α₁ α₂ a₁ b₁ a₂ b₂ w₁ w₂⟩, ?_⟩
  have key : ∀ x : {a : ℝ // ∃ b : ℝ, IsRelativelyBoundedWith A B₁ a b},
      ∀ y : {a : ℝ // ∃ b : ℝ, IsRelativelyBoundedWith A B₂ a b},
      relativeBound A (α₁ • B₁ + α₂ • B₂) ≤
        ENNReal.ofReal ‖α₁‖ * ENNReal.ofReal x.1 + ENNReal.ofReal ‖α₂‖ * ENNReal.ofReal y.1 := by
    rintro ⟨x, bx, hx⟩ ⟨y, by', hy⟩
    have hc := P470d9745.combWith A B₁ B₂ α₁ α₂ x bx y by' hx hy
    have hx0 : 0 ≤ x := hx.2.1
    have hy0 : 0 ≤ y := hy.2.1
    have le1 : relativeBound A (α₁ • B₁ + α₂ • B₂) ≤ ENNReal.ofReal (‖α₁‖ * x + ‖α₂‖ * y) :=
      iInf₂_le _ ⟨_, hc⟩
    refine le1.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _)]
  have ne₁ : Nonempty {a : ℝ // ∃ b : ℝ, IsRelativelyBoundedWith A B₁ a b} := ⟨⟨a₁, b₁, w₁⟩⟩
  have ne₂ : Nonempty {a : ℝ // ∃ b : ℝ, IsRelativelyBoundedWith A B₂ a b} := ⟨⟨a₂, b₂, w₂⟩⟩
  have e₁ : relativeBound A B₁ =
      ⨅ x : {a : ℝ // ∃ b : ℝ, IsRelativelyBoundedWith A B₁ a b}, ENNReal.ofReal x.1 := by
    unfold relativeBound; exact iInf_subtype'
  have e₂ : relativeBound A B₂ =
      ⨅ x : {a : ℝ // ∃ b : ℝ, IsRelativelyBoundedWith A B₂ a b}, ENNReal.ofReal x.1 := by
    unfold relativeBound; exact iInf_subtype'
  rw [e₁, e₂]
  rw [ENNReal.mul_iInf (fun h => absurd h ENNReal.ofReal_ne_top),
    ENNReal.mul_iInf (fun h => absurd h ENNReal.ofReal_ne_top), ENNReal.iInf_add]
  refine le_iInf fun x => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun y => ?_
  exact key x y
