-- Prove2me | solution 1 for TeschlQM.Dynamics.compactOperators_closed_star_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:52:35.370558+00:00
-- url     : https://prove2.me/submissions/4bcc62eb-1052-4bcd-9a9e-ab0cd8f19d13

import Mathlib
import Definitions.Def_TeschlQM_Shared_compactOperators

set_option autoImplicit false

namespace P30d1ca58

open TeschlQM.Shared

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma fr_zero : IsFiniteRank (0 : H →L[ℂ] H) := by
  unfold IsFiniteRank
  have : LinearMap.range ((0 : H →L[ℂ] H) : H →ₗ[ℂ] H) = ⊥ := by
    ext x; simp
  rw [this]; infer_instance

lemma fr_add (K L : H →L[ℂ] H) (hK : IsFiniteRank K) (hL : IsFiniteRank L) :
    IsFiniteRank (K + L) := by
  unfold IsFiniteRank at *
  have hle : LinearMap.range ((K + L : H →L[ℂ] H) : H →ₗ[ℂ] H) ≤
      LinearMap.range (K : H →ₗ[ℂ] H) ⊔ LinearMap.range (L : H →ₗ[ℂ] H) := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

lemma fr_smul (c : ℂ) (K : H →L[ℂ] H) (hK : IsFiniteRank K) : IsFiniteRank (c • K) := by
  unfold IsFiniteRank at *
  have hle : LinearMap.range ((c • K : H →L[ℂ] H) : H →ₗ[ℂ] H) ≤
      LinearMap.range (K : H →ₗ[ℂ] H) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨c • x, by simp⟩
  exact Submodule.finiteDimensional_of_le hle

lemma fr_mul_left (B K : H →L[ℂ] H) (hK : IsFiniteRank K) : IsFiniteRank (B * K) := by
  unfold IsFiniteRank at *
  have hle : LinearMap.range ((B * K : H →L[ℂ] H) : H →ₗ[ℂ] H) ≤
      (LinearMap.range (K : H →ₗ[ℂ] H)).map (B : H →ₗ[ℂ] H) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨K x, ⟨x, rfl⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

lemma fr_mul_right (K B : H →L[ℂ] H) (hK : IsFiniteRank K) : IsFiniteRank (K * B) := by
  unfold IsFiniteRank at *
  have hle : LinearMap.range ((K * B : H →L[ℂ] H) : H →ₗ[ℂ] H) ≤
      LinearMap.range (K : H →ₗ[ℂ] H) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨B x, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

lemma fr_star [CompleteSpace H] (K : H →L[ℂ] H) (hK : IsFiniteRank K) :
    IsFiniteRank (star K) := by
  unfold IsFiniteRank at *
  set U := LinearMap.range (K : H →ₗ[ℂ] H) with hU
  have : CompleteSpace U := FiniteDimensional.complete ℂ U
  have hle : LinearMap.range ((star K : H →L[ℂ] H) : H →ₗ[ℂ] H) ≤
      U.map ((star K : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := U.exists_add_mem_mem_orthogonal y
    have hb0 : (star K) b = 0 := by
      rw [ContinuousLinearMap.star_eq_adjoint]
      have : b ∈ LinearMap.ker ((ContinuousLinearMap.adjoint K : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
        rw [← ContinuousLinearMap.orthogonal_range]; exact hb
      simpa using this
    refine ⟨a, ha, ?_⟩
    simp [hab, map_add, hb0]
  exact Submodule.finiteDimensional_of_le hle

end P30d1ca58

theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    IsClosed (TeschlQM.Shared.compactOperators H) ∧ (0 : H →L[ℂ] H) ∈ TeschlQM.Shared.compactOperators H ∧
    (∀ K ∈ TeschlQM.Shared.compactOperators H, ∀ L ∈ TeschlQM.Shared.compactOperators H, K + L ∈ TeschlQM.Shared.compactOperators H) ∧
    (∀ (c : ℂ), ∀ K ∈ TeschlQM.Shared.compactOperators H, c • K ∈ TeschlQM.Shared.compactOperators H) ∧
    (∀ K ∈ TeschlQM.Shared.compactOperators H, ∀ B : H →L[ℂ] H,
      B * K ∈ TeschlQM.Shared.compactOperators H ∧ K * B ∈ TeschlQM.Shared.compactOperators H) ∧
    (∀ K ∈ TeschlQM.Shared.compactOperators H, star K ∈ TeschlQM.Shared.compactOperators H) := by
  unfold TeschlQM.Shared.compactOperators
  refine ⟨isClosed_closure, subset_closure P30d1ca58.fr_zero, ?_, ?_, ?_, ?_⟩
  · intro K hK L hL
    exact map_mem_closure₂ continuous_add hK hL fun a ha b hb => P30d1ca58.fr_add a b ha hb
  · intro c K hK
    exact map_mem_closure (continuous_const_smul c) hK fun a ha => P30d1ca58.fr_smul c a ha
  · intro K hK B
    exact ⟨map_mem_closure (f := fun a => B * a) (continuous_const.mul continuous_id) hK fun a ha => P30d1ca58.fr_mul_left B a ha,
      map_mem_closure (f := fun a => a * B) (continuous_id.mul continuous_const) hK fun a ha => P30d1ca58.fr_mul_right a B ha⟩
  · intro K hK
    exact map_mem_closure continuous_star hK fun a ha => P30d1ca58.fr_star a ha
