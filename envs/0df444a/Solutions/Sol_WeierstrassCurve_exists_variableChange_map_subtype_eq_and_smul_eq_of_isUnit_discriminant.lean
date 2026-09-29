-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5a5a46b5-fbc6-5c4a-82a4-fd876c91a859

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ a₃ a₁ map map_b₂ b₂ variableChange_a₃ a₄ variableChange_b₈ a₂ a₆ isIntegral_iff variableChange_a₆ variableChange_b₆ variableChange_Δ VariableChange.map_u variableChange_a₂ IsIntegral map_b₆ map_injective map_Δ map_a₆ b₆ b₈ variableChange_a₁ map_a₁ map_a₄ Δ VariableChange map_b₈ map_a₂ map_variableChange b₄ map_a₃"
namespace IntegralIsoOfGoodModels
p2m_open "WeierstrassCurve"

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem mem_of_monic_of_eval₂_eq_zero {q : A[X]} (hq : q.Monic) {x : L}
    (hx : q.eval₂ (algebraMap A L) x = 0) : x ∈ A := by
  have hint : _root_.IsIntegral A x := ⟨q, hq, hx⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := L)).mp hint
  rw [← hy]
  exact y.2

theorem mem_of_quadratic {x b c : L} (hb : b ∈ A) (hc : c ∈ A)
    (h : x ^ 2 + b * x + c = 0) : x ∈ A := by
  refine mem_of_monic_of_eval₂_eq_zero A (q := X ^ 2 + (C ⟨b, hb⟩ * X + C ⟨c, hc⟩)) ?_ ?_
  · exact monic_X_pow_add ((degree_linear_le).trans_lt (by norm_num))
  · simp only [eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X]
    change x ^ 2 + (b * x + c) = 0
    rw [← h]
    ring

theorem mem_of_quartic {x b c d : L} (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (h : x ^ 4 + b * x ^ 2 + c * x + d = 0) : x ∈ A := by
  refine mem_of_monic_of_eval₂_eq_zero A
    (q := X ^ 4 + (C ⟨b, hb⟩ * X ^ 2 + C ⟨c, hc⟩ * X + C ⟨d, hd⟩)) ?_ ?_
  · exact monic_X_pow_add ((degree_quadratic_le).trans_lt (by norm_num))
  · simp only [eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X]
    change x ^ 4 + (b * x ^ 2 + c * x + d) = 0
    rw [← h]
    ring

theorem exists_unit_coe_eq {E₁ E₂ : WeierstrassCurve A} (h₁ : IsUnit E₁.Δ) (h₂ : IsUnit E₂.Δ)
    {C : WeierstrassCurve.VariableChange L} (hC : C • E₁.map A.subtype = E₂.map A.subtype) :
    ∃ u₀ : Aˣ, ((u₀ : A) : L) = (C.u : L) := by
  have hΔ : (E₂.Δ : L) = ((C.u⁻¹ : Lˣ) : L) ^ 12 * (E₁.Δ : L) := by
    have h := congrArg WeierstrassCurve.Δ hC
    rw [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ] at h
    exact h.symm
  have hu0 : (C.u : L) ≠ 0 := C.u.ne_zero
  rcases A.mem_or_inv_mem (C.u : L) with hu | hu
  ·
    have hrel : (⟨(C.u : L), hu⟩ : A) ^ 12 * E₂.Δ = E₁.Δ := by
      apply Subtype.ext
      push_cast
      rw [hΔ, Units.val_inv_eq_inv_val]
      field_simp
    have hunit : IsUnit ((⟨(C.u : L), hu⟩ : A) ^ 12) :=
      isUnit_of_mul_isUnit_left (hrel ▸ h₁)
    obtain ⟨u₀, hu₀⟩ := (isUnit_pow_iff (by norm_num)).mp hunit
    exact ⟨u₀, by rw [hu₀]⟩
  ·
    have hrel : (⟨(C.u : L)⁻¹, hu⟩ : A) ^ 12 * E₁.Δ = E₂.Δ := by
      apply Subtype.ext
      push_cast
      rw [hΔ, Units.val_inv_eq_inv_val]
    have hunit : IsUnit ((⟨(C.u : L)⁻¹, hu⟩ : A) ^ 12) :=
      isUnit_of_mul_isUnit_left (hrel ▸ h₂)
    obtain ⟨u₀, hu₀⟩ := (isUnit_pow_iff (by norm_num)).mp hunit
    refine ⟨u₀⁻¹, ?_⟩
    have h3 : ((u₀ : A) : L) = (C.u : L)⁻¹ := by rw [hu₀]
    have h4 : (((u₀⁻¹ : Aˣ) : A) : L) * ((u₀ : A) : L) = 1 := by
      have h5 : ((u₀⁻¹ : Aˣ) : A) * (u₀ : A) = 1 := Units.inv_mul u₀
      exact_mod_cast congrArg (fun z : A => (z : L)) h5
    rw [h3] at h4
    exact (mul_inv_eq_one₀ hu0).mp h4

theorem main (E₁ E₂ : WeierstrassCurve A) (h₁ : IsUnit E₁.Δ) (h₂ : IsUnit E₂.Δ)
    (C : WeierstrassCurve.VariableChange L) (hC : C • E₁.map A.subtype = E₂.map A.subtype) :
    ∃ C₀ : WeierstrassCurve.VariableChange A, C₀.map A.subtype = C ∧ C₀ • E₁ = E₂ := by
  obtain ⟨u₀, hu₀⟩ := exists_unit_coe_eq A h₁ h₂ hC
  set u : L := (C.u : L) with hu_def
  have hu0 : u ≠ 0 := C.u.ne_zero
  have huA : u ∈ A := hu₀ ▸ (u₀ : A).2
  have hui : ((C.u⁻¹ : Lˣ) : L) = u⁻¹ := Units.val_inv_eq_inv_val _

  have hb₆ := congrArg WeierstrassCurve.b₆ hC
  have hb₈ := congrArg WeierstrassCurve.b₈ hC
  have ha₁ := congrArg WeierstrassCurve.a₁ hC
  have ha₂ := congrArg WeierstrassCurve.a₂ hC
  have ha₃ := congrArg WeierstrassCurve.a₃ hC
  have ha₆ := congrArg WeierstrassCurve.a₆ hC
  have hsub : ∀ z : A, A.subtype z = (z : L) := fun _ => rfl
  simp only [hsub, WeierstrassCurve.variableChange_b₆, WeierstrassCurve.variableChange_b₈,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₆,
    WeierstrassCurve.map_b₆, WeierstrassCurve.map_b₈, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, hui]
    at hb₆ hb₈ ha₁ ha₂ ha₃ ha₆

  have hr : C.r ∈ A := by
    refine mem_of_quartic A (b := -(E₁.b₄ : L)) (c := -(2 * E₁.b₆ + u ^ 6 * E₂.b₆ : L))
      (d := -(E₁.b₈ - u ^ 8 * E₂.b₈ : L)) ?_ ?_ ?_ ?_
    · exact A.toSubring.neg_mem (E₁.b₄).2
    · exact A.toSubring.neg_mem (A.toSubring.add_mem (A.toSubring.mul_mem (by norm_num) (E₁.b₆).2)
        (A.toSubring.mul_mem (A.toSubring.pow_mem huA 6) (E₂.b₆).2))
    · exact A.toSubring.neg_mem (A.toSubring.sub_mem (E₁.b₈).2
        (A.toSubring.mul_mem (A.toSubring.pow_mem huA 8) (E₂.b₈).2))
    · have e6 : u ^ 6 * (E₂.b₆ : L) = E₁.b₆ + 2 * C.r * E₁.b₄ + C.r ^ 2 * E₁.b₂ + 4 * C.r ^ 3 := by
        rw [← hb₆]; field_simp
      have e8 : u ^ 8 * (E₂.b₈ : L) =
          E₁.b₈ + 3 * C.r * E₁.b₆ + 3 * C.r ^ 2 * E₁.b₄ + C.r ^ 3 * E₁.b₂ + 3 * C.r ^ 4 := by
        rw [← hb₈]; field_simp
      linear_combination e8 - C.r * e6

  have hs : C.s ∈ A := by
    refine mem_of_quadratic A (b := (E₁.a₁ : L)) (c := (u ^ 2 * E₂.a₂ - E₁.a₂ - 3 * C.r : L))
      (E₁.a₁).2 ?_ ?_
    · exact A.toSubring.sub_mem (A.toSubring.sub_mem
        (A.toSubring.mul_mem (A.toSubring.pow_mem huA 2) (E₂.a₂).2) (E₁.a₂).2)
        (A.toSubring.mul_mem (by norm_num) hr)
    · have e2 : u ^ 2 * (E₂.a₂ : L) = E₁.a₂ - C.s * E₁.a₁ + 3 * C.r - C.s ^ 2 := by
        rw [← ha₂]; field_simp
      linear_combination e2

  have ht : C.t ∈ A := by
    refine mem_of_quadratic A (b := (E₁.a₃ + C.r * E₁.a₁ : L))
      (c := (u ^ 6 * E₂.a₆ - E₁.a₆ - C.r * E₁.a₄ - C.r ^ 2 * E₁.a₂ - C.r ^ 3 : L)) ?_ ?_ ?_
    · exact A.toSubring.add_mem (E₁.a₃).2 (A.toSubring.mul_mem hr (E₁.a₁).2)
    · exact A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.sub_mem
        (A.toSubring.mul_mem (A.toSubring.pow_mem huA 6) (E₂.a₆).2) (E₁.a₆).2)
        (A.toSubring.mul_mem hr (E₁.a₄).2))
        (A.toSubring.mul_mem (A.toSubring.pow_mem hr 2) (E₁.a₂).2)) (A.toSubring.pow_mem hr 3)
    · have e6 : u ^ 6 * (E₂.a₆ : L) = E₁.a₆ + C.r * E₁.a₄ + C.r ^ 2 * E₁.a₂ + C.r ^ 3
          - C.t * E₁.a₃ - C.t ^ 2 - C.r * C.t * E₁.a₁ := by
        rw [← ha₆]; field_simp
      linear_combination e6

  refine ⟨⟨u₀, ⟨C.r, hr⟩, ⟨C.s, hs⟩, ⟨C.t, ht⟩⟩, ?_, ?_⟩
  · ext
    · simp only [WeierstrassCurve.VariableChange.map_u, Units.coe_map]
      exact hu₀
    · rfl
    · rfl
    · rfl
  · apply WeierstrassCurve.map_injective A.subtype_injective
    dsimp only
    rw [← WeierstrassCurve.map_variableChange, ← hC]
    congr 1
    ext
    · simp only [WeierstrassCurve.VariableChange.map_u, Units.coe_map]
      exact hu₀
    · rfl
    · rfl
    · rfl

end WeierstrassCurve.IntegralIsoOfGoodModels

theorem solution {L : Type*} [Field L] (A : ValuationSubring L) (E₁ E₂ : WeierstrassCurve A) (h₁ : IsUnit E₁.Δ) (h₂ : IsUnit E₂.Δ) (C : WeierstrassCurve.VariableChange L) (hC : C • E₁.map A.subtype = E₂.map A.subtype) : ∃ C₀ : WeierstrassCurve.VariableChange A, C₀.map A.subtype = C ∧ C₀ • E₁ = E₂ :=
  WeierstrassCurve.IntegralIsoOfGoodModels.main A E₁ E₂ h₁ h₂ C hC

end S_WeierstrassCurve_exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant (solution)
