-- Prove2me | solution 1 for PI.WeylForKWork.minimal_irreducible_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:39:35.189766+00:00
-- url     : https://prove2.me/submissions/f2f97b2f-6930-4aca-8ba0-6b27a9d3ca2e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
import Definitions.Def_Lemmata_GeneralBFactLeftVariant_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Weights
import Theorems.Thm_PI_WeylForKWork_wt_perp_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix
open scoped InnerProductSpace
namespace PI.WeylForKWork
theorem _root_.solution : MinIrr := by
  classical
  intro p H _ _ σ₁ S μ v hσ hS hSst hvS hv0 hvw
  have hex : ∃ n, ∃ X : Submodule ℂ H, X ≤ S ∧ IsKStableOn (allPos p) σ₁ X ∧
      (∃ x ∈ X, x ≠ 0 ∧ IsWtOn (Kset (allPos p)) σ₁ μ x) ∧ Module.finrank ℂ X = n :=
    ⟨_, S, le_rfl, hSst, ⟨v, hvS, hv0, hvw⟩, rfl⟩
  obtain ⟨X, hXS, hXst, ⟨x, hxX, hx0, hxw⟩, hXn⟩ := Nat.find_spec hex
  have hmin : ∀ X₁ : Submodule ℂ H, X₁ ≤ S → IsKStableOn (allPos p) σ₁ X₁ →
      (∃ x ∈ X₁, x ≠ 0 ∧ IsWtOn (Kset (allPos p)) σ₁ μ x) →
      Module.finrank ℂ X ≤ Module.finrank ℂ X₁ := fun X₁ h1 h2 h3 => by
    rw [hXn]; exact Nat.find_min' hex ⟨X₁, h1, h2, h3, rfl⟩
  have : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le hXS
  refine ⟨X, hXS, hXst, ?_, x, hxX, hx0, hxw⟩
  intro X' hX'X hX'st
  have : FiniteDimensional ℂ X' := Submodule.finiteDimensional_of_le hX'X
  have : CompleteSpace X' := FiniteDimensional.complete ℂ X'
  have hX''st := wt_perp_stable (allPos p) σ₁ hσ X' X hX'st hXst
  have hxsup : x ∈ X' ⊔ X'ᗮ := by rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxsup
  have hzX : z ∈ X := by
    have : z = x - y := by rw [← hyz]; abel
    rw [this]; exact X.sub_mem hxX (hX'X hy)
  have hz'' : z ∈ X'ᗮ ⊓ X := ⟨hz, hzX⟩
  have hperp0 : ∀ u, u ∈ X' → u ∈ X'ᗮ → u = 0 := fun u h1 h2 =>
    inner_self_eq_zero.mp ((Submodule.mem_orthogonal X' u).mp h2 u h1)
  have hsplit : ∀ θ : Fin p → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos p) →
      σ₁ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) y =
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • y ∧
      σ₁ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) z =
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • z := by
    intro θ hT
    have hx := hxw θ hT
    have hAy := hX'st _ hT y hy
    have hAz := (hX''st _ hT z hz'').1
    set A := σ₁ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) with hA
    set e := Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) with he
    have hu1 : A y - e • y ∈ X' := X'.sub_mem hAy (X'.smul_mem e hy)
    have hu2 : A z - e • z ∈ X'ᗮ := X'ᗮ.sub_mem hAz (X'ᗮ.smul_mem e hz)
    have hsum : A y - e • y + (A z - e • z) = 0 := by
      rw [← hyz, map_add, smul_add] at hx
      rw [show A y - e • y + (A z - e • z) = (A y + A z) - (e • y + e • z) by abel, hx, sub_self]
    have hneg : A y - e • y = -(A z - e • z) := eq_neg_of_add_eq_zero_left hsum
    have h0y : A y - e • y = 0 := hperp0 _ hu1 (by rw [hneg]; exact X'ᗮ.neg_mem hu2)
    have h0z : A z - e • z = 0 := by rw [h0y] at hneg; exact neg_eq_zero.mp hneg.symm
    exact ⟨sub_eq_zero.mp h0y, sub_eq_zero.mp h0z⟩
  have hwy : IsWtOn (Kset (allPos p)) σ₁ μ y := fun θ hT => (hsplit θ hT).1
  have hwz : IsWtOn (Kset (allPos p)) σ₁ μ z := fun θ hT => (hsplit θ hT).2
  by_cases hy0 : y = 0
  · left
    have hzx : z = x := by rw [← hyz, hy0, zero_add]
    have hz0 : z ≠ 0 := by rw [hzx]; exact hx0
    have hle : X'ᗮ ⊓ X ≤ X := inf_le_right
    have heq : X'ᗮ ⊓ X = X := Submodule.eq_of_le_of_finrank_le hle
      (hmin _ (hle.trans hXS) hX''st ⟨z, hz'', hz0, hwz⟩)
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hu' : u ∈ X'ᗮ ⊓ X := by rw [heq]; exact hX'X hu
    exact hperp0 u hu hu'.1
  · right
    exact Submodule.eq_of_le_of_finrank_le hX'X (hmin X' (hX'X.trans hXS) hX'st ⟨y, hy, hy0, hwy⟩)
end PI.WeylForKWork
