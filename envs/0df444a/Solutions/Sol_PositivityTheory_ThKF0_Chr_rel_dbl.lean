-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.rel_dbl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:41.429513+00:00
-- url     : https://prove2.me/submissions/b5f1d35f-a407-4e01-95b1-a2ba0f7f790e

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ExistsDoubledUnitaryBlock
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsSp_trans
import Theorems.Thm_PositivityTheory_ThKF0_Chr_rel_dv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β β₁ ν κ κ₁ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁]
  [Fintype ν] [DecidableEq ν] [Fintype κ] [Fintype κ₁] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {ι : Matrix β β₁ E} {X : Matrix β ν E}
  {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
omit [DecidableEq α] [Invertible (2 : R)] [DecidableEq ν]
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution (hj : Function.Injective j) {d : Darboux (symp c ξ JA J) κ} {d₁ : Darboux (symp c ξ JA J₁) κ₁}
    (hrel : ∀ u z, Rel S j (d.e u) (d₁.e z) ↔ ∃ a : Matrix α ν E, u = z * ιᵀ + a * Xᵀ)
    {dd : Darboux (symp c ξ JA (dbl J)) (κ ⊕ κ)} {dd₁ : Darboux (symp c ξ JA (dbl J₁)) (κ₁ ⊕ κ₁)}
    (hd : IsDblCoord c ξ JA J d dd) (hd₁ : IsDblCoord c ξ JA J₁ d₁ dd₁) (u z) :
    Rel (dbS S) (Sum.map j j) (dd.e u) (dd₁.e z) ↔ ∃ a : Matrix α (ν ⊕ ν) E, u = z * (dd2 ι)ᵀ + a * (dd2 X)ᵀ := by
  rw [← fromCols_toCols u, ← fromCols_toCols z, hd, hd₁]
  generalize u.toCols₁ = u₁, u.toCols₂ = u₂, z.toCols₁ = z₁, z.toCols₂ = z₂
  have e : ∀ a₁ a₂ : Matrix α ν E, fromCols z₁ z₂ * (dd2 ι)ᵀ + fromCols a₁ a₂ * (dd2 X)ᵀ =
      fromCols (z₁ * ιᵀ + a₁ * Xᵀ) (z₂ * ιᵀ + a₂ * Xᵀ) := fun a₁ a₂ => by
    simp only [fromBlocks_transpose, fromCols_mul_fromBlocks, transpose_zero, Matrix.mul_zero, add_zero, zero_add]
    ext i (k | k) <;> rfl
  refine (rel_dv hj).trans ⟨fun ⟨p, q⟩ => ?_, fun ⟨a, ha⟩ => ?_⟩
  · obtain ⟨a₁, rfl⟩ := (hrel _ _).1 p
    obtain ⟨a₂, rfl⟩ := (hrel _ _).1 q
    exact ⟨fromCols a₁ a₂, (e _ _).symm⟩
  · rw [← fromCols_toCols a, e, fromCols_ext_iff] at ha
    exact ⟨(hrel _ _).2 ⟨_, ha.1⟩, (hrel _ _).2 ⟨_, ha.2⟩⟩
end PositivityTheory.ThKF0.Chr
