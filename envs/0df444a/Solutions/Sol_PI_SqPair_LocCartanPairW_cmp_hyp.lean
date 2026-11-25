-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:29.503329+00:00
-- url     : https://prove2.me/submissions/f1c4f806-e603-4abf-b77a-cdbae743ad2c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair
import Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_gram_pre

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
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
namespace PI.SqPair.LocCartanPairW
theorem _root_.solution [IsDomain R] {ι : Type*} [Fintype ι] (A A' h : Matrix ι ι R) (s : R) (hs : s ≠ 0)
    (hh : (h.map σ)ᵀ * A * h = s • A') (c₁ c₂ : R) (hc : σ c₁ * c₂ = s)
    (x₁ y₁ v₁ w₁ : ι → R) (hv : h *ᵥ v₁ = c₁ • x₁) (hw : h *ᵥ w₁ = c₂ • y₁)
    (hxx : (fun i => σ (x₁ i)) ⬝ᵥ (A *ᵥ x₁) = 0) (hyy : (fun i => σ (y₁ i)) ⬝ᵥ (A *ᵥ y₁) = 0)
    (hxy : (fun i => σ (x₁ i)) ⬝ᵥ (A *ᵥ y₁) = 1) :
    (fun i => σ (v₁ i)) ⬝ᵥ (A' *ᵥ v₁) = 0 ∧ (fun i => σ (w₁ i)) ⬝ᵥ (A' *ᵥ w₁) = 0 ∧
      (fun i => σ (v₁ i)) ⬝ᵥ (A' *ᵥ w₁) = 1 := by
  refine ⟨cmp_gram_pre σ A A' h s hs hh v₁ v₁ x₁ x₁ c₁ c₁ 0 hv hv (by rw [hxx]; ring),
    cmp_gram_pre σ A A' h s hs hh w₁ w₁ y₁ y₁ c₂ c₂ 0 hw hw (by rw [hyy]; ring),
    cmp_gram_pre σ A A' h s hs hh v₁ w₁ x₁ y₁ c₁ c₂ 1 hv hw (by rw [hxy, hc]; ring)⟩
end PI.SqPair.LocCartanPairW
