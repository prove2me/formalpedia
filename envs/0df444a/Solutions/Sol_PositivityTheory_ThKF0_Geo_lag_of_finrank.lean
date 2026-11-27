-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.lag_of_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:45.208026+00:00
-- url     : https://prove2.me/submissions/4e5f1421-6963-4ab3-82c4-a602e28f7e3c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg
import Theorems.Thm_PositivityTheory_ThKF0_Geo_om_apply
import Theorems.Thm_PositivityTheory_ThKF0_Geo_eq_zero_of_om
import Theorems.Thm_PositivityTheory_ThKF0_Geo_om_refl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM Module
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Geo
variable {F : Type} [Field F] {κ : Type} [Fintype κ]
namespace PositivityTheory.ThKF0.Geo
theorem _root_.solution (L : Submodule F ((κ → F) × (κ → F))) (h : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (hr : finrank F L = Fintype.card κ) (a) : a ∈ L ↔ ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
  have hiso : L ≤ (om F κ).orthogonal L := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [om_apply, h y hy x hx, sub_self]
  have hbot : (L ⊓ (om F κ).orthogonal ⊤ : Submodule F ((κ → F) × (κ → F))) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply eq_zero_of_om
    intro w'
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx.2) w' Submodule.mem_top
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal (om_refl (F := F) (κ := κ)) L
  rw [hbot, finrank_bot, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hr] at hdim
  have heq : L = (om F κ).orthogonal L := Submodule.eq_of_le_of_finrank_eq hiso (by rw [hr]; omega)
  constructor
  · intro ha
    exact h a ha
  · intro ha
    rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [om_apply, ha y hy, sub_self]
end PositivityTheory.ThKF0.Geo
