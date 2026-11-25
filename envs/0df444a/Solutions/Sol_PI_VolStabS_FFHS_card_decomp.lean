-- Prove2me | solution 1 for PI.VolStabS.FFHS.card_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:29.676538+00:00
-- url     : https://prove2.me/submissions/e308c719-64ee-4c6f-aec0-a6e6b1b82af3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
import Theorems.Thm_PI_VolStabS_FFHS_perp_sub_mem
import Theorems.Thm_PI_VolStabS_FFHS_decomp_val
import Theorems.Thm_PI_VolStabS_FFHS_mem_perp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
private theorem natCard_sigma_eq_sum {α : Type} [Fintype α] {β : α → Type} [∀ a, Finite (β a)] :
    Nat.card (Sigma β) = ∑ a, Nat.card (β a) := by
  exact Nat.card_sigma
end PI.VolStabS.FFHS
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.VolStabS.FFHS
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Finite V] {h : V → V → K}
    (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) (c : K) :
    Nat.card {x : V // h x x = c} =
      ∑ t : K, Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} := by
  have hcoef : ∀ (t : K) (w : V), h e w = 0 → (h e e)⁻¹ * h e (t • e + w) = t := by
    intro t w hw
    rw [hs.add_right, hs.smul_right, hw, add_zero]
    rw [mul_comm t, ← mul_assoc, inv_mul_cancel₀ he, one_mul]
  let E : {x : V // h x x = c} ≃
      Σ t : K, {w : perp hs e // h w w = c - σ t * t * h e e} :=
    { toFun := fun x => ⟨(h e e)⁻¹ * h e x.1,
        ⟨⟨x.1 - ((h e e)⁻¹ * h e x.1) • e, perp_sub_mem hs e x.1 he⟩, by
          have hw := (mem_perp hs e _).1 (perp_sub_mem hs e x.1 he)
          have key := decomp_val hs e _ hw ((h e e)⁻¹ * h e x.1)
          have hx : ((h e e)⁻¹ * h e x.1) • e + (x.1 - ((h e e)⁻¹ * h e x.1) • e) = x.1 := by
            abel
          rw [hx, x.2] at key
          show h (x.1 - ((h e e)⁻¹ * h e x.1) • e) (x.1 - ((h e e)⁻¹ * h e x.1) • e) = _
          linear_combination -key⟩⟩
      invFun := fun p => ⟨p.1 • e + (p.2.1 : V), by
          rw [decomp_val hs e _ ((mem_perp hs e _).1 p.2.1.2) p.1, p.2.2]
          ring⟩
      left_inv := fun x => Subtype.ext (by
          show ((h e e)⁻¹ * h e x.1) • e + (x.1 - ((h e e)⁻¹ * h e x.1) • e) = x.1
          abel)
      right_inv := by
        rintro ⟨t, ⟨w, hw⟩, hww⟩
        have hw0 := (mem_perp hs e w).1 hw
        refine Sigma.subtype_ext (hcoef t w hw0) ?_
        apply Subtype.ext
        show t • e + w - ((h e e)⁻¹ * h e (t • e + w)) • e = w
        rw [hcoef t w hw0]
        abel }
  rw [Nat.card_congr E, natCard_sigma_eq_sum]
end PI.VolStabS.FFHS
