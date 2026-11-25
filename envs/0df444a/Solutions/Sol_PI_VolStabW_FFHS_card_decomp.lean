-- Prove2me | solution 1 for PI.VolStabW.FFHS.card_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:32.805207+00:00
-- url     : https://prove2.me/submissions/845d5b31-c44a-4643-9805-91328438830d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFCnt
import Theorems.Thm_PI_VolStabW_FFHS_perp_sub_mem
import Theorems.Thm_PI_VolStabW_FFHS_decomp_val
import Theorems.Thm_PI_VolStabW_FFHS_mem_perp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.VolStabW.FFHS
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Finite V] {h : V → V → K}
    (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) (c : K) :
    Nat.card {x : V // h x x = c} =
      ∑ t : K, Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} := by
  let E1 : {x : V // h x x = c} ≃
      {p : K × perp hs e // h p.2 p.2 = c - σ p.1 * p.1 * h e e} :=
    { toFun := fun x => ⟨((h e e)⁻¹ * h e x.1, ⟨_, perp_sub_mem hs e x.1 he⟩), by
        have hw := (mem_perp hs e _).1 (perp_sub_mem hs e x.1 he)
        have := decomp_val hs e _ hw ((h e e)⁻¹ * h e x.1)
        rw [add_sub_cancel, x.2] at this
        simp only
        linear_combination -this⟩
      invFun := fun p => ⟨p.1.1 • e + p.1.2, by
        rw [decomp_val hs e _ ((mem_perp hs e _).1 p.1.2.2), p.2]; ring⟩
      left_inv := fun x => Subtype.ext (add_sub_cancel _ _)
      right_inv := by
        rintro ⟨⟨t, w⟩, hw⟩
        have hew : h e w = 0 := (mem_perp hs e w).1 w.2
        have ht : (h e e)⁻¹ * h e (t • e + (w : V)) = t := by
          rw [hs.add_right, hs.smul_right, hew, add_zero, mul_comm, mul_assoc,
            mul_inv_cancel₀ he, mul_one]
        apply Subtype.ext
        apply Prod.ext
        · exact ht
        · apply Subtype.ext
          show t • e + (w : V) - ((h e e)⁻¹ * h e (t • e + (w : V))) • e = w
          rw [ht, add_sub_cancel_left] }
  rw [Nat.card_congr (E1.trans (Equiv.subtypeProdEquivSigmaSubtype
    (fun t (w : perp hs e) => h w w = c - σ t * t * h e e))), Nat.card_sigma]
end PI.VolStabW.FFHS
