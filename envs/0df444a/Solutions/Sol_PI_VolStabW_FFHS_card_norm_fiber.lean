-- Prove2me | solution 1 for PI.VolStabW.FFHS.card_norm_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:05:46.740888+00:00
-- url     : https://prove2.me/submissions/35e70834-21ee-4f8e-9fa4-c81cb95fedf3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFIn
import Theorems.Thm_PI_VolStabW_FFHS_mem_range_of_pow

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
open Module Polynomial
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
namespace PI.VolStabW.FFHS
theorem _root_.solution (σ : K ≃ₐ[k] K) (hfrob : ∀ x, σ x = x ^ Fintype.card k)
    (h2 : finrank k K = 2) (d : K) (hd : σ d = d) :
    Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else Fintype.card k + 1 := by
  classical
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1 := ⟨Fintype.card k - 1, by omega⟩
  have hr0 : 0 < r := by omega
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), h2]
  have hnorm : ∀ t : K, t * σ t = algebraMap k K (Algebra.norm k t) := by
    intro t
    rw [FiniteField.algebraMap_norm_eq_pow, hfrob, ← pow_succ', Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, hK, hr, Nat.add_sub_cancel,
      Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = (r + 2) * r + 1 by ring),
      Nat.mul_div_cancel _ hr0]
  by_cases hd0 : d = 0
  · rw [if_pos hd0]
    subst hd0
    exact Nat.card_eq_one_iff_exists.2 ⟨⟨0, by simp⟩, fun y => Subtype.ext (by
      rcases mul_eq_zero.1 y.2 with h | h
      · exact h
      · exact (map_eq_zero_iff σ σ.injective).1 h)⟩
  rw [if_neg hd0]
  have hfix : d ^ Fintype.card k = d := by rw [← hfrob, hd]
  obtain ⟨d0, hd0e⟩ := mem_range_of_pow d hfix
  have hd00 : d0 ≠ 0 := by rintro rfl; exact hd0 (by rw [← hd0e, map_zero])
  let f : Kˣ →* kˣ := Units.map (Algebra.norm k (S := K) : K →* k)
  have hsurj : Function.Surjective f := FiniteField.unitsMap_norm_surjective k K
  have hall : ∀ y : kˣ, (Finset.univ.filter (fun g => f g = y)).card =
      (Finset.univ.filter (fun g => f g = 1)).card := fun y =>
    MonoidHom.card_fiber_eq_of_mem_range f (hsurj y) (hsurj 1)
  have htot := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ)
    (t := Finset.univ) (fun x _ => Finset.mem_coe.2 (Finset.mem_univ _))
  rw [Finset.sum_congr rfl (fun y _ => hall y), Finset.sum_const, Finset.card_univ,
    Finset.card_univ, smul_eq_mul, Fintype.card_units, Fintype.card_units, hK, hr,
    Nat.add_sub_cancel, Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = (r + 2) * r + 1 by ring),
    mul_comm] at htot
  have hF : (Finset.univ.filter (fun g => f g = 1)).card = r + 2 :=
    (Nat.eq_of_mul_eq_mul_left hr0 htot).symm
  let E : {t : K // t * σ t = d} ≃ {g : Kˣ // f g = Units.mk0 d0 hd00} :=
    { toFun := fun t => ⟨Units.mk0 t.1 (fun h0 => hd0 (by rw [← t.2, h0, zero_mul])),
        Units.ext (by
          simp only [f, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe]
          apply (algebraMap k K).injective
          rw [← hnorm, t.2, hd0e])⟩
      invFun := fun g => ⟨g.1.1, by
        have := congrArg Units.val g.2
        simp only [f, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] at this
        rw [hnorm, this, hd0e]⟩
      left_inv := fun t => rfl
      right_inv := fun g => Subtype.ext (Units.ext rfl) }
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_subtype, hall, hF, hr]
end PI.VolStabW.FFHS
