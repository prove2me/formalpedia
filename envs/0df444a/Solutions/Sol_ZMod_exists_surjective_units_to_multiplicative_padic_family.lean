-- Prove2me | solution 1 for ZMod.exists_surjective_units_to_multiplicative_padic_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/fe453f46-60f0-55ff-aa0b-239905a517a2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZMod_exists_surjective_units_to_multiplicative_padic_family

set_option autoImplicit false

namespace SurjD

theorem exists_surjective_of_dvd_card (G : Type*) [CommGroup G] [Finite G] [hG : IsCyclic G]
    (n : ℕ) [NeZero n] (hn : n ∣ Nat.card G) :
    ∃ f : G →* Multiplicative (ZMod n), Function.Surjective f := by

  let e : G ≃* Multiplicative (ZMod (Nat.card G)) := (zmodCyclicMulEquiv hG).symm

  let r : Multiplicative (ZMod (Nat.card G)) →* Multiplicative (ZMod n) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom hn (ZMod n)).toAddMonoidHom
  refine ⟨r.comp e.toMonoidHom, ?_⟩
  have hr : Function.Surjective r := by
    intro y
    refine ⟨Multiplicative.ofAdd (((Multiplicative.toAdd y).val : ℕ) : ZMod (Nat.card G)), ?_⟩
    show Multiplicative.ofAdd (ZMod.castHom hn (ZMod n) (((Multiplicative.toAdd y).val : ℕ) : ZMod (Nat.card G))) = y
    rw [map_natCast, ZMod.natCast_zmod_val]
    rfl
  exact hr.comp e.surjective

noncomputable def piDelta (p : ℕ) [Fact p.Prime] (q : ℕ) :
    (ZMod q)ˣ →* Multiplicative (ZMod (p ^ padicValNat p (q - 1))) :=
  if h : q.Prime ∧ (p ^ padicValNat p (q - 1) ∣ Nat.card (ZMod q)ˣ) then
    haveI : Fact q.Prime := ⟨h.1⟩
    (exists_surjective_of_dvd_card (ZMod q)ˣ (p ^ padicValNat p (q - 1)) h.2).choose
  else 1

theorem main (p : ℕ) [Fact p.Prime] :
    ∃ πΔ : (q : ℕ) → ((ZMod q)ˣ →* Multiplicative (ZMod (p ^ padicValNat p (q - 1)))),
      ∀ q : ℕ, q.Prime → q ≠ p → Function.Surjective (πΔ q) := by
  refine ⟨piDelta p, fun q hq _ => ?_⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdvd : p ^ padicValNat p (q - 1) ∣ Nat.card (ZMod q)ˣ := by
    rw [hcard]; exact pow_padicValNat_dvd
  have h : q.Prime ∧ (p ^ padicValNat p (q - 1) ∣ Nat.card (ZMod q)ˣ) := ⟨hq, hdvd⟩
  unfold piDelta
  rw [dif_pos h]
  exact (exists_surjective_of_dvd_card (ZMod q)ˣ (p ^ padicValNat p (q - 1)) h.2).choose_spec

end SurjD

theorem solution (p : ℕ) [Fact p.Prime] :
    ∃ πΔ : (q : ℕ) → ((ZMod q)ˣ →* Multiplicative (ZMod (p ^ padicValNat p (q - 1)))),
      ∀ q : ℕ, q.Prime → q ≠ p → Function.Surjective (πΔ q) :=
  SurjD.main p

end S_ZMod_exists_surjective_units_to_multiplicative_padic_family
end P2MW
export P2MW.S_ZMod_exists_surjective_units_to_multiplicative_padic_family (solution)
