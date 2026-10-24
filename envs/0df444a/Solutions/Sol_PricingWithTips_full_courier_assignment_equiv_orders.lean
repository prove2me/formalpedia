-- Prove2me | solution 1 for PricingWithTips.full_courier_assignment_equiv_orders
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:48:00.788118+00:00
-- url     : https://prove2.me/submissions/d5a149a1-072e-4f4d-8df4-b437f5e09be5

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private noncomputable def fullCourierOrder (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d) (d : D) :
    {p : B × S // A.Delivers p.1 p.2} := by
  classical
  let b := Classical.choose (hfull d)
  let hb := Classical.choose_spec (hfull d)
  let s := Classical.choose hb
  exact ⟨(b, s), ⟨d, Classical.choose_spec hb⟩⟩

private theorem fullCourierOrder_trades (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d) (d : D) :
    A.Trades (fullCourierOrder A hfull d).1.1
      (fullCourierOrder A hfull d).1.2 d := by
  unfold fullCourierOrder
  exact Classical.choose_spec (Classical.choose_spec (hfull d))

private theorem fullCourierOrder_bijective (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d) :
    Function.Bijective (fullCourierOrder A hfull) := by
  classical
  constructor
  · intro d e hde
    have hd := fullCourierOrder_trades A hfull d
    have he := fullCourierOrder_trades A hfull e
    have hpair := congrArg Subtype.val hde
    rw [hpair] at hd
    have hp : some ((fullCourierOrder A hfull e).1.2, d) =
        some ((fullCourierOrder A hfull e).1.2, e) := hd.symm.trans he
    exact congrArg Prod.snd (Option.some.inj hp)
  · intro o
    rcases o with ⟨⟨b, s⟩, ⟨d, ht⟩⟩
    refine ⟨d, ?_⟩
    apply Subtype.ext
    have hd := fullCourierOrder_trades A hfull d
    have hb : (fullCourierOrder A hfull d).1.1 = b := A.courier_unique hd ht
    have hs : (fullCourierOrder A hfull d).1.2 = s := by
      have hd' : A.Trades b (fullCourierOrder A hfull d).1.2 d := by
        simpa [hb] using hd
      have hp : some ((fullCourierOrder A hfull d).1.2, d) = some (s, d) :=
        hd'.symm.trans ht
      exact congrArg Prod.fst (Option.some.inj hp)
    exact Prod.ext hb hs

end PricingWithTips

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution (A : Allocation B S D) (hfull : ∀ d, A.CourierWorks d) :
    ∃ e : D ≃ {p : B × S // A.Delivers p.1 p.2},
      ∀ d, A.Trades (e d).1.1 (e d).1.2 d := by
  let e := Equiv.ofBijective (PricingWithTips.fullCourierOrder A hfull)
    (PricingWithTips.fullCourierOrder_bijective A hfull)
  exact ⟨e, PricingWithTips.fullCourierOrder_trades A hfull⟩
