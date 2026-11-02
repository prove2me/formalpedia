-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_eq_of_le_of_adjPairCard_le__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:36:31.348604+00:00
-- url     : https://prove2.me/submissions/67072b9a-e6e3-4a3f-8259-2c0910b0ddc2

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hcard : Nat.card {p : V × V // K.Adj p.1 p.2} ≤
      Nat.card {p : V × V // H.Adj p.1 p.2}) :
    K = H := by
  classical
  let A := {p : V × V // H.Adj p.1 p.2}
  let B := {p : V × V // K.Adj p.1 p.2}
  let f : A → B := fun p => ⟨p.1, hHK p.2⟩
  have hf : Function.Injective f := by
    intro x y h
    cases x with
    | mk xv hx =>
      cases y with
      | mk yv hy =>
        dsimp [f] at h
        cases h
        rfl
  have hcard' : Fintype.card B ≤ Fintype.card A := by
    simpa only [A, B, Nat.card_eq_fintype_card] using hcard
  have hcards : Fintype.card A = Fintype.card B :=
    (Fintype.card_le_of_injective f hf).antisymm hcard'
  have hsurj : Function.Surjective f := by
    by_contra h
    have hlt := Fintype.card_lt_of_injective_not_surjective f hf h
    omega
  have hKH : K ≤ H := by
    intro u v huv
    obtain ⟨⟨p, hp⟩, heq⟩ := hsurj ⟨(u, v), huv⟩
    have hval : p = (u, v) := congrArg (fun z : B => z.1) heq
    simpa [hval] using hp
  exact le_antisymm hKH hHK