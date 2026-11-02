-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_adjacency_card_strict__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:18:10.595771+00:00
-- url     : https://prove2.me/submissions/0ad4ffa1-174f-49fd-9ba8-f02e03755d9c

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (hne : G ≠ H) :
    Fintype.card {p : V × V // G.Adj p.1 p.2} <
      Fintype.card {p : V × V // H.Adj p.1 p.2} := by
  classical
  let A := {p : V × V // G.Adj p.1 p.2}
  let B := {p : V × V // H.Adj p.1 p.2}
  have hdiff : ∃ u v, H.Adj u v ∧ ¬ G.Adj u v := by
    by_contra hnot
    apply hne
    ext u v
    constructor
    · intro huv
      exact hGH huv
    · intro huv
      by_contra hguv
      exact hnot ⟨u, v, huv, hguv⟩
  let f : A → B := fun p => ⟨p.1, hGH p.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : B => z.1) hab
  obtain ⟨u, v, huv, hnot⟩ := hdiff
  let y : B := ⟨(u, v), huv⟩
  let g : A ⊕ Unit → B := Sum.elim f (fun _ => y)
  have hg : Function.Injective g := by
    intro s t hst
    cases s with
    | inl a =>
      cases t with
      | inl b =>
        have hab : f a = f b := by simpa [g] using hst
        exact congrArg Sum.inl (hf hab)
      | inr z =>
        have hfy : f a = y := by simpa [g] using hst
        have hval : a.1 = (u, v) := congrArg (fun z : B => z.1) hfy
        exact False.elim (hnot (by simpa [hval] using a.2))
    | inr z =>
      cases t with
      | inl a =>
        have hyf : y = f a := by simpa [g] using hst
        have hval : a.1 = (u, v) := congrArg (fun z : B => z.1) hyf.symm
        exact False.elim (hnot (by simpa [hval] using a.2))
      | inr w =>
        have : z = w := Subsingleton.elim _ _
        subst w
        rfl
  have hcard : Fintype.card (A ⊕ Unit) ≤ Fintype.card B :=
    Fintype.card_le_of_injective g hg
  have hcard' : Fintype.card A + 1 ≤ Fintype.card B := by
    simpa using hcard
  simpa [A, B] using (Nat.lt_of_succ_le hcard')