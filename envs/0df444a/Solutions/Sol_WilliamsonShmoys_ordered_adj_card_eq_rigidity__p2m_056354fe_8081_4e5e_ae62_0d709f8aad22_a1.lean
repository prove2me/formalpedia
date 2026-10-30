-- Prove2me | solution 1 for WilliamsonShmoys.ordered_adj_card_eq_rigidity__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:12:28.169869+00:00
-- url     : https://prove2.me/submissions/e20cf748-a462-42d0-b871-04dfa054c880

import Mathlib

theorem solution {V : Type} [Fintype V] (K L : SimpleGraph V) (hKL : K ≤ L)
    (hcard : Nat.card {p : V × V // L.Adj p.1 p.2} =
      Nat.card {p : V × V // K.Adj p.1 p.2}) : L ≤ K := by
  let f : {p : V × V // K.Adj p.1 p.2} → {p : V × V // L.Adj p.1 p.2} :=
    fun p => ⟨p.1, hKL p.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val hab
  have hsurj : Function.Surjective f :=
    (hf.bijective_of_nat_card_le (le_of_eq hcard)).surjective
  intro v w hvw
  obtain ⟨p, hp⟩ := hsurj ⟨(v, w), hvw⟩
  have hpval : p.1 = (v, w) := congrArg Subtype.val hp
  rcases p with ⟨⟨a, b⟩, hab⟩
  have hp' : (a, b) = (v, w) := by simpa using hpval
  rcases Prod.mk.inj hp' with ⟨rfl, rfl⟩
  exact hab
