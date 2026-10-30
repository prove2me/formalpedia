-- Prove2me | solution 1 for WilliamsonShmoys.finite_monotone_property_has_maximal_supergraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:33:30.885234+00:00
-- url     : https://prove2.me/submissions/a47a0bc7-9481-46fa-985b-ee9d82e91f30

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V → Prop)
    (hmono : ∀ {G H : SimpleGraph V}, G ≤ H → Q H → Q G)
    (K : SimpleGraph V) (hK : Q K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ Q H ∧
      ∀ H' : SimpleGraph V, H ≤ H' → Q H' → H' = H := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K ≤ G ∧ Q G
  have hadmissible : admissible.Nonempty := by
    refine ⟨K, ?_⟩
    simp [admissible, hK]
  let edgeCount : SimpleGraph V → Nat := fun G =>
    Fintype.card {p : V × V // G.Adj p.1 p.2}
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image admissible edgeCount hadmissible
  have hKH : K ≤ H := (Finset.mem_filter.mp hHmem).2.1
  have hQH : Q H := (Finset.mem_filter.mp hHmem).2.2
  refine ⟨H, hKH, hQH, ?_⟩
  intro H' hHH' hQH'
  by_contra hne
  have hcard : edgeCount H < edgeCount H' := by
    let f : {p : V × V // H.Adj p.1 p.2} →
        {p : V × V // H'.Adj p.1 p.2} := fun p => ⟨p.1, hHH' p.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hp : (a : V × V) = (b : V × V) := by
        exact congrArg (fun z : {p : V × V // H'.Adj p.1 p.2} => (z : V × V)) hab
      exact Subtype.ext hp
    have hdiff : ∃ x y, H'.Adj x y ∧ ¬ H.Adj x y := by
      by_contra h
      push_neg at h
      have heq : H'.Adj = H.Adj := by
        funext x y
        apply propext
        exact ⟨h x y, fun hxy => hHH' hxy⟩
      exact hne ((SimpleGraph.adj_inj).mp heq)
    obtain ⟨x, y, hxy, hnxy⟩ := hdiff
    have hnot_surj : ¬ Function.Surjective f := by
      intro hsurj
      obtain ⟨a, ha⟩ := hsurj ⟨(x, y), hxy⟩
      have hv : (a : V × V) = (x, y) := by
        exact congrArg (fun z : {p : V × V // H'.Adj p.1 p.2} => (z : V × V)) ha
      apply hnxy
      simpa [hv] using a.property
    exact Fintype.card_lt_of_injective_not_surjective f hf hnot_surj
  have hH'mem : H' ∈ admissible := by
    simp only [admissible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hKH.trans hHH', hQH'⟩
  have hmax' := hHmax H' hH'mem
  exact (Nat.not_lt_of_ge hmax') hcard