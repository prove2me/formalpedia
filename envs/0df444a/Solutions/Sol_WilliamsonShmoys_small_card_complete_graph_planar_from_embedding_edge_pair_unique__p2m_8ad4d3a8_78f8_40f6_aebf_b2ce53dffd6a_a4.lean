-- Prove2me | solution 1 for WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_edge_pair_unique__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:54:37.937298+00:00
-- url     : https://prove2.me/submissions/5ef09e71-718d-4239-9de7-a4114a131ae6

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hsmall : Fintype.card V < 3) (u v x y : V)
    (huv : u < v) (hxy : x < y) (hne : Not ((u, v) = (x, y))) :
    False := by
  have impossible (a b c : V) (hab : a ≠ b) (hac : a ≠ c)
      (hbc : b ≠ c) : False := by
    have hcard : (insert a (insert b ({c} : Finset V))).card = 3 := by
      simp [hab, hac, hbc]
    have hle : (insert a (insert b ({c} : Finset V))).card ≤ Fintype.card V := by
      calc
        (insert a (insert b ({c} : Finset V))).card ≤
            (Finset.univ : Finset V).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card V := Finset.card_univ
    rw [hcard] at hle
    omega
  by_cases hxu : x = u
  · subst x
    apply impossible u v y
    · exact ne_of_lt huv
    · exact ne_of_lt hxy
    · intro hyv
      apply hne
      exact Prod.ext rfl hyv
  · by_cases hxv : x = v
    · have hvy : v < y := by simpa [hxv] using hxy
      have huy : u < y := lt_trans huv hvy
      apply impossible u v y
      · exact ne_of_lt huv
      · exact ne_of_lt huy
      · exact ne_of_lt hvy
    · apply impossible u v x
      · exact ne_of_lt huv
      · exact Ne.symm hxu
      · exact Ne.symm hxv