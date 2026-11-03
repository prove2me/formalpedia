-- Prove2me | solution 1 for WilliamsonShmoys.component_bounds_sum_le__p2m_666f06c4_d624_4127_b254_b308e951621e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T09:06:30.783902+00:00
-- url     : https://prove2.me/submissions/ef9d2d53-6afd-4c09-93dc-7e5c89f175fc

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_support_ncard_sum

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V) (hdisconn : ¬ K.Connected) :
    letI : Fintype K.ConnectedComponent := Fintype.ofFinite _
    ∑ c : K.ConnectedComponent,
      (letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
       3 * Fintype.card {v : V // v ∈ c.supp} - 3) ≤ 3 * Fintype.card V - 6 := by
  classical
  letI : Fintype K.ConnectedComponent := Fintype.ofFinite _
  have hsumSet :
      (@Finset.univ K.ConnectedComponent SetLike.instFintype).sum
        (fun c => c.supp.ncard) = Fintype.card V := by
    letI : Fintype K.ConnectedComponent := SetLike.instFintype
    exact WilliamsonShmoys.component_support_ncard_sum K
  have huniv :
      (@Finset.univ K.ConnectedComponent SetLike.instFintype) =
        (@Finset.univ K.ConnectedComponent (Fintype.ofFinite K.ConnectedComponent)) := by
    ext c
    simp
  have hsum : (∑ c : K.ConnectedComponent, c.supp.ncard) = Fintype.card V := by
    change (@Finset.univ K.ConnectedComponent
      (Fintype.ofFinite K.ConnectedComponent)).sum
        (fun c => c.supp.ncard) = Fintype.card V
    rw [← huniv]
    exact hsumSet
  have hneV : Nonempty V := by
    apply Fintype.card_pos_iff.mp
    omega
  have hnonpre : ¬ K.Preconnected := by
    intro hp
    letI : Nonempty V := hneV
    exact hdisconn ⟨hp⟩
  have hcomponents : 2 ≤ Fintype.card K.ConnectedComponent := by
    change ¬ (∀ u v : V, K.Reachable u v) at hnonpre
    push_neg at hnonpre
    obtain ⟨u, hu⟩ := hnonpre
    obtain ⟨v, huv⟩ := hu
    have hne : K.connectedComponentMk u ≠ K.connectedComponentMk v := by
      intro heq
      exact huv (SimpleGraph.ConnectedComponent.exact heq)
    have hpair :
        ({K.connectedComponentMk u, K.connectedComponentMk v} :
          Finset K.ConnectedComponent).card = 2 := by
      simp [hne]
    calc
      2 = ({K.connectedComponentMk u, K.connectedComponentMk v} :
          Finset K.ConnectedComponent).card := hpair.symm
      _ ≤ Finset.univ.card := Finset.card_le_univ _
      _ = Fintype.card K.ConnectedComponent := by simp
  have hpos (c : K.ConnectedComponent) : 1 ≤ c.supp.ncard := by
    letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
    obtain ⟨v, hv⟩ := c.nonempty_supp
    have hc : 0 < Fintype.card {v : V // v ∈ c.supp} :=
      Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
    have hc' : 0 < c.supp.ncard := by
      simpa only [Set.fintypeCard_eq_ncard] using hc
    omega
  have hsplit :
      (∑ c : K.ConnectedComponent, (c.supp.ncard - 1)) +
        Fintype.card K.ConnectedComponent = Fintype.card V := by
    calc
      (∑ c : K.ConnectedComponent, (c.supp.ncard - 1)) +
          Fintype.card K.ConnectedComponent =
        (∑ c : K.ConnectedComponent, (c.supp.ncard - 1)) +
          (∑ c : K.ConnectedComponent, (1 : Nat)) := by simp
      _ = ∑ c : K.ConnectedComponent, ((c.supp.ncard - 1) + 1) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ c : K.ConnectedComponent, c.supp.ncard := by
        apply Finset.sum_congr rfl
        intro c hc
        have := hpos c
        omega
      _ = Fintype.card V := hsum
  have hrewrite :
      (∑ c : K.ConnectedComponent, (3 * c.supp.ncard - 3)) =
        3 * (∑ c : K.ConnectedComponent, (c.supp.ncard - 1)) := by
    calc
      (∑ c : K.ConnectedComponent, (3 * c.supp.ncard - 3)) =
          ∑ c : K.ConnectedComponent, (3 * (c.supp.ncard - 1)) := by
        apply Finset.sum_congr rfl
        intro c hc
        have := hpos c
        omega
      _ = 3 * (∑ c : K.ConnectedComponent, (c.supp.ncard - 1)) := by
        rw [Finset.mul_sum]
  have hbound :
      (∑ c : K.ConnectedComponent, (3 * c.supp.ncard - 3)) ≤
        3 * Fintype.card V - 6 := by
    rw [hrewrite]
    omega
  simpa only [Set.fintypeCard_eq_ncard] using hbound