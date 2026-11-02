-- Prove2me | solution 1 for WilliamsonShmoys.le_ncard_edgeSet_eq__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:15:56.095405+00:00
-- url     : https://prove2.me/submissions/80c7d4c6-0bbf-4f77-bd28-fb5aaf233562

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    {H K : SimpleGraph V} (hHK : H ≤ K)
    (hcard : Set.ncard H.edgeSet ≥ Set.ncard K.edgeSet) : K = H := by
  letI : Fintype H.edgeSet := Fintype.ofFinite H.edgeSet
  letI : Fintype K.edgeSet := Fintype.ofFinite K.edgeSet
  have hsub : H.edgeSet ⊆ K.edgeSet := SimpleGraph.edgeSet_mono hHK
  have hsubFin : H.edgeSet.toFinset ⊆ K.edgeSet.toFinset := by
    intro e he
    exact Set.mem_toFinset.mpr (hsub (Set.mem_toFinset.mp he))
  have hcardFin : K.edgeSet.toFinset.card ≤ H.edgeSet.toFinset.card := by
    calc
      K.edgeSet.toFinset.card = K.edgeSet.ncard :=
        (Set.ncard_eq_toFinset_card _).symm
      _ ≤ H.edgeSet.ncard := hcard
      _ = H.edgeSet.toFinset.card := Set.ncard_eq_toFinset_card _
  have hedgeFin : H.edgeSet.toFinset = K.edgeSet.toFinset :=
    Finset.eq_of_subset_of_card_le hsubFin hcardFin
  have hedge : H.edgeSet = K.edgeSet := by
    ext e
    constructor
    · intro he
      have he' : e ∈ H.edgeSet.toFinset := Set.mem_toFinset.mpr he
      have hk : e ∈ K.edgeSet.toFinset := by rw [← hedgeFin]; exact he'
      exact Set.mem_toFinset.mp hk
    · intro he
      have he' : e ∈ K.edgeSet.toFinset := Set.mem_toFinset.mpr he
      have hh : e ∈ H.edgeSet.toFinset := by rw [hedgeFin]; exact he'
      exact Set.mem_toFinset.mp hh
  apply SimpleGraph.ext
  funext v w
  apply propext
  constructor
  · intro hvw
    have hw : s(v, w) ∈ K.edgeSet := by simpa using hvw
    rw [← hedge] at hw
    simpa using hw
  · intro hvw
    exact hHK hvw
