-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:40:08.352282+00:00
-- url     : https://prove2.me/submissions/732274f7-d0cd-4b02-a345-149017b34cb8

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun K => G ≤ K ∧ P K)
  have hGmem : G ∈ candidates := by
    simp [candidates, hG]
  let edges : SimpleGraph V → Finset (V × V) := fun L =>
    Finset.univ.filter (fun p => L.Adj p.1 p.2)
  obtain ⟨H, hHmem, hmax⟩ :=
    candidates.exists_max_image (fun L => (edges L).card) ⟨G, hGmem⟩
  have hHprops : G ≤ H ∧ P H := (Finset.mem_filter.mp hHmem).2
  refine ⟨H, hHprops.1, hHprops.2, ?_⟩
  intro K hHK hPK
  have hKmem : K ∈ candidates := by
    simp [candidates, hHprops.1.trans hHK, hPK]
  by_contra hneq
  have hnotKH : ¬ K ≤ H := fun hKH => hneq (le_antisymm hKH hHK)
  have hnotAdj : ¬ (∀ ⦃a b⦄, K.Adj a b → H.Adj a b) := hnotKH
  push_neg at hnotAdj
  obtain ⟨a, b, hab, hnotab⟩ := hnotAdj
  have hsubset : edges H ⊆ edges K := by
    intro p hp
    simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hHK hp
  have hstrict : edges H ⊂ edges K := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
    intro heq
    have hp : (a, b) ∈ edges K := by
      simp [edges, hab]
    have hp' : (a, b) ∈ edges H := by rw [← heq] at hp; exact hp
    exact hnotab (by simpa [edges] using hp')
  have hcardlt : (edges H).card < (edges K).card := Finset.card_lt_card hstrict
  have hcardle : (edges K).card ≤ (edges H).card := hmax K hKmem
  exact (not_lt_of_ge hcardle hcardlt)