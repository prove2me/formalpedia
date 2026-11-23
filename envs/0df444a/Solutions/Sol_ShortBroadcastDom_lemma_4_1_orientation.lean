-- Prove2me | solution 1 for ShortBroadcastDom.lemma_4_1_orientation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:10:42.527482+00:00
-- url     : https://prove2.me/submissions/060c2b4c-bb2a-4d99-a925-ead786b8545d

import Mathlib.Combinatorics.Hall.Finite
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE

open ShortBroadcastDom

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (p : ℕ) (hp : 1 ≤ p)
    (hG : SubgraphDensityLE (p : ℝ) G) :
    ∃ o : V → V → Prop, (∀ u v, o u v → G.Adj u v) ∧ (∀ u v, G.Adj u v → (o u v ↔ ¬ o v u)) ∧
      ∀ v, {w | o v w}.ncard ≤ p := by
  classical
  let _ : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  let t : G.edgeSet → Finset (V × Fin p) := fun e =>
    (Finset.univ.filter fun v : V => v ∈ e.1) ×ˢ (Finset.univ : Finset (Fin p))
  have hHall : ∀ s : Finset G.edgeSet, s.card ≤ (s.biUnion t).card := by
    intro s
    let S : Finset V := s.biUnion fun e => Finset.univ.filter fun v : V => v ∈ e.1
    have hprod : S ×ˢ (Finset.univ : Finset (Fin p)) ⊆ s.biUnion t := by
      intro x hx
      rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
      rcases Finset.mem_biUnion.mp hx1 with ⟨e, hes, hve⟩
      exact Finset.mem_biUnion.mpr ⟨e, hes, Finset.mem_product.mpr ⟨hve, hx2⟩⟩
    have hcard_prod : p * S.card ≤ (s.biUnion t).card := by
      have hc := Finset.card_le_card hprod
      simpa [Finset.card_product, Nat.mul_comm] using hc
    let s' : Finset (Sym2 V) := s.map ⟨Subtype.val, Subtype.val_injective⟩
    have hs'_sub : (s' : Set (Sym2 V)) ⊆ {e | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} := by
      intro e he
      rcases Finset.mem_map.mp (Finset.mem_coe.mp he) with ⟨e0, he0s, rfl⟩
      refine ⟨e0.2, fun v hv => ?_⟩
      exact Finset.mem_biUnion.mpr ⟨e0, he0s, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
    have hs_ncard : s.card ≤ ({e | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} : Set (Sym2 V)).ncard := by
      have hfin : ({e | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} : Set (Sym2 V)).Finite := Set.toFinite _
      have hle := Set.ncard_le_ncard hs'_sub hfin
      rwa [Set.ncard_coe_finset, Finset.card_map] at hle
    have hd_real : (({e | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} : Set (Sym2 V)).ncard : ℝ) ≤
        (p : ℝ) * (S.card : ℝ) := hG S
    have hd_nat : ({e | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} : Set (Sym2 V)).ncard ≤ p * S.card := by
      exact_mod_cast hd_real
    exact le_trans (le_trans hs_ncard hd_nat) hcard_prod
  rcases (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall with ⟨f, hf_inj, hf_mem⟩
  let o : V → V → Prop := fun u v =>
    ∃ h : G.Adj u v, (f ⟨s(u, v), G.mem_edgeSet.mpr h⟩).1 = u
  refine ⟨o, ?_, ?_, ?_⟩
  · rintro u v ⟨h, -⟩
    exact h
  · intro u v huv
    have hvu : G.Adj v u := huv.symm
    have hne : u ≠ v := G.ne_of_adj huv
    let euv : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr huv⟩
    let evu : G.edgeSet := ⟨s(v, u), G.mem_edgeSet.mpr hvu⟩
    have heq : euv = evu := Subtype.ext Sym2.eq_swap
    have hmem : (f euv).1 ∈ s(u, v) := by
      have hm := (Finset.mem_product.mp (hf_mem euv)).1
      exact (Finset.mem_filter.mp hm).2
    have hor : (f euv).1 = u ∨ (f euv).1 = v := Sym2.mem_iff.mp hmem
    constructor
    · rintro ⟨_, hfu⟩ ⟨_, hfv⟩
      have hfu' : (f euv).1 = u := hfu
      have hfv' : (f euv).1 = v := by simpa [heq] using hfv
      exact hne (hfu'.symm.trans hfv')
    · intro hnot
      refine ⟨huv, ?_⟩
      rcases hor with hu | hv
      · exact hu
      · exfalso
        apply hnot
        refine ⟨hvu, ?_⟩
        simpa [heq] using hv
  · intro v
    let W : Finset V := Finset.univ.filter fun w => o v w
    have hW_eq : ({w | o v w} : Set V) = (W : Set V) := by
      ext w
      simp [W]
    rw [hW_eq, Set.ncard_coe_finset]
    let g : {w // w ∈ W} → Fin p := fun w =>
      (f ⟨s(v, w.1), G.mem_edgeSet.mpr ((Finset.mem_filter.mp w.2).2.choose)⟩).2
    have hg_inj : Function.Injective g := by
      intro w1 w2 hgeq
      rcases (Finset.mem_filter.mp w1.2).2 with ⟨h1, hf1⟩
      rcases (Finset.mem_filter.mp w2.2).2 with ⟨h2, hf2⟩
      let e1 : G.edgeSet := ⟨s(v, w1.1), G.mem_edgeSet.mpr h1⟩
      let e2 : G.edgeSet := ⟨s(v, w2.1), G.mem_edgeSet.mpr h2⟩
      have hfeq : f e1 = f e2 := Prod.ext (hf1.trans hf2.symm) hgeq
      have he12 : s(v, w1.1) = s(v, w2.1) := congrArg Subtype.val (hf_inj hfeq)
      rcases Sym2.eq_iff.mp he12 with ⟨-, hw⟩ | ⟨hvw2, hw1v⟩
      · exact Subtype.ext hw
      · exact Subtype.ext (hw1v.trans hvw2)
    have hcard : Fintype.card {w // w ∈ W} ≤ Fintype.card (Fin p) :=
      Fintype.card_le_of_injective g hg_inj
    simpa using hcard
