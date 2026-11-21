-- Prove2me | solution 1 for QMaxCutBeyond.TwoQubit.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:35:12.635855+00:00
-- url     : https://prove2.me/submissions/715c7e20-7a22-456d-853b-95294987192f

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace Aux_QMaxCutBeyond_TwoQubit_lemma_2

lemma fiber_sub {n : ℕ} (V' : Finset (Fin n)) (c : Fin n → Sym2 (Fin n))
    (hvc : ∀ v ∈ V', v ∈ c v) (a b : Fin n) :
    V'.filter (fun v => c v = s(a, b)) ⊆ ({a, b} : Finset (Fin n)) := by
  intro v hv
  rw [Finset.mem_filter] at hv
  have h := hvc v hv.1
  rw [hv.2, Sym2.mem_iff] at h
  rw [Finset.mem_insert, Finset.mem_singleton]
  exact h

lemma fiber_card_le {n : ℕ} (V' : Finset (Fin n)) (c : Fin n → Sym2 (Fin n))
    (hvc : ∀ v ∈ V', v ∈ c v) (e : Sym2 (Fin n)) :
    (V'.filter (fun v => c v = e)).card ≤ 2 := by
  induction e using Sym2.ind with
  | h a b => exact (Finset.card_le_card (fiber_sub V' c hvc a b)).trans Finset.card_le_two

lemma fiber_full {n : ℕ} (V' : Finset (Fin n)) (c : Fin n → Sym2 (Fin n))
    (hvc : ∀ v ∈ V', v ∈ c v) (e : Sym2 (Fin n))
    (h2 : (V'.filter (fun v => c v = e)).card = 2) (v : Fin n) (hv : v ∈ e) :
    v ∈ V'.filter (fun v => c v = e) := by
  induction e using Sym2.ind with
  | h a b =>
    have hsub := fiber_sub V' c hvc a b
    have hle : ({a, b} : Finset (Fin n)).card ≤ (V'.filter (fun v => c v = s(a, b))).card := by
      rw [h2]
      exact Finset.card_le_two
    have heq := Finset.eq_of_subset_of_card_le hsub hle
    rw [heq, Finset.mem_insert, Finset.mem_singleton]
    exact Sym2.mem_iff.mp hv

end Aux_QMaxCutBeyond_TwoQubit_lemma_2

open Aux_QMaxCutBeyond_TwoQubit_lemma_2 in
open QMaxCutBeyond.TwoQubit in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) :
    ∃ M F : Finset (Sym2 (Fin n)), M ⊆ G.edgeFinset ∧ F ⊆ G.edgeFinset ∧
      IsEdgeMatching M ∧ (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).IsAcyclic ∧
      ∑ v, maxIncident G w v = ∑ e ∈ M, w e + ∑ e ∈ F, w e := by
  -- a total order on edges refining the weights
  obtain ⟨code, hcode⟩ : ∃ code : Sym2 (Fin n) → ℕ, Function.Injective code :=
    ⟨fun e => ((Fintype.equivFin (Sym2 (Fin n))) e : ℕ),
      fun a b h => (Fintype.equivFin (Sym2 (Fin n))).injective (Fin.ext h)⟩
  obtain ⟨key, hkeydef⟩ : ∃ key : Sym2 (Fin n) → Lex (ℝ × ℕ),
      key = fun e => toLex (w e, code e) := ⟨_, rfl⟩
  have hkey : Function.Injective key := by
    intro a b h
    rw [hkeydef] at h
    have h' := congrArg (fun p => (ofLex p).2) h
    exact hcode h'
  have hkey_w : ∀ e e', key e ≤ key e' → w e ≤ w e' := by
    intro e e' h
    rw [hkeydef] at h
    rcases Prod.Lex.toLex_le_toLex.mp h with h1 | ⟨h1, _⟩
    · exact h1.le
    · exact h1.le
  -- each vertex chooses a key-maximal incident edge
  have hex : ∀ v, ∃ e, (G.incidenceFinset v).Nonempty →
      e ∈ G.incidenceFinset v ∧ ∀ e' ∈ G.incidenceFinset v, key e' ≤ key e := by
    intro v
    by_cases h : (G.incidenceFinset v).Nonempty
    · obtain ⟨e, he, hmax⟩ := Finset.exists_max_image _ key h
      exact ⟨e, fun _ => ⟨he, hmax⟩⟩
    · exact ⟨s(v, v), fun h' => absurd h' h⟩
  choose c hc using hex
  obtain ⟨V', hV'⟩ : ∃ V' : Finset (Fin n),
      V' = Finset.univ.filter fun v => (G.incidenceFinset v).Nonempty := ⟨_, rfl⟩
  have hV'mem : ∀ v, v ∈ V' ↔ (G.incidenceFinset v).Nonempty := by
    intro v
    rw [hV', Finset.mem_filter]
    simp
  have hcmem : ∀ v ∈ V', c v ∈ G.incidenceFinset v := fun v hv => (hc v ((hV'mem v).mp hv)).1
  have hcinc : ∀ v ∈ V', c v ∈ G.edgeSet ∧ v ∈ c v := by
    intro v hv
    exact Set.mem_sep_iff.mp ((G.mem_incidenceFinset _ _).mp (hcmem v hv))
  have hvc : ∀ v ∈ V', v ∈ c v := fun v hv => (hcinc v hv).2
  obtain ⟨C, hCdef⟩ : ∃ C : Finset (Sym2 (Fin n)), C = V'.image c := ⟨_, rfl⟩
  have hCG : C ⊆ G.edgeFinset := by
    intro e he
    rw [hCdef, Finset.mem_image] at he
    obtain ⟨v, hv, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset]
    exact (hcinc v hv).1
  obtain ⟨M, hMdef⟩ : ∃ M : Finset (Sym2 (Fin n)),
      M = C.filter (fun e => (V'.filter (fun v => c v = e)).card = 2) := ⟨_, rfl⟩
  have hMC : M ⊆ C := by
    rw [hMdef]
    exact Finset.filter_subset _ _
  refine ⟨M, C, hMC.trans hCG, hCG, ?_, ?_, ?_⟩
  · -- matching
    intro e he e' he' hne v hv hv'
    rw [hMdef, Finset.mem_filter] at he he'
    have h1 := Finset.mem_filter.mp (fiber_full V' c hvc e he.2 v hv)
    have h2 := Finset.mem_filter.mp (fiber_full V' c hvc e' he'.2 v hv')
    exact hne (h1.2.symm.trans h2.2)
  · -- forest
    intro v0 cyc hcyc
    have hne : cyc.edges.toFinset.Nonempty := by
      obtain ⟨e, he⟩ := cyc.edges.exists_mem_of_ne_nil
        (SimpleGraph.Walk.edges_eq_nil.not.mpr hcyc.not_nil)
      exact ⟨e, List.mem_toFinset.mpr he⟩
    have hedgeC : ∀ e ∈ cyc.edges, e ∈ C := by
      intro e he
      have h := cyc.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_fromEdgeSet] at h
      exact h.1
    obtain ⟨e0, he0, hmin⟩ := Finset.exists_min_image _ key hne
    have he0' : e0 ∈ cyc.edges := List.mem_toFinset.mp he0
    have he0C := hedgeC e0 he0'
    rw [hCdef, Finset.mem_image] at he0C
    obtain ⟨u, hu, hue⟩ := he0C
    have hu0 : u ∈ e0 := hue ▸ hvc u hu
    obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hu0
    have husupp : u ∈ cyc.support := by
      rw [hx] at he0'
      exact cyc.fst_mem_support_of_mem_edges he0'
    have hc' := hcyc.rotate husupp
    have hnil := hc'.not_nil
    have hE1 := (cyc.rotate u husupp).mk_start_snd_mem_edges hnil
    have hE2 := (cyc.rotate u husupp).mk_penultimate_end_mem_edges hnil
    have hrot : ∀ a, a ∈ (cyc.rotate u husupp).edges → a ∈ cyc.edges :=
      fun a ha => (cyc.rotate_edges u husupp).mem_iff.mp ha
    have hsn := hc'.snd_ne_penultimate
    have hadj := (cyc.rotate u husupp).adj_snd hnil
    have hE12 : s(u, (cyc.rotate u husupp).snd) ≠ s((cyc.rotate u husupp).penultimate, u) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨_, h2⟩
      · exact (SimpleGraph.Adj.ne hadj) h2.symm
      · exact hsn h2
    -- an edge of the cycle at u other than e0
    obtain ⟨e', he'mem, he'u, he'ne⟩ : ∃ e', e' ∈ cyc.edges ∧ u ∈ e' ∧ e' ≠ e0 := by
      by_cases h : s(u, (cyc.rotate u husupp).snd) = e0
      · refine ⟨s((cyc.rotate u husupp).penultimate, u), hrot _ hE2, Sym2.mem_mk_right _ _, ?_⟩
        rw [← h]
        exact hE12.symm
      · exact ⟨s(u, (cyc.rotate u husupp).snd), hrot _ hE1, Sym2.mem_mk_left _ _, h⟩
    have he'C := hedgeC e' he'mem
    have he'G : e' ∈ G.edgeSet := (SimpleGraph.mem_edgeFinset).mp (hCG he'C)
    have he'inc : e' ∈ G.incidenceFinset u := (G.mem_incidenceFinset _ _).mpr (Set.mem_sep_iff.mpr ⟨he'G, he'u⟩)
    have hle1 : key e' ≤ key (c u) := (hc u ((hV'mem u).mp hu)).2 e' he'inc
    have hle2 : key e0 ≤ key e' := hmin e' (List.mem_toFinset.mpr he'mem)
    rw [hue] at hle1
    exact he'ne (hkey (le_antisymm hle1 hle2))
  · -- the weight identity
    have hmax : ∀ v ∈ V', maxIncident G w v = w (c v) := by
      intro v hv
      have hcv := hc v ((hV'mem v).mp hv)
      have hsup : ((G.incidenceFinset v).sup fun e => (w e).toNNReal) = (w (c v)).toNNReal := by
        apply le_antisymm
        · exact Finset.sup_le fun e he => Real.toNNReal_le_toNNReal (hkey_w e (c v) (hcv.2 e he))
        · exact Finset.le_sup (f := fun e => (w e).toNNReal) hcv.1
      unfold maxIncident
      rw [hsup, Real.coe_toNNReal _ (hw _)]
    have hzero : ∀ v, v ∉ V' → maxIncident G w v = 0 := by
      intro v hv
      have hemp : G.incidenceFinset v = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        exact fun h => hv ((hV'mem v).mpr h)
      unfold maxIncident
      rw [hemp, Finset.sup_empty]
      simp
    have hL : ∑ v, maxIncident G w v = ∑ v ∈ V', w (c v) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => v ∈ V')]
      have h1 : ∑ v ∈ Finset.univ.filter (fun v => v ∉ V'), maxIncident G w v = 0 :=
        Finset.sum_eq_zero fun v hv => hzero v (Finset.mem_filter.mp hv).2
      have h2 : Finset.univ.filter (fun v => v ∈ V') = V' := by
        ext v
        simp
      rw [h1, add_zero, h2]
      exact Finset.sum_congr rfl fun v hv => hmax v hv
    rw [hL, Finset.sum_comp (fun e => w e) c, ← hCdef]
    rw [hMdef, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    have hpos : 1 ≤ (V'.filter (fun v => c v = e)).card := by
      rw [hCdef, Finset.mem_image] at he
      obtain ⟨v, hv, hve⟩ := he
      exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hve⟩⟩
    have hle := fiber_card_le V' c hvc e
    rw [nsmul_eq_mul]
    rcases (show (V'.filter (fun v => c v = e)).card = 1 ∨
        (V'.filter (fun v => c v = e)).card = 2 by omega) with h | h
    · rw [h, if_neg (show ¬ ((1 : ℕ) = 2) by norm_num), Nat.cast_one]
      ring
    · rw [h, if_pos rfl, Nat.cast_ofNat]
      ring
