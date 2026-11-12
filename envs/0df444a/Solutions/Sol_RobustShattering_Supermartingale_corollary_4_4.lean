-- Prove2me | solution 1 for RobustShattering.Supermartingale.corollary_4_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:35:58.640181+00:00
-- url     : https://prove2.me/submissions/76fe173b-e468-44d7-ad0d-73b0c9f01324

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_XConnected
import Theorems.Thm_RobustShattering_Supermartingale_lemma_4_3

section
set_option autoImplicit false

namespace RobustShattering.Dev.C44
open Finset
open scoped Classical

variable {V : Type}

lemma nat_of_le {G : SimpleGraph V} {v u : V} {R : ℕ} (h : G.edist v u ≤ (R : ℕ∞)) :
    ∃ d : ℕ, G.edist v u = (d : ℕ∞) ∧ d ≤ R := by
  have hne : G.edist v u ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top R) h
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hne
  refine ⟨d, hd.symm, ?_⟩
  rw [← hd] at h
  exact_mod_cast h

lemma exists_pred {G : SimpleGraph V} {v u : V} {d : ℕ}
    (h : G.edist v u = ((d + 1 : ℕ) : ℕ∞)) :
    ∃ p, G.Adj p u ∧ G.edist v p = (d : ℕ∞) := by
  obtain ⟨q, hq⟩ := G.exists_walk_of_edist_eq_coe h
  have hlen : (q.reverse).length = d + 1 := by rw [SimpleGraph.Walk.length_reverse, hq]
  generalize q.reverse = w at hlen
  cases w with
  | nil => simp at hlen
  | @cons _ p _ hadj w' =>
    have hl : w'.length = d := by simpa using hlen
    refine ⟨p, hadj.symm, ?_⟩
    have h1 : G.edist p v ≤ (d : ℕ∞) := by
      have := G.edist_le w'
      rw [hl] at this; exact this
    rw [G.edist_comm] at h1
    have h2 : G.edist v u ≤ G.edist v p + 1 := by
      have := G.edist_triangle (u := v) (v := p) (w := u)
      rwa [SimpleGraph.edist_eq_one_iff_adj.2 hadj.symm] at this
    obtain ⟨k, hk, hkd⟩ := nat_of_le h1
    rw [hk] at h2 ⊢
    rw [h] at h2
    have : d + 1 ≤ k + 1 := by exact_mod_cast h2
    have : k = d := by omega
    rw [this]

lemma ball_card_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) (x : ℕ) :
    (LocalLLL.Main.ball G v x \ {v}).ncard ≤ Δ ^ x := by
  set B : ℕ → Finset V := fun r => univ.filter (fun u => u ≠ v ∧ G.edist v u ≤ (r : ℕ∞)) with hBdef
  have hset : LocalLLL.Main.ball G v x \ {v} = ((B x : Finset V) : Set V) := by
    ext u; simp [hBdef, LocalLLL.Main.ball, and_comm]
  rw [hset, Set.ncard_coe_finset]
  have hN : (univ.filter (G.Adj v)).card ≤ Δ := by
    have : univ.filter (G.Adj v) = G.neighborFinset v := by
      ext u; simp
    rw [this, SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg v
  have hB0 : (B 0).card = 0 := by
    rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro u hu
    simp only [hBdef, mem_filter, mem_univ, true_and] at hu
    have : G.edist v u = 0 := by simpa using hu.2
    exact hu.1 ((G.edist_eq_zero_iff.1 this).symm)
  have hB1 : (B 1).card ≤ Δ := by
    refine le_trans (card_le_card ?_) hN
    intro u hu
    simp only [hBdef, mem_filter, mem_univ, true_and] at hu ⊢
    have := (SimpleGraph.edist_le_one_iff_adj_or_eq).1 (by simpa using hu.2)
    rcases this with h | h
    · exact h
    · exact absurd h.symm hu.1
  have hrec : ∀ r, 1 ≤ r → (B (r+1)).card ≤ Δ + (Δ - 1) * (B r).card := by
    intro r hr
    set T := (B (r+1)).filter (fun u => ¬ G.Adj v u) with hT
    have hsub : B (r+1) ⊆ (univ.filter (G.Adj v)) ∪ T := by
      intro u hu
      by_cases h : G.Adj v u
      · simp [h]
      · exact mem_union_right _ (mem_filter.2 ⟨hu, h⟩)
    -- predecessor map
    let pred : V → V := fun u =>
      if h : ∃ p, G.Adj p u ∧ G.edist v p + 1 = G.edist v u then Classical.choose h else u
    have hpred : ∀ u ∈ T, G.Adj (pred u) u ∧ G.edist v (pred u) + 1 = G.edist v u := by
      intro u hu
      simp only [hT, hBdef, mem_filter, mem_univ, true_and] at hu
      obtain ⟨⟨hne, hle⟩, hnadj⟩ := hu
      obtain ⟨d', hd', hd'r⟩ := nat_of_le hle
      have hd2 : 2 ≤ d' := by
        by_contra hlt
        have : d' = 0 ∨ d' = 1 := by omega
        rcases this with h0 | h1
        · rw [h0] at hd'; exact hne ((G.edist_eq_zero_iff.1 (by simpa using hd')).symm)
        · rw [h1] at hd'
          exact hnadj (SimpleGraph.edist_eq_one_iff_adj.1 (by simpa using hd'))
      obtain ⟨d, rfl⟩ : ∃ d, d' = d + 1 := ⟨d' - 1, by omega⟩
      obtain ⟨p, hp1, hp2⟩ := exists_pred hd'
      have hex : ∃ p, G.Adj p u ∧ G.edist v p + 1 = G.edist v u :=
        ⟨p, hp1, by rw [hp2, hd']; norm_cast⟩
      simp only [pred, dif_pos hex]
      exact Classical.choose_spec hex
    have himg : T.image pred ⊆ B r := by
      intro a ha
      obtain ⟨u, hu, rfl⟩ := mem_image.1 ha
      obtain ⟨h1, h2⟩ := hpred u hu
      simp only [hT, hBdef, mem_filter, mem_univ, true_and] at hu
      obtain ⟨⟨hne, hle⟩, hnadj⟩ := hu
      obtain ⟨d', hd', hd'r⟩ := nat_of_le hle
      have hd2 : 2 ≤ d' := by
        by_contra hlt
        have : d' = 0 ∨ d' = 1 := by omega
        rcases this with h0 | h1
        · rw [h0] at hd'; exact hne ((G.edist_eq_zero_iff.1 (by simpa using hd')).symm)
        · rw [h1] at hd'
          exact hnadj (SimpleGraph.edist_eq_one_iff_adj.1 (by simpa using hd'))
      obtain ⟨e, he⟩ : ∃ e : ℕ, G.edist v (pred u) = (e : ℕ∞) := by
        have : G.edist v (pred u) ≠ ⊤ := by
          intro htop; rw [htop, hd'] at h2; simp at h2
        exact (ENat.ne_top_iff_exists.1 this).imp fun e he => he.symm
      rw [he, hd'] at h2
      have : e + 1 = d' := by exact_mod_cast h2
      simp only [hBdef, mem_filter, mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro hv
        rw [hv, SimpleGraph.edist_self] at he
        have : e = 0 := by exact_mod_cast he.symm
        omega
      · rw [he]; exact_mod_cast (by omega : e ≤ r)
    have hfib : ∀ a ∈ T.image pred, (T.filter (fun u => pred u = a)).card ≤ Δ - 1 := by
      intro a ha
      have haB := himg ha
      obtain ⟨u0, hu0, rfl⟩ := mem_image.1 ha
      simp only [hBdef, mem_filter, mem_univ, true_and] at haB
      obtain ⟨hav, hale⟩ := haB
      obtain ⟨e, he, her⟩ := nat_of_le hale
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := by
        refine ⟨e - 1, ?_⟩
        have : e ≠ 0 := by
          intro h0; rw [h0] at he
          exact hav ((G.edist_eq_zero_iff.1 (by simpa using he)).symm)
        omega
      obtain ⟨q, hq1, hq2⟩ := exists_pred he
      have hqmem : q ∈ G.neighborFinset (pred u0) := by simpa using hq1.symm
      calc (T.filter (fun u => pred u = pred u0)).card
          ≤ ((G.neighborFinset (pred u0)).erase q).card := by
            apply card_le_card
            intro u hu
            simp only [mem_filter] at hu
            obtain ⟨huT, hpu⟩ := hu
            obtain ⟨h1, h2⟩ := hpred u huT
            rw [hpu] at h1 h2
            rw [mem_erase]
            refine ⟨?_, by simpa using h1⟩
            intro huq
            rw [huq, hq2, he] at h2
            have h3 : e' + 1 + 1 = e' := by exact_mod_cast h2
            omega
        _ ≤ Δ - 1 := by
            rw [card_erase_of_mem hqmem, SimpleGraph.card_neighborFinset_eq_degree]
            exact Nat.sub_le_sub_right (hdeg _) 1
    have hT : T.card ≤ (Δ - 1) * (B r).card := by
      calc T.card ≤ (Δ - 1) * (T.image pred).card := card_le_mul_card_image T _ hfib
        _ ≤ _ := Nat.mul_le_mul_left _ (card_le_card himg)
    calc (B (r+1)).card ≤ ((univ.filter (G.Adj v)) ∪ T).card := card_le_card hsub
      _ ≤ (univ.filter (G.Adj v)).card + T.card := card_union_le _ _
      _ ≤ _ := Nat.add_le_add hN hT
  have hmain : ∀ r, 1 ≤ r → (B r).card ≤ Δ ^ r := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => simpa using hB1
    | succ r hr ih =>
      refine le_trans (hrec r hr) ?_
      have hΔr : Δ ≤ Δ ^ r := by
        calc Δ = Δ ^ 1 := (pow_one Δ).symm
          _ ≤ Δ ^ r := Nat.pow_le_pow_right (by omega) hr
      obtain ⟨k, rfl⟩ : ∃ k, Δ = k + 1 := ⟨Δ - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      calc k + 1 + k * (B r).card ≤ k + 1 + k * (k+1)^r :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ ih) _
        _ ≤ (k+1)^r + k * (k+1)^r := Nat.add_le_add_right hΔr _
        _ = (k+1)^(r+1) := by ring
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [hB0]
  · exact hmain x hx


lemma ballF_card_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) (r : ℕ) :
    (univ.filter (fun u => G.edist v u ≤ (r : ℕ∞))).card ≤ Δ ^ r + 1 := by
  set F := univ.filter (fun u => G.edist v u ≤ (r : ℕ∞)) with hF
  have hv : v ∈ F := by simp [hF]
  have h1 := ball_card_le G Δ hΔ hdeg v r
  have h2 : (LocalLLL.Main.ball G v r \ {v}) = ((F.erase v : Finset V) : Set V) := by
    ext u; simp [hF, LocalLLL.Main.ball, and_comm]
  rw [h2, Set.ncard_coe_finset] at h1
  have := Finset.card_erase_add_one hv
  omega

lemma xconn_insert (H : SimpleGraph V) (S : Set V) (hS : (H.induce S).Connected) (u s : V)
    (hs : s ∈ S) (hadj : H.Adj u s) : (H.induce (insert u S)).Connected := by
  have hle : S ⊆ insert u S := Set.subset_insert _ _
  have key : ∀ a : (insert u S : Set V),
      (H.induce (insert u S)).Reachable a ⟨s, Set.mem_insert_of_mem _ hs⟩ := by
    rintro ⟨a, ha⟩
    rcases ha with rfl | ha
    · exact SimpleGraph.Adj.reachable (by simpa using hadj)
    · exact (hS.preconnected ⟨a, ha⟩ ⟨s, hs⟩).map (SimpleGraph.induceHomOfLE H hle).toHom
  haveI : Nonempty (insert u S : Set V) := ⟨⟨u, Set.mem_insert _ _⟩⟩
  exact ⟨fun a b => (key a).trans (key b).symm⟩

lemma exists_S [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (c : ℕ) (C : Finset V)
    (hC : (G.induce (C : Set V)).Connected) :
    ∃ S : Finset V, S ⊆ C ∧ LocalLLL.Main.separated G c (S : Set V) ∧
      RobustShattering.Supermartingale.XConnected G (c + 1) (S : Set V) ∧
      C.card ≤ S.card * (Δ ^ c + 1) := by
  obtain ⟨⟨v0, hv0⟩⟩ := hC.nonempty
  let P : Finset V → Prop := fun S => S ⊆ C ∧ LocalLLL.Main.separated G c (S : Set V) ∧
      RobustShattering.Supermartingale.XConnected G (c + 1) (S : Set V)
  have hP1 : P {v0} := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact hv0
    · intro a ha b hb hab
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      exact absurd (ha.trans hb.symm) hab
    · haveI : Nonempty (({v0} : Finset V) : Set V) := ⟨⟨v0, by simp⟩⟩
      refine ⟨fun a b => ?_⟩
      have : a = b := by
        apply Subtype.ext
        have ha := a.2; have hb := b.2
        simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
        rw [ha, hb]
      rw [this]
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image (C.powerset.filter P) Finset.card
    ⟨{v0}, by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hP1.1, hP1⟩⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hSmem
  obtain ⟨hSC, hSsep, hSX⟩ := hSmem.2
  refine ⟨S, hSC, hSsep, hSX, ?_⟩
  -- cover
  have hcover : ∀ y ∈ C, ∃ s ∈ S, G.edist s y ≤ (c : ℕ∞) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨y, hyC, hy⟩ := hcon
    obtain ⟨⟨s0, hs0⟩⟩ := hSX.nonempty
    let p : ↥(C : Set V) → Prop := fun a => ∃ s ∈ S, G.edist s a.1 ≤ (c : ℕ∞)
    have hs0C : s0 ∈ (C : Set V) := hSC hs0
    have hp0 : p ⟨s0, hs0C⟩ := ⟨s0, hs0, by simp⟩
    have hpy : ¬ p ⟨y, hyC⟩ := by
      rintro ⟨s, hs, h⟩; exact absurd h (not_le.2 (hy s hs))
    obtain ⟨w⟩ := hC.preconnected ⟨s0, hs0C⟩ ⟨y, hyC⟩
    obtain ⟨d, -, hd1, hd2⟩ := w.exists_boundary_dart {a | p a} hp0 hpy
    have hadj : G.Adj d.fst.1 d.snd.1 := by simpa using d.adj
    obtain ⟨s, hs, hsa⟩ := hd1
    have hnp : ∀ s ∈ S, ¬ G.edist s d.snd.1 ≤ (c : ℕ∞) := fun s hs h => hd2 ⟨s, hs, h⟩
    set u := d.snd.1 with hu
    have hsu : G.edist s u ≤ ((c + 1 : ℕ) : ℕ∞) := by
      have := G.edist_triangle (u := s) (v := d.fst.1) (w := u)
      rw [SimpleGraph.edist_eq_one_iff_adj.2 hadj] at this
      refine this.trans ?_
      push_cast
      exact add_le_add_left hsa 1
    have huS : u ∉ S := fun h => hnp u h (by simp)
    have hP : P (insert u S) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact d.snd.2
        · exact hSC hx
      · intro a ha b hb hab hadj'
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
        have hle := hadj'.2
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact hab rfl
        · rw [G.edist_comm] at hle; exact hnp b hb hle
        · exact hnp a ha hle
        · exact hSsep a ha b hb hab ⟨hab, hle⟩
      · rw [Finset.coe_insert]
        refine xconn_insert _ _ hSX u s (by simpa using hs) ⟨?_, ?_⟩
        · intro h; exact huS (h ▸ hs)
        · rw [G.edist_comm]; exact hsu
    have := hSmax (insert u S) (by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hP.1, hP⟩)
    rw [Finset.card_insert_of_notMem huS] at this
    omega
  have hsub : C ⊆ S.biUnion (fun s => univ.filter (fun u => G.edist s u ≤ (c : ℕ∞))) := by
    intro y hy
    obtain ⟨s, hs, h⟩ := hcover y hy
    exact Finset.mem_biUnion.2 ⟨s, hs, by simpa using h⟩
  calc C.card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ s ∈ S, (univ.filter (fun u => G.edist s u ≤ (c : ℕ∞))).card := Finset.card_biUnion_le
    _ ≤ ∑ s ∈ S, (Δ ^ c + 1) := Finset.sum_le_sum fun s _ => ballF_card_le G Δ hΔ hdeg s c
    _ = S.card * (Δ ^ c + 1) := by simp

end RobustShattering.Dev.C44

open MeasureTheory

namespace RobustShattering.Supermartingale

theorem chk_corollary_4_4 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (c₂ : ℕ) (c₃ : ℝ) (hc₃ : 0 ≤ c₃)
    (t : ℕ) (ht : Real.logb Δ (Fintype.card V) ≤ (t : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Set V)
    (hB : ∀ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) → S.card = t →
      P {ω | (S : Set V) ⊆ B ω} ≤
        ENNReal.ofReal ((Δ : ℝ) ^ (-(((c₂ : ℝ) + c₃ + 3) * (S.card : ℝ))))) :
    P {ω | ∃ C : Finset V, (C : Set V) ⊆ B ω ∧ (G.induce (C : Set V)).Connected ∧
        t * (Δ ^ c₂ + 1) < C.card} ≤
      ENNReal.ofReal ((Δ : ℝ) ^ (-(c₃ * (t : ℝ)))) := by
  have h := (lemma_4_3 G Δ hΔ hdeg c₂ (c₂ + 1) c₃ hc₃ P B).2 t ht (by
    intro S hS hSc
    have := hB S hS hSc
    have e : (((c₂ + 1 : ℕ) : ℝ) + c₃ + 2) = (c₂ : ℝ) + c₃ + 3 := by push_cast; ring
    rw [e]; exact this)
  refine le_trans (measure_mono ?_) h
  rintro ω ⟨C, hCB, hCc, hCt⟩
  obtain ⟨S, hSC, hSsep, hSX, hSc⟩ := RobustShattering.Dev.C44.exists_S G Δ hΔ hdeg c₂ C hCc
  refine ⟨S, hSsep, hSX, fun x hx => hCB (hSC hx), ?_⟩
  exact Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le hCt hSc)

end RobustShattering.Supermartingale
end

theorem solution : type_of% @RobustShattering.Supermartingale.chk_corollary_4_4 := @RobustShattering.Supermartingale.chk_corollary_4_4
