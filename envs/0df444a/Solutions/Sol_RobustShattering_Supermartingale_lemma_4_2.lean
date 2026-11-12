-- Prove2me | solution 1 for RobustShattering.Supermartingale.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:35:57.884876+00:00
-- url     : https://prove2.me/submissions/63a12898-2145-4d0d-849f-63f5c0cb443d

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_XConnected

section
set_option autoImplicit false

namespace RobustShattering.Dev.L42
open Finset
open scoped Classical

variable {V : Type}

/-- `S ⊆ A`, `R ⊆ S`, and every vertex of `S` is joined to some root in `R` by a path inside `S`. -/
def Gen (H : SimpleGraph V) (A R S : Finset V) : Prop :=
  S ⊆ A ∧ R ⊆ S ∧ ∀ u ∈ S, ∃ r ∈ R,
    Relation.ReflTransGen (fun a b => H.Adj a b ∧ b ∈ S) r u

lemma rtg_mem {H : SimpleGraph V} {S : Finset V} {r u : V}
    (h : Relation.ReflTransGen (fun a b => H.Adj a b ∧ b ∈ S) r u) (hr : r ∈ S) : u ∈ S := by
  induction h with
  | refl => exact hr
  | tail _ hbc _ => exact hbc.2

lemma vand (M s n : ℕ) :
    ∑ k ∈ range (M+1), M.choose k * (if k ≤ n then (M*s).choose (n-k) else 0)
      = (M*(s+1)).choose n := by
  have e : M*(s+1) = M + M*s := by ring
  rw [e, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h1 : ∑ k ∈ range (M+1), M.choose k * (if k ≤ n then (M*s).choose (n-k) else 0)
      = ∑ k ∈ range (M+n+1), M.choose k * (if k ≤ n then (M*s).choose (n-k) else 0) := by
    apply sum_subset (range_subset_range.2 (by omega))
    intro k _ hk
    simp only [mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have h2 : ∑ k ∈ range (n+1), M.choose k * (M*s).choose (n-k)
      = ∑ k ∈ range (M+n+1), M.choose k * (if k ≤ n then (M*s).choose (n-k) else 0) := by
    rw [← sum_subset (range_subset_range.2 (show n+1 ≤ M+n+1 by omega))]
    · apply sum_congr rfl
      intro k hk
      simp only [mem_range] at hk
      rw [if_pos (by omega)]
    · intro k _ hk
      simp only [mem_range] at hk
      rw [if_neg (by omega)]; simp
  rw [h1, h2]

theorem gen_count [Fintype V] (H : SimpleGraph V) (M : ℕ)
    (hM : ∀ u, (univ.filter (H.Adj u)).card ≤ M) :
    ∀ (s : ℕ) (A R : Finset V),
      ((A.powerset).filter (fun S => S.card = s ∧ Gen H A R S)).card
        ≤ if R.card ≤ s then (M*s).choose (s - R.card) else 0 := by
  intro s
  induction s with
  | zero =>
    intro A R
    by_cases hR : R.card ≤ 0
    · rw [if_pos hR]
      have : (A.powerset.filter (fun S => S.card = 0 ∧ Gen H A R S)) ⊆ {∅} := by
        intro S hS
        simp only [mem_filter, mem_powerset] at hS
        simp [card_eq_zero.1 hS.2.1]
      calc _ ≤ ({∅} : Finset (Finset V)).card := card_le_card this
        _ ≤ _ := by simp
    · rw [if_neg hR]
      have : (A.powerset.filter (fun S => S.card = 0 ∧ Gen H A R S)) = ∅ := by
        apply eq_empty_of_forall_notMem
        intro S hS
        simp only [mem_filter] at hS
        have := card_le_card hS.2.2.2.1
        omega
      rw [this, card_empty]
  | succ s ih =>
    intro A R
    by_cases hR : R.card ≤ s+1
    swap
    · rw [if_neg hR]
      have : (A.powerset.filter (fun S => S.card = s+1 ∧ Gen H A R S)) = ∅ := by
        apply eq_empty_of_forall_notMem
        intro S hS
        simp only [mem_filter] at hS
        have := card_le_card hS.2.2.2.1
        omega
      simp [this]
    rw [if_pos hR]
    rcases R.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
    · have : (A.powerset.filter (fun S => S.card = s+1 ∧ Gen H A ∅ S)) = ∅ := by
        apply eq_empty_of_forall_notMem
        intro S hS
        simp only [mem_filter] at hS
        obtain ⟨u, hu⟩ : S.Nonempty := card_pos.1 (by omega)
        obtain ⟨r, hr, _⟩ := hS.2.2.2.2 u hu
        simp at hr
      simp [this]
    · have hr1 : 1 ≤ R.card := card_pos.2 ⟨w, hw⟩
      set P : Finset V := ((A.erase w).filter (H.Adj w)) \ R with hP
      have hPM : P.card ≤ M := by
        refine le_trans (card_le_card ?_) (hM w)
        intro x hx
        simp only [hP, mem_sdiff, mem_filter] at hx
        simp [hx.1.2]
      set n := s + 1 - R.card with hn
      set g : ℕ → ℕ := fun k => if k ≤ n then (M*s).choose (n-k) else 0 with hg
      have hB : ∀ W : Finset V, W ∈ P.powerset →
          (((A.erase w).powerset.filter
              (fun S' => S'.card = s ∧ Gen H (A.erase w) ((R.erase w) ∪ W) S')).image
              (insert w)).card ≤ g W.card := by
        intro W hW
        have hWP : W ⊆ P := mem_powerset.1 hW
        have hdisj : Disjoint (R.erase w) W := by
          rw [disjoint_left]
          intro x hx hxW
          have := hWP hxW
          simp only [hP, mem_sdiff] at this
          exact this.2 (mem_of_mem_erase hx)
        have hcardR : ((R.erase w) ∪ W).card = R.card - 1 + W.card := by
          rw [card_union_of_disjoint hdisj, card_erase_of_mem hw]
        refine le_trans card_image_le (le_trans (ih (A.erase w) ((R.erase w) ∪ W)) ?_)
        rw [hcardR]
        simp only [hg, hn]
        split_ifs with h1 h2 h2
        · apply le_of_eq; congr 1; omega
        · omega
        · omega
        · exact le_rfl
      have hcover : (A.powerset.filter (fun S => S.card = s+1 ∧ Gen H A R S)) ⊆
          P.powerset.biUnion (fun W => ((A.erase w).powerset.filter
              (fun S' => S'.card = s ∧ Gen H (A.erase w) ((R.erase w) ∪ W) S')).image
              (insert w)) := by
        intro S hS
        simp only [mem_filter, mem_powerset] at hS
        obtain ⟨hSA, hcard, _, hRS, hconn⟩ := hS
        have hwS : w ∈ S := hRS hw
        set W : Finset V := ((S.erase w).filter (H.Adj w)) \ R with hW
        have hWP : W ⊆ P := by
          intro x hx
          simp only [hW, hP, mem_sdiff, mem_filter] at hx ⊢
          refine ⟨⟨?_, hx.1.2⟩, hx.2⟩
          exact mem_erase.2 ⟨(mem_erase.1 hx.1.1).1, hSA (mem_erase.1 hx.1.1).2⟩
        rw [mem_biUnion]
        refine ⟨W, mem_powerset.2 hWP, ?_⟩
        rw [mem_image]
        refine ⟨S.erase w, ?_, insert_erase hwS⟩
        rw [mem_filter, mem_powerset]
        have hWS : W ⊆ S.erase w := by
          intro x hx
          simp only [hW, mem_sdiff, mem_filter] at hx
          exact hx.1.1
        refine ⟨erase_subset_erase w hSA, by rw [card_erase_of_mem hwS]; omega,
          erase_subset_erase w hSA, ?_, ?_⟩
        · intro x hx
          rw [mem_union] at hx
          rcases hx with hx | hx
          · exact erase_subset_erase w hRS hx
          · exact hWS hx
        · intro u hu
          obtain ⟨r, hrR, hch⟩ := hconn u (mem_of_mem_erase hu)
          have huw : u ≠ w := ne_of_mem_erase hu
          -- generalised induction on the chain
          have key : ∀ u', Relation.ReflTransGen (fun a b => H.Adj a b ∧ b ∈ S) r u' →
              u' ∈ S.erase w → ∃ r' ∈ (R.erase w) ∪ W,
                Relation.ReflTransGen (fun a b => H.Adj a b ∧ b ∈ S.erase w) r' u' := by
            intro u' h
            induction h with
            | refl =>
              intro hu'
              refine ⟨r, ?_, Relation.ReflTransGen.refl⟩
              exact mem_union_left _ (mem_erase.2 ⟨ne_of_mem_erase hu', hrR⟩)
            | @tail b c hrb hbc ihb =>
              intro hc
              by_cases hbw : b = w
              · subst hbw
                refine ⟨c, ?_, Relation.ReflTransGen.refl⟩
                by_cases hcR : c ∈ R
                · exact mem_union_left _ (mem_erase.2 ⟨ne_of_mem_erase hc, hcR⟩)
                · apply mem_union_right
                  simp only [hW, mem_sdiff, mem_filter]
                  exact ⟨⟨hc, hbc.1⟩, hcR⟩
              · have hbS : b ∈ S := rtg_mem hrb (hRS hrR)
                obtain ⟨r', hr', hch'⟩ := ihb (mem_erase.2 ⟨hbw, hbS⟩)
                exact ⟨r', hr', hch'.tail ⟨hbc.1, hc⟩⟩
          exact key u hch hu
      calc _ ≤ _ := card_le_card hcover
        _ ≤ ∑ W ∈ P.powerset, (((A.erase w).powerset.filter
              (fun S' => S'.card = s ∧ Gen H (A.erase w) ((R.erase w) ∪ W) S')).image
              (insert w)).card := card_biUnion_le
        _ ≤ ∑ W ∈ P.powerset, g W.card := sum_le_sum hB
        _ = ∑ m ∈ range (P.card+1), P.card.choose m • g m := sum_powerset_apply_card g
        _ ≤ ∑ m ∈ range (P.card+1), M.choose m * g m := by
            apply sum_le_sum
            intro m _
            rw [smul_eq_mul]
            exact Nat.mul_le_mul_right _ (Nat.choose_le_choose _ hPM)
        _ ≤ ∑ m ∈ range (M+1), M.choose m * g m :=
            sum_le_sum_of_subset (range_subset_range.2 (by omega))
        _ = (M*(s+1)).choose n := vand M s n


lemma connected_gen [Fintype V] (H : SimpleGraph V) (S : Finset V) (v : V) (hv : v ∈ S)
    (hc : (H.induce (S : Set V)).Connected) : Gen H univ {v} S := by
  refine ⟨subset_univ _, by simpa using hv, ?_⟩
  intro u hu
  refine ⟨v, mem_singleton_self _, ?_⟩
  have hr : (H.induce (S : Set V)).Reachable ⟨v, hv⟩ ⟨u, hu⟩ := hc.preconnected _ _
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  have := Relation.ReflTransGen.lift (Subtype.val : ((S : Set V) : Type) → V)
    (r := fun a b => (H.induce (S : Set V)).Adj a b)
    (p := fun a b => H.Adj a b ∧ b ∈ S) (fun a b hab => ⟨by simpa using hab, b.2⟩) _ _ hr
  exact this

lemma choose_real_le (M t : ℕ) (ht : 1 ≤ t) :
    (((M*t).choose (t-1) : ℕ) : ℝ) ≤ Real.exp t * (M : ℝ)^(t-1) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k+1 := ⟨t-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 := Nat.choose_le_pow_div (α := ℝ) k (M*(k+1))
  have h2 := Real.pow_div_factorial_le_exp ((k+1 : ℕ) : ℝ) (by positivity) (k+1)
  have h3 : (((k+1 : ℕ) : ℝ))^(k+1) / ((k+1).factorial : ℝ)
      = ((k+1 : ℕ) : ℝ)^k / (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; field_simp; ring
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  calc (((M*(k+1)).choose k : ℕ) : ℝ) ≤ ((M*(k+1) : ℕ) : ℝ)^k / (k.factorial : ℝ) := h1
    _ = (M : ℝ)^k * (((k+1 : ℕ) : ℝ)^k / (k.factorial : ℝ)) := by
        push_cast; rw [mul_pow]; ring
    _ ≤ (M : ℝ)^k * Real.exp ((k+1 : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← h3]; exact h2
    _ = _ := by push_cast; ring

theorem count_le [Fintype V] (H : SimpleGraph V) (M : ℕ)
    (hM : ∀ u, (univ.filter (H.Adj u)).card ≤ M) (t : ℕ) (ht : 1 ≤ t) :
    (({S : Finset V | S.card = t ∧ (H.induce (S : Set V)).Connected}.ncard : ℕ) : ℝ)
      ≤ Real.exp t * (Fintype.card V : ℝ) * (M : ℝ)^(t-1) := by
  set Tf : Finset (Finset V) := univ.filter
    (fun S => S.card = t ∧ (H.induce (S : Set V)).Connected) with hTf
  have hset : {S : Finset V | S.card = t ∧ (H.induce (S : Set V)).Connected} = (Tf : Set (Finset V)) := by
    ext S; simp [hTf]
  rw [hset, Set.ncard_coe_finset]
  have hcov : Tf ⊆ univ.biUnion (fun v => (univ : Finset V).powerset.filter
      (fun S => S.card = t ∧ Gen H univ {v} S)) := by
    intro S hS
    simp only [hTf, mem_filter, mem_univ, true_and] at hS
    have hne : S.Nonempty := card_pos.1 (by omega)
    obtain ⟨v, hv⟩ := hne
    rw [mem_biUnion]
    exact ⟨v, mem_univ _, mem_filter.2 ⟨mem_powerset.2 (subset_univ _), hS.1,
      connected_gen H S v hv hS.2⟩⟩
  have hsum : Tf.card ≤ Fintype.card V * (M*t).choose (t-1) := by
    calc Tf.card ≤ _ := card_le_card hcov
      _ ≤ ∑ v : V, ((univ : Finset V).powerset.filter
            (fun S => S.card = t ∧ Gen H univ {v} S)).card := card_biUnion_le
      _ ≤ ∑ v : V, (M*t).choose (t-1) := by
          apply sum_le_sum
          intro v _
          have := gen_count H M hM t univ {v}
          simpa [card_singleton, ht] using this
      _ = _ := by simp
  calc (Tf.card : ℝ) ≤ ((Fintype.card V * (M*t).choose (t-1) : ℕ) : ℝ) := by exact_mod_cast hsum
    _ = (Fintype.card V : ℝ) * (((M*t).choose (t-1) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (Fintype.card V : ℝ) * (Real.exp t * (M : ℝ)^(t-1)) :=
        mul_le_mul_of_nonneg_left (choose_real_le M t ht) (by positivity)
    _ = _ := by ring


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

end RobustShattering.Dev.L42

namespace RobustShattering.Supermartingale

theorem chk_lemma_4_2 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ t x : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (ht : 1 ≤ t) :
    (({S : Finset V | S.card = t ∧ XConnected G x (S : Set V)}.ncard : ℕ) : ℝ)
        ≤ Real.exp t * (Fintype.card V : ℝ) * (Δ : ℝ) ^ (x * (t - 1)) ∧
      (({S : Finset V | S.card = t ∧ XConnected G x (S : Set V)}.ncard : ℕ) : ℝ)
        ≤ Real.exp t * (Fintype.card V : ℝ) *
          ((Finset.univ.sup fun v : V => (LocalLLL.Main.ball G v x \ {v}).ncard : ℕ) : ℝ)
            ^ (t - 1) := by
  classical
  set M0 : ℕ := Finset.univ.sup fun v : V => (LocalLLL.Main.ball G v x \ {v}).ncard with hM0
  have hdegH : ∀ u, (Finset.univ.filter ((LocalLLL.Main.graphPower G x).Adj u)).card ≤ M0 := by
    intro u
    have h1 : (Finset.univ.filter ((LocalLLL.Main.graphPower G x).Adj u)).card
        = (LocalLLL.Main.ball G u x \ {u}).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext w
      rw [Finset.mem_coe, Finset.mem_filter]
      show _ ∧ (_ ≠ _ ∧ _) ↔ (G.edist u w ≤ (x : ℕ∞)) ∧ ¬ w = u
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h2, fun h => h1 h.symm⟩
      · rintro ⟨h1, h2⟩; exact ⟨Finset.mem_univ _, fun h => h2 h.symm, h1⟩
    rw [h1]
    exact Finset.le_sup (f := fun v : V => (LocalLLL.Main.ball G v x \ {v}).ncard)
      (Finset.mem_univ u)
  have hmain := RobustShattering.Dev.L42.count_le (LocalLLL.Main.graphPower G x) M0 hdegH t ht
  have hM : M0 ≤ Δ ^ x := by
    refine Finset.sup_le ?_
    intro v _
    exact RobustShattering.Dev.L42.ball_card_le G Δ hΔ hdeg v x
  refine ⟨?_, hmain⟩
  refine le_trans hmain ?_
  have h1 : (M0 : ℝ) ^ (t - 1) ≤ (Δ : ℝ) ^ (x * (t - 1)) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast hM
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

end RobustShattering.Supermartingale
end

theorem solution : type_of% @RobustShattering.Supermartingale.chk_lemma_4_2 := @RobustShattering.Supermartingale.chk_lemma_4_2
