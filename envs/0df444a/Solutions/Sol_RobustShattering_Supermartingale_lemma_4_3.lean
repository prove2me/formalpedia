-- Prove2me | solution 1 for RobustShattering.Supermartingale.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:35:58.733565+00:00
-- url     : https://prove2.me/submissions/ba94f23c-52f6-4cf0-8fac-fda0a68a0d3a

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_XConnected
import Theorems.Thm_RobustShattering_Supermartingale_lemma_4_2

section
set_option autoImplicit false

open MeasureTheory

namespace RobustShattering.Dev.Key
open RobustShattering.Supermartingale
open scoped Classical

variable {V : Type}

/-- connectivity of the induced subgraph on a finset -/
def Conn (H : SimpleGraph V) (S : Finset V) : Prop := (H.induce (S : Set V)).Connected

lemma exists_erase [Finite V] (H : SimpleGraph V) (S : Finset V) (hS : Conn H S)
    (h2 : 2 ≤ S.card) : ∃ v ∈ S, Conn H (S.erase v) := by
  have : Nontrivial (S : Set V) := by
    rw [Set.nontrivial_coe_sort]
    exact Finset.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w, hw⟩ := hS.exists_connected_induce_compl_singleton_of_finite_nontrivial
  refine ⟨w.1, w.2, ?_⟩
  have hmem : ∀ a : ↥({w}ᶜ : Set (S : Set V)),
      a.1.1 ∈ ((S.erase w.1 : Finset V) : Set V) := by
    intro a
    have h1 : a.1 ≠ w := a.2
    simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
    exact ⟨a.1.2, fun h => h1 (Subtype.ext h)⟩
  let f : ((H.induce (S : Set V)).induce ({w}ᶜ : Set (S : Set V))) →g
      H.induce ((S.erase w.1 : Finset V) : Set V) :=
    { toFun := fun a => ⟨a.1.1, hmem a⟩
      map_rel' := fun {a b} hab => hab }
  refine SimpleGraph.Connected.map f ?_ hw
  rintro ⟨u, hu⟩
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hu
  exact ⟨⟨⟨u, hu.1⟩, fun h => hu.2 (by simpa using congrArg Subtype.val h)⟩, rfl⟩

lemma exists_sub [Finite V] (H : SimpleGraph V) (m : ℕ) (hm : 1 ≤ m) :
    ∀ (k : ℕ) (S : Finset V), S.card = m + k → Conn H S →
      ∃ T ⊆ S, T.card = m ∧ Conn H T := by
  intro k
  induction k with
  | zero => intro S hS hc; exact ⟨S, subset_rfl, by simpa using hS, hc⟩
  | succ k ih =>
    intro S hS hc
    obtain ⟨v, hv, hc'⟩ := exists_erase H S hc (by omega)
    obtain ⟨T, hT, hTc, hTconn⟩ := ih (S.erase v) (by rw [Finset.card_erase_of_mem hv]; omega) hc'
    exact ⟨T, hT.trans (Finset.erase_subset _ _), hTc, hTconn⟩


/-! ### Δ = 2: spheres have at most two vertices -/

section Two
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma edist_succ_of_adj {r w u : V} (h : G.Adj w u) :
    G.edist r u ≤ G.edist r w + 1 := by
  calc G.edist r u ≤ G.edist r w + G.edist w u := G.edist_triangle
    _ = G.edist r w + 1 := by rw [SimpleGraph.edist_eq_one_iff_adj.mpr h]

lemma pred_exists {r u : V} {k : ℕ} (h : G.edist r u = ((k + 1 : ℕ) : ℕ∞)) :
    ∃ w, G.Adj w u ∧ G.edist r w = (k : ℕ∞) := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe h
  have hr : p.reverse.length = k + 1 := by simpa using hp
  cases hq : p.reverse with
  | nil => rw [hq] at hr; simp at hr
  | cons hadj q =>
    rename_i w
    rw [hq] at hr
    simp only [SimpleGraph.Walk.length_cons] at hr
    have hqk : q.length = k := by omega
    have h1 : G.edist r w ≤ (k : ℕ∞) := by
      rw [G.edist_comm]
      have := q.edist_le
      rw [hqk] at this
      exact this
    have h2 := edist_succ_of_adj G (r := r) hadj.symm
    rw [h] at h2
    refine ⟨w, hadj.symm, le_antisymm h1 ?_⟩
    generalize G.edist r w = z at h1 h2
    induction z using ENat.recTopCoe with
    | top => simp at h1
    | coe z =>
      norm_cast at h1 h2 ⊢
      omega

lemma lvl_card (hdeg : ∀ v, G.degree v ≤ 2) (r : V) :
    ∀ l : ℕ, (Finset.univ.filter (fun v => G.edist r v = (l : ℕ∞))).card ≤ 2 := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    rcases l with _ | l
    · have : (Finset.univ.filter (fun v => G.edist r v = ((0 : ℕ) : ℕ∞))) ⊆ {r} := by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_zero,
          SimpleGraph.edist_eq_zero_iff] at hv
        simp [hv.symm]
      exact (Finset.card_le_card this).trans (by simp)
    · rcases l with _ | l
      · have : (Finset.univ.filter (fun v => G.edist r v = ((0 + 1 : ℕ) : ℕ∞))) ⊆
            G.neighborFinset r := by
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, zero_add, Nat.cast_one,
            SimpleGraph.edist_eq_one_iff_adj] at hv
          simpa using hv
        exact (Finset.card_le_card this).trans (hdeg r)
      · -- sphere l+2 injects into sphere l+1
        have hex : ∀ u ∈ Finset.univ.filter (fun v => G.edist r v = ((l + 1 + 1 : ℕ) : ℕ∞)),
            ∃ w, G.Adj w u ∧ G.edist r w = ((l + 1 : ℕ) : ℕ∞) := by
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          exact pred_exists G hu
        choose! f hf using hex
        have hinj : Set.InjOn f ↑(Finset.univ.filter
            (fun v => G.edist r v = ((l + 1 + 1 : ℕ) : ℕ∞))) := by
          intro u hu u' hu' hfe
          by_contra hne
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hu hu'
          have hw := (hf u (by simpa using hu)).2
          obtain ⟨q, hq1, hq2⟩ := pred_exists G (r := r) (u := f u) (k := l) hw
          have hqu : q ≠ u := by
            rintro rfl
            rw [hu] at hq2
            have : (l + 1 + 1 : ℕ) = l := by exact_mod_cast hq2
            omega
          have hqu' : q ≠ u' := by
            rintro rfl
            rw [hu'] at hq2
            have : (l + 1 + 1 : ℕ) = l := by exact_mod_cast hq2
            omega
          have hsub : ({q, u, u'} : Finset V) ⊆ G.neighborFinset (f u) := by
            intro a ha
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl | rfl
            · simpa using hq1.symm
            · simpa using (hf a (by simpa using hu)).1
            · rw [hfe]; simpa using (hf a (by simpa using hu')).1
          have := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem (by simp [hqu, hqu']),
            Finset.card_pair hne] at this
          have := hdeg (f u)
          simp at *
          omega
        have hmaps : ∀ u ∈ Finset.univ.filter
            (fun v => G.edist r v = ((l + 1 + 1 : ℕ) : ℕ∞)),
            f u ∈ Finset.univ.filter (fun v => G.edist r v = ((l + 1 : ℕ) : ℕ∞)) := by
          intro u hu
          simpa using (hf u hu).2
        exact (Finset.card_le_card_of_injOn f hmaps hinj).trans (ih (l + 1) (by omega))



noncomputable def dd (r v : V) : ℕ := (G.edist r v).toNat

lemma coe_dd {r v : V} (h : G.edist r v ≠ ⊤) : ((dd G r v : ℕ) : ℕ∞) = G.edist r v :=
  ENat.natCast_toNat h

/-- the invariant of a "chain above level `k`" -/
def Inv (x : ℕ) (r : V) (k : ℕ) (U : Finset V) : Prop :=
  (∀ u ∈ U, (k : ℕ∞) ≤ G.edist r u ∧ G.edist r u ≠ ⊤) ∧
  (U.Nonempty → ∃ u ∈ U, G.edist r u ≤ ((k + x : ℕ) : ℕ∞)) ∧
  (∀ t : ℕ, k ≤ t → (∃ u ∈ U, (t : ℕ∞) < G.edist r u) →
     ∃ u ∈ U, (t : ℕ∞) < G.edist r u ∧ G.edist r u ≤ ((t + x : ℕ) : ℕ∞))

noncomputable def ring (x : ℕ) (r : V) (k : ℕ) : Finset V :=
  Finset.univ.filter (fun v => G.edist r v ≠ ⊤ ∧ k ≤ dd G r v ∧ dd G r v ≤ k + x)

lemma ring_card (hdeg : ∀ v, G.degree v ≤ 2) (x : ℕ) (r : V) (k : ℕ) :
    (ring G x r k).card ≤ 2 * x + 2 := by
  have hsub : ring G x r k ⊆ (Finset.range (x + 1)).biUnion
      (fun i => Finset.univ.filter (fun v => G.edist r v = ((k + i : ℕ) : ℕ∞))) := by
    intro v hv
    simp only [ring, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ,
      true_and]
    refine ⟨dd G r v - k, by omega, ?_⟩
    rw [← coe_dd G hv.1]
    congr 1
    omega
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc _ ≤ ∑ i ∈ Finset.range (x + 1), 2 :=
        Finset.sum_le_sum (fun i _ => lvl_card G hdeg r (k + i))
    _ = 2 * x + 2 := by simp; ring

lemma fam_card (hdeg : ∀ v, G.degree v ≤ 2) (x : ℕ) (r : V) :
    ∀ (j k : ℕ), (Finset.univ.filter (fun U : Finset V => U.card = j ∧ Inv G x r k U)).card
      ≤ (2 * x + 2) ^ j := by
  intro j
  induction j with
  | zero =>
    intro k
    have : (Finset.univ.filter (fun U : Finset V => U.card = 0 ∧ Inv G x r k U)) ⊆ {∅} := by
      intro U hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_eq_zero] at hU
      simp [hU.1]
    simpa using (Finset.card_le_card this).trans (by simp)
  | succ j ih =>
    intro k
    have hsub : (Finset.univ.filter (fun U : Finset V => U.card = j + 1 ∧ Inv G x r k U)) ⊆
        (ring G x r k).biUnion (fun u =>
          (Finset.univ.filter (fun U : Finset V => U.card = j ∧ Inv G x r (dd G r u) U)).image
            (insert u)) := by
      intro U hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
      obtain ⟨hcard, h1, h2, h3⟩ := hU
      have hne : U.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨u1, hu1, hu1le⟩ := h2 hne
      obtain ⟨u0, hu0, hmin⟩ := Finset.exists_min_image U (dd G r) hne
      have hfin0 := (h1 u0 hu0).2
      have hfin1 := (h1 u1 hu1).2
      have hu1d : dd G r u1 ≤ k + x := by
        have := coe_dd G hfin1
        rw [← this] at hu1le
        exact_mod_cast hu1le
      have hk0 : k ≤ dd G r u0 := by
        have := (h1 u0 hu0).1
        rw [← coe_dd G hfin0] at this
        exact_mod_cast this
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and]
      refine ⟨u0, ?_, U.erase u0, ⟨?_, ?_⟩, Finset.insert_erase hu0⟩
      · simp only [ring, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hfin0, hk0, (hmin u1 hu1).trans hu1d⟩
      · rw [Finset.card_erase_of_mem hu0]; omega
      · have e0 := coe_dd G hfin0
        have hge : ∀ u ∈ U.erase u0, G.edist r u0 ≤ G.edist r u := by
          intro u hu
          have hu' := Finset.mem_of_mem_erase hu
          rw [← e0, ← coe_dd G (h1 u hu').2]
          exact_mod_cast hmin u hu'
        refine ⟨?_, ?_, ?_⟩
        · intro u hu
          exact ⟨by rw [← e0] at hge; simpa [e0] using hge u hu, (h1 u (Finset.mem_of_mem_erase hu)).2⟩
        · intro hne'
          obtain ⟨w, hw⟩ := hne'
          by_cases hcase : ∃ u ∈ U.erase u0, G.edist r u ≤ G.edist r u0
          · obtain ⟨u, hu, hle⟩ := hcase
            refine ⟨u, hu, ?_⟩
            rw [← e0] at hle
            exact hle.trans (by exact_mod_cast Nat.le_add_right _ _)
          · push Not at hcase
            obtain ⟨u, hu, hlt, hle⟩ := h3 (dd G r u0) hk0
              ⟨w, Finset.mem_of_mem_erase hw, by rw [e0]; exact hcase w hw⟩
            rw [e0] at hlt
            refine ⟨u, Finset.mem_erase.mpr ⟨?_, hu⟩, hle⟩
            rintro rfl
            exact lt_irrefl _ hlt
        · intro t ht ⟨w, hw, hwt⟩
          have ht' : k ≤ t := hk0.trans ht
          obtain ⟨u, hu, hlt, hle⟩ := h3 t ht' ⟨w, Finset.mem_of_mem_erase hw, hwt⟩
          refine ⟨u, Finset.mem_erase.mpr ⟨?_, hu⟩, hlt, hle⟩
          rintro rfl
          have : G.edist r u ≤ (t : ℕ∞) := by
            rw [← e0]; exact_mod_cast ht
          exact absurd hlt (not_lt.mpr this)
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ u ∈ ring G x r k, ((Finset.univ.filter
            (fun U : Finset V => U.card = j ∧ Inv G x r (dd G r u) U)).image (insert u)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ u ∈ ring G x r k, (2 * x + 2) ^ j :=
          Finset.sum_le_sum (fun u _ => Finset.card_image_le.trans (ih _))
      _ = (ring G x r k).card * (2 * x + 2) ^ j := by simp
      _ ≤ (2 * x + 2) * (2 * x + 2) ^ j :=
          Nat.mul_le_mul_right _ (ring_card G hdeg x r k)
      _ = (2 * x + 2) ^ (j + 1) := by ring



lemma cross {W : Type} (H : SimpleGraph W) (hc : H.Connected) (A : Set W) {a b : W}
    (ha : a ∈ A) (hb : b ∉ A) : ∃ a' ∈ A, ∃ b', b' ∉ A ∧ H.Adj a' b' := by
  obtain ⟨p⟩ := hc a b
  obtain ⟨d, -, h1, h2⟩ := p.exists_boundary_dart A ha hb
  exact ⟨d.fst, h1, d.snd, h2, d.adj⟩

lemma conn_finite (x : ℕ) (r : V) (S : Finset V) (hS : Conn (LocalLLL.Main.graphPower G x) S)
    (hr : r ∈ S) : ∀ u ∈ S, G.edist r u ≠ ⊤ := by
  intro u hu
  by_contra hcon
  have key := cross _ hS (A := {a : (S : Set V) | G.edist r a.1 ≠ ⊤})
    (a := ⟨r, hr⟩) (b := ⟨u, hu⟩) (by simp) (by simpa using hcon)
  obtain ⟨a', ha', b', hb', hadj⟩ := key
  have hadj' : (LocalLLL.Main.graphPower G x).Adj a'.1 b'.1 := hadj
  have h1 : G.edist r b'.1 ≤ G.edist r a'.1 + G.edist a'.1 b'.1 := G.edist_triangle
  have h2 : G.edist r a'.1 + G.edist a'.1 b'.1 ≠ ⊤ :=
    WithTop.add_ne_top.2 ⟨ha', ne_top_of_le_ne_top (ENat.coe_ne_top x) hadj'.2⟩
  exact hb' (ne_top_of_le_ne_top h2 h1)

lemma conn_chain (x : ℕ) (r : V) (S : Finset V) (hS : Conn (LocalLLL.Main.graphPower G x) S)
    (hr : r ∈ S) (t : ℕ) (h : ∃ u ∈ S, (t : ℕ∞) < G.edist r u) :
    ∃ u ∈ S, (t : ℕ∞) < G.edist r u ∧ G.edist r u ≤ ((t + x : ℕ) : ℕ∞) := by
  obtain ⟨u, hu, hut⟩ := h
  have key := cross _ hS (A := {a : (S : Set V) | G.edist r a.1 ≤ (t : ℕ∞)})
    (a := ⟨r, hr⟩) (b := ⟨u, hu⟩) (by simp) (by simpa using hut)
  obtain ⟨a', ha', b', hb', hadj⟩ := key
  have hadj' : (LocalLLL.Main.graphPower G x).Adj a'.1 b'.1 := hadj
  have h1 : G.edist r b'.1 ≤ G.edist r a'.1 + G.edist a'.1 b'.1 := G.edist_triangle
  refine ⟨b'.1, b'.2, by simpa using hb', ?_⟩
  refine h1.trans ?_
  push_cast
  exact add_le_add (by simpa using ha') hadj'.2

lemma two_count (hdeg : ∀ v, G.degree v ≤ 2) (x m : ℕ) (hm : 1 ≤ m) :
    {S : Finset V | S.card = m ∧ XConnected G x (S : Set V)}.ncard ≤
      Fintype.card V * (2 * x + 2) ^ (m - 1) := by
  have hset : {S : Finset V | S.card = m ∧ XConnected G x (S : Set V)} =
      ↑(Finset.univ.filter (fun S : Finset V => S.card = m ∧ XConnected G x (S : Set V))) := by
    ext S; simp
  rw [hset, Set.ncard_coe_finset]
  have hsub : (Finset.univ.filter (fun S : Finset V => S.card = m ∧ XConnected G x (S : Set V)))
      ⊆ Finset.univ.biUnion (fun r =>
        (Finset.univ.filter (fun U : Finset V => U.card = m - 1 ∧ Inv G x r 0 U)).image
          (insert r)) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨hcard, hconn⟩ := hS
    have hSc : Conn (LocalLLL.Main.graphPower G x) S := hconn
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨r, hr⟩ := hne
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_filter]
    refine ⟨r, S.erase r, ⟨?_, ?_⟩, Finset.insert_erase hr⟩
    · rw [Finset.card_erase_of_mem hr]; omega
    · have hfin := conn_finite G x r S hSc hr
      have hch := conn_chain G x r S hSc hr
      have hup : ∀ t : ℕ, (∃ u ∈ S.erase r, (t : ℕ∞) < G.edist r u) →
          ∃ u ∈ S.erase r, (t : ℕ∞) < G.edist r u ∧ G.edist r u ≤ ((t + x : ℕ) : ℕ∞) := by
        intro t ⟨u, hu, hut⟩
        obtain ⟨u', hu', h1, h2⟩ := hch t ⟨u, Finset.mem_of_mem_erase hu, hut⟩
        refine ⟨u', Finset.mem_erase.mpr ⟨?_, hu'⟩, h1, h2⟩
        rintro rfl
        simp at h1
      refine ⟨fun u hu => ⟨by simp, hfin u (Finset.mem_of_mem_erase hu)⟩, ?_, fun t _ h => hup t h⟩
      intro ⟨u, hu⟩
      have hpos : ((0 : ℕ) : ℕ∞) < G.edist r u :=
        SimpleGraph.edist_pos_of_ne (Finset.ne_of_mem_erase hu).symm
      obtain ⟨u', hu', -, h2⟩ := hup 0 ⟨u, hu, hpos⟩
      exact ⟨u', hu', by simpa using h2⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc _ ≤ ∑ r : V, (2 * x + 2) ^ (m - 1) :=
        Finset.sum_le_sum (fun r _ => Finset.card_image_le.trans (fam_card G hdeg x r (m - 1) 0))
    _ = _ := by simp

end Two


section Main
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma n_le_pow (Δ : ℕ) (hΔ : 2 ≤ Δ) (m : ℕ)
    (hm : Real.logb Δ (Fintype.card V) ≤ (m : ℝ)) : Fintype.card V ≤ Δ ^ m := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
  · simp [h]
  · have hΔ' : (1 : ℝ) < Δ := by exact_mod_cast hΔ
    have := (Real.logb_le_iff_le_rpow hΔ' (by exact_mod_cast h)).1 hm
    rw [Real.rpow_natCast] at this
    exact_mod_cast this

theorem key_aux (Δ : ℕ) (hΔ : 2 ≤ Δ) (c₂ x : ℕ) (c₃ : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → Set V) (m : ℕ) (hm1 : 1 ≤ m)
    (hcount : {S : Finset V | S.card = m ∧ XConnected G x (S : Set V)}.ncard ≤ Δ ^ ((x + 2) * m))
    (h : ∀ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) → S.card = m →
          P {ω | (S : Set V) ⊆ B ω} ≤
            ENNReal.ofReal ((Δ : ℝ) ^ (-(((x : ℝ) + c₃ + 2) * (S.card : ℝ))))) :
    P {ω | ∃ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) ∧
        XConnected G x (S : Set V) ∧ (S : Set V) ⊆ B ω ∧ m ≤ S.card} ≤
      ENNReal.ofReal ((Δ : ℝ) ^ (-(c₃ * (m : ℝ)))) := by
  set 𝒯 : Finset (Finset V) := Finset.univ.filter (fun T : Finset V =>
    T.card = m ∧ LocalLLL.Main.separated G c₂ (T : Set V) ∧ XConnected G x (T : Set V)) with h𝒯
  have hsub : {ω | ∃ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) ∧
        XConnected G x (S : Set V) ∧ (S : Set V) ⊆ B ω ∧ m ≤ S.card} ⊆
      ⋃ T ∈ 𝒯, {ω | (T : Set V) ⊆ B ω} := by
    rintro ω ⟨S, hsep, hconn, hSB, hmS⟩
    have hSc : Conn (LocalLLL.Main.graphPower G x) S := hconn
    obtain ⟨T, hTS, hTc, hTconn⟩ := exists_sub (LocalLLL.Main.graphPower G x) m hm1
      (S.card - m) S (by omega) hSc
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨T, ?_, (Finset.coe_subset.mpr hTS).trans hSB⟩
    simp only [h𝒯, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hTc, fun u hu v hv hne => hsep u (hTS hu) v (hTS hv) hne, hTconn⟩
  have hD : (0 : ℝ) < Δ := by have : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
                              linarith
  set a : ℝ := (Δ : ℝ) ^ (-(((x : ℝ) + c₃ + 2) * (m : ℝ))) with ha
  have hterm : ∀ T ∈ 𝒯, P {ω | (T : Set V) ⊆ B ω} ≤ ENNReal.ofReal a := by
    intro T hT
    simp only [h𝒯, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    have := h T hT.2.1 hT.1
    rwa [hT.1] at this
  have hcard : 𝒯.card ≤ Δ ^ ((x + 2) * m) := by
    refine le_trans ?_ hcount
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro T hT
    simp only [h𝒯, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hT
    exact ⟨hT.1, hT.2.2⟩
  calc P {ω | ∃ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) ∧
        XConnected G x (S : Set V) ∧ (S : Set V) ⊆ B ω ∧ m ≤ S.card}
      ≤ P (⋃ T ∈ 𝒯, {ω | (T : Set V) ⊆ B ω}) := measure_mono hsub
    _ ≤ ∑ T ∈ 𝒯, P {ω | (T : Set V) ⊆ B ω} := measure_biUnion_finset_le _ _
    _ ≤ 𝒯.card • ENNReal.ofReal a := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ENNReal.ofReal ((𝒯.card : ℝ) * a) := by
        rw [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        set N : ℕ := (x + 2) * m with hN
        have hDN : (0 : ℝ) < (Δ : ℝ) ^ N := pow_pos hD N
        have hy : 0 < (Δ : ℝ) ^ (-(c₃ * (m : ℝ))) := Real.rpow_pos_of_pos hD _
        have hexp : -(((x : ℝ) + c₃ + 2) * (m : ℝ)) = -((N : ℝ)) + -(c₃ * (m : ℝ)) := by
          rw [hN]; push_cast; ring
        have ha' : a = ((Δ : ℝ) ^ N)⁻¹ * (Δ : ℝ) ^ (-(c₃ * (m : ℝ))) := by
          rw [ha, hexp, Real.rpow_add hD, Real.rpow_neg hD.le, Real.rpow_natCast]
        rw [ha', ← mul_assoc]
        have hc : (𝒯.card : ℝ) * ((Δ : ℝ) ^ N)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hDN]
          exact_mod_cast hcard
        nlinarith

lemma two_pow_bound (x m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : n ≤ 2 ^ m) :
    n * (2 * x + 2) ^ (m - 1) ≤ 2 ^ ((x + 2) * m) := by
  have h1 : 2 * x + 2 ≤ 2 ^ (x + 1) := by
    have := Nat.lt_two_pow_self (n := x)
    rw [pow_succ]; omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  calc n * (2 * x + 2) ^ m' ≤ 2 ^ (m' + 1) * (2 ^ (x + 1)) ^ m' :=
        Nat.mul_le_mul hn (Nat.pow_le_pow_left h1 m')
    _ = 2 ^ (m' + 1 + (x + 1) * m') := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((x + 2) * (m' + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem key (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (c₂ x : ℕ) (c₃ : ℝ)
    (hc₃ : 0 ≤ c₃) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Set V) (m : ℕ) (hm : Real.logb Δ (Fintype.card V) ≤ (m : ℝ))
    (h : ∀ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) → S.card = m →
          P {ω | (S : Set V) ⊆ B ω} ≤
            ENNReal.ofReal ((Δ : ℝ) ^ (-(((x : ℝ) + c₃ + 2) * (S.card : ℝ))))) :
    P {ω | ∃ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) ∧
        XConnected G x (S : Set V) ∧ (S : Set V) ⊆ B ω ∧ m ≤ S.card} ≤
      ENNReal.ofReal ((Δ : ℝ) ^ (-(c₃ * (m : ℝ)))) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, ENNReal.ofReal_one]
    exact prob_le_one
  refine key_aux G Δ hΔ c₂ x c₃ P B m hm1 ?_ h
  have hn := n_le_pow Δ hΔ m hm
  rcases Nat.lt_or_ge Δ 3 with h3 | h3
  · have hΔ2 : Δ = 2 := by omega
    subst hΔ2
    exact (two_count G hdeg x m hm1).trans (two_pow_bound x m hm1 _ hn)
  · have hD : (3 : ℝ) ≤ Δ := by exact_mod_cast h3
    have hn' : (Fintype.card V : ℝ) ≤ (Δ : ℝ) ^ m := by exact_mod_cast hn
    have h42 := (lemma_4_2 G Δ m x hΔ hdeg hm1).1
    have hexp : Real.exp (m : ℝ) ≤ (Δ : ℝ) ^ m := by
      have : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
        rw [← Real.exp_nat_mul, mul_one]
      rw [this]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le
        (by linarith [Real.exp_one_lt_d9]) m
    have h1D : (1 : ℝ) ≤ Δ := by linarith
    have : ((({S : Finset V | S.card = m ∧ XConnected G x (S : Set V)}.ncard : ℕ)) : ℝ) ≤
        (Δ : ℝ) ^ ((x + 2) * m) := by
      refine h42.trans ?_
      calc Real.exp (m : ℝ) * (Fintype.card V : ℝ) * (Δ : ℝ) ^ (x * (m - 1))
          ≤ (Δ : ℝ) ^ m * (Δ : ℝ) ^ m * (Δ : ℝ) ^ (x * m) := by
            gcongr
            · exact Nat.sub_le _ _
        _ = (Δ : ℝ) ^ ((x + 2) * m) := by
            rw [← pow_add, ← pow_add]; congr 1; ring
    exact_mod_cast this

end Main

end RobustShattering.Dev.Key
end

section
set_option autoImplicit false

open MeasureTheory

namespace RobustShattering.Supermartingale

/-- Lemma 4.3 (Shattering Lemma). -/
theorem chk_lemma_4_3 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (c₂ x : ℕ) (c₃ : ℝ) (hc₃ : 0 ≤ c₃)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Set V) :
    ((∀ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) →
        S.card = ⌈Real.logb Δ (Fintype.card V)⌉₊ →
          P {ω | (S : Set V) ⊆ B ω} ≤
            ENNReal.ofReal ((Δ : ℝ) ^ (-(((x : ℝ) + c₃ + 2) * (S.card : ℝ))))) →
      P {ω | ∃ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) ∧
          XConnected G x (S : Set V) ∧ (S : Set V) ⊆ B ω ∧
          ⌈Real.logb Δ (Fintype.card V)⌉₊ < S.card} ≤
        ENNReal.ofReal ((Fintype.card V : ℝ) ^ (-c₃))) ∧
    (∀ t : ℕ, Real.logb Δ (Fintype.card V) ≤ (t : ℝ) →
      (∀ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) → S.card = t →
          P {ω | (S : Set V) ⊆ B ω} ≤
            ENNReal.ofReal ((Δ : ℝ) ^ (-(((x : ℝ) + c₃ + 2) * (S.card : ℝ))))) →
        P {ω | ∃ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) ∧
            XConnected G x (S : Set V) ∧ (S : Set V) ⊆ B ω ∧ t < S.card} ≤
          ENNReal.ofReal ((Δ : ℝ) ^ (-(c₃ * (t : ℝ))))) := by
  have part2 : ∀ t : ℕ, Real.logb Δ (Fintype.card V) ≤ (t : ℝ) →
      (∀ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) → S.card = t →
          P {ω | (S : Set V) ⊆ B ω} ≤
            ENNReal.ofReal ((Δ : ℝ) ^ (-(((x : ℝ) + c₃ + 2) * (S.card : ℝ))))) →
        P {ω | ∃ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) ∧
            XConnected G x (S : Set V) ∧ (S : Set V) ⊆ B ω ∧ t < S.card} ≤
          ENNReal.ofReal ((Δ : ℝ) ^ (-(c₃ * (t : ℝ)))) := by
    intro t ht h
    refine le_trans (measure_mono ?_)
      (RobustShattering.Dev.Key.key G Δ hΔ hdeg c₂ x c₃ hc₃ P B t ht h)
    rintro ω ⟨S, h1, h2, h3, h4⟩
    exact ⟨S, h1, h2, h3, h4.le⟩
  refine ⟨fun h => ?_, part2⟩
  set m := ⌈Real.logb Δ (Fintype.card V)⌉₊ with hm
  have h2 := part2 m (Nat.le_ceil _) h
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · -- no vertices: an x-connected set is nonempty, so the event is empty
    have hempty : {ω | ∃ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) ∧
          XConnected G x (S : Set V) ∧ (S : Set V) ⊆ B ω ∧ m < S.card} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨S, -, hconn, -, -⟩
      have hne : Nonempty (S : Set V) := hconn.nonempty
      obtain ⟨⟨v, -⟩⟩ := hne
      have := Fintype.card_pos_iff.mpr ⟨v⟩
      omega
    rw [hempty, measure_empty]
    exact zero_le
  refine h2.trans ?_
  · have hD : (1 : ℝ) < Δ := by exact_mod_cast hΔ
    have hD0 : (0 : ℝ) < Δ := by linarith
    have hn : (Fintype.card V : ℝ) ≤ (Δ : ℝ) ^ m := by
      have := RobustShattering.Dev.Key.n_le_pow Δ hΔ m (Nat.le_ceil _)
      exact_mod_cast this
    have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast hpos
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg hD0.le, Real.rpow_neg hnpos.le]
    apply inv_anti₀ (Real.rpow_pos_of_pos hnpos _)
    calc (Fintype.card V : ℝ) ^ c₃ ≤ ((Δ : ℝ) ^ m) ^ c₃ :=
          Real.rpow_le_rpow hnpos.le hn hc₃
      _ = (Δ : ℝ) ^ (c₃ * (m : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le, mul_comm]

end RobustShattering.Supermartingale
end

theorem solution : type_of% @RobustShattering.Supermartingale.chk_lemma_4_3 := @RobustShattering.Supermartingale.chk_lemma_4_3
