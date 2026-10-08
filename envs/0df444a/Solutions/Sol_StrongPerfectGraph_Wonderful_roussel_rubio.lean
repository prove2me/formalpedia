-- Prove2me | solution 1 for StrongPerfectGraph.Wonderful.roussel_rubio
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T15:53:00.311319+00:00
-- url     : https://prove2.me/submissions/63768380-706e-4e4f-ae31-1ad65dffec8e

/-
The Wonderful Lemma of Roussel and Rubio (Theorem 1.2 of Chudnovsky, "A short proof of the
Wonderful Lemma"; Theorem 2.1 of Chudnovsky-Robertson-Seymour-Thomas, "The strong perfect graph
theorem"), formalized with the platform's `IsBerge` and list-based `IsInducedPath`.

The proof follows Chudnovsky's short proof: strong induction on `|X|` and, inside it, on the
length of the path. See docs/spgt/wonderful-lemma-notes.md in the repository for the design.
-/
import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace Wonderful

variable {V : Type*}

/-! ## Induced paths and holes given by index functions -/

/-- `p 0, …, p k` is an induced path of `H`. -/
structure IP (H : SimpleGraph V) (p : ℕ → V) (k : ℕ) : Prop where
  inj : ∀ i j, i ≤ k → j ≤ k → p i = p j → i = j
  adj : ∀ i j, i ≤ k → j ≤ k → (H.Adj (p i) (p j) ↔ (i + 1 = j ∨ j + 1 = i))

/-- `c 0, …, c (m-1)` is a hole of `H` (cyclically indexed). -/
structure IHole (H : SimpleGraph V) (c : ℕ → V) (m : ℕ) : Prop where
  four : 4 ≤ m
  inj : ∀ i j, i < m → j < m → c i = c j → i = j
  adj : ∀ i j, i < m → j < m →
    (H.Adj (c i) (c j) ↔ (i + 1 = j ∨ j + 1 = i ∨ (i = 0 ∧ j + 1 = m) ∨ (j = 0 ∧ i + 1 = m)))

/-- No hole of `H` has odd length. -/
def NoOdd (H : SimpleGraph V) : Prop :=
  ∀ L : List V, StrongPerfectGraph.Main.IsHole H L → Even L.length

theorem succ_mod_eq' {n x : ℕ} (hx : x < n) :
    (x + 1) % n = if x + 1 = n then 0 else x + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem IHole.even {H : SimpleGraph V} (hB : NoOdd H) {c : ℕ → V} {m : ℕ} (h : IHole H c m) :
    Even m := by
  have key : StrongPerfectGraph.Main.IsHole H ((List.range m).map c) := by
    unfold StrongPerfectGraph.Main.IsHole
    refine ⟨by simpa using h.four, ?_, ?_⟩
    · refine List.Nodup.map_on ?_ (List.nodup_range)
      intro x hx y hy hxy
      exact h.inj x y (List.mem_range.mp hx) (List.mem_range.mp hy) hxy
    · intro i j
      have hi := i.2
      have hj := j.2
      simp only [List.length_map, List.length_range] at hi hj
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, List.length_map,
        List.length_range]
      rw [h.adj i j hi hj, succ_mod_eq' hi, succ_mod_eq' hj]
      split_ifs <;> omega
  have := hB _ key
  simpa using this

/-! ## Gluing induced paths -/

/-- Concatenation of two index functions with a junction after `k`. -/
def app (p : ℕ → V) (k : ℕ) (q : ℕ → V) : ℕ → V := fun t => if t ≤ k then p t else q (t - k - 1)

theorem app_le {p q : ℕ → V} {k t : ℕ} (h : t ≤ k) : app p k q t = p t := by
  simp [app, h]

theorem app_gt {p q : ℕ → V} {k t : ℕ} (h : k < t) : app p k q t = q (t - k - 1) := by
  simp [app, Nat.not_le.mpr h]

theorem IP.single (H : SimpleGraph V) (z : V) : IP H (fun _ => z) 0 :=
  ⟨fun i j hi hj _ => by omega, fun i j hi hj => by
    have : i = 0 := by omega
    have : j = 0 := by omega
    subst_vars
    simp⟩

theorem IP.sub {H : SimpleGraph V} {p : ℕ → V} {k : ℕ} (h : IP H p k) (i j : ℕ) (hij : i ≤ j)
    (hj : j ≤ k) : IP H (fun t => p (i + t)) (j - i) :=
  ⟨fun a b ha hb hab => by
    have := h.inj (i + a) (i + b) (by omega) (by omega) hab
    omega,
   fun a b ha hb => by
    rw [h.adj (i + a) (i + b) (by omega) (by omega)]
    omega⟩

theorem IP.rev {H : SimpleGraph V} {p : ℕ → V} {k : ℕ} (h : IP H p k) :
    IP H (fun t => p (k - t)) k :=
  ⟨fun a b ha hb hab => by
    have := h.inj (k - a) (k - b) (by omega) (by omega) hab
    omega,
   fun a b ha hb => by
    rw [h.adj (k - a) (k - b) (by omega) (by omega)]
    omega⟩

theorem IP.append {H : SimpleGraph V} {p q : ℕ → V} {k l : ℕ} (h1 : IP H p k) (h2 : IP H q l)
    (hd : ∀ i j, i ≤ k → j ≤ l → p i ≠ q j)
    (hc : ∀ i j, i ≤ k → j ≤ l → (H.Adj (p i) (q j) ↔ (i = k ∧ j = 0))) :
    IP H (app p k q) (k + l + 1) := by
  refine ⟨fun a b ha hb hab => ?_, fun a b ha hb => ?_⟩
  · by_cases h1a : a ≤ k <;> by_cases h1b : b ≤ k
    · rw [app_le h1a, app_le h1b] at hab
      exact h1.inj a b h1a h1b hab
    · rw [app_le h1a, app_gt (by omega)] at hab
      exact absurd hab (hd a (b - k - 1) h1a (by omega))
    · rw [app_gt (by omega), app_le h1b] at hab
      exact absurd hab.symm (hd b (a - k - 1) h1b (by omega))
    · rw [app_gt (by omega), app_gt (by omega)] at hab
      have := h2.inj (a - k - 1) (b - k - 1) (by omega) (by omega) hab
      omega
  · by_cases h1a : a ≤ k <;> by_cases h1b : b ≤ k
    · rw [app_le h1a, app_le h1b, h1.adj a b h1a h1b]
    · rw [app_le h1a, app_gt (by omega), hc a (b - k - 1) h1a (by omega)]
      omega
    · rw [app_gt (by omega), app_le h1b, H.adj_comm, hc b (a - k - 1) h1b (by omega)]
      omega
    · rw [app_gt (by omega), app_gt (by omega), h2.adj (a - k - 1) (b - k - 1) (by omega) (by omega)]
      omega

/-- Two induced paths closed up by two edges form a hole. -/
theorem hole_of_append {H : SimpleGraph V} {p q : ℕ → V} {k l : ℕ} (h1 : IP H p k) (h2 : IP H q l)
    (hd : ∀ i j, i ≤ k → j ≤ l → p i ≠ q j)
    (hc : ∀ i j, i ≤ k → j ≤ l → (H.Adj (p i) (q j) ↔ ((i = k ∧ j = 0) ∨ (i = 0 ∧ j = l))))
    (h4 : 4 ≤ k + l + 2) : IHole H (app p k q) (k + l + 2) := by
  refine ⟨h4, fun a b ha hb hab => ?_, fun a b ha hb => ?_⟩
  · by_cases h1a : a ≤ k <;> by_cases h1b : b ≤ k
    · rw [app_le h1a, app_le h1b] at hab
      exact h1.inj a b h1a h1b hab
    · rw [app_le h1a, app_gt (by omega)] at hab
      exact absurd hab (hd a (b - k - 1) h1a (by omega))
    · rw [app_gt (by omega), app_le h1b] at hab
      exact absurd hab.symm (hd b (a - k - 1) h1b (by omega))
    · rw [app_gt (by omega), app_gt (by omega)] at hab
      have := h2.inj (a - k - 1) (b - k - 1) (by omega) (by omega) hab
      omega
  · by_cases h1a : a ≤ k <;> by_cases h1b : b ≤ k
    · rw [app_le h1a, app_le h1b, h1.adj a b h1a h1b]
      omega
    · rw [app_le h1a, app_gt (by omega), hc a (b - k - 1) h1a (by omega)]
      omega
    · rw [app_gt (by omega), app_le h1b, H.adj_comm, hc b (a - k - 1) h1b (by omega)]
      omega
    · rw [app_gt (by omega), app_gt (by omega), h2.adj (a - k - 1) (b - k - 1) (by omega) (by omega)]
      omega

/-- A vertex adjacent exactly to the two ends of an induced path of length `≥ 2` closes it to a
hole, so the path has even length when no hole is odd. -/
theorem apex_even {H : SimpleGraph V} (hB : NoOdd H) {q : ℕ → V} {ℓ : ℕ} (h : IP H q ℓ)
    (hℓ : 2 ≤ ℓ) (z : V) (hz : ∀ t, t ≤ ℓ → z ≠ q t) (h0 : H.Adj z (q 0))
    (hl : H.Adj z (q ℓ)) (hm : ∀ t, 0 < t → t < ℓ → ¬ H.Adj z (q t)) : Even ℓ := by
  have hz' : ∀ i j, i ≤ ℓ → j ≤ 0 → q i ≠ (fun _ : ℕ => z) j := fun i j hi hj hh =>
    hz i hi hh.symm
  have hc : ∀ i j, i ≤ ℓ → j ≤ 0 → (H.Adj (q i) ((fun _ : ℕ => z) j) ↔
      ((i = ℓ ∧ j = 0) ∨ (i = 0 ∧ j = 0))) := by
    intro i j hi hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only
    rw [H.adj_comm]
    constructor
    · intro hadj
      by_cases hi0 : i = 0
      · exact Or.inr ⟨hi0, trivial⟩
      · by_cases hil : i = ℓ
        · exact Or.inl ⟨hil, trivial⟩
        · exact absurd hadj (hm i (by omega) (by omega))
    · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
      · exact hl
      · exact h0
  have := (hole_of_append h (IP.single H z) hz' hc (by omega)).even hB
  have h2 : Even (ℓ + 0 + 2) := this
  simpa [Nat.even_add] using h2

/-! ## Anticonnected sets and non-cut vertices -/

/-- The subgraph of `G` induced on `T`, as a graph on the same vertex type. -/
def Hgraph (G : SimpleGraph V) (T : Finset V) : SimpleGraph V where
  Adj u w := G.Adj u w ∧ u ∈ T ∧ w ∈ T
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

theorem Hgraph_mono (G : SimpleGraph V) {T T' : Finset V} (h : T ⊆ T') :
    Hgraph G T ≤ Hgraph G T' := fun _ _ hh => ⟨hh.1, h hh.2.1, h hh.2.2⟩

theorem reach_mono (G : SimpleGraph V) {T T' : Finset V} (h : T ⊆ T') {u w : V}
    (hr : (Hgraph G T).Reachable u w) : (Hgraph G T').Reachable u w :=
  hr.mono (Hgraph_mono G h)

/-- `X` is anticonnected: nonempty, and connected in the complement of `G`. -/
def AC (G : SimpleGraph V) (X : Finset V) : Prop :=
  X.Nonempty ∧ ∀ a ∈ X, ∀ b ∈ X, (Hgraph Gᶜ X).Reachable a b

theorem AC.exists_nbr {G : SimpleGraph V} {X : Finset V} (hX : AC G X) {a b : V} (ha : a ∈ X)
    (hb : b ∈ X) (hab : a ≠ b) : ∃ n, n ∈ X ∧ n ≠ a ∧ Gᶜ.Adj a n := by
  have hr := (hX.2 a ha b hb)
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hac, _⟩
  · exact absurd h hab
  · exact ⟨c, hac.2.2, hac.1.ne.symm, hac.1⟩

section noncut
variable [DecidableEq V]

theorem AC.of_subsingleton (G : SimpleGraph V) (x : V) : AC G {x} := by
  refine ⟨⟨x, by simp⟩, fun a ha b hb => ?_⟩
  simp at ha hb
  subst ha; subst hb
  exact SimpleGraph.Reachable.refl _

/-- A connected anticonnected set with at least two elements has a non-cut vertex. -/
theorem AC.exists_noncut {G : SimpleGraph V} {X : Finset V} (hX : AC G X) (h2 : 2 ≤ X.card) :
    ∃ a ∈ X, AC G (X.erase a) := by
  classical
  let H : SimpleGraph ↥(X : Set V) := Gᶜ.induce (X : Set V)
  have hconn : H.Connected := by
    haveI : Nonempty ↥(X : Set V) := ⟨⟨hX.1.choose, by simpa using hX.1.choose_spec⟩⟩
    refine ⟨fun u w => ?_⟩
    have hr := hX.2 u.1 (by simpa using u.2) w.1 (by simpa using w.2)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    have key : ∀ c, Relation.ReflTransGen (Hgraph Gᶜ X).Adj u.1 c → ∀ hc : c ∈ X,
        H.Reachable u ⟨c, by simpa using hc⟩ := by
      intro c hc
      induction hc with
      | refl => intro _; exact SimpleGraph.Reachable.refl _
      | tail hab hbc ih =>
        rename_i b c'
        intro hc'
        have hb : b ∈ X := hbc.2.1
        refine (ih hb).trans (SimpleGraph.Adj.reachable ?_)
        exact hbc.1
    exact key w.1 hr (by simpa using w.2)
  haveI : Finite ↥(X : Set V) := inferInstance
  haveI : Nontrivial ↥(X : Set V) := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
    exact ⟨⟨⟨a, by simpa using ha⟩, ⟨b, by simpa using hb⟩, fun h => hab (congrArg Subtype.val h)⟩⟩
  obtain ⟨v, hv⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  refine ⟨v.1, by simpa using v.2, ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
    by_cases hav : a = v.1
    · exact ⟨b, Finset.mem_erase.mpr ⟨fun h => hab (hav.trans h.symm), hb⟩⟩
    · exact ⟨a, Finset.mem_erase.mpr ⟨hav, ha⟩⟩
  · intro a ha b hb
    have ha' := Finset.mem_erase.mp ha
    have hb' := Finset.mem_erase.mp hb
    have hrr := hv.preconnected ⟨⟨a, Finset.mem_coe.mpr ha'.2⟩,
        by rw [Set.mem_compl_singleton_iff]; exact fun h => ha'.1 (congrArg Subtype.val h)⟩
      ⟨⟨b, Finset.mem_coe.mpr hb'.2⟩,
        by rw [Set.mem_compl_singleton_iff]; exact fun h => hb'.1 (congrArg Subtype.val h)⟩
    let f : (H.induce ({v}ᶜ : Set ↥(X : Set V))) →g Hgraph Gᶜ (X.erase v.1) :=
      ⟨fun w => w.1.1, fun {w w'} hww => by
        have h1 : Gᶜ.Adj w.1.1 w'.1.1 := hww
        have hw : w.1.1 ∈ X.erase v.1 :=
          Finset.mem_erase.mpr ⟨fun h => w.2 (Set.mem_singleton_iff.mpr (Subtype.ext h)), Finset.mem_coe.mp w.1.2⟩
        have hw' : w'.1.1 ∈ X.erase v.1 :=
          Finset.mem_erase.mpr ⟨fun h => w'.2 (Set.mem_singleton_iff.mpr (Subtype.ext h)), Finset.mem_coe.mp w'.1.2⟩
        exact ⟨h1, hw, hw'⟩⟩
    exact hrr.map f

/-- Adding a vertex with a neighbour keeps a non-cut vertex a non-cut vertex. -/
theorem AC.extend {G : SimpleGraph V} {X : Finset V} {a c n : V} (ha : a ∈ X) (hc : c ∈ X)
    (hac : a ≠ c) (hA : AC G ((X.erase a)))
    (hAc : AC G ((X.erase a).erase c)) (hn : n ∈ X) (hna : n ≠ a) (hnc : n ≠ c)
    (hadj : Gᶜ.Adj a n) : AC G (X.erase c) := by
  have hmem : ∀ x ∈ (X.erase a).erase c, x ∈ X.erase c := fun x hx => by
    simp only [Finset.mem_erase] at hx ⊢
    exact ⟨hx.1, hx.2.2⟩
  have hsub : (X.erase a).erase c ⊆ X.erase c := hmem
  have hnmem : n ∈ (X.erase a).erase c := by simp [hna, hnc, hn]
  have hane : a ∈ X.erase c := by simp [hac, ha]
  have hadjH : (Hgraph Gᶜ (X.erase c)).Adj a n := ⟨hadj, hane, hsub hnmem⟩
  refine ⟨⟨a, hane⟩, fun u hu v hv => ?_⟩
  have hreach : ∀ w ∈ X.erase c, (Hgraph Gᶜ (X.erase c)).Reachable n w := by
    intro w hw
    by_cases hwa : w = a
    · subst hwa; exact hadjH.symm.reachable
    · have hw' : w ∈ (X.erase a).erase c := by
        simp only [Finset.mem_erase] at hw ⊢
        exact ⟨hw.1, hwa, hw.2⟩
      exact reach_mono Gᶜ hsub (hAc.2 n hnmem w hw')
  exact (hreach u hu).symm.trans (hreach v hv)

/-- Two distinct non-cut vertices exist whenever `|X| ≥ 2`. -/
theorem AC.two_noncut {G : SimpleGraph V} : ∀ (m : ℕ) (X : Finset V), X.card = m → AC G X → 2 ≤ m →
    ∃ c₁ ∈ X, ∃ c₂ ∈ X, c₁ ≠ c₂ ∧ AC G (X.erase c₁) ∧ AC G (X.erase c₂) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro X hXm hX h2
    by_cases hm2 : m = 2
    · subst hm2
      obtain ⟨u, w, huw, rfl⟩ := Finset.card_eq_two.mp hXm
      refine ⟨u, by simp, w, by simp, huw, ?_, ?_⟩
      · have : ({u, w} : Finset V).erase u = {w} := by
          rw [show ({u, w} : Finset V) = insert u {w} from rfl, Finset.erase_insert (by simp [huw])]
        rw [this]; exact AC.of_subsingleton G w
      · have : ({u, w} : Finset V).erase w = {u} := by
          rw [Finset.pair_comm, show ({w, u} : Finset V) = insert w {u} from rfl,
            Finset.erase_insert (by simp [huw.symm])]
        rw [this]; exact AC.of_subsingleton G u
    · have h3 : 3 ≤ m := by omega
      obtain ⟨a, ha, hA⟩ := hX.exists_noncut (by omega)
      have hcard : (X.erase a).card = m - 1 := by rw [Finset.card_erase_of_mem ha, hXm]
      obtain ⟨c₁, hc₁, c₂, hc₂, hne, hA1, hA2⟩ := ih (m - 1) (by omega) (X.erase a) hcard hA (by omega)
      obtain ⟨b, hb, hba⟩ : ∃ b ∈ X, b ≠ a := by
        obtain ⟨b, hb, hb'⟩ := Finset.exists_mem_ne (by omega : 1 < X.card) a
        exact ⟨b, hb, hb'⟩
      obtain ⟨n, hn, hna, hadj⟩ := hX.exists_nbr ha hb hba.symm
      have hc₁' := Finset.mem_erase.mp hc₁
      have hc₂' := Finset.mem_erase.mp hc₂
      by_cases hn1 : n = c₁
      · -- use c₂
        have hnc₂ : n ≠ c₂ := fun h => hne (hn1.symm.trans h)
        exact ⟨a, ha, c₂, hc₂'.2, fun h => hc₂'.1 h.symm, hA,
          AC.extend ha hc₂'.2 (fun h => hc₂'.1 h.symm) hA hA2 hn hna hnc₂ hadj⟩
      · exact ⟨a, ha, c₁, hc₁'.2, fun h => hc₁'.1 h.symm, hA,
          AC.extend ha hc₁'.2 (fun h => hc₁'.1 h.symm) hA hA1 hn hna hn1 hadj⟩

end noncut

section goodpair
variable [DecidableEq V]

/-- If there are no three distinct non-cut vertices, there is a pair of nonadjacent non-cut
vertices `a, c` whose removal together still leaves an anticonnected set. -/
theorem AC.good_pair {G : SimpleGraph V} {X : Finset V} (hX : AC G X) (h3 : 3 ≤ X.card)
    (hNC : ∀ a1 ∈ X, ∀ a2 ∈ X, ∀ a3 ∈ X, a1 ≠ a2 → a1 ≠ a3 → a2 ≠ a3 → AC G (X.erase a1) →
      AC G (X.erase a2) → AC G (X.erase a3) → False) :
    ∃ a ∈ X, ∃ c ∈ X, a ≠ c ∧ AC G (X.erase a) ∧ AC G (X.erase c) ∧ ¬ Gᶜ.Adj a c ∧
      AC G ((X.erase a).erase c) := by
  obtain ⟨a, ha, hA⟩ := hX.exists_noncut (by omega)
  have hcard : (X.erase a).card = X.card - 1 := Finset.card_erase_of_mem ha
  obtain ⟨c₁, hc₁, c₂, hc₂, hne, hA1, hA2⟩ :=
    AC.two_noncut (X.erase a).card (X.erase a) rfl hA (by omega)
  have hc₁' := Finset.mem_erase.mp hc₁
  have hc₂' := Finset.mem_erase.mp hc₂
  obtain ⟨b, hb, hba⟩ : ∃ b ∈ X, b ≠ a := Finset.exists_mem_ne (by omega : 1 < X.card) a
  obtain ⟨n0, hn0, hn0a, hadj0⟩ := hX.exists_nbr ha hb hba.symm
  by_cases hmulti : ∃ n1 n2, n1 ∈ X ∧ n2 ∈ X ∧ n1 ≠ n2 ∧ n1 ≠ a ∧ n2 ≠ a ∧ Gᶜ.Adj a n1 ∧
      Gᶜ.Adj a n2
  · exfalso
    obtain ⟨n1, n2, hn1, hn2, h12, hn1a, hn2a, hadj1, hadj2⟩ := hmulti
    have hX1 : AC G (X.erase c₁) := by
      by_cases h : n1 = c₁
      · exact AC.extend ha hc₁'.2 (fun h' => hc₁'.1 h'.symm) hA hA1 hn2 hn2a
          (fun h' => h12 (h.trans h'.symm)) hadj2
      · exact AC.extend ha hc₁'.2 (fun h' => hc₁'.1 h'.symm) hA hA1 hn1 hn1a h hadj1
    have hX2 : AC G (X.erase c₂) := by
      by_cases h : n1 = c₂
      · exact AC.extend ha hc₂'.2 (fun h' => hc₂'.1 h'.symm) hA hA2 hn2 hn2a
          (fun h' => h12 (h.trans h'.symm)) hadj2
      · exact AC.extend ha hc₂'.2 (fun h' => hc₂'.1 h'.symm) hA hA2 hn1 hn1a h hadj1
    exact hNC a ha c₁ hc₁'.2 c₂ hc₂'.2 (fun h => hc₁'.1 h.symm) (fun h => hc₂'.1 h.symm) hne hA
      hX1 hX2
  · push Not at hmulti
    have huniq : ∀ n, n ∈ X → n ≠ a → Gᶜ.Adj a n → n = n0 := by
      intro n hn hna hadj
      by_contra hne'
      exact absurd hadj0 (hmulti n n0 hn hn0 hne' hna hn0a hadj)
    by_cases hc1w : c₁ = n0
    · have hc2w : c₂ ≠ n0 := fun h => hne (hc1w.trans h.symm)
      refine ⟨a, ha, c₂, hc₂'.2, fun h => hc₂'.1 h.symm, hA,
        AC.extend ha hc₂'.2 (fun h => hc₂'.1 h.symm) hA hA2 hn0 hn0a (fun h => hc2w h.symm) hadj0,
        fun hadj => hc2w (huniq c₂ hc₂'.2 hc₂'.1 hadj), hA2⟩
    · refine ⟨a, ha, c₁, hc₁'.2, fun h => hc₁'.1 h.symm, hA,
        AC.extend ha hc₁'.2 (fun h => hc₁'.1 h.symm) hA hA1 hn0 hn0a (fun h => hc1w h.symm) hadj0,
        fun hadj => hc1w (huniq c₁ hc₁'.2 hc₁'.1 hadj), hA1⟩

/-- Two vertices of an anticonnected two-element set are nonadjacent in `G`. -/
theorem AC.pair_compl {G : SimpleGraph V} {u w : V} (huw : u ≠ w) (h : AC G {u, w}) :
    Gᶜ.Adj u w := by
  obtain ⟨n, hn, hnu, hadj⟩ := h.exists_nbr (by simp : u ∈ ({u, w} : Finset V))
    (by simp : w ∈ ({u, w} : Finset V)) huw
  simp at hn
  rcases hn with rfl | rfl
  · exact absurd rfl hnu
  · exact hadj

end goodpair

/-! ## Induced paths from reachability -/

/-- Walks of length `ℓ` from `u` to `w` in `H`, as index functions. -/
def Wk (H : SimpleGraph V) (u w : V) (ℓ : ℕ) : Prop :=
  ∃ q : ℕ → V, q 0 = u ∧ q ℓ = w ∧ ∀ t, t < ℓ → H.Adj (q t) (q (t + 1))

theorem Wk.of_reachable {H : SimpleGraph V} {u w : V} (h : H.Reachable u w) : ∃ ℓ, Wk H u w ℓ := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨0, fun _ => u, rfl, rfl, fun t ht => by omega⟩
  | @tail b c _ hbc ih =>
    obtain ⟨ℓ, q, h0, hℓ, hs⟩ := ih
    refine ⟨ℓ + 1, fun t => if t ≤ ℓ then q t else c, by simpa using h0, by simp, ?_⟩
    intro t ht
    by_cases h1 : t < ℓ
    · simp only [Nat.le_of_lt h1, if_true, Nat.succ_le_of_lt h1]
      exact hs t h1
    · have : t = ℓ := by omega
      subst this
      simp only [le_refl, if_true, Nat.not_succ_le_self, if_false]
      rw [hℓ]; exact hbc

theorem Wk.shortcut {H : SimpleGraph V} {u w : V} {ℓ : ℕ} {q : ℕ → V} (h0 : q 0 = u)
    (hℓ : q ℓ = w) (hs : ∀ t, t < ℓ → H.Adj (q t) (q (t + 1))) (i j : ℕ) (hij : i + 2 ≤ j)
    (hj : j ≤ ℓ) (hqa : H.Adj (q i) (q j)) : Wk H u w (ℓ - (j - i - 1)) := by
  refine ⟨fun t => if t ≤ i then q t else q (t + (j - i - 1)), by simpa using h0, ?_, ?_⟩
  · have : ¬ (ℓ - (j - i - 1) ≤ i) := by omega
    simp only [this, if_false]
    rw [show ℓ - (j - i - 1) + (j - i - 1) = ℓ by omega]
    exact hℓ
  · intro t ht
    by_cases h1 : t + 1 ≤ i
    · simp only [h1, show t ≤ i by omega, if_true]
      exact hs t (by omega)
    · by_cases h2 : t = i
      · subst h2
        simp only [le_refl, if_true, show ¬ (t + 1 ≤ t) by omega, if_false]
        rw [show t + 1 + (j - t - 1) = j by omega]
        exact hqa
      · have h3 : ¬ t ≤ i := by omega
        simp only [h3, show ¬ (t + 1 ≤ i) by omega, if_false]
        rw [show t + 1 + (j - i - 1) = t + (j - i - 1) + 1 by omega]
        exact hs _ (by omega)

/-- A shortest walk between two vertices of `T` inside `T` is an induced path. -/
theorem exists_induced_path (G' : SimpleGraph V) (T : Finset V) {u w : V} (hu : u ∈ T) (hw : w ∈ T)
    (hr : (Hgraph G' T).Reachable u w) :
    ∃ ℓ q, IP G' q ℓ ∧ q 0 = u ∧ q ℓ = w ∧ ∀ t, t ≤ ℓ → q t ∈ T := by
  classical
  have hex := Wk.of_reachable hr
  let ℓ := Nat.find hex
  have hℓ : Wk (Hgraph G' T) u w ℓ := Nat.find_spec hex
  have hmin : ∀ ℓ' < ℓ, ¬ Wk (Hgraph G' T) u w ℓ' := fun ℓ' h => Nat.find_min hex h
  obtain ⟨q, h0, hℓw, hs⟩ := hℓ
  have hT : ∀ t, t ≤ ℓ → q t ∈ T := by
    intro t ht
    by_cases h : t < ℓ
    · exact (hs t h).2.1
    · have : t = ℓ := by omega
      subst this; rw [hℓw]; exact hw
  have hshort : ∀ i j, i + 2 ≤ j → j ≤ ℓ → ¬ (Hgraph G' T).Adj (q i) (q j) := fun i j hij hj hadj =>
    hmin _ (by omega) (Wk.shortcut h0 hℓw hs i j hij hj hadj)
  have hinj' : ∀ i j, i < j → j ≤ ℓ → q i ≠ q j := by
    intro i j hij hj heq
    by_cases hjl : j = ℓ
    · subst hjl
      exact hmin i hij ⟨q, h0, heq.trans hℓw, fun t ht => hs t (by omega)⟩
    · have hjl' : j < ℓ := by omega
      have := hs j hjl'
      rw [← heq] at this
      exact hshort i (j + 1) (by omega) (by omega) this
  refine ⟨ℓ, q, ⟨?_, ?_⟩, h0, hℓw, hT⟩
  · intro i j hi hj hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (hinj' i j h hj)
    · exact h
    · exact absurd hij.symm (hinj' j i h hi)
  · intro i j hi hj
    constructor
    · intro hadj
      have hH : (Hgraph G' T).Adj (q i) (q j) := ⟨hadj, hT i hi, hT j hj⟩
      rcases lt_trichotomy i j with h | h | h
      · by_contra hne
        exact hshort i j (by omega) hj hH
      · subst h; exact absurd hadj (G'.loopless.irrefl _)
      · by_contra hne
        exact hshort j i (by omega) hi hH.symm
    · rintro (h | h)
      · subst h; exact (hs i (by omega)).1
      · subst h; exact (hs j (by omega)).1.symm


/-! ## The Wonderful Lemma: statements -/

/-- `v` is `X`-complete: `v ∉ X` and `v` is adjacent to every vertex of `X`. -/
def XC (G : SimpleGraph V) (X : Finset V) (v : V) : Prop := v ∉ X ∧ ∀ x ∈ X, G.Adj v x

/-- `a, b ∈ X` form a leap for the path `p 0, …, p k`. -/
def Leap (G : SimpleGraph V) (X : Finset V) (p : ℕ → V) (k : ℕ) (a b : V) : Prop :=
  a ∈ X ∧ b ∈ X ∧ a ≠ b ∧ ¬ G.Adj a b ∧
  (∀ i, i ≤ k → (G.Adj a (p i) ↔ (i = 0 ∨ i = 1 ∨ i = k))) ∧
  (∀ i, i ≤ k → (G.Adj b (p i) ↔ (i = 0 ∨ i + 1 = k ∨ i = k)))

/-- The three outcomes of the Wonderful Lemma for `X` and the path `p 0, …, p k`. -/
def Outcome (G : SimpleGraph V) (X : Finset V) (p : ℕ → V) (k : ℕ) : Prop :=
  (∃ i, i < k ∧ XC G X (p i) ∧ XC G X (p (i + 1))) ∨
  (5 ≤ k ∧ ∃ a b, Leap G X p k a b) ∨
  (k = 3 ∧ ∃ ℓ q, IP Gᶜ q ℓ ∧ Odd ℓ ∧ q 0 = p 1 ∧ q ℓ = p 2 ∧
    ∀ t, 0 < t → t < ℓ → q t ∈ X)

/-- The Wonderful Lemma holds for `X`: every odd induced path of `G` avoiding `X` with
`X`-complete ends has one of the three outcomes. -/
def WH (G : SimpleGraph V) (X : Finset V) : Prop :=
  ∀ (k : ℕ) (p : ℕ → V), IP G p k → Odd k → (∀ i, i ≤ k → p i ∉ X) → XC G X (p 0) →
    XC G X (p k) → Outcome G X p k

/-! ## Corollary 2.1 -/

/-- The path `a, p 1, …, p (k-1), b` of a leap. -/
def leapPath (p : ℕ → V) (k : ℕ) (a b : V) : ℕ → V :=
  fun t => if t = 0 then a else if t = k then b else p t

theorem leapPath_zero (p : ℕ → V) (k : ℕ) (a b : V) : leapPath p k a b 0 = a := by
  simp [leapPath]

theorem leapPath_last (p : ℕ → V) {k : ℕ} (hk : 0 < k) (a b : V) : leapPath p k a b k = b := by
  simp [leapPath, Nat.pos_iff_ne_zero.mp hk]

theorem leapPath_mid (p : ℕ → V) {k t : ℕ} (h0 : 0 < t) (h1 : t < k) (a b : V) :
    leapPath p k a b t = p t := by
  simp [leapPath, Nat.pos_iff_ne_zero.mp h0, Nat.ne_of_lt h1]

theorem leapPath_IP {G : SimpleGraph V} {X : Finset V} {p : ℕ → V} {k : ℕ} {a b : V}
    (hp : IP G p k) (hk : 5 ≤ k) (hpX : ∀ i, i ≤ k → p i ∉ X) (hl : Leap G X p k a b) :
    IP G (leapPath p k a b) k := by
  obtain ⟨haX, hbX, hab, hnab, hA, hB⟩ := hl
  have cls : ∀ t, t ≤ k → t = 0 ∨ t = k ∨ (0 < t ∧ t < k) := fun t ht => by omega
  have hpos : 0 < k := by omega
  refine ⟨fun i j hi hj hij => ?_, fun i j hi hj => ?_⟩
  · rcases cls i hi with rfl | rfl | ⟨h1, h2⟩ <;> rcases cls j hj with rfl | rfl | ⟨h3, h4⟩
    · rfl
    · rw [leapPath_zero, leapPath_last _ hpos] at hij; exact absurd hij hab
    · rw [leapPath_zero, leapPath_mid _ h3 h4] at hij
      exact absurd (hij ▸ haX) (hpX j hj)
    · rw [leapPath_zero, leapPath_last _ hpos] at hij; exact absurd hij.symm hab
    · rfl
    · rw [leapPath_last _ hpos, leapPath_mid _ h3 h4] at hij
      exact absurd (hij ▸ hbX) (hpX j hj)
    · rw [leapPath_zero, leapPath_mid _ h1 h2] at hij
      exact absurd (hij.symm ▸ haX) (hpX i hi)
    · rw [leapPath_last _ hpos, leapPath_mid _ h1 h2] at hij
      exact absurd (hij.symm ▸ hbX) (hpX i hi)
    · rw [leapPath_mid _ h1 h2, leapPath_mid _ h3 h4] at hij
      exact hp.inj i j hi hj hij
  · rcases cls i hi with rfl | rfl | ⟨h1, h2⟩ <;> rcases cls j hj with rfl | rfl | ⟨h3, h4⟩
    · rw [leapPath_zero]; simp
    · rw [leapPath_zero, leapPath_last _ hpos]
      simp only [hnab, false_iff]; omega
    · rw [leapPath_zero, leapPath_mid _ h3 h4, hA j hj]; omega
    · rw [leapPath_zero, leapPath_last _ hpos, G.adj_comm]
      simp only [hnab, false_iff]; omega
    · rw [leapPath_last _ hpos]; simp
    · rw [leapPath_last _ hpos, leapPath_mid _ h3 h4, hB j hj]; omega
    · rw [leapPath_zero, leapPath_mid _ h1 h2, G.adj_comm, hA i hi]; omega
    · rw [leapPath_last _ hpos, leapPath_mid _ h1 h2, G.adj_comm, hB i hi]; omega
    · rw [leapPath_mid _ h1 h2, leapPath_mid _ h3 h4, hp.adj i j hi hj]

theorem cor21 {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X : Finset V}
    {p : ℕ → V} {k : ℕ} (hp : IP G p k) (hk : Odd k) (hpX : ∀ i, i ≤ k → p i ∉ X)
    (hno : ¬ ∃ i, i < k ∧ XC G X (p i) ∧ XC G X (p (i + 1))) (hout : Outcome G X p k)
    {v : V} (hv : XC G X v) : ∃ t, 0 < t ∧ t < k ∧ G.Adj v (p t) := by
  by_contra hnone
  push Not at hnone
  rcases hout with h1 | ⟨hk5, a, b, hl⟩ | ⟨hk3, ℓ, q, hq, hodd, hq0, hqℓ, hqX⟩
  · exact hno h1
  · have hvmid : ∀ t, 0 < t → t < k → v ≠ p t := by
      intro t h1 h2 hvt
      by_cases ht : t + 1 < k
      · exact hnone (t + 1) (by omega) ht (hvt ▸ (hp.adj t (t + 1) (by omega) (by omega)).mpr
          (Or.inl rfl))
      · exact hnone (t - 1) (by omega) (by omega) (hvt ▸ (hp.adj t (t - 1) (by omega) (by omega)).mpr
          (Or.inr (by omega)))
    have hIP := leapPath_IP hp hk5 hpX hl
    have := apex_even hG.1 hIP (by omega) v (fun t ht hvt => by
        by_cases h0 : t = 0
        · subst h0; rw [leapPath_zero] at hvt; exact hv.1 (hvt ▸ hl.1)
        · by_cases hkt : t = k
          · subst hkt; rw [leapPath_last _ (by omega)] at hvt; exact hv.1 (hvt ▸ hl.2.1)
          · rw [leapPath_mid _ (by omega) (by omega)] at hvt
            exact hvmid t (by omega) (by omega) hvt)
      (by rw [leapPath_zero]; exact hv.2 a hl.1)
      (by rw [leapPath_last _ (by omega)]; exact hv.2 b hl.2.1)
      (fun t h1 h2 => by rw [leapPath_mid _ h1 h2]; exact hnone t h1 h2)
    exact (Nat.not_even_iff_odd.mpr hk) this
  · subst hk3
    have hp12 : G.Adj (p 1) (p 2) := (hp.adj 1 2 (by omega) (by omega)).mpr (Or.inl rfl)
    have hℓ2 : 2 ≤ ℓ := by
      rcases hodd with ⟨r, hr⟩
      by_contra hlt
      have hℓ1 : ℓ = 1 := by omega
      subst hℓ1
      have := (hq.adj 0 1 (by omega) (by omega)).mpr (Or.inl rfl)
      rw [hq0, hqℓ] at this
      exact this.2 hp12
    have hv1 : v ≠ p 1 := fun h => hnone 2 (by omega) (by omega) (by rw [h]; exact hp12)
    have hv2 : v ≠ p 2 := fun h => hnone 1 (by omega) (by omega) (by rw [h]; exact hp12.symm)
    have hvq : ∀ t, t ≤ ℓ → v ≠ q t := by
      intro t ht hvt
      by_cases h0 : t = 0
      · subst h0; rw [hq0] at hvt; exact hv1 hvt
      · by_cases hl : t = ℓ
        · subst hl; rw [hqℓ] at hvt; exact hv2 hvt
        · exact hv.1 (hvt ▸ hqX t (by omega) (by omega))
    have := apex_even hG.2 hq hℓ2 v hvq
      (by rw [hq0]; exact (SimpleGraph.compl_adj G _ _).mpr ⟨hv1, hnone 1 (by omega) (by omega)⟩)
      (by rw [hqℓ]; exact (SimpleGraph.compl_adj G _ _).mpr ⟨hv2, hnone 2 (by omega) (by omega)⟩)
      (fun t h1 h2 hadj => hadj.2 (hv.2 _ (hqX t h1 h2)))
    exact (Nat.not_even_iff_odd.mpr hodd) this


/-! ## Counting complete edges: Corollary 2.3 -/

open Classical in
/-- Number of `X`-complete edges `p t p (t+1)` with `i ≤ t < j`. -/
noncomputable def ecnt (G : SimpleGraph V) (X : Finset V) (p : ℕ → V) (i j : ℕ) : ℕ :=
  ∑ t ∈ Finset.Ico i j, if XC G X (p t) ∧ XC G X (p (t + 1)) then 1 else 0

theorem ecnt_split (G : SimpleGraph V) (X : Finset V) (p : ℕ → V) {i m j : ℕ} (h1 : i ≤ m)
    (h2 : m ≤ j) : ecnt G X p i j = ecnt G X p i m + ecnt G X p m j := by
  unfold ecnt
  rw [Finset.sum_Ico_consecutive _ h1 h2]

theorem ecnt_zero (G : SimpleGraph V) (X : Finset V) (p : ℕ → V) {i j : ℕ}
    (h : ∀ t, i ≤ t → t < j → ¬ (XC G X (p t) ∧ XC G X (p (t + 1)))) : ecnt G X p i j = 0 := by
  unfold ecnt
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_Ico] at ht
  simp [h t ht.1 ht.2]

theorem ecnt_one (G : SimpleGraph V) (X : Finset V) (p : ℕ → V) {i : ℕ}
    (h : XC G X (p i) ∧ XC G X (p (i + 1))) : ecnt G X p i (i + 1) = 1 := by
  unfold ecnt
  rw [Nat.Ico_succ_singleton, Finset.sum_singleton, if_pos h]

theorem ecnt_pos (G : SimpleGraph V) (X : Finset V) (p : ℕ → V) {i j : ℕ}
    (h : ecnt G X p i j % 2 = 1) : ∃ t, i ≤ t ∧ t < j ∧ XC G X (p t) ∧ XC G X (p (t + 1)) := by
  by_contra hno
  push Not at hno
  have := ecnt_zero G X p (fun t h1 h2 hh => hno t h1 h2 hh.1 hh.2)
  omega

/-- Parity of the number of `X`-complete edges of a sub-path with `X`-complete ends, given an
`X`-complete vertex outside it (Roussel–Rubio corollary 2.3). -/
theorem cor23_gen {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X : Finset V}
    (hW : WH G X) {p : ℕ → V} {k : ℕ} (hp : IP G p k) (hpX : ∀ i, i ≤ k → p i ∉ X) :
    ∀ n i j, j - i = n → i < j → j ≤ k → XC G X (p i) → XC G X (p j) →
      (∃ t, t ≤ k ∧ XC G X (p t) ∧ (t < i ∨ j < t)) → ecnt G X p i j % 2 = (j - i) % 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i j hn hij hj hXi hXj hwit
    by_cases hm : ∃ m, i < m ∧ m < j ∧ XC G X (p m)
    · obtain ⟨m, hm1, hm2, hmX⟩ := hm
      have e1 := ih (m - i) (by omega) i m rfl hm1 (by omega) hXi hmX
        (by obtain ⟨t, ht1, ht2, ht3⟩ := hwit; exact ⟨j, hj, hXj, Or.inr hm2⟩)
      have e2 := ih (j - m) (by omega) m j rfl hm2 hj hmX hXj
        (by obtain ⟨t, ht1, ht2, ht3⟩ := hwit; exact ⟨i, by omega, hXi, Or.inl hm1⟩)
      rw [ecnt_split G X p hm1.le hm2.le]
      omega
    · push Not at hm
      by_cases h1 : j = i + 1
      · subst h1
        rw [ecnt_one G X p ⟨hXi, hXj⟩]
        omega
      · have hz : ecnt G X p i j = 0 := by
          apply ecnt_zero
          intro t ht1 ht2 hh
          by_cases hti : t = i
          · subst hti
            exact hm (t + 1) (by omega) (by omega) hh.2
          · exact hm t (by omega) ht2 hh.1
        rw [hz]
        by_contra hodd
        have hodd' : Odd (j - i) := by
          rw [Nat.odd_iff]; omega
        obtain ⟨t, ht1, ht2, ht3⟩ := hwit
        have hsub := hp.sub i j hij.le hj
        have hout := hW (j - i) (fun s => p (i + s)) hsub hodd'
          (fun s hs => hpX _ (by omega)) (by simpa using hXi) (by simpa [Nat.add_sub_cancel' hij.le] using hXj)
        have hnoE : ¬ ∃ s, s < j - i ∧ XC G X (p (i + s)) ∧ XC G X (p (i + (s + 1))) := by
          rintro ⟨s, hs1, hs2, hs3⟩
          by_cases hs0 : s = 0
          · subst hs0; exact hm (i + 1) (by omega) (by omega) (by simpa using hs3)
          · exact hm (i + s) (by omega) (by omega) hs2
        obtain ⟨u, hu1, hu2, hu3⟩ := cor21 hG hsub hodd' (fun s hs => hpX _ (by omega)) hnoE hout ht2
        rw [hp.adj t (i + u) ht1 (by omega)] at hu3
        omega

theorem cor23 {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X : Finset V}
    (hW : WH G X) {p : ℕ → V} {k : ℕ} (hp : IP G p k) (hpX : ∀ i, i ≤ k → p i ∉ X)
    (h0 : XC G X (p 0)) (hk : XC G X (p k)) (m : ℕ) (hm0 : 0 < m) (hmk : m < k)
    (hm : XC G X (p m)) : ecnt G X p 0 k % 2 = k % 2 := by
  have e1 := cor23_gen hG hW hp hpX (m - 0) 0 m rfl hm0 hmk.le h0 hm ⟨k, le_refl _, hk, Or.inr hmk⟩
  have e2 := cor23_gen hG hW hp hpX (k - m) m k rfl hmk le_rfl hm hk ⟨0, by omega, h0, Or.inl hm0⟩
  rw [ecnt_split G X p (Nat.zero_le m) hmk.le]
  omega


/-! ## Two arms of a path joined through an apex vertex -/

/-- The walk `p x1, …, p y1, a, p x2, …, p y2`. -/
def apexJoin (p : ℕ → V) (a : V) (x1 y1 x2 : ℕ) : ℕ → V := fun t =>
  if t ≤ y1 - x1 then p (x1 + t) else if t = y1 - x1 + 1 then a else p (x2 + (t - (y1 - x1 + 2)))

theorem apexJoin_arm1 {p : ℕ → V} {a : V} {x1 y1 x2 t : ℕ} (h : t ≤ y1 - x1) :
    apexJoin p a x1 y1 x2 t = p (x1 + t) := by
  simp [apexJoin, h]

theorem apexJoin_apex {p : ℕ → V} {a : V} {x1 y1 x2 : ℕ} :
    apexJoin p a x1 y1 x2 (y1 - x1 + 1) = a := by
  simp [apexJoin]

theorem apexJoin_arm2 {p : ℕ → V} {a : V} {x1 y1 x2 t : ℕ} (h : y1 - x1 + 2 ≤ t) :
    apexJoin p a x1 y1 x2 t = p (x2 + (t - (y1 - x1 + 2))) := by
  have h1 : ¬ t ≤ y1 - x1 := by omega
  have h2 : ¬ t = y1 - x1 + 1 := by omega
  simp [apexJoin, h1, h2]

theorem apexJoin_IP {H : SimpleGraph V} {p : ℕ → V} {k : ℕ} (hp : IP H p k) (a : V)
    (hz : ∀ t, t ≤ k → a ≠ p t) (x1 y1 x2 y2 : ℕ) (h1 : x1 ≤ y1) (h1' : y1 ≤ k) (h2 : x2 ≤ y2)
    (h2' : y2 ≤ k) (hsep : y1 + 2 ≤ x2 ∨ y2 + 2 ≤ x1)
    (hadj : ∀ t, t ≤ k → ((x1 ≤ t ∧ t ≤ y1) ∨ (x2 ≤ t ∧ t ≤ y2)) →
      (H.Adj a (p t) ↔ (t = y1 ∨ t = x2))) :
    IP H (apexJoin p a x1 y1 x2) ((y1 - x1) + (y2 - x2) + 2) := by
  have cls : ∀ t, t ≤ (y1 - x1) + (y2 - x2) + 2 →
      t ≤ y1 - x1 ∨ t = y1 - x1 + 1 ∨ (y1 - x1 + 2 ≤ t ∧ x2 + (t - (y1 - x1 + 2)) ≤ y2) := by
    intro t ht; omega
  refine ⟨fun i j hi hj hij => ?_, fun i j hi hj => ?_⟩
  · rcases cls i hi with c1 | c1 | ⟨c1, c1'⟩ <;> rcases cls j hj with c2 | c2 | ⟨c2, c2'⟩
    · rw [apexJoin_arm1 c1, apexJoin_arm1 c2] at hij
      have := hp.inj _ _ (by omega) (by omega) hij; omega
    · rw [apexJoin_arm1 c1, c2, apexJoin_apex] at hij
      exact absurd hij.symm (hz _ (by omega))
    · rw [apexJoin_arm1 c1, apexJoin_arm2 c2] at hij
      have := hp.inj _ _ (by omega) (by omega) hij; omega
    · rw [apexJoin_arm1 c2, c1, apexJoin_apex] at hij
      exact absurd hij (hz _ (by omega))
    · omega
    · rw [c1, apexJoin_apex, apexJoin_arm2 c2] at hij
      exact absurd hij (hz _ (by omega))
    · rw [apexJoin_arm1 c2, apexJoin_arm2 c1] at hij
      have := hp.inj _ _ (by omega) (by omega) hij; omega
    · rw [apexJoin_arm2 c1, c2, apexJoin_apex] at hij
      exact absurd hij.symm (hz _ (by omega))
    · rw [apexJoin_arm2 c1, apexJoin_arm2 c2] at hij
      have := hp.inj _ _ (by omega) (by omega) hij; omega
  · rcases cls i hi with c1 | c1 | ⟨c1, c1'⟩ <;> rcases cls j hj with c2 | c2 | ⟨c2, c2'⟩
    · rw [apexJoin_arm1 c1, apexJoin_arm1 c2, hp.adj _ _ (by omega) (by omega)]; omega
    · rw [apexJoin_arm1 c1, c2, apexJoin_apex, H.adj_comm,
        hadj _ (by omega) (Or.inl ⟨by omega, by omega⟩)]
      omega
    · rw [apexJoin_arm1 c1, apexJoin_arm2 c2, hp.adj _ _ (by omega) (by omega)]; omega
    · rw [apexJoin_arm1 c2, c1, apexJoin_apex, hadj _ (by omega) (Or.inl ⟨by omega, by omega⟩)]
      omega
    · subst c1; subst c2; simp
    · rw [c1, apexJoin_apex, apexJoin_arm2 c2, hadj _ (by omega) (Or.inr ⟨by omega, by omega⟩)]
      omega
    · rw [apexJoin_arm1 c2, apexJoin_arm2 c1, hp.adj _ _ (by omega) (by omega)]; omega
    · rw [apexJoin_arm2 c1, c2, apexJoin_apex, H.adj_comm,
        hadj _ (by omega) (Or.inr ⟨by omega, by omega⟩)]
      omega
    · rw [apexJoin_arm2 c1, apexJoin_arm2 c2, hp.adj _ _ (by omega) (by omega)]; omega

theorem apexJoin_zero (p : ℕ → V) (a : V) (x1 y1 x2 : ℕ) : apexJoin p a x1 y1 x2 0 = p x1 := by
  rw [apexJoin_arm1 (Nat.zero_le _)]; simp

theorem apexJoin_last (p : ℕ → V) (a : V) {x1 y1 x2 y2 : ℕ} (h1 : x1 ≤ y1) (h2 : x2 ≤ y2) :
    apexJoin p a x1 y1 x2 ((y1 - x1) + (y2 - x2) + 2) = p y2 := by
  rw [apexJoin_arm2 (by omega)]
  congr 1
  omega

theorem apexJoin_interior (p : ℕ → V) (a : V) {x1 y1 x2 y2 t : ℕ} (h1 : x1 ≤ y1) (h2 : x2 ≤ y2)
    (ht0 : 0 < t) (ht : t < (y1 - x1) + (y2 - x2) + 2) :
    apexJoin p a x1 y1 x2 t = a ∨ ∃ u, ((x1 < u ∧ u ≤ y1) ∨ (x2 ≤ u ∧ u < y2)) ∧
      apexJoin p a x1 y1 x2 t = p u := by
  by_cases c1 : t ≤ y1 - x1
  · right; exact ⟨x1 + t, Or.inl ⟨by omega, by omega⟩, apexJoin_arm1 c1⟩
  · by_cases c2 : t = y1 - x1 + 1
    · left; rw [c2, apexJoin_apex]
    · right
      exact ⟨x2 + (t - (y1 - x1 + 2)), Or.inr ⟨by omega, by omega⟩, apexJoin_arm2 (by omega)⟩

/-! ## Segments between neighbours of a vertex -/

theorem seg_exists {G : SimpleGraph V} {A : Finset V} {p : ℕ → V} (Ia : ℕ → Prop) (L : ℕ)
    (hnoX : ∀ t, t < L → ¬ (XC G A (p t) ∧ XC G A (p (t + 1)) ∧ Ia t ∧ Ia (t + 1))) :
    ∀ n i j, j - i = n → i ≤ j → j ≤ L → Ia i → Ia j → ecnt G A p i j % 2 = 1 →
      ∃ i' j', i ≤ i' ∧ i' + 2 ≤ j' ∧ j' ≤ j ∧ Ia i' ∧ Ia j' ∧
        (∀ t, i' < t → t < j' → ¬ Ia t) ∧ ecnt G A p i' j' % 2 = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i j hn hij hjL hIi hIj hodd
    by_cases hm : ∃ m, i < m ∧ m < j ∧ Ia m
    · obtain ⟨m, hm1, hm2, hmI⟩ := hm
      rw [ecnt_split G A p hm1.le hm2.le] at hodd
      by_cases h1 : ecnt G A p i m % 2 = 1
      · obtain ⟨i', j', a1, a2, a3, a4, a5, a6, a7⟩ :=
          ih (m - i) (by omega) i m rfl hm1.le (by omega) hIi hmI h1
        exact ⟨i', j', a1, a2, by omega, a4, a5, a6, a7⟩
      · have h2 : ecnt G A p m j % 2 = 1 := by omega
        obtain ⟨i', j', a1, a2, a3, a4, a5, a6, a7⟩ :=
          ih (j - m) (by omega) m j rfl hm2.le hjL hmI hIj h2
        exact ⟨i', j', by omega, a2, a3, a4, a5, a6, a7⟩
    · push Not at hm
      by_cases h1 : j = i + 1
      · subst h1
        exfalso
        obtain ⟨t, ht1, ht2, ht3, ht4⟩ := ecnt_pos G A p hodd
        have : t = i := by omega
        subst this
        exact hnoX t (by omega) ⟨ht3, ht4, hIi, hIj⟩
      · by_cases h0 : j = i
        · subst h0
          simp [ecnt] at hodd
        · exact ⟨i, j, le_refl _, by omega, le_refl _, hIi, hIj, fun t h1 h2 => hm t h1 h2, hodd⟩

/-! ## Helper lemmas -/

theorem exists_min {P : ℕ → Prop} {i j : ℕ} (h : ∃ t, i ≤ t ∧ t ≤ j ∧ P t) :
    ∃ w, i ≤ w ∧ w ≤ j ∧ P w ∧ ∀ t, i ≤ t → t < w → ¬ P t := by
  classical
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2.1, (Nat.find_spec h).2.2, ?_⟩
  intro t h1 h2 hP
  exact Nat.find_min h h2 ⟨h1, by have := (Nat.find_spec h).2.1; omega, hP⟩

theorem exists_max {P : ℕ → Prop} {i j : ℕ} (h : ∃ t, i ≤ t ∧ t ≤ j ∧ P t) :
    ∃ u, i ≤ u ∧ u ≤ j ∧ P u ∧ ∀ t, u < t → t ≤ j → ¬ P t := by
  classical
  obtain ⟨t, hit, htj, ht⟩ := h
  refine ⟨Nat.findGreatest P j, ?_, Nat.findGreatest_le j, Nat.findGreatest_spec htj ht, ?_⟩
  · exact le_trans hit (Nat.le_findGreatest htj ht)
  · intro t' h1 h2 hP
    exact absurd (Nat.le_findGreatest h2 hP) (by omega)

theorem XC.mono {G : SimpleGraph V} {X Y : Finset V} {v : V} (h : XC G X v) (hYX : Y ⊆ X) :
    XC G Y v :=
  ⟨fun hv => h.1 (hYX hv), fun x hx => h.2 x (hYX hx)⟩

theorem XC.erase_of {G : SimpleGraph V} [DecidableEq V] {X : Finset V} {a v : V} (h : XC G X v) :
    XC G (X.erase a) v :=
  h.mono (Finset.erase_subset _ _)

theorem XC.of_erase {G : SimpleGraph V} [DecidableEq V] {X : Finset V} {a v : V}
    (h : XC G (X.erase a) v) (hva : G.Adj v a) : XC G X v := by
  refine ⟨fun hv => ?_, fun x hx => ?_⟩
  · exact h.1 (Finset.mem_erase.mpr ⟨hva.ne, hv⟩)
  · by_cases hxa : x = a
    · rw [hxa]; exact hva
    · exact h.2 x (Finset.mem_erase.mpr ⟨hxa, hx⟩)

/-- Corollary 2.1 in the form used for paths built by `apexJoin`. -/
theorem cor21W {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {A : Finset V}
    (hW : WH G A) {q : ℕ → V} {ℓ : ℕ} (hq : IP G q ℓ) (hℓ : Odd ℓ) (h3 : 3 ≤ ℓ)
    (hqA : ∀ t, t ≤ ℓ → q t ∉ A) (h0 : XC G A (q 0)) (hl : XC G A (q ℓ))
    (hint : ∀ t, 0 < t → t < ℓ → ¬ XC G A (q t)) {v : V} (hv : XC G A v) :
    ∃ t, 0 < t ∧ t < ℓ ∧ G.Adj v (q t) := by
  have hout := hW ℓ q hq hℓ hqA h0 hl
  refine cor21 hG hq hℓ hqA ?_ hout hv
  rintro ⟨i, hi, h1, h2⟩
  by_cases hi0 : i = 0
  · subst hi0; exact hint 1 (by omega) (by omega) h2
  · exact hint i (by omega) hi h1

theorem apexJoin_mem (p : ℕ → V) (a : V) {x1 y1 x2 y2 t : ℕ} (h1 : x1 ≤ y1) (h2 : x2 ≤ y2)
    (ht : t ≤ (y1 - x1) + (y2 - x2) + 2) :
    apexJoin p a x1 y1 x2 t = a ∨ ∃ u, ((x1 ≤ u ∧ u ≤ y1) ∨ (x2 ≤ u ∧ u ≤ y2)) ∧
      apexJoin p a x1 y1 x2 t = p u := by
  by_cases c1 : t ≤ y1 - x1
  · right; exact ⟨x1 + t, Or.inl ⟨by omega, by omega⟩, apexJoin_arm1 c1⟩
  · by_cases c2 : t = y1 - x1 + 1
    · left; rw [c2, apexJoin_apex]
    · right
      exact ⟨x2 + (t - (y1 - x1 + 2)), Or.inr ⟨by omega, by omega⟩, apexJoin_arm2 (by omega)⟩

/-- Corollary 2.1 applied to the path `p x1 … p y1, a, p x2 … p y2`. -/
theorem apex_cor21 {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {A : Finset V}
    (hW : WH G A) {p : ℕ → V} {k : ℕ} (hp : IP G p k) (hpA : ∀ t, t ≤ k → p t ∉ A) {a : V}
    (haA : a ∉ A) (hz : ∀ t, t ≤ k → a ≠ p t) (haN : ¬ XC G A a) {x1 y1 x2 y2 : ℕ}
    (h1 : x1 ≤ y1) (h1' : y1 ≤ k) (h2 : x2 ≤ y2) (h2' : y2 ≤ k)
    (hsep : y1 + 2 ≤ x2 ∨ y2 + 2 ≤ x1)
    (hadj : ∀ t, t ≤ k → ((x1 ≤ t ∧ t ≤ y1) ∨ (x2 ≤ t ∧ t ≤ y2)) →
      (G.Adj a (p t) ↔ (t = y1 ∨ t = x2)))
    (hodd : Odd ((y1 - x1) + (y2 - x2) + 2)) (hE1 : XC G A (p x1)) (hE2 : XC G A (p y2))
    (hint : ∀ t, ((x1 < t ∧ t ≤ y1) ∨ (x2 ≤ t ∧ t < y2)) → ¬ XC G A (p t)) {v : V}
    (hv : XC G A v) :
    G.Adj v a ∨ ∃ t, ((x1 < t ∧ t ≤ y1) ∨ (x2 ≤ t ∧ t < y2)) ∧ G.Adj v (p t) := by
  have hIP := apexJoin_IP hp a hz x1 y1 x2 y2 h1 h1' h2 h2' hsep hadj
  have h3 : 3 ≤ (y1 - x1) + (y2 - x2) + 2 := by
    rcases hodd with ⟨r, hr⟩; omega
  obtain ⟨t, ht0, htl, hadjt⟩ := cor21W hG hW hIP hodd h3
    (fun t ht hmem => by
      rcases apexJoin_mem p a h1 h2 ht with hh | ⟨u, hu, hu2⟩
      · rw [hh] at hmem; exact haA hmem
      · rw [hu2] at hmem
        exact hpA u (by rcases hu with ⟨_, h⟩ | ⟨_, h⟩ <;> omega) hmem)
    (by rw [apexJoin_zero]; exact hE1) (by rw [apexJoin_last p a h1 h2]; exact hE2)
    (fun t ht0 htl hx => by
      rcases apexJoin_interior p a h1 h2 ht0 htl with hh | ⟨u, hu, hu2⟩
      · rw [hh] at hx; exact haN hx
      · rw [hu2] at hx; exact hint u hu hx) hv
  rcases apexJoin_interior p a h1 h2 ht0 htl with hh | ⟨u, hu, hu2⟩
  · left; rw [hh] at hadjt; exact hadjt
  · right; rw [hu2] at hadjt; exact ⟨u, hu, hadjt⟩

/-- A vertex adjacent exactly to the two ends of a segment closes it to an even hole. -/
theorem seg_even {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {p : ℕ → V}
    {k : ℕ} (hp : IP G p k) {a : V} (hz : ∀ t, t ≤ k → a ≠ p t) {i j : ℕ} (hij : i + 2 ≤ j)
    (hjk : j ≤ k) (hai : G.Adj a (p i)) (haj : G.Adj a (p j))
    (hmid : ∀ t, i < t → t < j → ¬ G.Adj a (p t)) : Even (j - i) :=
  apex_even hG.1 (hp.sub i j (by omega) hjk) (by omega) a (fun t ht => hz _ (by omega))
    (by simpa using hai) (by simpa [Nat.add_sub_cancel' (by omega : i ≤ j)] using haj)
    (fun t h1 h2 => hmid (i + t) (by omega) (by omega))

/-- The two-vertex path `x, y`. -/
def pair2 (x y : V) : ℕ → V := fun t => if t = 0 then x else y

@[simp] theorem pair2_zero (x y : V) : pair2 x y 0 = x := by simp [pair2]

@[simp] theorem pair2_one (x y : V) : pair2 x y 1 = y := by simp [pair2]

/-- Closing a path `q 0 … q ℓ` by the edge `x y` (with `q ℓ ~ x`, `q 0 ~ y`) gives a hole of
length `ℓ + 3`. -/
theorem close_even {H : SimpleGraph V} (hB : NoOdd H) {q : ℕ → V} {ℓ : ℕ} (hq : IP H q ℓ)
    (hℓ : 1 ≤ ℓ) {x y : V} (hxy : H.Adj x y) (hdx : ∀ t, t ≤ ℓ → q t ≠ x)
    (hdy : ∀ t, t ≤ ℓ → q t ≠ y) (h0y : H.Adj (q 0) y) (hℓx : H.Adj (q ℓ) x)
    (hmx : ∀ t, t < ℓ → ¬ H.Adj (q t) x) (hmy : ∀ t, 0 < t → t ≤ ℓ → ¬ H.Adj (q t) y) :
    Even (ℓ + 3) := by
  have hr : IP H (pair2 x y) 1 := by
    refine ⟨fun i j hi hj hij => ?_, fun i j hi hj => ?_⟩
    · interval_cases i <;> interval_cases j <;> simp_all
    · interval_cases i <;> interval_cases j <;> simp_all [hxy.symm]
  have hd : ∀ i j, i ≤ ℓ → j ≤ 1 → q i ≠ pair2 x y j := by
    intro i j hi hj
    interval_cases j
    · simpa using hdx i hi
    · simpa using hdy i hi
  have hc : ∀ i j, i ≤ ℓ → j ≤ 1 →
      (H.Adj (q i) (pair2 x y j) ↔ ((i = ℓ ∧ j = 0) ∨ (i = 0 ∧ j = 1))) := by
    intro i j hi hj
    interval_cases j
    · simp only [pair2_zero]
      constructor
      · intro hadj
        have : i = ℓ := by by_contra hne; exact hmx i (by omega) hadj
        exact Or.inl ⟨this, trivial⟩
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · rw [h]; exact hℓx
        · omega
    · simp only [pair2_one]
      constructor
      · intro hadj
        have : i = 0 := by by_contra hne; exact hmy i (by omega) hi hadj
        exact Or.inr ⟨this, trivial⟩
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · omega
        · rw [h]; exact h0y
  have := (hole_of_append hq hr hd hc (by omega)).even hB
  have h' : ℓ + 1 + 2 = ℓ + 3 := by omega
  rwa [h'] at this

/-! ## Corollary 2.2 -/

/-- If the number of `A`-complete edges of a path with `A`-complete ends differs in parity from its
length, some segment between consecutive `A`-complete vertices is odd (and has `≥ 3` vertices). -/
theorem odd_seg_exists {G : SimpleGraph V} {A : Finset V} {p : ℕ → V} :
    ∀ n x y, y - x = n → x < y → XC G A (p x) → XC G A (p y) →
      ecnt G A p x y % 2 ≠ (y - x) % 2 →
      ∃ x1 y1, x ≤ x1 ∧ x1 + 2 ≤ y1 ∧ y1 ≤ y ∧ XC G A (p x1) ∧ XC G A (p y1) ∧
        (∀ t, x1 < t → t < y1 → ¬ XC G A (p t)) ∧ (y1 - x1) % 2 = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn hxy hx hy hne
    by_cases hm : ∃ m, x < m ∧ m < y ∧ XC G A (p m)
    · obtain ⟨m, hm1, hm2, hmX⟩ := hm
      rw [ecnt_split G A p hm1.le hm2.le] at hne
      by_cases h1 : ecnt G A p x m % 2 = (m - x) % 2
      · have h2 : ecnt G A p m y % 2 ≠ (y - m) % 2 := by omega
        obtain ⟨x1, y1, a1, a2, a3, a4, a5, a6, a7⟩ :=
          ih (y - m) (by omega) m y rfl hm2 hmX hy h2
        exact ⟨x1, y1, by omega, a2, a3, a4, a5, a6, a7⟩
      · obtain ⟨x1, y1, a1, a2, a3, a4, a5, a6, a7⟩ :=
          ih (m - x) (by omega) x m rfl hm1 hx hmX h1
        exact ⟨x1, y1, a1, a2, by omega, a4, a5, a6, a7⟩
    · push Not at hm
      by_cases h1 : y = x + 1
      · subst h1
        rw [ecnt_one G A p ⟨hx, hy⟩] at hne
        omega
      · have hz : ecnt G A p x y = 0 := by
          apply ecnt_zero
          intro t ht1 ht2 hh
          by_cases hti : t = x
          · subst hti
            exact hm (t + 1) (by omega) (by omega) hh.2
          · exact hm t (by omega) ht2 hh.1
        rw [hz] at hne
        exact ⟨x, y, le_refl _, by omega, le_refl _, hx, hy, fun t h1 h2 => hm t h1 h2, by omega⟩

/-- **Corollary 2.2** for the hole `a, p i, …, p j` (with `a` not `A`-complete): either an even
number of its edges are `A`-complete, or it has exactly one `A`-complete edge and exactly two
`A`-complete vertices. (A hole with every vertex `A`-complete has an even number of complete
edges because it has even length.) -/
theorem cor22 {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {A : Finset V}
    (hW : WH G A) {p : ℕ → V} {k : ℕ} (hp : IP G p k) (hpA : ∀ t, t ≤ k → p t ∉ A) {a : V}
    (haA : a ∉ A) (hz : ∀ t, t ≤ k → a ≠ p t) (haN : ¬ XC G A a) {i j : ℕ} (hij : i + 2 ≤ j)
    (hjk : j ≤ k) (hai : G.Adj a (p i)) (haj : G.Adj a (p j))
    (hmid : ∀ t, i < t → t < j → ¬ G.Adj a (p t)) :
    Even (ecnt G A p i j) ∨ (ecnt G A p i j = 1 ∧ ∃ s, i ≤ s ∧ s + 1 ≤ j ∧ XC G A (p s) ∧
      XC G A (p (s + 1)) ∧ ∀ t, i ≤ t → t ≤ j → XC G A (p t) → (t = s ∨ t = s + 1)) := by
  by_cases hevc : Even (ecnt G A p i j)
  · exact Or.inl hevc
  right
  have hodd : ecnt G A p i j % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hevc)
  have hev : Even (j - i) := seg_even hG hp hz hij hjk hai haj hmid
  have hevn : (j - i) % 2 = 0 := Nat.even_iff.mp hev
  have hadj0 : ∀ t, i ≤ t → t ≤ j → (G.Adj a (p t) ↔ (t = i ∨ t = j)) := by
    intro t h1 h2
    by_cases hti : t = i
    · rw [hti]; exact ⟨fun _ => Or.inl rfl, fun _ => hai⟩
    · by_cases htj : t = j
      · rw [htj]; exact ⟨fun _ => Or.inr rfl, fun _ => haj⟩
      · simp only [hti, htj, or_self, iff_false]
        exact hmid t (by omega) (by omega)
  obtain ⟨s0, hs1, hs2, hs3, hs4⟩ := ecnt_pos G A p hodd
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ :=
    exists_min (P := fun t => XC G A (p t)) (i := i) (j := j) ⟨s0, hs1, by omega, hs3⟩
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ :=
    exists_max (P := fun t => XC G A (p t)) (i := i) (j := j) ⟨s0 + 1, by omega, by omega, hs4⟩
  have hws : w ≤ s0 := by
    by_contra h; exact hw4 s0 hs1 (by omega) hs3
  have hus : s0 + 1 ≤ u := by
    by_contra h; exact hu4 (s0 + 1) (by omega) (by omega) hs4
  have hwu : w < u := by omega
  have e1 : ecnt G A p i w = 0 := ecnt_zero G A p (fun t ht1 ht2 hh => hw4 t ht1 ht2 hh.1)
  have e2 : ecnt G A p u j = 0 :=
    ecnt_zero G A p (fun t ht1 ht2 hh => hu4 (t + 1) (by omega) (by omega) hh.2)
  have hecnt : ecnt G A p i j = ecnt G A p w u := by
    rw [ecnt_split G A p hw1 (by omega : w ≤ j), ecnt_split G A p (by omega : w ≤ u) hu2, e1, e2]
    omega
  have hodd2 : ecnt G A p w u % 2 = 1 := by rw [← hecnt]; exact hodd
  have hnone : ∀ x, w < x → x < u → ¬ XC G A (p x) := by
    intro x hwx hxu hx
    by_cases hpar : (u - w) % 2 = 1
    · -- the segment through `a` is odd
      have hres := apex_cor21 hG hW hp hpA haA hz haN (x1 := u) (y1 := j) (x2 := i) (y2 := w)
        hu2 hjk hw1 (by omega) (Or.inr (by omega))
        (fun t ht hc => by rw [hadj0 t (by omega) (by omega)]; omega)
        (Nat.odd_iff.mpr (by omega)) hu3 hw3
        (fun t ht hxt => by
          rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hu4 t h1 h2 hxt
          · exact hw4 t h1 h2 hxt) hx
      rcases hres with hadj | ⟨t, ht, hadj⟩
      · exact hmid x (by omega) (by omega) hadj.symm
      · rw [hp.adj x t (by omega) (by omega)] at hadj
        omega
    · -- some segment between consecutive complete vertices of `[w, u]` is odd
      have hne : ecnt G A p w u % 2 ≠ (u - w) % 2 := by omega
      obtain ⟨x1, y1, b1, b2, b3, b4, b5, b6, b7⟩ :=
        odd_seg_exists (G := G) (A := A) (p := p) (u - w) w u rfl hwu hw3 hu3 hne
      have hR := hp.sub x1 y1 (by omega) (by omega)
      have hRodd : Odd (y1 - x1) := Nat.odd_iff.mpr b7
      have hside : w < x1 ∨ y1 < u := by
        by_contra hh
        push Not at hh
        exact b6 x (by omega) (by omega) hx
      have hcor : ∀ v, XC G A v → ∃ t, 0 < t ∧ t < y1 - x1 ∧ G.Adj v (p (x1 + t)) := by
        intro v hv
        exact cor21W hG hW hR hRodd (by omega) (fun t ht => hpA _ (by omega))
          (by simpa using b4) (by simpa [Nat.add_sub_cancel' (by omega : x1 ≤ y1)] using b5)
          (fun t h1 h2 => b6 (x1 + t) (by omega) (by omega)) hv
      rcases hside with hh | hh
      · obtain ⟨t, ht1, ht2, ht3⟩ := hcor _ hw3
        rw [hp.adj w (x1 + t) (by omega) (by omega)] at ht3
        omega
      · obtain ⟨t, ht1, ht2, ht3⟩ := hcor _ hu3
        rw [hp.adj u (x1 + t) (by omega) (by omega)] at ht3
        omega
  have huw : u = w + 1 := by
    by_contra hne
    have hz0 : ecnt G A p w u = 0 := by
      apply ecnt_zero
      intro t ht1 ht2 hh
      by_cases htw : t = w
      · subst htw
        exact hnone (t + 1) (by omega) (by omega) hh.2
      · exact hnone t (by omega) ht2 hh.1
    omega
  have hone : ecnt G A p i j = 1 := by
    rw [hecnt, huw]
    exact ecnt_one G A p ⟨hw3, by rw [← huw]; exact hu3⟩
  refine ⟨hone, w, hw1, by omega, hw3, by rw [← huw]; exact hu3, fun t h1 h2 ht => ?_⟩
  by_cases h3 : t < w
  · exact absurd ht (hw4 t h1 h3)
  · by_cases h4 : u < t
    · exact absurd ht (hu4 t h4 h2)
    · by_cases h5 : w < t ∧ t < u
      · exact absurd ht (hnone t h5.1 h5.2)
      · omega

/-! ## Step (2) of the proof: the oriented core -/

theorem step2_core {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X A : Finset V}
    {a : V} (ha : a ∈ X) (haA : a ∉ A) (hAsub : ∀ x ∈ A, x ∈ X)
    (hAX : ∀ v, XC G X v → XC G A v) (hXA : ∀ v, XC G A v → G.Adj v a → XC G X v)
    (hW : WH G A) (haN : ¬ XC G A a) {p : ℕ → V} {k : ℕ} (hp : IP G p k) (hkodd : Odd k)
    (hk5 : 5 ≤ k) (hpX : ∀ t, t ≤ k → p t ∉ X) (h0 : XC G X (p 0)) (hkX : XC G X (p k))
    (hno1 : ∀ t, 0 < t → t < k → ¬ XC G X (p t)) {i j s : ℕ} (hij : i + 2 ≤ j) (hjk : j ≤ k)
    (hai : G.Adj a (p i)) (haj : G.Adj a (p j)) (hmid : ∀ t, i < t → t < j → ¬ G.Adj a (p t))
    (his : i ≤ s) (hsj : s + 1 ≤ j) (hs : XC G A (p s)) (hs1 : XC G A (p (s + 1)))
    (huniq : ∀ t, i ≤ t → t ≤ j → XC G A (p t) → (t = s ∨ t = s + 1))
    (hev : Even (j - i)) (hsodd : Odd (s - i)) :
    XC G A (p (k - 1)) ∧ ∀ t, 0 < t → t < k - 1 → ¬ XC G A (p t) := by
  have hz : ∀ t, t ≤ k → a ≠ p t := fun t ht h => hpX t ht (h ▸ ha)
  have hpA : ∀ t, t ≤ k → p t ∉ A := fun t ht h => hpX t ht (hAsub _ h)
  have hnadj : ∀ t, 0 < t → t < k → XC G A (p t) → ¬ G.Adj a (p t) := by
    intro t h1 h2 hc hadj
    exact hno1 t h1 h2 (hXA _ hc hadj.symm)
  have hA0 : XC G A (p 0) := hAX _ h0
  have hAk : XC G A (p k) := hAX _ hkX
  have hap0 : G.Adj a (p 0) := (h0.2 a ha).symm
  have hapk : G.Adj a (p k) := (hkX.2 a ha).symm
  have hadj0 : ∀ t, i ≤ t → t ≤ j → (G.Adj a (p t) ↔ (t = i ∨ t = j)) := by
    intro t h1 h2
    by_cases hti : t = i
    · rw [hti]; exact ⟨fun _ => Or.inl rfl, fun _ => hai⟩
    · by_cases htj : t = j
      · rw [htj]; exact ⟨fun _ => Or.inr rfl, fun _ => haj⟩
      · simp only [hti, htj, or_self, iff_false]
        exact hmid t (by omega) (by omega)
  have hso : (s - i) % 2 = 1 := Nat.odd_iff.mp hsodd
  have hkoddn : k % 2 = 1 := Nat.odd_iff.mp hkodd
  have hevn : (j - i) % 2 = 0 := Nat.even_iff.mp hev
  have hsi : i + 1 ≤ s := by omega
  -- the A-complete edge sits at the very end of the path
  have hsk : s = k - 1 := by
    by_contra hne
    have hres := apex_cor21 hG hW hp hpA haA hz haN (x1 := k) (y1 := k) (x2 := i) (y2 := s)
      le_rfl le_rfl his (by omega) (Or.inr (by omega))
      (fun t ht hcase => by
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have htk : t = k := by omega
          rw [htk]; exact ⟨fun _ => Or.inl rfl, fun _ => hapk⟩
        · rw [hadj0 t h1 (by omega)]; omega)
      (Nat.odd_iff.mpr (by omega)) hAk hs
      (fun t ht hx => by
        rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · omega
        · have := huniq t h1 (by omega) hx; omega) hs1
    rcases hres with hadj | ⟨t, ht, hadj⟩
    · exact hnadj (s + 1) (by omega) (by omega) hs1 hadj.symm
    · rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · omega
      · rw [hp.adj (s + 1) t (by omega) (by omega)] at hadj
        omega
  have hjk' : j = k := by omega
  -- an A-complete vertex before the segment is adjacent to `p i`
  have hti1 : ∀ t, 0 < t → t < k - 1 → XC G A (p t) → t + 1 = i := by
    intro t ht1 ht2 hx
    have hti : t < i := by
      by_contra hge
      have := huniq t (by omega) (by omega) hx
      omega
    have hres := apex_cor21 hG hW hp hpA haA hz haN (x1 := 0) (y1 := 0) (x2 := i) (y2 := s)
      le_rfl (by omega) his (by omega) (Or.inl (by omega))
      (fun t' ht' hcase => by
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have htk : t' = 0 := by omega
          rw [htk]; exact ⟨fun _ => Or.inl rfl, fun _ => hap0⟩
        · rw [hadj0 t' h1 (by omega)]; omega)
      (Nat.odd_iff.mpr (by omega)) hA0 hs
      (fun t' ht' hx' => by
        rcases ht' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · omega
        · have := huniq t' h1 (by omega) hx'; omega) hx
    rcases hres with hadj | ⟨t', ht', hadj⟩
    · exact absurd hadj.symm (hnadj t ht1 (by omega) hx)
    · rcases ht' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · omega
      · rw [hp.adj t t' (by omega) (by omega)] at hadj
        omega
  have hsx : XC G A (p (k - 1)) := by rw [← hsk]; exact hs
  refine ⟨hsx, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht1, ht2, hx⟩ := hcon
  have hti : t + 1 = i := hti1 t ht1 ht2 hx
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := exists_max (P := fun x => G.Adj a (p x)) (i := 0)
    (j := i - 1) ⟨0, le_refl _, by omega, hap0⟩
  have hqi : q + 2 ≤ i := by
    by_contra hh
    have hqt : q = t := by omega
    rw [hqt] at hq3
    exact hnadj t ht1 (by omega) hx hq3
  have hevq : Even (i - q) :=
    seg_even hG hp hz hqi (by omega) hq3 hai (fun t' h1 h2 => hq4 t' h1 (by omega))
  have hevqn : (i - q) % 2 = 0 := Nat.even_iff.mp hevq
  have hq1' : 1 ≤ q := by omega
  have hres := apex_cor21 hG hW hp hpA haA hz haN (x1 := k) (y1 := k) (x2 := q) (y2 := i - 1)
    le_rfl le_rfl (by omega) (by omega) (Or.inr (by omega))
    (fun t' ht' hcase => by
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have htk : t' = k := by omega
        rw [htk]; exact ⟨fun _ => Or.inl rfl, fun _ => hapk⟩
      · by_cases htq : t' = q
        · rw [htq]; exact ⟨fun _ => Or.inr rfl, fun _ => hq3⟩
        · have hnot : ¬ G.Adj a (p t') := hq4 t' (by omega) h2
          exact ⟨fun h => absurd h hnot, fun h => by omega⟩)
    (Nat.odd_iff.mpr (by omega)) hAk (by have : t = i - 1 := by omega
                                         rw [← this]; exact hx)
    (fun t' ht' hx' => by
      rcases ht' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · omega
      · have := hti1 t' (by omega) (by omega) hx'
        omega) hsx
  rcases hres with hadj | ⟨t', ht', hadj⟩
  · exact hnadj (k - 1) (by omega) (by omega) hsx hadj.symm
  · rcases ht' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · rw [hp.adj (k - 1) t' (by omega) (by omega)] at hadj
      omega

theorem step2_core_rev {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G)
    {X A : Finset V} {a : V} (ha : a ∈ X) (haA : a ∉ A) (hAsub : ∀ x ∈ A, x ∈ X)
    (hAX : ∀ v, XC G X v → XC G A v) (hXA : ∀ v, XC G A v → G.Adj v a → XC G X v)
    (hW : WH G A) (haN : ¬ XC G A a) {p : ℕ → V} {k : ℕ} (hp : IP G p k) (hkodd : Odd k)
    (hk5 : 5 ≤ k) (hpX : ∀ t, t ≤ k → p t ∉ X) (h0 : XC G X (p 0)) (hkX : XC G X (p k))
    (hno1 : ∀ t, 0 < t → t < k → ¬ XC G X (p t)) {i j s : ℕ} (hij : i + 2 ≤ j) (hjk : j ≤ k)
    (hai : G.Adj a (p i)) (haj : G.Adj a (p j)) (hmid : ∀ t, i < t → t < j → ¬ G.Adj a (p t))
    (his : i ≤ s) (hsj : s + 1 ≤ j) (hs : XC G A (p s)) (hs1 : XC G A (p (s + 1)))
    (huniq : ∀ t, i ≤ t → t ≤ j → XC G A (p t) → (t = s ∨ t = s + 1))
    (hev : Even (j - i)) (hsodd : Odd (j - s - 1)) :
    XC G A (p 1) ∧ ∀ t, 1 < t → t < k → ¬ XC G A (p t) := by
  have key := step2_core hG ha haA hAsub hAX hXA hW haN (p := fun t => p (k - t)) hp.rev hkodd hk5
    (fun t ht => hpX _ (by omega)) (by simpa using hkX) (by simpa using h0)
    (fun t h1 h2 => hno1 (k - t) (by omega) (by omega)) (i := k - j) (j := k - i)
    (s := k - s - 1) (by omega) (by omega)
    (by simpa [Nat.sub_sub_self (by omega : j ≤ k)] using haj)
    (by simpa [Nat.sub_sub_self (by omega : i ≤ k)] using hai)
    (fun t h1 h2 => hmid (k - t) (by omega) (by omega)) (by omega) (by omega)
    (by
      have : k - (k - s - 1) = s + 1 := by omega
      simp only [this]; exact hs1)
    (by
      have : k - (k - s - 1 + 1) = s := by omega
      simp only [this]; exact hs)
    (fun t h1 h2 hx => by
      have := huniq (k - t) (by omega) (by omega) hx
      omega)
    (by have : k - i - (k - j) = j - i := by omega
        rw [this]; exact hev)
    (by have : k - s - 1 - (k - j) = j - s - 1 := by omega
        rw [this]; exact hsodd)
  have hk1 : k - (k - 1) = 1 := by omega
  refine ⟨by simpa [hk1] using key.1, fun t h1 h2 hx => key.2 (k - t) (by omega) (by omega) ?_⟩
  have : k - (k - t) = t := by omega
  simp only [this]; exact hx

/-! ## Step (2) of the proof for a single vertex `a` -/

theorem step2 {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X A : Finset V}
    {a : V} (ha : a ∈ X) (haA : a ∉ A) (hAsub : ∀ x ∈ A, x ∈ X)
    (hAX : ∀ v, XC G X v → XC G A v) (hXA : ∀ v, XC G A v → G.Adj v a → XC G X v)
    (hW : WH G A) (haN : ¬ XC G A a) {p : ℕ → V} {k : ℕ} (hp : IP G p k) (hkodd : Odd k)
    (hk5 : 5 ≤ k) (hpX : ∀ t, t ≤ k → p t ∉ X) (h0 : XC G X (p 0)) (hkX : XC G X (p k))
    (hno1 : ∀ t, 0 < t → t < k → ¬ XC G X (p t)) :
    (∃ b c, Leap G X p k b c) ∨
    (XC G A (p 1) ∧ ∀ t, 1 < t → t < k → ¬ XC G A (p t)) ∨
    (XC G A (p (k - 1)) ∧ ∀ t, 0 < t → t < k - 1 → ¬ XC G A (p t)) := by
  have hz : ∀ t, t ≤ k → a ≠ p t := fun t ht h => hpX t ht (h ▸ ha)
  have hpA : ∀ t, t ≤ k → p t ∉ A := fun t ht h => hpX t ht (hAsub _ h)
  have hA0 : XC G A (p 0) := hAX _ h0
  have hAk : XC G A (p k) := hAX _ hkX
  have hap0 : G.Adj a (p 0) := (h0.2 a ha).symm
  have hapk : G.Adj a (p k) := (hkX.2 a ha).symm
  have hkoddn : k % 2 = 1 := Nat.odd_iff.mp hkodd
  by_cases hex : ∃ t, 0 < t ∧ t < k ∧ XC G A (p t)
  · right
    obtain ⟨m, hm0, hmk, hm⟩ := hex
    have hodd : ecnt G A p 0 k % 2 = 1 := by
      have := cor23 hG hW hp hpA hA0 hAk m hm0 hmk hm
      omega
    obtain ⟨i, j, hi1, hij, hjk, hIi, hIj, hmid, hodd'⟩ :=
      seg_exists (G := G) (A := A) (p := p) (fun t => G.Adj a (p t)) k
        (fun t ht ⟨c1, c2, c3, c4⟩ => by
          have e1 : XC G X (p t) := hXA _ c1 c3.symm
          have e2 : XC G X (p (t + 1)) := hXA _ c2 c4.symm
          by_cases ht0 : t = 0
          · subst ht0; exact hno1 1 (by omega) (by omega) e2
          · exact hno1 t (by omega) ht e1)
        (k - 0) 0 k rfl (Nat.zero_le _) le_rfl hap0 hapk hodd
    have hev : Even (j - i) := seg_even hG hp hz (by omega) hjk hIi hIj (fun t h1 h2 => hmid t h1 h2)
    obtain ⟨_, s, his, hsj, hs, hs1, huniq⟩ : ecnt G A p i j = 1 ∧ ∃ s, i ≤ s ∧ s + 1 ≤ j ∧
        XC G A (p s) ∧ XC G A (p (s + 1)) ∧
        ∀ t, i ≤ t → t ≤ j → XC G A (p t) → (t = s ∨ t = s + 1) := by
      rcases cor22 hG hW hp hpA haA hz haN (by omega) hjk hIi hIj
        (fun t h1 h2 => hmid t h1 h2) with hE | hE
      · exfalso
        have := Nat.even_iff.mp hE
        omega
      · exact hE
    have hevn : (j - i) % 2 = 0 := Nat.even_iff.mp hev
    by_cases hso : (s - i) % 2 = 1
    · exact Or.inr (step2_core hG ha haA hAsub hAX hXA hW haN hp hkodd hk5 hpX h0 hkX hno1
        hij hjk hIi hIj (fun t h1 h2 => hmid t h1 h2) his hsj hs hs1 huniq hev
        (Nat.odd_iff.mpr hso))
    · exact Or.inl (step2_core_rev hG ha haA hAsub hAX hXA hW haN hp hkodd hk5 hpX h0 hkX hno1
        hij hjk hIi hIj (fun t h1 h2 => hmid t h1 h2) his hsj hs hs1 huniq hev
        (Nat.odd_iff.mpr (by omega)))
  · left
    push Not at hex
    have hout := hW k p hp hkodd hpA hA0 hAk
    rcases hout with ⟨i, hik, c1, c2⟩ | ⟨_, b, c, hl⟩ | ⟨hk3, _⟩
    · by_cases hi0 : i = 0
      · subst hi0; exact absurd c2 (hex 1 (by omega) (by omega))
      · exact absurd c1 (hex i (by omega) hik)
    · exact ⟨b, c, hAsub _ hl.1, hAsub _ hl.2.1, hl.2.2⟩
    · omega


/-! ## Base cases and the reduction (1) -/

/-- `|X| = 1`: the first outcome holds because `G` has no odd hole. -/
theorem case_single {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) (x : V) :
    WH G {x} := by
  intro k p hp hkodd hpX h0 hkX
  refine Or.inl ?_
  by_contra hno
  push Not at hno
  have hz : ∀ t, t ≤ k → x ≠ p t := fun t ht h =>
    hpX t ht (by rw [← h]; exact Finset.mem_singleton_self x)
  have hadj0 : G.Adj x (p 0) := (h0.2 x (Finset.mem_singleton_self x)).symm
  have key : ∀ t, t ≤ k → G.Adj x (p t) → Even t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro htk hadj
      by_cases ht0 : t = 0
      · rw [ht0]; exact ⟨0, rfl⟩
      · obtain ⟨q, hq1, hq2, hq3, hq4⟩ := exists_max (P := fun r => G.Adj x (p r)) (i := 0)
          (j := t - 1) ⟨0, le_refl _, by omega, hadj0⟩
        have hqt : q + 2 ≤ t := by
          by_contra hh
          have hqe : q + 1 = t := by omega
          apply hno q (by omega)
          · exact ⟨hpX q (by omega), fun y hy => by
              rw [Finset.mem_singleton.mp hy]; exact hq3.symm⟩
          · rw [hqe]
            exact ⟨hpX t htk, fun y hy => by rw [Finset.mem_singleton.mp hy]; exact hadj.symm⟩
        have he1 := seg_even hG hp hz hqt htk hq3 hadj (fun r h1 h2 => hq4 r h1 (by omega))
        have he2 := ih q (by omega) (by omega) hq3
        have h1' := Nat.even_iff.mp he1
        have h2' := Nat.even_iff.mp he2
        exact Nat.even_iff.mpr (by omega)
  have := key k le_rfl (hkX.2 x (Finset.mem_singleton_self x)).symm
  exact (Nat.not_even_iff_odd.mpr hkodd) this

/-- Step (1): an `X`-complete interior vertex splits `P` into a shorter odd path. -/
theorem reduce_step {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X : Finset V}
    {k : ℕ} (hkodd : Odd k) {p : ℕ → V} (hp : IP G p k) (hpX : ∀ t, t ≤ k → p t ∉ X)
    (h0 : XC G X (p 0)) (hkX : XC G X (p k))
    (IHk : ∀ k' < k, ∀ p' : ℕ → V, IP G p' k' → Odd k' → (∀ t, t ≤ k' → p' t ∉ X) →
      XC G X (p' 0) → XC G X (p' k') → Outcome G X p' k')
    {m : ℕ} (hm0 : 0 < m) (hmk : m < k) (hm : XC G X (p m)) : Outcome G X p k := by
  by_cases hmo : Odd m
  · have hR := hp.sub 0 m (Nat.zero_le _) hmk.le
    by_cases hE : ∃ t, t < m - 0 ∧ XC G X (p (0 + t)) ∧ XC G X (p (0 + (t + 1)))
    · obtain ⟨t, ht, c1, c2⟩ := hE
      exact Or.inl ⟨t, by omega, by simpa using c1, by simpa using c2⟩
    · have hmo' : Odd (m - 0) := by simpa using hmo
      have hout := IHk (m - 0) (by omega) _ hR hmo' (fun t ht => hpX _ (by omega))
        (by simpa using h0) (by simpa using hm)
      obtain ⟨t, ht1, ht2, ht3⟩ := cor21 hG hR hmo' (fun t ht => hpX _ (by omega)) hE hout hkX
      have h' : G.Adj (p k) (p (0 + t)) := ht3
      rw [hp.adj k (0 + t) (by omega) (by omega)] at h'
      omega
  · have hko : Odd (k - m) := by
      rw [Nat.odd_iff] at hkodd ⊢
      have := Nat.even_iff.mpr (Nat.not_odd_iff.mp hmo)
      have h2 := Nat.even_iff.mp this
      omega
    have hR := hp.sub m k hmk.le le_rfl
    by_cases hE : ∃ t, t < k - m ∧ XC G X (p (m + t)) ∧ XC G X (p (m + (t + 1)))
    · obtain ⟨t, ht, c1, c2⟩ := hE
      refine Or.inl ⟨m + t, by omega, c1, ?_⟩
      have : m + (t + 1) = m + t + 1 := by omega
      rw [← this]; exact c2
    · have hout := IHk (k - m) (by omega) _ hR hko (fun t ht => hpX _ (by omega))
        (by simpa using hm) (by simpa [Nat.add_sub_cancel' hmk.le] using hkX)
      obtain ⟨t, ht1, ht2, ht3⟩ := cor21 hG hR hko (fun t ht => hpX _ (by omega)) hE hout h0
      have h' : G.Adj (p 0) (p (m + t)) := ht3
      rw [hp.adj 0 (m + t) (by omega) (by omega)] at h'
      omega

/-- The case `k = 3`. -/
theorem case_three {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X : Finset V}
    (hX : AC G X) {p : ℕ → V} (hp : IP G p 3) (hpX : ∀ t, t ≤ 3 → p t ∉ X)
    (h0 : XC G X (p 0)) (h3 : XC G X (p 3)) : Outcome G X p 3 := by
  classical
  by_cases hv1 : XC G X (p 1)
  · exact Or.inl ⟨0, by omega, h0, hv1⟩
  by_cases hv2 : XC G X (p 2)
  · exact Or.inl ⟨2, by omega, hv2, h3⟩
  refine Or.inr (Or.inr ⟨rfl, ?_⟩)
  have hx1 : ∃ x ∈ X, ¬ G.Adj (p 1) x := by
    by_contra hh; push Not at hh; exact hv1 ⟨hpX 1 (by omega), hh⟩
  have hx2 : ∃ y ∈ X, ¬ G.Adj (p 2) y := by
    by_contra hh; push Not at hh; exact hv2 ⟨hpX 2 (by omega), hh⟩
  obtain ⟨x, hx, hnx⟩ := hx1
  obtain ⟨y, hy, hny⟩ := hx2
  have hsubT : X ⊆ insert (p 1) (insert (p 2) X) := fun z hz => by simp [hz]
  have hxT : x ∈ insert (p 1) (insert (p 2) X) := hsubT hx
  have hyT : y ∈ insert (p 1) (insert (p 2) X) := hsubT hy
  have hp1T : p 1 ∈ insert (p 1) (insert (p 2) X) := Finset.mem_insert_self _ _
  have hp2T : p 2 ∈ insert (p 1) (insert (p 2) X) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hr : (Hgraph Gᶜ (insert (p 1) (insert (p 2) X))).Reachable (p 1) (p 2) := by
    have e1 : (Hgraph Gᶜ (insert (p 1) (insert (p 2) X))).Adj (p 1) x :=
      ⟨(SimpleGraph.compl_adj G _ _).mpr
        ⟨fun h => hpX 1 (by omega) (by rw [h]; exact hx), hnx⟩, hp1T, hxT⟩
    have e3 : (Hgraph Gᶜ (insert (p 1) (insert (p 2) X))).Adj y (p 2) :=
      ⟨(SimpleGraph.compl_adj G _ _).mpr
        ⟨fun h => hpX 2 (by omega) (by rw [← h]; exact hy), fun hadj => hny hadj.symm⟩, hyT, hp2T⟩
    exact e1.reachable.trans ((reach_mono Gᶜ hsubT (hX.2 x hx y hy)).trans e3.reachable)
  obtain ⟨ℓ, q, hq, hq0, hqℓ, hqT⟩ := exists_induced_path Gᶜ _ hp1T hp2T hr
  have hℓ1 : 1 ≤ ℓ := by
    by_contra hh
    have h' : ℓ = 0 := by omega
    rw [h', hq0] at hqℓ
    have := hp.inj 1 2 (by omega) (by omega) hqℓ
    omega
  have hint : ∀ t, 0 < t → t < ℓ → q t ∈ X := by
    intro t h1 h2
    have hm := hqT t (by omega)
    simp only [Finset.mem_insert] at hm
    rcases hm with hm | hm | hm
    · exfalso
      have := hq.inj t 0 (by omega) (by omega) (by rw [hm, hq0]); omega
    · exfalso
      have := hq.inj t ℓ (by omega) (by omega) (by rw [hm, hqℓ]); omega
    · exact hm
  have hne : ∀ r, r ≤ 3 → r ≠ 1 → r ≠ 2 → ∀ t, t ≤ ℓ → q t ≠ p r := by
    intro r hr1 h1 h2 t ht h
    by_cases ht0 : t = 0
    · rw [ht0, hq0] at h
      have := hp.inj 1 r (by omega) hr1 h; omega
    · by_cases htl : t = ℓ
      · rw [htl, hqℓ] at h
        have := hp.inj 2 r (by omega) hr1 h; omega
      · exact hpX r hr1 (by rw [← h]; exact hint t (by omega) (by omega))
  have hxy : Gᶜ.Adj (p 0) (p 3) := (SimpleGraph.compl_adj G _ _).mpr
    ⟨fun h => by have := hp.inj 0 3 (by omega) (by omega) h; omega,
     fun h => by rw [hp.adj 0 3 (by omega) (by omega)] at h; omega⟩
  have h0y : Gᶜ.Adj (q 0) (p 3) := by
    rw [hq0]
    exact (SimpleGraph.compl_adj G _ _).mpr
      ⟨fun h => by have := hp.inj 1 3 (by omega) (by omega) h; omega,
       fun h => by rw [hp.adj 1 3 (by omega) (by omega)] at h; omega⟩
  have hℓx : Gᶜ.Adj (q ℓ) (p 0) := by
    rw [hqℓ]
    exact (SimpleGraph.compl_adj G _ _).mpr
      ⟨fun h => by have := hp.inj 2 0 (by omega) (by omega) h; omega,
       fun h => by rw [hp.adj 2 0 (by omega) (by omega)] at h; omega⟩
  have hmx : ∀ t, t < ℓ → ¬ Gᶜ.Adj (q t) (p 0) := fun t ht hh => by
    by_cases ht0 : t = 0
    · rw [ht0, hq0] at hh
      exact hh.2 ((hp.adj 1 0 (by omega) (by omega)).mpr (Or.inr rfl))
    · exact hh.2 (h0.2 (q t) (hint t (by omega) ht)).symm
  have hmy : ∀ t, 0 < t → t ≤ ℓ → ¬ Gᶜ.Adj (q t) (p 3) := fun t ht1 ht2 hh => by
    by_cases htl : t = ℓ
    · rw [htl, hqℓ] at hh
      exact hh.2 ((hp.adj 2 3 (by omega) (by omega)).mpr (Or.inl rfl))
    · exact hh.2 (h3.2 (q t) (hint t ht1 (by omega))).symm
  have hev : Even (ℓ + 3) := close_even hG.2 hq hℓ1 hxy
    (hne 0 (by omega) (by omega) (by omega)) (hne 3 (by omega) (by omega) (by omega))
    h0y hℓx hmx hmy
  refine ⟨ℓ, q, hq, Nat.odd_iff.mpr (by have := Nat.even_iff.mp hev; omega), hq0, hqℓ, hint⟩

/-! ## The final stage for `|X| = 2` -/

theorem leap_pair {G : SimpleGraph V} [DecidableEq V] {X : Finset V} {a b : V} (ha : a ∈ X)
    (hb : b ∈ X) (hab : a ≠ b) (hX2 : ∀ x ∈ X, x = a ∨ x = b) (hnadj : ¬ G.Adj a b)
    {p : ℕ → V} {k : ℕ} (hk5 : 5 ≤ k) (hpX : ∀ t, t ≤ k → p t ∉ X) (h0 : XC G X (p 0))
    (hkX : XC G X (p k))
    (S1 : XC G (X.erase a) (p 1) ∧ ∀ t, 1 < t → t < k → ¬ XC G (X.erase a) (p t))
    (S2 : XC G (X.erase b) (p (k - 1)) ∧ ∀ t, 0 < t → t < k - 1 → ¬ XC G (X.erase b) (p t)) :
    Leap G X p k b a := by
  have hA : ∀ x ∈ X.erase a, x = b := fun x hx => by
    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hx
    rcases hX2 x h2 with h | h
    · exact absurd h h1
    · exact h
  have hB : ∀ x ∈ X.erase b, x = a := fun x hx => by
    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hx
    rcases hX2 x h2 with h | h
    · exact h
    · exact absurd h h1
  refine ⟨hb, ha, hab.symm, fun h => hnadj h.symm, fun i hi => ?_, fun i hi => ?_⟩
  · constructor
    · intro hadj
      by_contra hne
      push Not at hne
      apply S1.2 i (by omega) (by omega)
      refine ⟨fun hmem => hpX i hi (Finset.mem_of_mem_erase hmem), fun x hx => ?_⟩
      rw [hA x hx]; exact hadj.symm
    · rintro (h | h | h)
      · rw [h]; exact (h0.2 b hb).symm
      · rw [h]; exact (S1.1.2 b (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)).symm
      · rw [h]; exact (hkX.2 b hb).symm
  · constructor
    · intro hadj
      by_contra hne
      push Not at hne
      apply S2.2 i (by omega) (by omega)
      refine ⟨fun hmem => hpX i hi (Finset.mem_of_mem_erase hmem), fun x hx => ?_⟩
      rw [hB x hx]; exact hadj.symm
    · rintro (h | h | h)
      · rw [h]; exact (h0.2 a ha).symm
      · have : i = k - 1 := by omega
        rw [this]; exact (S2.1.2 a (Finset.mem_erase.mpr ⟨hab, ha⟩)).symm
      · rw [h]; exact (hkX.2 a ha).symm

/-! ## The final stage for `|X| ≥ 3` -/

theorem final_ge3 {G : SimpleGraph V} [DecidableEq V] (hG : StrongPerfectGraph.Main.IsBerge G)
    {X : Finset V} (hX : AC G X) (IHX : ∀ A : Finset V, A.card < X.card → AC G A → WH G A)
    {a c : V} (ha : a ∈ X) (hc : c ∈ X) (hac : a ≠ c) (hadjac : G.Adj a c)
    (hCAC : AC G ((X.erase a).erase c)) {k : ℕ} (hk5 : 5 ≤ k) (hkodd : Odd k) {p : ℕ → V}
    (hp : IP G p k) (hpX : ∀ t, t ≤ k → p t ∉ X) (h0 : XC G X (p 0)) (hkX : XC G X (p k))
    (hno1 : ∀ t, 0 < t → t < k → ¬ XC G X (p t))
    (S1 : XC G (X.erase a) (p 1) ∧ ∀ t, 1 < t → t < k → ¬ XC G (X.erase a) (p t))
    (S2 : XC G (X.erase c) (p (k - 1)) ∧ ∀ t, 0 < t → t < k - 1 → ¬ XC G (X.erase c) (p t)) :
    False := by
  have hCcard : ((X.erase a).erase c).card < X.card :=
    lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem ha)
  have hWC : WH G ((X.erase a).erase c) := IHX _ hCcard hCAC
  have hCsubX : ∀ z ∈ (X.erase a).erase c, z ∈ X := fun z hz =>
    (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
  obtain ⟨ℓ, q, hq, hq0, hqℓ, hqX⟩ := exists_induced_path Gᶜ X ha hc (hX.2 a ha c hc)
  have hℓ2 : 2 ≤ ℓ := by
    by_contra hh
    have hℓ' : ℓ = 0 ∨ ℓ = 1 := by omega
    rcases hℓ' with h | h
    · rw [h, hq0] at hqℓ; exact hac hqℓ
    · rw [h] at hqℓ
      have := (hq.adj 0 1 (by omega) (by omega)).mpr (Or.inl rfl)
      rw [hq0, hqℓ] at this
      exact this.2 hadjac
  have hne_c : ∀ t, t < ℓ → q t ≠ c := fun t ht h => by
    have := hq.inj t ℓ (by omega) le_rfl (by rw [h, hqℓ]); omega
  have hne_a : ∀ t, 0 < t → t ≤ ℓ → q t ≠ a := fun t ht htl h => by
    have := hq.inj t 0 (by omega) (by omega) (by rw [h, hq0]); omega
  have hqC : ∀ t, 0 < t → t < ℓ → q t ∈ (X.erase a).erase c := fun t h1 h2 =>
    Finset.mem_erase.mpr ⟨hne_c t h2, Finset.mem_erase.mpr ⟨hne_a t h1 (by omega), hqX t (by omega)⟩⟩
  have hp1a : ¬ G.Adj (p 1) a := fun h => hno1 1 (by omega) (by omega) (XC.of_erase S1.1 h)
  have hpkc : ¬ G.Adj (p (k - 1)) c := fun h =>
    hno1 (k - 1) (by omega) (by omega) (XC.of_erase S2.1 h)
  -- closing `Q` with the edge `p (k-1) p 1` of the complement gives a hole of length `ℓ + 3`
  have hxy : Gᶜ.Adj (p (k - 1)) (p 1) := (SimpleGraph.compl_adj G _ _).mpr
    ⟨fun h => by have := hp.inj _ _ (by omega) (by omega) h; omega,
     fun h => by rw [hp.adj _ _ (by omega) (by omega)] at h; omega⟩
  have h0y : Gᶜ.Adj (q 0) (p 1) := by
    rw [hq0]
    exact (SimpleGraph.compl_adj G _ _).mpr
      ⟨fun h => hpX 1 (by omega) (by rw [← h]; exact ha), fun h => hp1a h.symm⟩
  have hℓx : Gᶜ.Adj (q ℓ) (p (k - 1)) := by
    rw [hqℓ]
    exact (SimpleGraph.compl_adj G _ _).mpr
      ⟨fun h => hpX (k - 1) (by omega) (by rw [← h]; exact hc), fun h => hpkc h.symm⟩
  have hmx : ∀ t, t < ℓ → ¬ Gᶜ.Adj (q t) (p (k - 1)) := fun t ht hh =>
    hh.2 (S2.1.2 (q t) (Finset.mem_erase.mpr ⟨hne_c t ht, hqX t (by omega)⟩)).symm
  have hmy : ∀ t, 0 < t → t ≤ ℓ → ¬ Gᶜ.Adj (q t) (p 1) := fun t ht1 ht2 hh =>
    hh.2 (S1.1.2 (q t) (Finset.mem_erase.mpr ⟨hne_a t ht1 ht2, hqX t ht2⟩)).symm
  have hev1 : Even (ℓ + 3) := close_even hG.2 hq (by omega) hxy
    (fun t ht h => hpX (k - 1) (by omega) (by rw [← h]; exact hqX t ht))
    (fun t ht h => hpX 1 (by omega) (by rw [← h]; exact hqX t ht))
    h0y hℓx hmx hmy
  -- a `C`-complete vertex inside the path `p 1 … p (k-1)`
  have hR := hp.sub 1 (k - 1) (by omega) (by omega)
  have hodd' : Odd (k - 1 - 1) := by
    rw [Nat.odd_iff] at hkodd ⊢; omega
  have hCsub1 : (X.erase a).erase c ⊆ X.erase a := Finset.erase_subset _ _
  have hCsub2 : (X.erase a).erase c ⊆ X.erase c := fun z hz =>
    Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1, hCsubX z hz⟩
  have hpC : ∀ t, t ≤ k - 1 - 1 → p (1 + t) ∉ (X.erase a).erase c := fun t ht hmem =>
    hpX (1 + t) (by omega) (hCsubX _ hmem)
  have hout := hWC (k - 1 - 1) (fun t => p (1 + t)) hR hodd' hpC
    (by simpa using S1.1.mono hCsub1)
    (by
      have : 1 + (k - 1 - 1) = k - 1 := by omega
      simp only [this]; exact S2.1.mono hCsub2)
  have hE : ∃ t, t < k - 1 - 1 ∧ XC G ((X.erase a).erase c) (p (1 + t)) ∧
      XC G ((X.erase a).erase c) (p (1 + (t + 1))) := by
    by_contra hE
    obtain ⟨t, ht1, ht2, ht3⟩ := cor21 hG hR hodd' hpC hE hout
      (h0.mono (fun z hz => hCsubX z hz))
    have h' : G.Adj (p 0) (p (1 + t)) := ht3
    rw [hp.adj 0 (1 + t) (by omega) (by omega)] at h'
    omega
  obtain ⟨t, ht, c1, c2⟩ := hE
  have hρ : ∃ ρ, 2 ≤ ρ ∧ ρ ≤ k - 2 ∧ XC G ((X.erase a).erase c) (p ρ) := by
    by_cases ht1 : 1 ≤ t
    · exact ⟨1 + t, by omega, by omega, c1⟩
    · exact ⟨1 + (t + 1), by omega, by omega, c2⟩
  obtain ⟨ρ, hρ1, hρ2, hρC⟩ := hρ
  have hρnc : ¬ G.Adj (p ρ) c := fun h => S1.2 ρ (by omega) (by omega) (XC.of_erase hρC h)
  have hρna : ¬ G.Adj (p ρ) a := by
    intro h
    apply S2.2 ρ (by omega) (by omega)
    have hρC' := hρC
    rw [Finset.erase_right_comm] at hρC'
    exact XC.of_erase hρC' h
  have hz0 : Gᶜ.Adj (p ρ) (q 0) := by
    rw [hq0]
    exact (SimpleGraph.compl_adj G _ _).mpr
      ⟨fun h => hpX ρ (by omega) (by rw [h]; exact ha), hρna⟩
  have hzl : Gᶜ.Adj (p ρ) (q ℓ) := by
    rw [hqℓ]
    exact (SimpleGraph.compl_adj G _ _).mpr
      ⟨fun h => hpX ρ (by omega) (by rw [h]; exact hc), hρnc⟩
  have hev2 : Even ℓ := apex_even hG.2 hq hℓ2 (p ρ)
    (fun t ht h => hpX ρ (by omega) (by rw [h]; exact hqX t ht)) hz0 hzl
    (fun t h1 h2 hh => hh.2 (hρC.2 (q t) (hqC t h1 h2)))
  have e1 := Nat.even_iff.mp hev1
  have e2 := Nat.even_iff.mp hev2
  omega

/-! ## The inductive step for `|X| ≥ 2` and `k ≥ 5` -/

theorem main_step {G : SimpleGraph V} [DecidableEq V] (hG : StrongPerfectGraph.Main.IsBerge G)
    {X : Finset V} (hX : AC G X) (IHX : ∀ A : Finset V, A.card < X.card → AC G A → WH G A)
    (h2 : 2 ≤ X.card) {k : ℕ} (hk5 : 5 ≤ k) (hkodd : Odd k) {p : ℕ → V} (hp : IP G p k)
    (hpX : ∀ t, t ≤ k → p t ∉ X) (h0 : XC G X (p 0)) (hkX : XC G X (p k))
    (hno1 : ∀ t, 0 < t → t < k → ¬ XC G X (p t)) : Outcome G X p k := by
  by_cases hL : ∃ b c, Leap G X p k b c
  · exact Or.inr (Or.inl ⟨hk5, hL⟩)
  exfalso
  have hS : ∀ a ∈ X, AC G (X.erase a) →
      (XC G (X.erase a) (p 1) ∧ ∀ t, 1 < t → t < k → ¬ XC G (X.erase a) (p t)) ∨
      (XC G (X.erase a) (p (k - 1)) ∧ ∀ t, 0 < t → t < k - 1 → ¬ XC G (X.erase a) (p t)) := by
    intro a ha hA
    have hW : WH G (X.erase a) := IHX _ (Finset.card_erase_lt_of_mem ha) hA
    obtain ⟨b, hb, hba⟩ : ∃ b ∈ X, b ≠ a := Finset.exists_mem_ne (by omega : 1 < X.card) a
    obtain ⟨n, hn, hna, hnadj⟩ := hX.exists_nbr ha hb hba.symm
    have haN : ¬ XC G (X.erase a) a := fun h =>
      hnadj.2 (h.2 n (Finset.mem_erase.mpr ⟨hna, hn⟩))
    rcases step2 hG ha (Finset.notMem_erase a X) (fun x hx => Finset.mem_of_mem_erase hx)
      (fun v hv => XC.erase_of hv) (fun v hv hva => XC.of_erase hv hva) hW haN hp hkodd hk5 hpX
      h0 hkX hno1 with h | h | h
    · exact absurd h hL
    · exact Or.inl h
    · exact Or.inr h
  have noS1 : ∀ a ∈ X, ∀ c ∈ X, a ≠ c →
      ¬ (XC G (X.erase a) (p 1) ∧ XC G (X.erase c) (p 1)) := by
    rintro a ha c hc hac ⟨h1, h2'⟩
    apply hno1 1 (by omega) (by omega)
    refine ⟨hpX 1 (by omega), fun x hx => ?_⟩
    by_cases hxa : x = a
    · rw [hxa]; exact h2'.2 a (Finset.mem_erase.mpr ⟨hac, ha⟩)
    · exact h1.2 x (Finset.mem_erase.mpr ⟨hxa, hx⟩)
  have noS2 : ∀ a ∈ X, ∀ c ∈ X, a ≠ c →
      ¬ (XC G (X.erase a) (p (k - 1)) ∧ XC G (X.erase c) (p (k - 1))) := by
    rintro a ha c hc hac ⟨h1, h2'⟩
    apply hno1 (k - 1) (by omega) (by omega)
    refine ⟨hpX (k - 1) (by omega), fun x hx => ?_⟩
    by_cases hxa : x = a
    · rw [hxa]; exact h2'.2 a (Finset.mem_erase.mpr ⟨hac, ha⟩)
    · exact h1.2 x (Finset.mem_erase.mpr ⟨hxa, hx⟩)
  by_cases h3 : 3 ≤ X.card
  · obtain ⟨a, ha, c, hc, hac, hAa, hAc, hnadj, hC⟩ := AC.good_pair hX h3 (by
      intro a1 e1 a2 e2 a3 e3 n12 n13 n23 A1 A2 A3
      have s1 := hS a1 e1 A1
      have s2 := hS a2 e2 A2
      have s3 := hS a3 e3 A3
      rcases s1 with s1 | s1 <;> rcases s2 with s2 | s2 <;> rcases s3 with s3 | s3 <;>
      first
        | exact noS1 a1 e1 a2 e2 n12 ⟨s1.1, s2.1⟩
        | exact noS1 a1 e1 a3 e3 n13 ⟨s1.1, s3.1⟩
        | exact noS1 a2 e2 a3 e3 n23 ⟨s2.1, s3.1⟩
        | exact noS2 a1 e1 a2 e2 n12 ⟨s1.1, s2.1⟩
        | exact noS2 a1 e1 a3 e3 n13 ⟨s1.1, s3.1⟩
        | exact noS2 a2 e2 a3 e3 n23 ⟨s2.1, s3.1⟩)
    have hadjac : G.Adj a c := by
      by_contra hh
      exact hnadj ((SimpleGraph.compl_adj G a c).mpr ⟨hac, hh⟩)
    rcases hS a ha hAa with sa | sa <;> rcases hS c hc hAc with sc | sc
    · exact noS1 a ha c hc hac ⟨sa.1, sc.1⟩
    · exact final_ge3 hG hX IHX ha hc hac hadjac hC hk5 hkodd hp hpX h0 hkX hno1 sa sc
    · exact final_ge3 hG hX IHX hc ha hac.symm hadjac.symm (by rwa [Finset.erase_right_comm])
        hk5 hkodd hp hpX h0 hkX hno1 sc sa
    · exact noS2 a ha c hc hac ⟨sa.1, sc.1⟩
  · have h2' : X.card = 2 := by omega
    obtain ⟨x, y, hxy, hXe⟩ := Finset.card_eq_two.mp h2'
    have hxX : x ∈ X := by rw [hXe]; simp
    have hyX : y ∈ X := by rw [hXe]; simp
    have ex : X.erase x = {y} := by
      rw [hXe, Finset.erase_insert (by simpa using hxy)]
    have ey : X.erase y = {x} := by
      rw [hXe, Finset.pair_comm, Finset.erase_insert (by simpa using hxy.symm)]
    have hAx : AC G (X.erase x) := by rw [ex]; exact AC.of_subsingleton G y
    have hAy : AC G (X.erase y) := by rw [ey]; exact AC.of_subsingleton G x
    have hX2 : ∀ z ∈ X, z = x ∨ z = y := fun z hz => by
      rw [hXe] at hz; simpa using hz
    have hnadj : ¬ G.Adj x y := by
      have := AC.pair_compl hxy (by rw [← hXe]; exact hX)
      exact this.2
    rcases hS x hxX hAx with sx | sx <;> rcases hS y hyX hAy with sy | sy
    · exact noS1 x hxX y hyX hxy ⟨sx.1, sy.1⟩
    · exact hL ⟨y, x, leap_pair hxX hyX hxy hX2 hnadj hk5 hpX h0 hkX sx sy⟩
    · exact hL ⟨x, y, leap_pair hyX hxX hxy.symm (fun z hz => (hX2 z hz).symm)
        (fun h => hnadj h.symm) hk5 hpX h0 hkX sy sx⟩
    · exact noS2 x hxX y hyX hxy ⟨sx.1, sy.1⟩

/-! ## The Wonderful Lemma -/

theorem wonderful_gen {G : SimpleGraph V} [DecidableEq V] (hG : StrongPerfectGraph.Main.IsBerge G) :
    ∀ (m : ℕ) (X : Finset V), X.card = m → AC G X → WH G X := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro X hm hX
    have IHX : ∀ A : Finset V, A.card < X.card → AC G A → WH G A := fun A hA hAC =>
      ih A.card (hm ▸ hA) A rfl hAC
    by_cases hc1 : X.card = 1
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc1
      exact case_single hG x
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      intro p hp hkodd hpX h0 hkX
      have hk : k = 1 ∨ k = 3 ∨ 5 ≤ k := by
        rcases hkodd with ⟨r, hr⟩; omega
      rcases hk with rfl | rfl | hk5
      · exact Or.inl ⟨0, by omega, h0, hkX⟩
      · exact case_three hG hX hp hpX h0 hkX
      · by_cases hint : ∃ t, 0 < t ∧ t < k ∧ XC G X (p t)
        · obtain ⟨t, ht0, htk, ht⟩ := hint
          exact reduce_step hG hkodd hp hpX h0 hkX (fun k' hk' => ihk k' hk') ht0 htk ht
        · push Not at hint
          have hpos := hX.1.card_pos
          exact main_step hG hX IHX (by omega) hk5 hkodd hp hpX h0 hkX hint

/-- **The Wonderful Lemma** (Roussel–Rubio; Chudnovsky's proof). -/
theorem wonderful {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X : Finset V}
    (hX : AC G X) (k : ℕ) (p : ℕ → V) (hp : IP G p k) (hk : Odd k) (hpX : ∀ i, i ≤ k → p i ∉ X)
    (h0 : XC G X (p 0)) (hkX : XC G X (p k)) : Outcome G X p k := by
  classical
  exact wonderful_gen hG X.card X rfl hX k p hp hk hpX h0 hkX


/-! ## The three corollaries, unconditionally -/

/-- The Wonderful Lemma for `X`, as the predicate `WH G X`. -/
theorem wonderful_WH {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X : Finset V}
    (hX : AC G X) : WH G X :=
  fun k p hp hk hpX h0 hkX => wonderful hG hX k p hp hk hpX h0 hkX

/-- **Corollary 2.1.** In a Berge graph, for an anticonnected `X` and an odd path `P` avoiding `X`
with `X`-complete ends and no `X`-complete edge, every `X`-complete vertex has a neighbour in the
interior of `P`. -/
theorem corollary_2_1 {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X : Finset V}
    (hX : AC G X) {p : ℕ → V} {k : ℕ} (hp : IP G p k) (hk : Odd k) (hpX : ∀ i, i ≤ k → p i ∉ X)
    (h0 : XC G X (p 0)) (hkX : XC G X (p k))
    (hno : ¬ ∃ i, i < k ∧ XC G X (p i) ∧ XC G X (p (i + 1))) {v : V} (hv : XC G X v) :
    ∃ t, 0 < t ∧ t < k ∧ G.Adj v (p t) :=
  cor21 hG hp hk hpX hno (wonderful hG hX k p hp hk hpX h0 hkX) hv

/-- **Corollary 2.2**, for the hole `a, p i, …, p j` with `a` not `X`-complete. -/
theorem corollary_2_2 {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X : Finset V}
    (hX : AC G X) {p : ℕ → V} {k : ℕ} (hp : IP G p k) (hpX : ∀ t, t ≤ k → p t ∉ X) {a : V}
    (haX : a ∉ X) (hz : ∀ t, t ≤ k → a ≠ p t) (haN : ¬ XC G X a) {i j : ℕ} (hij : i + 2 ≤ j)
    (hjk : j ≤ k) (hai : G.Adj a (p i)) (haj : G.Adj a (p j))
    (hmid : ∀ t, i < t → t < j → ¬ G.Adj a (p t)) :
    Even (ecnt G X p i j) ∨ (ecnt G X p i j = 1 ∧ ∃ s, i ≤ s ∧ s + 1 ≤ j ∧ XC G X (p s) ∧
      XC G X (p (s + 1)) ∧ ∀ t, i ≤ t → t ≤ j → XC G X (p t) → (t = s ∨ t = s + 1)) :=
  cor22 hG (wonderful_WH hG hX) hp hpX haX hz haN hij hjk hai haj hmid

/-- **Corollary 2.3.** An odd path with `X`-complete ends and an `X`-complete interior vertex has
an odd number of `X`-complete edges. -/
theorem corollary_2_3 {G : SimpleGraph V} (hG : StrongPerfectGraph.Main.IsBerge G) {X : Finset V}
    (hX : AC G X) {p : ℕ → V} {k : ℕ} (hp : IP G p k) (hk : Odd k) (hpX : ∀ i, i ≤ k → p i ∉ X)
    (h0 : XC G X (p 0)) (hkX : XC G X (p k)) (m : ℕ) (hm0 : 0 < m) (hmk : m < k)
    (hm : XC G X (p m)) : ecnt G X p 0 k % 2 = 1 := by
  have := cor23 hG (wonderful_WH hG hX) hp hpX h0 hkX m hm0 hmk hm
  rw [Nat.odd_iff.mp hk] at this
  exact this

/-! ## The Wonderful Lemma in the platform's vocabulary -/

section lists

open StrongPerfectGraph.Main

theorem getD_of_getElem? {l : List V} {i : ℕ} {v d : V} (h : l[i]? = some v) :
    l.getD i d = v := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getElem?_getD_of_lt {l : List V} {i : ℕ} (d : V) (h : i < l.length) :
    l[i]? = some (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_eq_getElem' {l : List V} {i : ℕ} (d : V) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- A list-based induced path is an induced path in the index-function encoding. -/
theorem IP_of_isInducedPath {G : SimpleGraph V} {P : List V} (hP : IsInducedPath G P) (d : V) :
    IP G (fun t => P.getD t d) (P.length - 1) := by
  obtain ⟨hne, hnd, hadj⟩ := hP
  have hpos : 0 < P.length := List.length_pos_iff.mpr hne
  refine ⟨fun i j hi hj hij => ?_, fun i j hi hj => ?_⟩
  · rw [getD_eq_getElem' d (by omega), getD_eq_getElem' d (by omega)] at hij
    exact hnd.getElem_inj_iff.mp hij
  · rw [getD_eq_getElem' d (by omega), getD_eq_getElem' d (by omega)]
    exact hadj ⟨i, by omega⟩ ⟨j, by omega⟩

/-- Connectivity of the complement induced on `X` gives anticonnectedness. -/
theorem AC_of_connected {G : SimpleGraph V} {X : Finset V}
    (h : (Gᶜ.induce (X : Set V)).Connected) : AC G X := by
  refine ⟨?_, fun a ha b hb => ?_⟩
  · obtain ⟨⟨x, hx⟩⟩ := h.nonempty
    exact ⟨x, Finset.mem_coe.mp hx⟩
  · let f : Gᶜ.induce (X : Set V) →g Hgraph Gᶜ X :=
      ⟨fun x => x.1, fun {x y} hxy => ⟨hxy, Finset.mem_coe.mp x.2, Finset.mem_coe.mp y.2⟩⟩
    exact (h.preconnected ⟨a, Finset.mem_coe.mpr ha⟩ ⟨b, Finset.mem_coe.mpr hb⟩).map f

/-- A path of `Gᶜ` given by an index function, as a list. -/
theorem isInducedPath_of_IP {H : SimpleGraph V} {q : ℕ → V} {ℓ : ℕ} (h : IP H q ℓ) :
    IsInducedPath H ((List.range (ℓ + 1)).map q) := by
  refine ⟨by simp, ?_, ?_⟩
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro x hx y hy hxy
    exact h.inj x y (by have := List.mem_range.mp hx; omega) (by have := List.mem_range.mp hy; omega) hxy
  · intro i j
    have hi := i.2
    have hj := j.2
    simp only [List.length_map, List.length_range] at hi hj
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    exact h.adj i j (by omega) (by omega)

/-- **Theorem 1.2 (the Wonderful Lemma)**, with the path and anticonnectivity hypotheses in the
platform's vocabulary: `P` is a list-based induced path (`v0 … vk`, `k` odd, i.e. an even number
of vertices), disjoint from the anticonnected set `X`, with both ends complete to `X`. Then
(1) two consecutive vertices of `P` are both complete to `X`, or (2) `k ≥ 5` and `X` contains a
leap, or (3) `k = 3` and there is an odd antipath from `v1` to `v2` with interior in `X`. -/
theorem wonderful_lists {G : SimpleGraph V} (hG : IsBerge G) {X : Finset V}
    (hX : (Gᶜ.induce (X : Set V)).Connected) {P : List V} (hP : IsInducedPath G P)
    (hlen : Even P.length) (hdisj : ∀ v ∈ P, v ∉ X) {v0 vk : V} (h0 : P.head? = some v0)
    (hk : P.getLast? = some vk) (hv0 : ∀ x ∈ X, G.Adj v0 x) (hvk : ∀ x ∈ X, G.Adj vk x) :
    (∃ (i : ℕ) (u w : V), P[i]? = some u ∧ P[i + 1]? = some w ∧ (∀ x ∈ X, G.Adj u x) ∧
        (∀ x ∈ X, G.Adj w x)) ∨
    (6 ≤ P.length ∧ ∃ a ∈ X, ∃ b ∈ X, a ≠ b ∧ ¬ G.Adj a b ∧
        (∀ (i : ℕ) (v : V), P[i]? = some v →
          (G.Adj a v ↔ (i = 0 ∨ i = 1 ∨ i + 1 = P.length))) ∧
        (∀ (i : ℕ) (v : V), P[i]? = some v →
          (G.Adj b v ↔ (i = 0 ∨ i + 2 = P.length ∨ i + 1 = P.length)))) ∨
    (P.length = 4 ∧ ∃ Q : List V, IsInducedPath Gᶜ Q ∧ Even Q.length ∧
        (∃ v1 v2, P[1]? = some v1 ∧ P[2]? = some v2 ∧ Q.head? = some v1 ∧
          Q.getLast? = some v2) ∧
        ∀ (i : ℕ) (v : V), Q[i]? = some v → 0 < i → i + 1 < Q.length → v ∈ X) := by
  have hne := hP.1
  have hpos : 0 < P.length := List.length_pos_iff.mpr hne
  have hlen2 : 2 ≤ P.length := by obtain ⟨r, hr⟩ := hlen; omega
  have hlevn := Nat.even_iff.mp hlen
  have hkodd : Odd (P.length - 1) := Nat.odd_iff.mpr (by omega)
  have hIP := IP_of_isInducedPath hP v0
  have hpX : ∀ t, t ≤ P.length - 1 → P.getD t v0 ∉ X := fun t ht => by
    rw [getD_eq_getElem' v0 (by omega)]; exact hdisj _ (List.getElem_mem _)
  have hp0 : P.getD 0 v0 = v0 := getD_of_getElem? (by rwa [← List.head?_eq_getElem?])
  have hpk : P.getD (P.length - 1) v0 = vk :=
    getD_of_getElem? (by rw [← List.getLast?_eq_getElem?]; exact hk)
  have hv0P : v0 ∈ P := List.mem_of_mem_head? h0
  have hvkP : vk ∈ P := List.mem_of_getLast? hk
  have hout := wonderful hG (AC_of_connected hX) (P.length - 1) _ hIP hkodd hpX
    ⟨by rw [hp0]; exact hdisj v0 hv0P, by rw [hp0]; exact hv0⟩
    ⟨by rw [hpk]; exact hdisj vk hvkP, by rw [hpk]; exact hvk⟩
  rcases hout with ⟨i, hik, c1, c2⟩ | ⟨hk5, a, b, hl⟩ | ⟨hk3, ℓ, q, hq, hodd, hq0, hqℓ, hqX⟩
  · exact Or.inl ⟨i, P.getD i v0, P.getD (i + 1) v0, getElem?_getD_of_lt v0 (by omega),
      getElem?_getD_of_lt v0 (by omega), c1.2, c2.2⟩
  · obtain ⟨haX, hbX, hab, hnab, hA, hB⟩ := hl
    refine Or.inr (Or.inl ⟨by omega, a, haX, b, hbX, hab, hnab, ?_, ?_⟩)
    · intro i v hv
      have hi : i < P.length := (List.getElem?_eq_some_iff.mp hv).1
      have this : G.Adj a (P.getD i v0) ↔ _ := hA i (by omega)
      rw [getD_of_getElem? hv] at this
      rw [this]; omega
    · intro i v hv
      have hi : i < P.length := (List.getElem?_eq_some_iff.mp hv).1
      have this : G.Adj b (P.getD i v0) ↔ _ := hB i (by omega)
      rw [getD_of_getElem? hv] at this
      rw [this]; omega
  · refine Or.inr (Or.inr ⟨by omega, (List.range (ℓ + 1)).map q, isInducedPath_of_IP hq, ?_, ?_, ?_⟩)
    · simpa using (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hodd))
    · refine ⟨P.getD 1 v0, P.getD 2 v0, getElem?_getD_of_lt v0 (by omega),
        getElem?_getD_of_lt v0 (by omega), ?_, ?_⟩
      · rw [List.head?_eq_getElem?]; simp [hq0]
      · rw [List.getLast?_eq_getElem?]; simp [hqℓ]
    · intro i v hv h0i hil
      simp only [List.length_map, List.length_range] at hil
      rw [List.getElem?_map, List.getElem?_range (by omega)] at hv
      simp only [Option.map_some] at hv
      rw [← Option.some.inj hv]
      exact hqX i h0i (by omega)

end lists

end Wonderful


open StrongPerfectGraph.Main in
theorem solution {V : Type*} {G : SimpleGraph V} (hG : IsBerge G) {X : Finset V}
    (hX : (Gᶜ.induce (X : Set V)).Connected) {P : List V} (hP : IsInducedPath G P)
    (hlen : Even P.length) (hdisj : ∀ v ∈ P, v ∉ X) {v0 vk : V} (h0 : P.head? = some v0)
    (hk : P.getLast? = some vk) (hv0 : ∀ x ∈ X, G.Adj v0 x) (hvk : ∀ x ∈ X, G.Adj vk x) :
    (∃ (i : ℕ) (u w : V), P[i]? = some u ∧ P[i + 1]? = some w ∧ (∀ x ∈ X, G.Adj u x) ∧
        (∀ x ∈ X, G.Adj w x)) ∨
    (6 ≤ P.length ∧ ∃ a ∈ X, ∃ b ∈ X, a ≠ b ∧ ¬ G.Adj a b ∧
        (∀ (i : ℕ) (v : V), P[i]? = some v →
          (G.Adj a v ↔ (i = 0 ∨ i = 1 ∨ i + 1 = P.length))) ∧
        (∀ (i : ℕ) (v : V), P[i]? = some v →
          (G.Adj b v ↔ (i = 0 ∨ i + 2 = P.length ∨ i + 1 = P.length)))) ∨
    (P.length = 4 ∧ ∃ Q : List V, IsInducedPath Gᶜ Q ∧ Even Q.length ∧
        (∃ v1 v2, P[1]? = some v1 ∧ P[2]? = some v2 ∧ Q.head? = some v1 ∧
          Q.getLast? = some v2) ∧
        ∀ (i : ℕ) (v : V), Q[i]? = some v → 0 < i → i + 1 < Q.length → v ∈ X) :=
  Wonderful.wonderful_lists hG hX hP hlen hdisj h0 hk hv0 hvk
