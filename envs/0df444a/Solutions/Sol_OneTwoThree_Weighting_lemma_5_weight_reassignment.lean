-- Prove2me | solution 1 for OneTwoThree.Weighting.lemma_5_weight_reassignment
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-12T23:47:30.08502+00:00
-- url     : https://prove2.me/submissions/6b9a1a31-2a16-48cd-97ae-f1d040dad625

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

set_option autoImplicit false

open OneTwoThree.Weighting

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (B : Finset V)
    (hB : ∀ u v, G.Adj u v → (u ∈ B ↔ v ∉ B)) (α : V → ℕ)
    (hα : ∀ v ∈ B, (α v : ℤ) = 2 * (G.degree v : ℤ) - 1 ∨ (α v : ℤ) = 2 * (G.degree v : ℤ) ∨
      (α v : ℤ) = 2 * (G.degree v : ℤ) + 1)
    (R' : Finset V) (hR' : R' ⊆ Bᶜ)
    (E_o : Finset (Sym2 V)) (hE_o : (E_o : Set (Sym2 V)) ⊆ G.edgeSet)
    (hpar_e : ∀ v, Odd (Finset.card (E_o.filter (fun e => v ∈ e))) ↔
      v ∈ R' ∪ B.filter (fun u => α u ≠ 2 * G.degree u)) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧
      (∀ v ∈ Bᶜ \ R', Even (wdeg G ω v)) ∧
      (∀ v ∈ R', Odd (wdeg G ω v)) ∧
      (∀ v ∈ B, wdeg G ω v = α v) := by
  classical
  -- Membership in an unordered pair.
  have hmem_eq : ∀ (x a b : V), (x ∈ s(a, b)) ↔ (x = a ∨ x = b) := by
    intro x a b
    rw [← Sym2.mem_iff_mem]
    exact Sym2.mem_iff'
  -- Parity of a sum of odd naturals.
  have ott : ∀ (t : Finset V) (f : V → ℕ), (∀ i ∈ t, Odd (f i)) →
      (Odd (Finset.sum t f) ↔ Odd (Finset.card t)) := by
    intro t f
    refine Finset.induction_on t ?_ ?_
    · intro _
      rw [Finset.sum_empty, Finset.card_empty]
    · intro a s has ih hall
      have hfa : Odd (f a) := hall a (Finset.mem_insert_self a s)
      have ih' := ih (fun i hi => hall i (Finset.mem_insert_of_mem hi))
      have hsymm : ∀ n : ℕ, (Even n ↔ ¬ Odd n) := fun n => (Nat.not_odd_iff_even.symm)
      have h3 : Even (Finset.sum s f) ↔ Even (Finset.card s) := by
        rw [hsymm _, hsymm _]
        exact not_congr ih'
      rw [Finset.sum_insert has, Finset.card_insert_of_notMem has, Nat.odd_add,
        iff_true_intro hfa, true_iff, h3]
      exact (Nat.not_odd_iff_even.symm.trans Nat.odd_add_one.symm)
  -- For each v ∈ B, choose how many E_o-edges at v get weight 1.
  have hkv : ∀ v ∈ B, ∃ k : ℕ, k ≤ Finset.card (E_o.filter (fun e => v ∈ e)) ∧
      2 * G.degree v + Finset.card (E_o.filter (fun e => v ∈ e)) - 2 * k = α v := by
    intro v hv
    rcases hα v hv with hA | hB | hC
    · -- α v = 2*deg - 1 (odd below): Odd card, k = m+1
      have hne : α v ≠ 2 * G.degree v := by
        intro hcon
        have hconZ : (α v : ℤ) = 2 * (G.degree v : ℤ) := by exact_mod_cast hcon
        omega
      have hmem : v ∈ R' ∪ B.filter (fun u => α u ≠ 2 * G.degree u) :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hv, hne⟩))
      obtain ⟨m, hm⟩ := (hpar_e v).mpr hmem
      have hdeg1 : 1 ≤ 2 * G.degree v := by
        have hα_nonneg : (0 : ℤ) ≤ (α v : ℤ) := Int.natCast_nonneg _
        omega
      exact ⟨m + 1, by omega, by omega⟩
    · -- α v = 2*deg: Even card, k = m
      have hBnat : α v = 2 * G.degree v := by exact_mod_cast hB
      have hnemem : v ∉ R' ∪ B.filter (fun u => α u ≠ 2 * G.degree u) := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hR | hBf
        · exact (Finset.mem_compl.mp (hR' hR)) hv
        · exact (Finset.mem_filter.mp hBf).2 hBnat
      have heven : Even (Finset.card (E_o.filter (fun e => v ∈ e))) :=
        Nat.not_odd_iff_even.mp (fun hodd => hnemem ((hpar_e v).mp hodd))
      obtain ⟨m, hm⟩ := heven
      exact ⟨m, by omega, by omega⟩
    · -- α v = 2*deg + 1 (odd above): Odd card, k = m
      have hne : α v ≠ 2 * G.degree v := by
        intro hcon
        have hconZ : (α v : ℤ) = 2 * (G.degree v : ℤ) := by exact_mod_cast hcon
        omega
      have hmem : v ∈ R' ∪ B.filter (fun u => α u ≠ 2 * G.degree u) :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hv, hne⟩))
      obtain ⟨m, hm⟩ := (hpar_e v).mpr hmem
      exact ⟨m, by omega, by omega⟩
  -- Realize the choice as subsets S v ⊆ E_o-edges at v.
  have hsub : ∀ v ∈ B, ∃ S : Finset (Sym2 V), S ⊆ E_o.filter (fun e => v ∈ e) ∧
      2 * G.degree v + Finset.card (E_o.filter (fun e => v ∈ e)) - 2 * Finset.card S
        = α v := by
    intro v hv
    obtain ⟨k, hkle, hkeq⟩ := hkv v hv
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hkle
    exact ⟨S, hSsub, by rw [hScard]; exact hkeq⟩
  have hSk : ∀ v, ∃ S : Finset (Sym2 V), S ⊆ E_o.filter (fun e => v ∈ e) ∧
      (v ∈ B → 2 * G.degree v + Finset.card (E_o.filter (fun e => v ∈ e))
        - 2 * Finset.card S = α v) := by
    intro v
    by_cases hv : v ∈ B
    · obtain ⟨S, h1, h2⟩ := hsub v hv
      exact ⟨S, h1, fun _ => h2⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => absurd h hv⟩
  obtain ⟨S, hS⟩ := Classical.skolem.mp hSk
  -- The weighting: E_o-edges get 1 (chosen) or 3, everything else 2.
  set ω : Sym2 V → ℕ := fun e =>
    if e ∈ E_o then (if ∃ u ∈ B, u ∈ e ∧ e ∈ S u then 1 else 3) else 2 with hωdef
  -- At a B-vertex, the inner choice sees exactly S a.
  have hchar : ∀ (a b : V), a ∈ B → s(a, b) ∈ E_o →
      ((∃ x ∈ B, x ∈ s(a, b) ∧ s(a, b) ∈ S x) ↔ s(a, b) ∈ S a) := by
    intro a b haB heE
    constructor
    · rintro ⟨x, hxB, hxe, hxS⟩
      rcases (hmem_eq x a b).mp hxe with hxa | hxb
      · rw [hxa] at hxS; exact hxS
      · exfalso
        have hadj : G.Adj a b := by
          have hmem : s(a, b) ∈ G.edgeSet := hE_o (Finset.mem_coe.mpr heE)
          rwa [SimpleGraph.mem_edgeSet] at hmem
        have hnb : b ∉ B := (hB a b hadj).mp haB
        rw [← hxb] at hnb
        exact hnb hxB
    · intro h
      exact ⟨a, haB, (hmem_eq a a b).mpr (Or.inl rfl), h⟩
  -- The neighbor-to-edge map is injective on E_o-incident neighbors.
  have hinjA : ∀ v, Set.InjOn (fun w => s(v, w))
      ↑((G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o)) := by
    intro v w₁ hw₁ w₂ hw₂ h
    have hw₁' := Finset.mem_coe.mp hw₁
    have hw₂' := Finset.mem_coe.mp hw₂
    have h1 : w₁ ∈ s(v, w₂) := by
      have h' : s(v, w₁) = s(v, w₂) := h
      rw [← h']; exact (hmem_eq w₁ v w₁).mpr (Or.inr rfl)
    rcases (hmem_eq w₁ v w₂).mp h1 with hvv | hww
    · exfalso
      have hadj : G.Adj v w₁ :=
        (SimpleGraph.mem_neighborFinset G v w₁).mp (Finset.mem_of_mem_filter w₁ hw₁')
      rw [hvv] at hadj
      exact hadj.ne rfl
    · exact hww
  -- So E_o-incident neighbors are in bijection with E_o-edges at v.
  have hcardA : ∀ v, Finset.card ((G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o))
      = Finset.card (E_o.filter (fun e => v ∈ e)) := by
    intro v
    have himg : ((G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o)).image (fun w => s(v, w))
        = E_o.filter (fun e => v ∈ e) := by
      ext e
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨w, ⟨-, hweE⟩, rfl⟩
        exact ⟨hweE, (hmem_eq v v w).mpr (Or.inl rfl)⟩
      · intro he
        obtain ⟨heE, hve⟩ := he
        obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hve
        subst hw
        have hadj : G.Adj v w := by
          have hmem : s(v, w) ∈ G.edgeSet := hE_o (Finset.mem_coe.mpr heE)
          rwa [SimpleGraph.mem_edgeSet] at hmem
        have hwN : w ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v w).mpr hadj
        exact ⟨w, ⟨hwN, heE⟩, rfl⟩
    rw [← himg, Finset.card_image_of_injOn (hinjA v)]
  -- ω is a {1,2,3}-weighting.
  have hW : IsWeighting G 3 ω := by
    intro e he
    simp only [hωdef]
    by_cases heE : e ∈ E_o
    · rw [if_pos heE]
      by_cases hP : ∃ u ∈ B, u ∈ e ∧ e ∈ S u
      · rw [if_pos hP]; decide
      · rw [if_neg hP]; decide
    · rw [if_neg heE]; decide
  -- Off B, E_o-incident edges carry odd weights.
  have hoddA : ∀ (v : V) (_ : v ∉ B) (w : V),
      w ∈ (G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o) → Odd (ω s(v, w)) := by
    intro v hvB w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨-, heE⟩ := hw
    simp only [hωdef]
    rw [if_pos heE]
    by_cases hP : ∃ u ∈ B, u ∈ s(v, w) ∧ s(v, w) ∈ S u
    · rw [if_pos hP]; exact odd_one
    · rw [if_neg hP]; exact ⟨1, rfl⟩
  -- The non-E_o part of wdeg is even.
  have heven_rest : ∀ (v : V) (_ : v ∉ B),
      Even (∑ w ∈ (G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o), ω s(v, w)) := by
    intro v hvB
    have h2 : ∀ w ∈ (G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o), ω s(v, w) = 2 := by
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨-, hne⟩ := hw
      simp only [hωdef]
      rw [if_neg hne]
    have hsum2 : ∑ w ∈ (G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o), ω s(v, w)
        = Finset.card ((G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o)) * 2 := by
      rw [Finset.sum_congr rfl (fun w hw => h2 w hw)]
      simp [Finset.sum_const]
    rw [hsum2]
    exact even_iff_two_dvd.mpr (dvd_mul_left 2 _)
  -- Case v ∈ B: wdeg = α v.
  have hBcase : ∀ v ∈ B, wdeg G ω v = α v := by
    intro v hv
    have h2 := (hS v).2 hv
    have h1 := (hS v).1
    set A := (G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o) with hAdef
    set U := A.filter (fun w => s(v, w) ∈ S v) with hUdef
    have eA : Finset.card A = Finset.card (E_o.filter (fun e => v ∈ e)) := hcardA v
    have eU : Finset.card U = Finset.card (S v) := by
      have hsubU : ↑U ⊆ ↑A := by
        rw [hUdef]
        exact Finset.coe_subset.mpr (Finset.filter_subset _ _)
      have hinjU : Set.InjOn (fun w => s(v, w)) ↑U := Set.InjOn.mono hsubU (hinjA v)
      have himgU : U.image (fun w => s(v, w)) = S v := by
        ext e
        rw [hUdef, hAdef]
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨w, ⟨⟨-, hweE⟩, hwsS⟩, rfl⟩
          exact hwsS
        · intro he
          have hsub := h1 he
          rw [Finset.mem_filter] at hsub
          obtain ⟨heE, hve⟩ := hsub
          obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hve
          subst hw
          have hadj : G.Adj v w := by
            have hmem : s(v, w) ∈ G.edgeSet := hE_o (Finset.mem_coe.mpr heE)
            rwa [SimpleGraph.mem_edgeSet] at hmem
          have hwN : w ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v w).mpr hadj
          exact ⟨w, ⟨⟨hwN, heE⟩, he⟩, rfl⟩
      rw [← himgU, Finset.card_image_of_injOn hinjU]
    have hterm1 : ∀ w ∈ U, ω s(v, w) = 1 := by
      intro w hw
      rw [hUdef, Finset.mem_filter] at hw
      obtain ⟨hwA, hmS⟩ := hw
      rw [hAdef, Finset.mem_filter] at hwA
      obtain ⟨-, heE⟩ := hwA
      have hch := hchar v w hv heE
      simp only [hωdef]
      rw [if_pos heE, if_pos (hch.mpr hmS)]
    have hterm3 : ∀ w ∈ A.filter (fun w => ¬ s(v, w) ∈ S v), ω s(v, w) = 3 := by
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hwA, hnmS⟩ := hw
      rw [hAdef, Finset.mem_filter] at hwA
      obtain ⟨-, heE⟩ := hwA
      have hch := hchar v w hv heE
      simp only [hωdef]
      rw [if_pos heE, if_neg (fun h => hnmS (hch.mp h))]
    have hterm2 : ∀ w ∈ (G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o), ω s(v, w) = 2 := by
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨-, hne⟩ := hw
      simp only [hωdef]
      rw [if_neg hne]
    have sU : ∑ w ∈ U, ω s(v, w) = Finset.card U := by
      rw [Finset.sum_congr rfl (fun w hw => hterm1 w hw), Finset.card_eq_sum_ones]
    have sA3 : ∑ w ∈ A.filter (fun w => ¬ s(v, w) ∈ S v), ω s(v, w)
        = Finset.card (A.filter (fun w => ¬ s(v, w) ∈ S v)) * 3 := by
      rw [Finset.sum_congr rfl (fun w hw => hterm3 w hw)]
      simp [Finset.sum_const]
    have sN2 : ∑ w ∈ (G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o), ω s(v, w)
        = Finset.card ((G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o)) * 2 := by
      rw [Finset.sum_congr rfl (fun w hw => hterm2 w hw)]
      simp [Finset.sum_const]
    have hsplit1 : ∑ w ∈ U, ω s(v, w) + ∑ w ∈ A.filter (fun w => ¬ s(v, w) ∈ S v), ω s(v, w)
        = ∑ w ∈ A, ω s(v, w) :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hsplit2 : ∑ w ∈ A, ω s(v, w)
        + ∑ w ∈ (G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o), ω s(v, w)
        = ∑ w ∈ G.neighborFinset v, ω s(v, w) :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hcsplit : ∀ (t : Finset V) (p : V → Prop) [DecidablePred p],
        Finset.card (t.filter p) + Finset.card (t.filter (fun x => ¬ p x))
          = Finset.card t := by
      intro t p _
      have h : ∑ x ∈ t.filter p, (1 : ℕ) + ∑ x ∈ t.filter (fun x => ¬ p x), (1 : ℕ)
          = ∑ x ∈ t, (1 : ℕ) :=
        Finset.sum_filter_add_sum_filter_not _ _ _
      simp only [← Finset.card_eq_sum_ones] at h
      exact h
    have c1 : Finset.card U + Finset.card (A.filter (fun w => ¬ s(v, w) ∈ S v))
        = Finset.card A := by
      have h := hcsplit A (fun w => s(v, w) ∈ S v)
      rw [← hUdef] at h
      exact h
    have c2 : Finset.card A
        + Finset.card ((G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o))
        = Finset.card (G.neighborFinset v) := by
      have h := hcsplit (G.neighborFinset v) (fun w => s(v, w) ∈ E_o)
      rw [← hAdef] at h
      exact h
    have edeg : Finset.card (G.neighborFinset v) = G.degree v := rfl
    have hwdeg : wdeg G ω v = ∑ w ∈ G.neighborFinset v, ω s(v, w) := rfl
    rw [hwdeg]
    have hsum : ∑ w ∈ G.neighborFinset v, ω s(v, w)
        = (∑ w ∈ U, ω s(v, w))
          + (∑ w ∈ A.filter (fun w => ¬ s(v, w) ∈ S v), ω s(v, w))
          + (∑ w ∈ (G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o), ω s(v, w)) := by
      rw [← hsplit2, ← hsplit1]
    rw [hsum, sU, sA3, sN2]
    omega
  -- Case v ∈ R': wdeg is odd.
  have hRcase : ∀ v ∈ R', Odd (wdeg G ω v) := by
    intro v hvR
    have hvB : v ∉ B := Finset.mem_compl.mp (hR' hvR)
    have hA : ∀ w ∈ (G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o), Odd (ω s(v, w)) :=
      fun w hw => hoddA v hvB w hw
    have hodd_card : Odd (Finset.card ((G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o))) := by
      rw [hcardA v]
      exact (hpar_e v).mpr (Finset.mem_union.mpr (Or.inl hvR))
    have hodd_sum : Odd (∑ w ∈ (G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o), ω s(v, w)) :=
      (ott _ _ hA).mpr hodd_card
    have hsplit : ∑ w ∈ (G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o), ω s(v, w)
        + ∑ w ∈ (G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o), ω s(v, w)
        = ∑ w ∈ G.neighborFinset v, ω s(v, w) :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hwdeg : wdeg G ω v = ∑ w ∈ G.neighborFinset v, ω s(v, w) := rfl
    rw [hwdeg, ← hsplit]
    exact hodd_sum.add_even (heven_rest v hvB)
  -- Case v ∈ Bᶜ \ R': wdeg is even.
  have hEcase : ∀ v ∈ Bᶜ \ R', Even (wdeg G ω v) := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    obtain ⟨hvBc, hvR⟩ := hv
    have hvB : v ∉ B := Finset.mem_compl.mp hvBc
    have hA : ∀ w ∈ (G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o), Odd (ω s(v, w)) :=
      fun w hw => hoddA v hvB w hw
    have hne : ¬ Odd (Finset.card (E_o.filter (fun e => v ∈ e))) := by
      intro hodd
      have hmem := (hpar_e v).mp hodd
      rcases Finset.mem_union.mp hmem with hR | hBf
      · exact hvR hR
      · exact hvB (Finset.mem_filter.mp hBf).1
    have heven_card : Even (Finset.card ((G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o))) := by
      rw [hcardA v]
      exact Nat.not_odd_iff_even.mp hne
    have heven_sum : Even (∑ w ∈ (G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o), ω s(v, w)) := by
      have hnot : ¬ Odd (∑ w ∈ (G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o), ω s(v, w)) := by
        intro hcon
        exact (Nat.not_odd_iff_even.mpr heven_card) ((ott _ _ hA).mp hcon)
      exact Nat.not_odd_iff_even.mp hnot
    have hsplit : ∑ w ∈ (G.neighborFinset v).filter (fun w => s(v, w) ∈ E_o), ω s(v, w)
        + ∑ w ∈ (G.neighborFinset v).filter (fun w => ¬ s(v, w) ∈ E_o), ω s(v, w)
        = ∑ w ∈ G.neighborFinset v, ω s(v, w) :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hwdeg : wdeg G ω v = ∑ w ∈ G.neighborFinset v, ω s(v, w) := rfl
    rw [hwdeg, ← hsplit]
    exact heven_sum.add (heven_rest v hvB)
  exact ⟨ω, hW, hEcase, hRcase, hBcase⟩

theorem OneTwoThree.Weighting.lemma_5_weight_reassignment {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (B : Finset V)
    (hB : ∀ u v, G.Adj u v → (u ∈ B ↔ v ∉ B)) (α : V → ℕ)
    (hα : ∀ v ∈ B, (α v : ℤ) = 2 * (G.degree v : ℤ) - 1 ∨ (α v : ℤ) = 2 * (G.degree v : ℤ) ∨
      (α v : ℤ) = 2 * (G.degree v : ℤ) + 1)
    (R' : Finset V) (hR' : R' ⊆ Bᶜ)
    (E_o : Finset (Sym2 V)) (hE_o : (E_o : Set (Sym2 V)) ⊆ G.edgeSet)
    (hpar_e : ∀ v, Odd (Finset.card (E_o.filter (fun e => v ∈ e))) ↔
      v ∈ R' ∪ B.filter (fun u => α u ≠ 2 * G.degree u)) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧
      (∀ v ∈ Bᶜ \ R', Even (wdeg G ω v)) ∧
      (∀ v ∈ R', Odd (wdeg G ω v)) ∧
      (∀ v ∈ B, wdeg G ω v = α v) :=
  solution G hG B hB α hα R' hR' E_o hE_o hpar_e
