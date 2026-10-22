-- Prove2me | solution 1 for ObliviousRAM.LowerBound.counting_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:50:07.687812+00:00
-- url     : https://prove2.me/submissions/d4c0e4b2-1669-47b2-8f2a-98162d999029

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

open ObliviousRAM.LowerBound
open Classical

noncomputable def oram_run {m : ℕ} (b : ℕ) (s : Option (State m)) (l : List (Action m)) :
    Option (State m) :=
  l.foldl (fun os act => os.bind (fun s => step b s act)) s

theorem oram_run_none {m : ℕ} (b : ℕ) (l : List (Action m)) : oram_run b none l = none := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [oram_run, List.foldl_cons] using ih

theorem oram_run_cons {m : ℕ} (b : ℕ) (s : State m) (a : Action m) (l : List (Action m)) :
    oram_run b (some s) (a :: l) = oram_run b (step b s a) l := by
  simp [oram_run, List.foldl_cons]

theorem oram_step_hand {m : ℕ} (b : ℕ) (s s' : State m) (a : Action m)
    (h : step b s a = some s') (hs : s.hand.card ≤ b) : s'.hand.card ≤ b := by
  obtain ⟨v, h0⟩ := a
  cases h0 with
  | take =>
    simp only [step] at h
    split at h
    · simp at h
    · split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      exact (Finset.card_insert_le _ _).trans (by omega)
  | place β =>
    simp only [step] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    exact (Finset.card_erase_le).trans hs
  | nothing =>
    simp only [step, Option.some.injEq] at h
    subst h; exact hs

theorem oram_heads {m : ℕ} (b : ℕ) (s : State m) (v : Fin m) (hs : s.hand.card ≤ b) :
    (Finset.univ.filter fun h : Hidden m => (step b s (v, h)).isSome).card ≤ b + 2 := by
  have hsub : (Finset.univ.filter fun h : Hidden m => (step b s (v, h)).isSome) ⊆
      insert Hidden.take (insert Hidden.nothing (s.hand.image Hidden.place)) := by
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    cases h with
    | take => simp
    | nothing => simp
    | place β =>
      simp only [step] at hh
      split_ifs at hh with hc
      · simp [hc.2]
      · simp at hh
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_insert_le _ _).trans ?_
  have := Finset.card_insert_le Hidden.nothing (s.hand.image Hidden.place)
  have := Finset.card_image_le (s := s.hand) (f := Hidden.place)
  omega

theorem oram_main {m : ℕ} (b : ℕ) (V : List (Fin m)) :
    ∀ s : State m, s.hand.card ≤ b →
      (Finset.univ.filter fun H : Fin V.length → Hidden m =>
        (oram_run b (some s) (List.ofFn fun i => (V.get i, H i))).isSome).card ≤ (b + 2) ^ V.length := by
  induction V with
  | nil =>
    intro s _
    simp only [List.length_nil, pow_zero]
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  | cons v V ih =>
    intro s hs
    set n := V.length
    let P : (Fin (n + 1) → Hidden m) → Prop := fun H =>
      (oram_run b (some s) (List.ofFn fun i => ((v :: V).get i, H i))).isSome
    have key : ∀ H : Fin (n + 1) → Hidden m, P H ↔
        (oram_run b (step b s (v, H 0)) (List.ofFn fun i : Fin n => (V.get i, H i.succ))).isSome := by
      intro H
      simp only [P, List.ofFn_succ, oram_run_cons]
      rfl
    show (Finset.univ.filter P).card ≤ (b + 2) ^ (n + 1)
    rw [Finset.card_eq_sum_card_fiberwise (f := fun H => H 0) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    -- bound each fiber
    have hfib : ∀ h : Hidden m, ((Finset.univ.filter P).filter (fun H => H 0 = h)).card ≤
        if (step b s (v, h)).isSome then (b + 2) ^ n else 0 := by
      intro h
      rcases hst : step b s (v, h) with _ | s'
      · simp only [Option.isSome_none, Bool.false_eq_true, if_false, Nat.le_zero,
          Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro H hH h0
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH
        rw [key, h0, hst, oram_run_none] at hH
        simp at hH
      · simp only [Option.isSome_some, if_true]
        have hs' := oram_step_hand b s s' _ hst hs
        refine le_trans ?_ (ih s' hs')
        apply Finset.card_le_card_of_injOn (fun H => fun i : Fin n => H i.succ)
        · intro H hH
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hH ⊢
          have := (key H).1 hH.1
          rw [hH.2, hst] at this
          exact this
        · intro H1 hH1 H2 hH2 heq
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hH1 hH2
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · rw [hH1.2, hH2.2]
          · exact congrFun heq j
    calc ∑ h : Hidden m, ((Finset.univ.filter P).filter (fun H => H 0 = h)).card
        ≤ ∑ h : Hidden m, (if (step b s (v, h)).isSome then (b + 2) ^ n else 0) :=
          Finset.sum_le_sum (fun h _ => hfib h)
      _ = (Finset.univ.filter fun h : Hidden m => (step b s (v, h)).isSome).card * (b + 2) ^ n := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
      _ ≤ (b + 2) * (b + 2) ^ n := Nat.mul_le_mul_right _ (oram_heads b s v hs)
      _ = (b + 2) ^ (n + 1) := by ring

theorem oram_card_hidden {b m : ℕ} (V : List (Fin m)) :
    (Finset.univ.filter fun H : Fin V.length → Hidden m =>
      Legal b (List.ofFn fun i => (V.get i, H i))).card ≤ (b + 2) ^ V.length := by
  have h := oram_main b V (initState m) (by simp [initState])
  convert h using 3 with H
  simp only [Legal, stateAfter, List.length_ofFn, oram_run]
  rw [List.take_of_length_le (by simp)]

theorem oram_run_hand {m : ℕ} (b : ℕ) (l : List (Action m)) :
    ∀ s s' : State m, s.hand.card ≤ b → oram_run b (some s) l = some s' → s'.hand.card ≤ b := by
  induction l with
  | nil =>
    intro s s' hs h
    simp only [oram_run, List.foldl_nil, Option.some.injEq] at h
    subst h; exact hs
  | cons a l ih =>
    intro s s' hs h
    rw [oram_run_cons] at h
    rcases hst : step b s a with _ | s1
    · rw [hst, oram_run_none] at h; simp at h
    · rw [hst] at h
      exact ih s1 s' (oram_step_hand b s s1 a hst hs) h

theorem oram_handAfter_card {m : ℕ} (b : ℕ) (a : List (Action m)) (k : ℕ) :
    (handAfter b a k).card ≤ b := by
  unfold handAfter
  rcases h : stateAfter b a k with _ | s
  · simp
  · simp only [Option.map_some, Option.getD_some]
    have : oram_run b (some (initState m)) (a.take k) = some s := h
    exact oram_run_hand b _ _ _ (by simp [initState]) this

theorem oram_mono_inj {t L : ℕ} (g1 g2 : Fin t → Fin L) (h1 : Monotone g1) (h2 : Monotone g2)
    (h : Finset.univ.val.map g1 = Finset.univ.val.map g2) : g1 = g2 := by
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at h
  exact List.ofFn_injective (List.Perm.eq_of_sortedLE h1.sortedLE_ofFn h2.sortedLE_ofFn h)

theorem oram_card_mono (t L : ℕ) :
    (Finset.univ.filter fun g : Fin t → Fin L => Monotone g).card ≤ Nat.multichoose L t := by
  let f : (Fin t → Fin L) → Sym (Fin L) t := fun g => ⟨Finset.univ.val.map g, by simp⟩
  have hinj : Set.InjOn f ↑(Finset.univ.filter fun g : Fin t → Fin L => Monotone g) := by
    intro g1 hg1 g2 hg2 heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg1 hg2
    apply oram_mono_inj g1 g2 hg1 hg2
    exact congrArg Subtype.val heq
  rw [← Finset.card_image_of_injOn hinj, ← Sym.card_sym_fin_eq_multichoose L t]
  exact Finset.card_le_univ _

theorem oram_card_sat {b m t : ℕ} (a : List (Action m)) :
    (Finset.univ.filter fun r : Fin t → Fin m => Satisfies b a r).card ≤
      Nat.multichoose a.length t * b ^ t := by
  set L := a.length with hL
  let J : Finset (Fin t → Fin L) := Finset.univ.filter fun g => Monotone g
  have hsub : (Finset.univ.filter fun r : Fin t → Fin m => Satisfies b a r) ⊆
      J.biUnion (fun g => Fintype.piFinset (fun i => handAfter b a (g i + 1))) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨-, j, hjm, hj1, hjL, -, hjr⟩ := hr
    rw [Finset.mem_biUnion]
    refine ⟨fun i => ⟨j i - 1, by have := hj1 i; have := hjL i; omega⟩, ?_, ?_⟩
    · simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x y hxy
      have := hjm hxy
      simp only [Fin.mk_le_mk]
      omega
    · rw [Fintype.mem_piFinset]
      intro i
      have : j i - 1 + 1 = j i := by have := hj1 i; omega
      simp only
      rw [this]; exact hjr i
  calc _ ≤ (J.biUnion (fun g => Fintype.piFinset (fun i => handAfter b a (g i + 1)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ g ∈ J, (Fintype.piFinset (fun i => handAfter b a (g i + 1))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ J, b ^ t := by
        apply Finset.sum_le_sum
        intro g _
        rw [Fintype.card_piFinset]
        calc ∏ i, (handAfter b a (g i + 1)).card ≤ ∏ _i : Fin t, b :=
              Finset.prod_le_prod' (fun i _ => oram_handAfter_card b a _)
          _ = b ^ t := by simp
    _ = J.card * b ^ t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Nat.multichoose L t * b ^ t := Nat.mul_le_mul_right _ (oram_card_mono t L)

theorem oram_reconstruct {m : ℕ} (a' : List (Action m)) (V : List (Fin m)) (hV : visible a' = V) :
    ∃ H : Fin V.length → Hidden m, List.ofFn (fun i => (V.get i, H i)) = a' := by
  subst hV
  have hlen : (visible a').length = a'.length := by simp [visible]
  refine ⟨fun i => (a'.get (i.cast hlen)).2, ?_⟩
  apply List.ext_get
  · simp [visible]
  · intro n h1 h2
    simp only [List.get_eq_getElem, List.getElem_ofFn, Fin.val_cast]
    simp [visible]

theorem solution {b m t : ℕ} (P : ObliviousPlayer b m t)
    (r : Fin t → Fin m) (a : List (Action m)) (ha : a ∈ (P.play r).support) :
    m ^ t ≤ (b + 2) ^ a.length * (Nat.multichoose a.length t * b ^ t) := by
  set V := visible a with hVdef
  have hVlen : V.length = a.length := by simp [V, visible]
  -- every r' is satisfied by some run with visible sequence V
  have hcover : ∀ r' : Fin t → Fin m, ∃ H : Fin V.length → Hidden m,
      Legal b (List.ofFn fun i => (V.get i, H i)) ∧ Satisfies b (List.ofFn fun i => (V.get i, H i)) r' := by
    intro r'
    have hmem : V ∈ ((P.play r').map visible).support := by
      rw [← P.oblivious r r', PMF.support_map]
      exact ⟨a, ha, rfl⟩
    rw [PMF.support_map] at hmem
    obtain ⟨a', ha', hva'⟩ := hmem
    obtain ⟨H, hH⟩ := oram_reconstruct a' V hva'
    have hsat := P.correct r' a' ha'
    rw [← hH] at hsat
    exact ⟨H, hsat.1, hsat⟩
  let LH : Finset (Fin V.length → Hidden m) :=
    Finset.univ.filter fun H => Legal b (List.ofFn fun i => (V.get i, H i))
  have hsub : (Finset.univ : Finset (Fin t → Fin m)) ⊆ LH.biUnion (fun H =>
      Finset.univ.filter fun r' : Fin t → Fin m => Satisfies b (List.ofFn fun i => (V.get i, H i)) r') := by
    intro r' _
    obtain ⟨H, hl, hs⟩ := hcover r'
    rw [Finset.mem_biUnion]
    exact ⟨H, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hcard
  refine hcard.trans ?_
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ H ∈ LH, (Finset.univ.filter fun r' : Fin t → Fin m =>
          Satisfies b (List.ofFn fun i => (V.get i, H i)) r').card
      ≤ ∑ _H ∈ LH, Nat.multichoose a.length t * b ^ t := by
        apply Finset.sum_le_sum
        intro H _
        have := oram_card_sat (b := b) (t := t) (List.ofFn fun i => (V.get i, H i))
        refine this.trans (le_of_eq ?_)
        rw [List.length_ofFn, hVlen]
    _ = LH.card * (Nat.multichoose a.length t * b ^ t) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (b + 2) ^ a.length * (Nat.multichoose a.length t * b ^ t) := by
        apply Nat.mul_le_mul_right
        have := oram_card_hidden (b := b) V
        refine this.trans (le_of_eq ?_)
        rw [hVlen]
