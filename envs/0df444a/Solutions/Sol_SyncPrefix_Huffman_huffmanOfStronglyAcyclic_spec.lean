-- Prove2me | solution 1 for SyncPrefix.Huffman.huffmanOfStronglyAcyclic_spec
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:13:28.276287+00:00
-- url     : https://prove2.me/submissions/f38b6a58-c024-460a-a487-5f93a57ba960

import Definitions.Def_SyncPrefix_Huffman_Automata
import Definitions.Def_SyncPrefix_Huffman_Lemma5Construction

open SyncPrefix.Huffman

private lemma run_nil {σ α : Type} (δ : σ → α → σ) (q : σ) : run δ q [] = q := rfl

private lemma run_cons {σ α : Type} (δ : σ → α → σ) (q : σ) (a : α) (w : List α) :
    run δ q (a :: w) = run δ (δ q a) w := rfl

private lemma run_append {σ α : Type} (δ : σ → α → σ) (q : σ) (u v : List α) :
    run δ q (u ++ v) = run δ (run δ q u) v :=
  List.foldl_append

private lemma run_isSink {σ α : Type} {δ : σ → α → σ} {f : σ} (hf : IsSink δ f) :
    ∀ w : List α, run δ f w = f
  | [] => rfl
  | a :: w => by rw [run_cons, hf a, run_isSink hf w]

private lemma finite_words_length_le (k B : ℕ) :
    {w : List (Fin k) | w.length ≤ B}.Finite := by
  let S : Finset (List (Fin k)) :=
    (Finset.range (B + 1)).biUnion (fun m =>
      (Finset.univ : Finset (Fin m → Fin k)).image List.ofFn)
  refine S.finite_toSet.subset (fun w hw => ?_)
  change w.length ≤ B at hw
  simp only [S, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact ⟨w.length, by omega, fun i => w.get i, List.ofFn_get w⟩

private lemma n_pos_of_isSynchronizing (A : Automaton) (hSync : IsSynchronizing A.δ) :
    0 < A.n := by
  rcases hSync with ⟨_, q, _⟩
  exact q.pos

private lemma k_pos_of_two_le_n (A : Automaton) (hSync : IsSynchronizing A.δ) (hn : 2 ≤ A.n) :
    1 ≤ A.k := by
  by_contra hk
  have hk0 : A.k = 0 := by omega
  rcases hSync with ⟨w, q, hq⟩
  cases w with
  | nil =>
    have h0 := hq ⟨0, by omega⟩
    have h1 := hq ⟨1, by omega⟩
    rw [run_nil] at h0 h1
    have h01 : (0 : ℕ) = 1 := congrArg Fin.val (h0.trans h1.symm)
    omega
  | cons a _ =>
    exact Fin.elim0 (hk0 ▸ a)

private lemma sync_of_n_eq_one {n k : ℕ} (hn : n = 1) (δ : Fin n → Fin k → Fin n) :
    IsHuffmanDecoder δ ∧ IsSynchronizing δ ∧ syncLength δ = 0 := by
  subst hn
  have hsub : ∀ p q : Fin 1, p = q := fun p q => Subsingleton.elim p q
  let r : Fin 1 := ⟨0, Nat.one_pos⟩
  have hsc : StronglyConnected δ := fun p q => ⟨[], hsub _ _⟩
  have hfr : {w : List (Fin k) | IsFirstReturn δ r w}.Finite := by
    refine (finite_words_length_le k 1).subset (fun w hw => ?_)
    change IsFirstReturn δ r w at hw
    change w.length ≤ 1
    by_contra hgt
    have h1 : 1 < w.length := by omega
    exact hw.2.2 1 zero_lt_one h1 (hsub _ _)
  have hsync_nil : IsSyncWord δ [] := ⟨r, fun q' => hsub _ _⟩
  refine ⟨⟨hsc, ⟨r, hfr⟩⟩, ⟨[], hsync_nil⟩, ?_⟩
  unfold syncLength
  exact Nat.le_zero.mp (Nat.sInf_le ⟨[], rfl, hsync_nil⟩)

private lemma sa_cycle_isSink {A : Automaton} (hSA : StronglyAcyclic A.δ)
    (q : Fin A.n) (w : List (Fin A.k)) (hw : w ≠ []) (hloop : run A.δ q w = q) :
    IsSink A.δ q := by
  cases w with
  | nil => contradiction
  | cons a u =>
    have h1 := hSA.1 q (a :: u) hloop 1 (by simp)
    simp only [List.take, run_cons, run_nil] at h1
    exact hSA.2 q a h1

private lemma sa_prefix_eq_isSink {A : Automaton} (hSA : StronglyAcyclic A.δ)
    (q₀ : Fin A.n) (w : List (Fin A.k)) {i j : ℕ} (hij : i < j) (hj : j ≤ w.length)
    (heq : run A.δ q₀ (w.take i) = run A.δ q₀ (w.take j)) :
    IsSink A.δ (run A.δ q₀ (w.take i)) := by
  have hsplit : w.take j = w.take i ++ (w.drop i).take (j - i) := by
    rw [← List.take_append_drop i (w.take j), List.take_take, Nat.min_eq_left (Nat.le_of_lt hij),
      List.drop_take]
  let u := (w.drop i).take (j - i)
  have hu_len : u.length = j - i := by
    simp only [u, List.length_take, List.length_drop]
    omega
  have hu_ne : u ≠ [] := by
    intro hnil
    rw [hnil, List.length_nil] at hu_len
    omega
  have hloop : run A.δ (run A.δ q₀ (w.take i)) u = run A.δ q₀ (w.take i) := by
    rw [← run_append, ← hsplit, ← heq]
  exact sa_cycle_isSink hSA (run A.δ q₀ (w.take i)) u hu_ne hloop

private lemma run_drop_take_eq {σ α : Type} (δ : σ → α → σ) (q₀ : σ) (w : List α) (i : ℕ) :
    run δ (run δ q₀ (w.take i)) (w.drop i) = run δ q₀ w := by
  rw [← run_append, List.take_append_drop]

private lemma sa_prefix_eq_run_eq {A : Automaton} (hSA : StronglyAcyclic A.δ)
    (q₀ : Fin A.n) (w : List (Fin A.k)) {i j : ℕ} (hij : i < j) (hj : j ≤ w.length)
    (heq : run A.δ q₀ (w.take i) = run A.δ q₀ (w.take j)) :
    run A.δ q₀ w = run A.δ q₀ (w.take i) ∧ IsSink A.δ (run A.δ q₀ w) := by
  have hsink := sa_prefix_eq_isSink hSA q₀ w hij hj heq
  have hrun : run A.δ q₀ w = run A.δ q₀ (w.take i) := by
    rw [← run_drop_take_eq A.δ q₀ w i, run_isSink hsink]
  exact ⟨hrun, hrun.symm ▸ hsink⟩

private lemma sa_run_length_ge_n_isSink {A : Automaton} (hSA : StronglyAcyclic A.δ)
    (q₀ : Fin A.n) (w : List (Fin A.k)) (hw : A.n ≤ w.length) :
    IsSink A.δ (run A.δ q₀ w) := by
  let g : Fin (A.n + 1) → Fin A.n := fun i => run A.δ q₀ (w.take i.val)
  have hnotinj : ∃ i j : Fin (A.n + 1), g i = g j ∧ i ≠ j := by
    by_contra h
    have hinj : Function.Injective g := fun i j hij => by
      by_contra hne
      exact h ⟨i, j, hij, hne⟩
    have hcard := Fintype.card_le_of_injective g hinj
    simp only [Fintype.card_fin] at hcard
    omega
  rcases hnotinj with ⟨i, j, hij_eq, hij_ne⟩
  rcases lt_trichotomy i.val j.val with hlt | heq_val | hgt
  · exact (sa_prefix_eq_run_eq hSA q₀ w hlt (by omega) hij_eq).2
  · exact absurd (Fin.ext heq_val) hij_ne
  · exact (sa_prefix_eq_run_eq hSA q₀ w hgt (by omega) hij_eq.symm).2

private lemma sink_unique {A : Automaton} (hSync : IsSynchronizing A.δ)
    {q₁ q₂ : Fin A.n} (h₁ : IsSink A.δ q₁) (h₂ : IsSink A.δ q₂) : q₁ = q₂ := by
  rcases hSync with ⟨w, q_sync, hw⟩
  have hq₁ := hw q₁
  have hq₂ := hw q₂
  rw [run_isSink h₁] at hq₁
  rw [run_isSink h₂] at hq₂
  exact hq₁.trans hq₂.symm

private lemma sinkOf_isSink (A : Automaton) (hSA : StronglyAcyclic A.δ)
    (_hSync : IsSynchronizing A.δ) (hn : 0 < A.n) (hk : 1 ≤ A.k) :
    IsSink A.δ (sinkOf A hn) := by
  let w := List.replicate A.n (⟨0, by omega⟩ : Fin A.k)
  have hsink₀ : IsSink A.δ (run A.δ ⟨0, hn⟩ w) :=
    sa_run_length_ge_n_isSink hSA ⟨0, hn⟩ w (by simp [w])
  let q₀ := run A.δ ⟨0, hn⟩ w
  have hmem : q₀ ∈ (List.finRange A.n).filter (fun q =>
      (List.finRange A.k).all fun a => decide (A.δ q a = q)) := by
    rw [List.mem_filter]
    refine ⟨List.mem_finRange q₀, ?_⟩
    rw [List.all_eq_true]
    intro a _
    exact decide_eq_true_eq.mpr (hsink₀ a)
  unfold sinkOf
  generalize hL : (List.finRange A.n).filter (fun q =>
      (List.finRange A.k).all fun a => decide (A.δ q a = q)) = L at hmem ⊢
  cases L with
  | nil => simp at hmem
  | cons q qs =>
    dsimp
    have hq_mem : q ∈ (List.finRange A.n).filter (fun q =>
        (List.finRange A.k).all fun a => decide (A.δ q a = q)) := by
      rw [hL]
      exact List.mem_cons_self
    rw [List.mem_filter, List.all_eq_true] at hq_mem
    intro a
    have ha := hq_mem.2 a (List.mem_finRange a)
    exact decide_eq_true_eq.mp ha

private lemma sa_run_length_ge_n_eq_sinkOf (A : Automaton) (hSA : StronglyAcyclic A.δ)
    (hSync : IsSynchronizing A.δ) (hn : 0 < A.n) (hk : 1 ≤ A.k)
    (q₀ : Fin A.n) (w : List (Fin A.k)) (hw : A.n ≤ w.length) :
    run A.δ q₀ w = sinkOf A hn :=
  sink_unique hSync (sa_run_length_ge_n_isSink hSA q₀ w hw) (sinkOf_isSink A hSA hSync hn hk)

private lemma mem_sourcesOf_iff (A : Automaton) (f : Fin A.n) (q : Fin A.n) :
    q ∈ sourcesOf A f ↔ q ≠ f ∧ ∀ p a, A.δ p a ≠ q := by
  simp [sourcesOf]

private lemma sourcesOf_nodup (A : Automaton) (f : Fin A.n) :
    (sourcesOf A f).Nodup :=
  (List.nodup_finRange A.n).filter _

private lemma exists_source_reaches (A : Automaton) (hSA : StronglyAcyclic A.δ)
    (hSync : IsSynchronizing A.δ) (hn : 0 < A.n) (hk : 1 ≤ A.k)
    (q : Fin A.n) (hq : q ≠ sinkOf A hn) :
    ∃ s ∈ sourcesOf A (sinkOf A hn), ∃ w : List (Fin A.k), run A.δ s w = q := by
  by_contra hnot
  have hchain : ∀ m : ℕ, ∃ (p : Fin A.n) (w : List (Fin A.k)),
      w.length = m ∧ run A.δ p w = q := by
    intro m
    induction m with
    | zero => exact ⟨q, [], rfl, rfl⟩
    | succ m ih =>
      rcases ih with ⟨p, w, hlen, hrun⟩
      have hpf : p ≠ sinkOf A hn := by
        intro heq
        subst heq
        rw [run_isSink (sinkOf_isSink A hSA hSync hn hk)] at hrun
        exact hq hrun.symm
      have hp_not_src : p ∉ sourcesOf A (sinkOf A hn) := fun hmem => hnot ⟨p, hmem, w, hrun⟩
      rw [mem_sourcesOf_iff] at hp_not_src
      have hex : ∃ p' a, A.δ p' a = p := by
        by_contra hall
        exact hp_not_src ⟨hpf, fun p' a hpa => hall ⟨p', a, hpa⟩⟩
      rcases hex with ⟨p', a, hp'a⟩
      exact ⟨p', a :: w, by simp [hlen], by rw [run_cons, hp'a, hrun]⟩
  rcases hchain A.n with ⟨p, w, hlen, hrun⟩
  have hsink := sa_run_length_ge_n_eq_sinkOf A hSA hSync hn hk p w (by omega)
  exact hq (hrun.symm.trans hsink)

private lemma sourcesOf_length_bounds (A : Automaton) (hSA : StronglyAcyclic A.δ)
    (hSync : IsSynchronizing A.δ) (hn2 : 2 ≤ A.n) (hk : 1 ≤ A.k) (hn : 0 < A.n) :
    1 ≤ (sourcesOf A (sinkOf A hn)).length ∧ (sourcesOf A (sinkOf A hn)).length ≤ A.n - 1 := by
  set f := sinkOf A hn
  constructor
  · have hex : ∃ q : Fin A.n, q ≠ f := by
      by_cases h0 : (⟨0, by omega⟩ : Fin A.n) = f
      · refine ⟨⟨1, by omega⟩, fun h1 => ?_⟩
        have h01 : (0 : ℕ) = 1 := congrArg Fin.val (h0.trans h1.symm)
        omega
      · exact ⟨⟨0, by omega⟩, h0⟩
    rcases hex with ⟨q, hq⟩
    rcases exists_source_reaches A hSA hSync hn hk q hq with ⟨s, hs, _⟩
    exact List.length_pos_of_mem hs
  · have hsub : (sourcesOf A f).toFinset ⊆ Finset.univ.erase f := by
      intro s hs
      rw [List.mem_toFinset, mem_sourcesOf_iff] at hs
      exact Finset.mem_erase.mpr ⟨hs.1, Finset.mem_univ s⟩
    have hcard := Finset.card_le_card hsub
    rw [List.card_toFinset, (sourcesOf_nodup A f).dedup, Finset.card_erase_of_mem (Finset.mem_univ f),
      Finset.card_univ, Fintype.card_fin] at hcard
    exact hcard

private lemma take_succ_eq_take_append {α : Type} :
    ∀ (w : List α) (i : ℕ) (hi : i < w.length),
      w.take (i + 1) = w.take i ++ [w.get ⟨i, hi⟩]
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | a :: u, 0, _ => rfl
  | a :: u, i + 1, hi => by
    simp only [List.take_succ_cons, List.get_cons_succ, List.cons_append]
    exact congrArg (a :: ·) (take_succ_eq_take_append u i (Nat.lt_of_succ_lt_succ hi))

private lemma sa_run_length_ge_d_eq_sinkOf (A : Automaton) (hSA : StronglyAcyclic A.δ)
    (hSync : IsSynchronizing A.δ) (hn2 : 2 ≤ A.n) (hk : 1 ≤ A.k) (hn : 0 < A.n)
    (q₀ : Fin A.n) (w : List (Fin A.k))
    (hw : A.n - (sourcesOf A (sinkOf A hn)).length ≤ w.length) :
    run A.δ q₀ w = sinkOf A hn := by
  have hbounds := sourcesOf_length_bounds A hSA hSync hn2 hk hn
  have hd_pos : 1 ≤ A.n - (sourcesOf A (sinkOf A hn)).length := by omega
  set f := sinkOf A hn
  set d := A.n - (sourcesOf A f).length
  let U : Finset (Fin A.n) := Finset.univ \ (sourcesOf A f).toFinset
  have hU_card : U.card = d := by
    have hsub : (sourcesOf A f).toFinset ⊆ Finset.univ := Finset.subset_univ _
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin, List.card_toFinset,
      (sourcesOf_nodup A f).dedup]
  have hf_mem_U : f ∈ U := by
    simp [U, mem_sourcesOf_iff]
  have hstep_mem_U : ∀ j : Fin d, run A.δ q₀ (w.take (j.val + 1)) ∈ U := by
    intro j
    have hj_lt : j.val < w.length := by omega
    rw [take_succ_eq_take_append w j.val hj_lt, run_append, run_cons, run_nil]
    simp only [U, Finset.mem_sdiff, Finset.mem_univ, List.mem_toFinset, mem_sourcesOf_iff, true_and]
    intro hsrc
    exact hsrc.2 (run A.δ q₀ (w.take j.val)) (w.get ⟨j.val, hj_lt⟩) rfl
  let g : Fin d → U := fun j => ⟨run A.δ q₀ (w.take (j.val + 1)), hstep_mem_U j⟩
  by_cases hinj : Function.Injective g
  · have hcard_eq : Fintype.card (Fin d) = Fintype.card U := by
      rw [Fintype.card_fin, Fintype.card_coe, hU_card]
    have hsurj : Function.Surjective g :=
      ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hinj, hcard_eq⟩).2
    rcases hsurj ⟨f, hf_mem_U⟩ with ⟨j, hj⟩
    have hj_val : run A.δ q₀ (w.take (j.val + 1)) = f := congrArg Subtype.val hj
    rw [← run_drop_take_eq A.δ q₀ w (j.val + 1), hj_val,
      run_isSink (sinkOf_isSink A hSA hSync hn hk)]
  · have hnotinj : ∃ i j : Fin d, g i = g j ∧ i ≠ j := by
      by_contra h
      exact hinj (fun i j hij => by by_contra hne; exact h ⟨i, j, hij, hne⟩)
    rcases hnotinj with ⟨i, j, hij_eq, hij_ne⟩
    have hij_val : run A.δ q₀ (w.take (i.val + 1)) = run A.δ q₀ (w.take (j.val + 1)) :=
      congrArg Subtype.val hij_eq
    rcases lt_trichotomy i.val j.val with hlt | heq_val | hgt
    · have h1 := (sa_prefix_eq_run_eq hSA q₀ w (by omega : i.val + 1 < j.val + 1)
        (by omega) hij_val).2
      exact sink_unique hSync h1 (sinkOf_isSink A hSA hSync hn hk)
    · exact absurd (Fin.ext heq_val) hij_ne
    · have h1 := (sa_prefix_eq_run_eq hSA q₀ w (by omega : j.val + 1 < i.val + 1)
        (by omega) hij_val.symm).2
      exact sink_unique hSync h1 (sinkOf_isSink A hSA hSync hn hk)

private lemma syncLength_le_d (A : Automaton) (hSA : StronglyAcyclic A.δ)
    (hSync : IsSynchronizing A.δ) (hn2 : 2 ≤ A.n) (hk : 1 ≤ A.k) (hn : 0 < A.n) :
    syncLength A.δ ≤ A.n - (sourcesOf A (sinkOf A hn)).length := by
  let d := A.n - (sourcesOf A (sinkOf A hn)).length
  let w := List.replicate d (⟨0, by omega⟩ : Fin A.k)
  have hsync_w : IsSyncWord A.δ w :=
    ⟨sinkOf A hn, fun q' => sa_run_length_ge_d_eq_sinkOf A hSA hSync hn2 hk hn q' w (by simp [w, d])⟩
  unfold syncLength
  exact Nat.sInf_le ⟨w, List.length_replicate, hsync_w⟩

private def δH (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k)
    (q : Fin (2 * A.n)) (a : Fin (A.k + 2)) : Fin (2 * A.n) :=
  let f : Fin A.n := sinkOf A hn
  let S : List (Fin A.n) := sourcesOf A f
  let d : ℕ := A.n - S.length
  if hq : q.val < A.n then
    let q₀ : Fin A.n := ⟨q.val, hq⟩
    if ha : a.val < A.k then
      let q' := A.δ q₀ ⟨a.val, ha⟩
      ⟨q'.val, by omega⟩
    else if q₀ = f then
      ⟨A.n, by omega⟩
    else
      let q' := A.δ q₀ ⟨0, hk⟩
      ⟨q'.val, by omega⟩
  else
    let i : ℕ := q.val - A.n
    if _ha : a.val < A.k then
      ⟨f.val, by omega⟩
    else if i < d then
      if hnext : i + 1 < A.n then
        ⟨A.n + (i + 1), by omega⟩
      else
        ⟨f.val, by omega⟩
    else
      let j : ℕ := i - d
      let s_j : Fin A.n := S.getD j f
      if a.val = A.k then
        ⟨s_j.val, by omega⟩
      else if hnext : i + 1 < A.n then
        ⟨A.n + (i + 1), by omega⟩
      else
        ⟨s_j.val, by omega⟩

private def embS {n : ℕ} (q : Fin n) : Fin (2 * n) := ⟨q.val, by omega⟩
private def embL {k : ℕ} (a : Fin k) : Fin (k + 2) := ⟨a.val, by omega⟩
private def b1 (k : ℕ) : Fin (k + 2) := ⟨k, by omega⟩
private def b2 (k : ℕ) : Fin (k + 2) := ⟨k + 1, by omega⟩
private def projL {k : ℕ} (hk : 0 < k) (x : Fin (k + 2)) : Fin k :=
  if hx : x.val < k then ⟨x.val, hx⟩ else ⟨0, hk⟩

private lemma δH_embS_embL (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k)
    (q : Fin A.n) (a : Fin A.k) :
    δH A hn hk (embS q) (embL a) = embS (A.δ q a) := by
  unfold δH embS embL
  simp [q.isLt, a.isLt]

private lemma δH_aux_embL (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k)
    (q : Fin (2 * A.n)) (hq : A.n ≤ q.val) (a : Fin A.k) :
    δH A hn hk q (embL a) = embS (sinkOf A hn) := by
  unfold δH embS embL
  have hnot : ¬ q.val < A.n := by omega
  simp [hnot, a.isLt]

private lemma δH_embS_ne_sink (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k)
    (q : Fin A.n) (hq : q ≠ sinkOf A hn) (x : Fin (A.k + 2)) :
    δH A hn hk (embS q) x = embS (A.δ q (projL hk x)) := by
  unfold δH embS projL
  simp only [q.isLt, hq, ↓reduceDIte, ↓reduceIte]
  split_ifs <;> rfl

private lemma δH_sink_b2 (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k) :
    δH A hn hk (embS (sinkOf A hn)) (b2 A.k) = ⟨A.n, by omega⟩ := by
  unfold δH embS b2
  have hnot : ¬ A.k + 1 < A.k := by omega
  simp [(sinkOf A hn).isLt, hnot]

private lemma δH_aux_b2 (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k)
    (i : ℕ) (hi : i + 1 < A.n) :
    δH A hn hk ⟨A.n + i, by omega⟩ (b2 A.k) = ⟨A.n + (i + 1), by omega⟩ := by
  apply Fin.ext
  unfold δH b2
  have hnot1 : ¬ A.n + i < A.n := by omega
  have hnot2 : ¬ A.k + 1 < A.k := by omega
  have hne : A.k + 1 ≠ A.k := by omega
  have hi' : (A.n + i) - A.n + 1 < A.n := by omega
  simp only [hnot1, hnot2, hne, hi', ↓reduceDIte, ↓reduceIte]
  split_ifs <;> dsimp <;> omega

private lemma δH_aux_b1_of_ge_d (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k)
    (j : ℕ) (hj : j < (sourcesOf A (sinkOf A hn)).length)
    (hdj : A.n - (sourcesOf A (sinkOf A hn)).length + j < A.n) :
    δH A hn hk ⟨A.n + (A.n - (sourcesOf A (sinkOf A hn)).length + j), by omega⟩ (b1 A.k) =
      embS ((sourcesOf A (sinkOf A hn)).get ⟨j, hj⟩) := by
  have hnot1 : ¬ A.n + (A.n - (sourcesOf A (sinkOf A hn)).length + j) < A.n := by omega
  have hnot2 : ¬ A.k < A.k := by omega
  have hnot3 : ¬ (A.n + (A.n - (sourcesOf A (sinkOf A hn)).length + j) - A.n) <
      A.n - (sourcesOf A (sinkOf A hn)).length := by omega
  have hsub : (A.n + (A.n - (sourcesOf A (sinkOf A hn)).length + j) - A.n) -
      (A.n - (sourcesOf A (sinkOf A hn)).length) = j := by omega
  unfold δH b1 embS
  simp only [hnot1, hnot2, hnot3, hsub, ↓reduceDIte, ↓reduceIte, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, Option.getD_some, List.get_eq_getElem]

private lemma run_δH_embS_map_embL (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k) :
    ∀ (w : List (Fin A.k)) (q : Fin A.n),
      run (δH A hn hk) (embS q) (w.map embL) = embS (run A.δ q w)
  | [], _ => rfl
  | a :: u, q => by
    simp only [List.map_cons, run_cons, δH_embS_embL, run_δH_embS_map_embL A hn hk u]

private lemma run_δH_map_embL_eq_sink (A : Automaton) (hSA : StronglyAcyclic A.δ)
    (hSync : IsSynchronizing A.δ) (hn : 0 < A.n) (hk : 0 < A.k)
    (w : List (Fin A.k)) (hw_ne : w ≠ []) (hw_sync : ∀ q, run A.δ q w = sinkOf A hn)
    (q : Fin (2 * A.n)) :
    run (δH A hn hk) q (w.map embL) = embS (sinkOf A hn) := by
  by_cases hq : q.val < A.n
  · have hq_eq : q = embS ⟨q.val, hq⟩ := rfl
    rw [hq_eq, run_δH_embS_map_embL, hw_sync]
  · cases w with
    | nil => contradiction
    | cons a u =>
      simp only [List.map_cons, run_cons]
      rw [δH_aux_embL A hn hk q (by omega) a, run_δH_embS_map_embL,
        run_isSink (sinkOf_isSink A hSA hSync hn (by omega))]

private lemma run_δH_embS_of_run_projL_ne_sink (A : Automaton) (hSA : StronglyAcyclic A.δ)
    (hSync : IsSynchronizing A.δ) (hn : 0 < A.n) (hk : 0 < A.k) :
    ∀ (w : List (Fin (A.k + 2))) (q : Fin A.n),
      run A.δ q (w.map (projL hk)) ≠ sinkOf A hn →
      run (δH A hn hk) (embS q) w = embS (run A.δ q (w.map (projL hk)))
  | [], _, _ => rfl
  | x :: u, q, hne => by
    have hqf : q ≠ sinkOf A hn := by
      intro heq
      subst heq
      exact hne (run_isSink (sinkOf_isSink A hSA hSync hn (by omega)) _)
    simp only [List.map_cons, run_cons] at hne ⊢
    rw [δH_embS_ne_sink A hn hk q hqf x]
    exact run_δH_embS_of_run_projL_ne_sink A hSA hSync hn hk u (A.δ q (projL hk x)) hne

private lemma step_δH_inDelay (A : Automaton) (hSA : StronglyAcyclic A.δ)
    (hSync : IsSynchronizing A.δ) (hn2 : 2 ≤ A.n) (hk : 0 < A.k) (hn : 0 < A.n)
    (t : ℕ) (ht : t < A.n - (sourcesOf A (sinkOf A hn)).length)
    (q : Fin (2 * A.n)) (hq : q = embS (sinkOf A hn) ∨ (A.n ≤ q.val ∧ q.val < A.n + t))
    (x : Fin (A.k + 2)) :
    let q' := δH A hn hk q x
    q' = embS (sinkOf A hn) ∨ (A.n ≤ q'.val ∧ q'.val < A.n + (t + 1)) := by
  have hbounds := sourcesOf_length_bounds A hSA hSync hn2 (by omega) hn
  have hsink := sinkOf_isSink A hSA hSync hn (by omega)
  rcases hq with rfl | ⟨hq1, hq2⟩
  · unfold δH embS
    simp only [(sinkOf A hn).isLt, ↓reduceDIte, ↓reduceIte]
    split_ifs with hx
    · left
      apply Fin.ext
      dsimp
      exact congrArg Fin.val (hsink ⟨x.val, hx⟩)
    · right
      dsimp
      omega
  · unfold δH embS
    have hnot : ¬ q.val < A.n := by omega
    have hi_d : q.val - A.n < A.n - (sourcesOf A (sinkOf A hn)).length := by omega
    have hi_n : (q.val - A.n) + 1 < A.n := by omega
    simp only [hnot, hi_d, hi_n, ↓reduceDIte, ↓reduceIte]
    split_ifs with hx
    · left; rfl
    · right; dsimp; omega

private lemma run_δH_inDelay (A : Automaton) (hSA : StronglyAcyclic A.δ)
    (hSync : IsSynchronizing A.δ) (hn2 : 2 ≤ A.n) (hk : 0 < A.k) (hn : 0 < A.n) :
    ∀ (w : List (Fin (A.k + 2))) (t : ℕ) (q : Fin (2 * A.n)),
      t + w.length ≤ A.n - (sourcesOf A (sinkOf A hn)).length →
      (q = embS (sinkOf A hn) ∨ (A.n ≤ q.val ∧ q.val < A.n + t)) →
      (run (δH A hn hk) q w = embS (sinkOf A hn) ∨ A.n ≤ (run (δH A hn hk) q w).val)
  | [], _, q, _, hq => hq.imp id And.left
  | x :: u, t, q, hlen, hq => by
    simp only [List.length_cons] at hlen
    have hstep := step_δH_inDelay A hSA hSync hn2 hk hn t (by omega) q hq x
    exact run_δH_inDelay A hSA hSync hn2 hk hn u (t + 1) (δH A hn hk q x) (by omega) hstep

private lemma run_δH_b2_replicate (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k) :
    ∀ (i : ℕ) (hi : i < A.n),
      run (δH A hn hk) (embS (sinkOf A hn)) (List.replicate (i + 1) (b2 A.k)) =
        ⟨A.n + i, by omega⟩
  | 0, _ => by
    simp only [List.replicate, run_cons, run_nil, δH_sink_b2, Nat.add_zero]
  | i + 1, hi => by
    rw [List.replicate_succ', run_append,
      run_δH_b2_replicate A hn hk i (by omega), run_cons, run_nil,
      δH_aux_b2 A hn hk i hi]

private lemma step_δH_aux_lt_or_inc (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k)
    (q : Fin (2 * A.n)) (hq : A.n ≤ q.val) (x : Fin (A.k + 2)) :
    (δH A hn hk q x).val < A.n ∨ (δH A hn hk q x).val = q.val + 1 := by
  unfold δH
  have hnot : ¬ q.val < A.n := by omega
  simp only [hnot, ↓reduceDIte]
  split_ifs <;> dsimp
  · left; exact (sinkOf A hn).isLt
  · right; omega
  · left; exact (sinkOf A hn).isLt
  · left; exact ((sourcesOf A (sinkOf A hn)).getD _ (sinkOf A hn)).isLt
  · right; omega
  · left; exact ((sourcesOf A (sinkOf A hn)).getD _ (sinkOf A hn)).isLt

private lemma aux_hits_lt_n (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k) :
    ∀ (m : ℕ) (q : Fin (2 * A.n)) (w : List (Fin (A.k + 2))),
      2 * A.n ≤ q.val + m → m ≤ w.length →
      ∃ t ≤ m, (run (δH A hn hk) q (w.take t)).val < A.n
  | 0, q, _, hqm, _ => absurd hqm (by have := q.isLt; omega)
  | m + 1, q, w, hqm, hlen => by
    by_cases hq : q.val < A.n
    · exact ⟨0, Nat.zero_le _, hq⟩
    · cases w with
      | nil => simp at hlen
      | cons x u =>
        simp only [List.length_cons] at hlen
        rcases step_δH_aux_lt_or_inc A hn hk q (by omega) x with hlt | hinc
        · refine ⟨1, by omega, ?_⟩
          simp only [List.take_succ_cons, List.take_zero, run_cons, run_nil]
          exact hlt
        · rcases aux_hits_lt_n A hn hk m (δH A hn hk q x) u (by omega) (by omega) with
            ⟨t, ht, hrun⟩
          refine ⟨t + 1, by omega, ?_⟩
          simp only [List.take_succ_cons, run_cons]
          exact hrun

private lemma embS_hits_sink (A : Automaton) (hn : 0 < A.n) (hk : 0 < A.k) :
    ∀ (v : List (Fin (A.k + 2))) (p : Fin A.n),
      run A.δ p (v.map (projL hk)) = sinkOf A hn →
      ∃ t ≤ v.length, run (δH A hn hk) (embS p) (v.take t) = embS (sinkOf A hn)
  | [], p, hrun => ⟨0, le_rfl, congrArg embS hrun⟩
  | x :: u, p, hrun => by
    by_cases hp : p = sinkOf A hn
    · exact ⟨0, Nat.zero_le _, congrArg embS hp⟩
    · simp only [List.map_cons, run_cons] at hrun
      rcases embS_hits_sink A hn hk u (A.δ p (projL hk x)) hrun with ⟨t, ht, ht_run⟩
      refine ⟨t + 1, by simp [ht], ?_⟩
      simp only [List.take_succ_cons, run_cons, δH_embS_ne_sink A hn hk p hp x, ht_run]

private lemma walk_hits_sink (A : Automaton) (hSA : StronglyAcyclic A.δ)
    (hSync : IsSynchronizing A.δ) (hn : 0 < A.n) (hk : 0 < A.k)
    (q : Fin (2 * A.n)) (v : List (Fin (A.k + 2))) (hv : 2 * A.n ≤ v.length) :
    ∃ t ≤ 2 * A.n, run (δH A hn hk) q (v.take t) = embS (sinkOf A hn) := by
  have ht1 : ∃ t₁ ≤ A.n, (run (δH A hn hk) q (v.take t₁)).val < A.n := by
    by_cases hq : q.val < A.n
    · exact ⟨0, Nat.zero_le _, hq⟩
    · exact aux_hits_lt_n A hn hk A.n q v (by omega) (by omega)
  rcases ht1 with ⟨t₁, ht₁_le, ht₁_lt⟩
  let p₁ : Fin A.n := ⟨(run (δH A hn hk) q (v.take t₁)).val, ht₁_lt⟩
  have hp₁_eq : run (δH A hn hk) q (v.take t₁) = embS p₁ := rfl
  let u := (v.drop t₁).take A.n
  have hu_len : u.length = A.n := by
    simp only [u, List.length_take, List.length_drop]
    omega
  have hu_sink : run A.δ p₁ (u.map (projL hk)) = sinkOf A hn :=
    sa_run_length_ge_n_eq_sinkOf A hSA hSync hn (by omega) p₁ (u.map (projL hk))
      (by simp [hu_len])
  rcases embS_hits_sink A hn hk u p₁ hu_sink with ⟨t₂, ht₂_le, ht₂_run⟩
  have ht₂_le_n : t₂ ≤ A.n := le_trans ht₂_le (le_of_eq hu_len)
  refine ⟨t₁ + t₂, by omega, ?_⟩
  have hsplit : v.take (t₁ + t₂) = v.take t₁ ++ u.take t₂ := by
    simp only [u, List.take_take, Nat.min_eq_left ht₂_le_n, List.take_add]
  rw [hsplit, run_append, hp₁_eq, ht₂_run]

theorem solution (A : Automaton)
    (hSA : StronglyAcyclic A.δ) (hSync : IsSynchronizing A.δ) :
    IsHuffmanDecoder (huffmanOfStronglyAcyclic A).δ ∧
      IsSynchronizing (huffmanOfStronglyAcyclic A).δ ∧
      syncLength (huffmanOfStronglyAcyclic A).δ = syncLength A.δ := by
  have hn_pos : 0 < A.n := n_pos_of_isSynchronizing A hSync
  let P (M : Automaton) : Prop :=
    IsHuffmanDecoder M.δ ∧ IsSynchronizing M.δ ∧ syncLength M.δ = syncLength A.δ
  change P (huffmanOfStronglyAcyclic A)
  unfold huffmanOfStronglyAcyclic
  split_ifs with h
  · dsimp only [P]
    rcases h with ⟨hn2, hk1⟩
    have hn : 0 < A.n := by omega
    have hk : 0 < A.k := by omega
    change IsHuffmanDecoder (δH A hn hk) ∧ IsSynchronizing (δH A hn hk) ∧
      syncLength (δH A hn hk) = syncLength A.δ
    set f := sinkOf A hn
    set S := sourcesOf A f
    set d := A.n - S.length
    have hsink : IsSink A.δ f := sinkOf_isSink A hSA hSync hn hk1
    have hbounds := sourcesOf_length_bounds A hSA hSync hn2 hk1 hn
    have hsync_w_sink : ∀ w : List (Fin A.k), IsSyncWord A.δ w →
        w ≠ [] ∧ ∀ q, run A.δ q w = f := by
      intro w ⟨q_sync, hw⟩
      have hfs : q_sync = f := by
        have hf_run := hw f
        rw [run_isSink hsink] at hf_run
        exact hf_run.symm
      subst hfs
      refine ⟨?_, hw⟩
      intro hnil
      subst hnil
      have h0 := hw ⟨0, by omega⟩
      have h1 := hw ⟨1, by omega⟩
      rw [run_nil] at h0 h1
      have h01 : (0 : ℕ) = 1 := congrArg Fin.val (h0.trans h1.symm)
      omega
    have hSyncH : IsSynchronizing (δH A hn hk) := by
      let w₀ := List.replicate A.n (⟨0, hk⟩ : Fin A.k)
      have hw₀_ne : w₀ ≠ [] := by
        intro hnil
        have hlen := congrArg List.length hnil
        simp [w₀] at hlen
        omega
      have hw₀_sync : ∀ q, run A.δ q w₀ = f :=
        fun q => sa_run_length_ge_n_eq_sinkOf A hSA hSync hn hk1 q w₀ (by simp [w₀])
      exact ⟨w₀.map embL, embS f,
        run_δH_map_embL_eq_sink A hSA hSync hn hk w₀ hw₀_ne hw₀_sync⟩
    have hSC : StronglyConnected (δH A hn hk) := by
      intro p q
      let w₀ := List.replicate A.n (⟨0, hk⟩ : Fin A.k)
      have hw₀_ne : w₀ ≠ [] := by
        intro hnil
        have hlen := congrArg List.length hnil
        simp [w₀] at hlen
        omega
      have hw₀_sync : ∀ q', run A.δ q' w₀ = f :=
        fun q' => sa_run_length_ge_n_eq_sinkOf A hSA hSync hn hk1 q' w₀ (by simp [w₀])
      have hp_to_f : run (δH A hn hk) p (w₀.map embL) = embS f :=
        run_δH_map_embL_eq_sink A hSA hSync hn hk w₀ hw₀_ne hw₀_sync p
      have hf_to_q : ∃ u : List (Fin (A.k + 2)), run (δH A hn hk) (embS f) u = q := by
        by_cases hq : q.val < A.n
        · let q₀ : Fin A.n := ⟨q.val, hq⟩
          have hq_eq : q = embS q₀ := rfl
          rw [hq_eq]
          by_cases hqf : q₀ = f
          · rw [hqf]; exact ⟨[], rfl⟩
          · rcases exists_source_reaches A hSA hSync hn hk1 q₀ hqf with ⟨s, hs_mem, w_s, hw_s⟩
            rcases List.mem_iff_get.mp hs_mem with ⟨idx, hidx⟩
            let j := idx.val
            have hj : j < S.length := idx.isLt
            have hdj : d + j < A.n := by omega
            let u₁ := List.replicate (d + j + 1) (b2 A.k) ++ [b1 A.k]
            have hu₁ : run (δH A hn hk) (embS f) u₁ = embS s := by
              dsimp only [u₁, f, d, S]
              rw [run_append, run_δH_b2_replicate A hn hk _ hdj, run_cons, run_nil,
                δH_aux_b1_of_ge_d A hn hk j hj hdj]
              exact congrArg embS hidx
            refine ⟨u₁ ++ w_s.map embL, ?_⟩
            rw [run_append, hu₁, run_δH_embS_map_embL, hw_s]
        · let i := q.val - A.n
          have hi : i < A.n := by omega
          have hq_eq : q = ⟨A.n + i, by omega⟩ := Fin.ext (by dsimp [i]; omega)
          rw [hq_eq]
          exact ⟨List.replicate (i + 1) (b2 A.k), run_δH_b2_replicate A hn hk i hi⟩
      rcases hf_to_q with ⟨u, hu⟩
      exact ⟨w₀.map embL ++ u, by rw [run_append, hp_to_f, hu]⟩
    have hFR_fin : {w : List (Fin (A.k + 2)) | IsFirstReturn (δH A hn hk) (embS f) w}.Finite := by
      refine (finite_words_length_le (A.k + 2) (2 * A.n + 1)).subset (fun w hw => ?_)
      change IsFirstReturn (δH A hn hk) (embS f) w at hw
      change w.length ≤ 2 * A.n + 1
      by_contra hgt
      cases w with
      | nil => exact hw.1 rfl
      | cons x v =>
        simp only [List.length_cons] at hgt
        rcases walk_hits_sink A hSA hSync hn hk (δH A hn hk (embS f) x) v (by omega) with
          ⟨t, ht_le, ht_run⟩
        have hi_pos : 0 < t + 1 := by omega
        have hi_lt : t + 1 < (x :: v).length := by simp; omega
        refine hw.2.2 (t + 1) hi_pos hi_lt ?_
        simp only [List.take_succ_cons, run_cons, f]
        exact ht_run
    have hLen_eq : syncLength (δH A hn hk) = syncLength A.δ := by
      apply le_antisymm
      · have ⟨wA, hwA⟩ := hSync
        have hspec : ∃ w : List (Fin A.k), w.length = syncLength A.δ ∧ IsSyncWord A.δ w :=
          @Nat.sInf_mem {ℓ | ∃ w : List (Fin A.k), w.length = ℓ ∧ IsSyncWord A.δ w}
            ⟨wA.length, wA, rfl, hwA⟩
        rcases hspec with ⟨w, hw_len, hw_sync⟩
        rcases hsync_w_sink w hw_sync with ⟨hw_ne, hw_f⟩
        have hsyncH_w : IsSyncWord (δH A hn hk) (w.map embL) :=
          ⟨embS f, run_δH_map_embL_eq_sink A hSA hSync hn hk w hw_ne hw_f⟩
        unfold syncLength at hw_len ⊢
        rw [← hw_len]
        exact Nat.sInf_le ⟨w.map embL, List.length_map embL, hsyncH_w⟩
      · have ⟨wH₀, hwH₀⟩ := hSyncH
        have hspec : ∃ w : List (Fin (A.k + 2)),
            w.length = syncLength (δH A hn hk) ∧ IsSyncWord (δH A hn hk) w :=
          @Nat.sInf_mem {ℓ | ∃ w : List (Fin (A.k + 2)), w.length = ℓ ∧ IsSyncWord (δH A hn hk) w}
            ⟨wH₀.length, wH₀, rfl, hwH₀⟩
        rcases hspec with ⟨w, hw_len, q_sync, hw_sync⟩
        rw [← hw_len]
        by_contra hlt
        have hd_le := syncLength_le_d A hSA hSync hn2 hk1 hn
        change syncLength A.δ ≤ d at hd_le
        have hw_le_d : w.length ≤ d := by omega
        have hf_inDelay := run_δH_inDelay A hSA hSync hn2 hk hn w 0 (embS f)
          (by change 0 + w.length ≤ d; omega) (Or.inl rfl)
        have hnot_syncA : ¬ IsSyncWord A.δ (w.map (projL hk)) := by
          intro hsyncA
          have hle : syncLength A.δ ≤ (w.map (projL hk)).length :=
            Nat.sInf_le ⟨w.map (projL hk), rfl, hsyncA⟩
          simp only [List.length_map] at hle
          omega
        have hex_ne : ∃ q₀ : Fin A.n, run A.δ q₀ (w.map (projL hk)) ≠ f := by
          by_contra hall
          exact hnot_syncA ⟨f, fun q₀ => by by_contra hne; exact hall ⟨q₀, hne⟩⟩
        rcases hex_ne with ⟨q₀, hq₀_ne⟩
        have hq₀_run := run_δH_embS_of_run_projL_ne_sink A hSA hSync hn hk w q₀ hq₀_ne
        have heq_runs : run (δH A hn hk) (embS q₀) w = run (δH A hn hk) (embS f) w :=
          (hw_sync (embS q₀)).trans (hw_sync (embS f)).symm
        rw [hq₀_run] at heq_runs
        rcases hf_inDelay with hf_eq | hf_ge
        · rw [hf_eq] at heq_runs
          have hval : (embS (run A.δ q₀ (w.map (projL hk)))).val = (embS (sinkOf A hn)).val :=
            congrArg Fin.val heq_runs
          exact hq₀_ne (Fin.ext hval)
        · rw [← heq_runs] at hf_ge
          have hlt_n : (embS (run A.δ q₀ (w.map (projL hk)))).val < A.n :=
            (run A.δ q₀ (w.map (projL hk))).isLt
          omega
    exact ⟨⟨hSC, ⟨embS f, hFR_fin⟩⟩, hSyncH, hLen_eq⟩
  · dsimp only [P]
    have hn1 : A.n = 1 := by
      by_contra hne1
      have hn2 : 2 ≤ A.n := by omega
      exact h ⟨hn2, k_pos_of_two_le_n A hSync hn2⟩
    obtain ⟨hHuff, hSync', hLen1⟩ :=
      sync_of_n_eq_one hn1 (fun (q : Fin A.n) (_ : Fin (A.k + 2)) => q)
    obtain ⟨_, _, hLen2⟩ := sync_of_n_eq_one hn1 A.δ
    exact ⟨hHuff, hSync', hLen1.trans hLen2.symm⟩
