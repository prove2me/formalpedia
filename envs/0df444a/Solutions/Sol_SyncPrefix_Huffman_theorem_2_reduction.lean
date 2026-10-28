-- Prove2me | solution 1 for SyncPrefix.Huffman.theorem_2_reduction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T22:41:17.062183+00:00
-- url     : https://prove2.me/submissions/21248189-3588-4f2b-b810-d0ecd5b1b597

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

open SyncPrefix.Huffman SetCoverThreshold.SetCover

lemma t2r_lt (I : SCInstance) (q : Fin (scAutomaton I).n) : q.val < I.n * I.n + 1 := q.isLt

def t2rF (I : SCInstance) : Fin (scAutomaton I).n := ⟨I.n * I.n, Nat.lt_succ_self _⟩

lemma t2r_delta_f (I : SCInstance) (a : Fin (scAutomaton I).k) :
    (scAutomaton I).δ (t2rF I) a = t2rF I := by
  simp [scAutomaton, t2rF]

lemma t2r_run_f (I : SCInstance) (w : List (Fin (scAutomaton I).k)) :
    run (scAutomaton I).δ (t2rF I) w = t2rF I := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    show run _ ((scAutomaton I).δ (t2rF I) a) w = _
    rw [t2r_delta_f]; exact ih

lemma t2r_delta_gt (I : SCInstance) (q : Fin (scAutomaton I).n) (a : Fin (scAutomaton I).k)
    (h : q.val < I.n * I.n) : q.val < ((scAutomaton I).δ q a).val := by
  simp only [scAutomaton]
  rw [dif_pos h]
  split_ifs <;> simp <;> omega

lemma t2r_delta_ge (I : SCInstance) (q : Fin (scAutomaton I).n) (a : Fin (scAutomaton I).k) :
    q.val ≤ ((scAutomaton I).δ q a).val := by
  by_cases h : q.val < I.n * I.n
  · exact (t2r_delta_gt I q a h).le
  · have := t2r_lt I q
    simp only [scAutomaton]
    rw [dif_neg h]
    simp; omega

lemma t2r_run_ge (I : SCInstance) (w : List (Fin (scAutomaton I).k)) :
    ∀ q : Fin (scAutomaton I).n, q.val ≤ (run (scAutomaton I).δ q w).val := by
  induction w with
  | nil => intro q; exact le_refl _
  | cons a w ih =>
    intro q
    exact le_trans (t2r_delta_ge I q a) (ih _)

lemma t2r_div (q p : ℕ) (hp : 0 < p) (h : ¬ q % p + 1 = p) : (q + 1) / p = q / p := by
  have h1 := Nat.mod_lt q hp
  have h2 := Nat.div_add_mod q p
  have h3 : q + 1 = (q % p + 1) + p * (q / p) := by omega
  rw [h3, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega), zero_add]

lemma t2r_cover (I : SCInstance) (j : Fin I.n) :
    ∀ (w : List (Fin (scAutomaton I).k)) (q : Fin (scAutomaton I).n),
      (q.val < I.n * I.n → q.val / I.n = j.val) → (∃ a ∈ w, j ∈ I.sets.get a) →
        run (scAutomaton I).δ q w = t2rF I := by
  intro w
  induction w with
  | nil => intro q _ h; simp at h
  | cons a w ih =>
    intro q hq ⟨b, hb, hjb⟩
    show run _ ((scAutomaton I).δ q a) w = _
    rcases List.mem_cons.1 hb with rfl | hb'
    · have : (scAutomaton I).δ q b = t2rF I := by
        by_cases h : q.val < I.n * I.n
        · simp only [scAutomaton]
          rw [dif_pos h, if_pos]
          · rfl
          · right
            have : (⟨q.val / I.n, Nat.div_lt_of_lt_mul h⟩ : Fin I.n) = j := Fin.ext (hq h)
            rw [this]; exact hjb
        · simp only [scAutomaton]
          rw [dif_neg h]; rfl
      rw [this]; exact t2r_run_f I w
    · apply ih _ _ ⟨b, hb', hjb⟩
      intro hlt
      by_cases h : q.val < I.n * I.n
      · have hp : 0 < I.n := by
          rcases Nat.eq_zero_or_pos I.n with h0 | h0
          · rw [h0] at h; simp at h
          · exact h0
        revert hlt
        simp only [scAutomaton]
        rw [dif_pos h]
        split_ifs with h2
        · simp
        · intro _
          simp only
          push_neg at h2
          rw [t2r_div _ _ hp h2.1]
          exact hq h
      · exfalso
        have := t2r_delta_ge I q a
        omega

lemma t2r_pipe (I : SCInstance) (j : Fin I.n) :
    ∀ (w : List (Fin (scAutomaton I).k)) (i : ℕ) (q : Fin (scAutomaton I).n),
      q.val = j.val * I.n + i → i + w.length < I.n → (∀ a ∈ w, j ∉ I.sets.get a) →
        (run (scAutomaton I).δ q w).val = j.val * I.n + i + w.length := by
  intro w
  induction w with
  | nil => intro i q hq _ _; simpa [run] using hq
  | cons a w ih =>
    intro i q hq hi hw
    show (run _ ((scAutomaton I).δ q a) w).val = _
    have hp : 0 < I.n := by simp at hi; omega
    have hj := j.isLt
    have hqlt : q.val < I.n * I.n := by
      rw [hq]; simp at hi; nlinarith
    have hmod : q.val % I.n = i := by
      rw [hq, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by simp at hi; omega)]
    have hdiv : q.val / I.n = j.val := by
      rw [hq, add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (by simp at hi; omega),
        zero_add]
    have hstep : ((scAutomaton I).δ q a).val = q.val + 1 := by
      simp only [scAutomaton]
      rw [dif_pos hqlt, if_neg]
      push_neg
      refine ⟨by rw [hmod]; simp at hi; omega, ?_⟩
      have : (⟨q.val / I.n, Nat.div_lt_of_lt_mul hqlt⟩ : Fin I.n) = j := Fin.ext hdiv
      rw [this]
      exact hw a (List.mem_cons_self ..)
    have := ih (i + 1) ((scAutomaton I).δ q a) (by rw [hstep, hq]; ring)
      (by simp at hi ⊢; omega) (fun b hb => hw b (List.mem_cons_of_mem _ hb))
    rw [this]; simp; ring

lemma t2r_sync_target (I : SCInstance) (w : List (Fin (scAutomaton I).k))
    (hw : IsSyncWord (scAutomaton I).δ w) : ∀ q, run (scAutomaton I).δ q w = t2rF I := by
  obtain ⟨q0, hq0⟩ := hw
  have : q0 = t2rF I := by rw [← hq0 (t2rF I), t2r_run_f]
  intro q; rw [hq0 q, this]

theorem solution (I : SCInstance) (hI : I.Coverable) :
    (scAutomaton I).n = I.n ^ 2 + 1 ∧ (scAutomaton I).k = I.sets.length ∧
      StronglyAcyclic (scAutomaton I).δ ∧ IsSynchronizing (scAutomaton I).δ ∧
        syncLength (scAutomaton I).δ = minCover I := by
  have hget : ∀ x : Fin I.n, ∃ i : Fin I.sets.length, x ∈ I.sets.get i := by
    intro x
    obtain ⟨S, hS, hxS⟩ := hI x
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 hS
    exact ⟨i, by rw [hi]; exact hxS⟩
  have hCov : I.IsCover Finset.univ := by
    intro x
    obtain ⟨i, hi⟩ := hget x
    exact ⟨i, Finset.mem_univ _, hi⟩
  obtain ⟨C0, hC0, hC0card⟩ : ∃ C, I.IsCover C ∧ C.card = minCover I :=
    Nat.sInf_mem (s := {c | ∃ C, I.IsCover C ∧ C.card = c}) ⟨_, Finset.univ, hCov, rfl⟩
  have hsync0 : IsSyncWord (scAutomaton I).δ C0.toList := by
    refine ⟨t2rF I, fun q => ?_⟩
    by_cases hq : q.val < I.n * I.n
    · obtain ⟨i, hi, hji⟩ := hC0 ⟨q.val / I.n, Nat.div_lt_of_lt_mul hq⟩
      exact t2r_cover I ⟨q.val / I.n, Nat.div_lt_of_lt_mul hq⟩ _ q (fun _ => rfl)
        ⟨i, Finset.mem_toList.2 hi, hji⟩
    · have : q = t2rF I := by
        have := t2r_lt I q
        exact Fin.ext (by simp [t2rF]; omega)
      rw [this]; exact t2r_run_f I _
  refine ⟨by simp [scAutomaton, sq], rfl, ⟨?_, ?_⟩, ⟨_, hsync0⟩, ?_⟩
  · intro q w hw i hi
    have h1 := t2r_run_ge I (w.take i) q
    have h2 := t2r_run_ge I (w.drop i) (run (scAutomaton I).δ q (w.take i))
    have h3 : run (scAutomaton I).δ q w =
        run (scAutomaton I).δ (run (scAutomaton I).δ q (w.take i)) (w.drop i) := by
      conv_lhs => rw [← List.take_append_drop i w]
      exact List.foldl_append
    rw [← h3, hw] at h2
    exact Fin.ext (le_antisymm h2 h1)
  · intro q a hqa b
    have hq : ¬ q.val < I.n * I.n := by
      intro h
      have := t2r_delta_gt I q a h
      rw [hqa] at this; exact lt_irrefl _ this
    simp only [scAutomaton]
    rw [dif_neg hq]
    have := t2r_lt I q
    exact Fin.ext (by simp; omega)
  · apply le_antisymm
    · rw [← hC0card, ← Finset.length_toList]
      exact Nat.sInf_le ⟨_, rfl, hsync0⟩
    · obtain ⟨w, hwlen, hw⟩ : ∃ w : List (Fin (scAutomaton I).k),
          w.length = syncLength (scAutomaton I).δ ∧ IsSyncWord (scAutomaton I).δ w :=
        Nat.sInf_mem (s := {ℓ | ∃ w : List (Fin (scAutomaton I).k), w.length = ℓ ∧
          IsSyncWord (scAutomaton I).δ w}) ⟨_, _, rfl, hsync0⟩
      rw [← hwlen]
      have htarget := t2r_sync_target I w hw
      by_cases hlen : w.length < I.n
      · have hC : I.IsCover w.toFinset := by
          intro x
          by_contra hn
          push_neg at hn
          have hx := x.isLt
          have hqlt : x.val * I.n + 0 < (scAutomaton I).n := by
            show _ < I.n * I.n + 1; nlinarith
          have := t2r_pipe I x w 0 ⟨x.val * I.n + 0, hqlt⟩ rfl (by omega)
            (fun a ha => hn a (List.mem_toFinset.2 ha))
          rw [htarget] at this
          simp [t2rF] at this
          nlinarith
        exact le_trans (Nat.sInf_le ⟨_, hC, rfl⟩) (List.toFinset_card_le w)
      · let g : Fin I.n → Fin I.sets.length := fun x => Classical.choose (hget x)
        have hC : I.IsCover (Finset.univ.image g) := by
          intro x
          exact ⟨g x, Finset.mem_image_of_mem _ (Finset.mem_univ _),
            Classical.choose_spec (hget x)⟩
        have : (Finset.univ.image g).card ≤ I.n := by
          have := Finset.card_image_le (s := (Finset.univ : Finset (Fin I.n))) (f := g)
          simpa using this
        exact le_trans (Nat.sInf_le ⟨_, hC, rfl⟩) (by omega)
