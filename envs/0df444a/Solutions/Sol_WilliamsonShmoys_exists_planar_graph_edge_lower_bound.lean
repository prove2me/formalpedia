-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_graph_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:26:04.023658+00:00
-- url     : https://prove2.me/submissions/83975750-0a78-4a13-86c5-95c44e764815

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace Aux_planarLB

noncomputable def pos (m : ℕ) : ℝ × ℝ :=
  if m = 0 then (-1, 0) else if m = 1 then (1, 0) else (0, (m : ℝ))

noncomputable def seg (a b : ℕ) (t : ℝ) : ℝ × ℝ :=
  ((1 - t) * (pos a).1 + t * (pos b).1, (1 - t) * (pos a).2 + t * (pos b).2)

def R (a b : ℕ) : Prop := a ≠ b ∧ (a ≤ 1 ∨ b ≤ 1 ∨ a = b + 1 ∨ b = a + 1)

lemma pos0 : pos 0 = (-1, 0) := by simp [pos]
lemma pos1 : pos 1 = (1, 0) := by simp [pos]
lemma posb {m : ℕ} (h : 2 ≤ m) : pos m = (0, (m : ℝ)) := by
  have h0 : m ≠ 0 := by omega
  have h1 : m ≠ 1 := by omega
  simp [pos, h0, h1]

lemma kind {a b : ℕ} (hab : a < b) (h : R a b) :
    (a = 0 ∧ b = 1) ∨ (a = 0 ∧ 2 ≤ b) ∨ (a = 1 ∧ 2 ≤ b) ∨ (2 ≤ a ∧ b = a + 1) := by
  unfold R at h; omega

lemma kindv (m : ℕ) : m = 0 ∨ m = 1 ∨ 2 ≤ m := by omega

lemma pos_inj {a b : ℕ} (h : pos a = pos b) : a = b := by
  rcases kindv a with rfl | rfl | ha <;> rcases kindv b with rfl | rfl | hb
  · rfl
  · rw [pos0, pos1] at h; norm_num at h
  · rw [pos0, posb hb] at h; norm_num at h
  · rw [pos1, pos0] at h; norm_num at h
  · rfl
  · rw [pos1, posb hb] at h; norm_num at h
  · rw [posb ha, pos0] at h; norm_num at h
  · rw [posb ha, pos1] at h; norm_num at h
  · rw [posb ha, posb hb, Prod.mk.injEq] at h
    exact_mod_cast h.2

lemma seg_fst (a b : ℕ) (t : ℝ) : (seg a b t).1 = (1 - t) * (pos a).1 + t * (pos b).1 := rfl
lemma seg_snd (a b : ℕ) (t : ℝ) : (seg a b t).2 = (1 - t) * (pos a).2 + t * (pos b).2 := rfl

lemma seg_injOn {a b : ℕ} (hab : a < b) (h : R a b) : Set.InjOn (seg a b) (Set.Icc 0 1) := by
  intro t _ t' _ heq
  have e1 := congrArg Prod.fst heq
  have e2 := congrArg Prod.snd heq
  simp only [seg_fst, seg_snd] at e1 e2
  rcases kind hab h with ⟨rfl, rfl⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨ha, rfl⟩
  · simp only [pos0, pos1] at e1; linarith
  · simp only [pos0, posb hb] at e1; linarith
  · simp only [pos1, posb hb] at e1; linarith
  · simp only [posb ha, posb (show 2 ≤ a + 1 by omega)] at e2; push_cast at e2; linarith

lemma seg_avoid {a b : ℕ} (hab : a < b) (h : R a b) (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1)
    (m : ℕ) : seg a b t ≠ pos m := by
  obtain ⟨ht0, ht1⟩ := ht
  intro heq
  have e1 := congrArg Prod.fst heq
  have e2 := congrArg Prod.snd heq
  simp only [seg_fst, seg_snd] at e1 e2
  rcases kind hab h with ⟨rfl, rfl⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨ha, rfl⟩ <;>
    rcases kindv m with rfl | rfl | hm
  all_goals try simp only [pos0, pos1] at e1 e2
  all_goals first
    | linarith
    | (simp only [posb hm] at e1 e2; first
        | linarith
        | (have : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
           linarith))
    | (simp only [posb hb] at e1 e2; first
        | linarith
        | (simp only [posb hm] at e1 e2; linarith))
    | (simp only [posb ha, posb (show 2 ≤ a + 1 by omega)] at e1 e2; first
        | linarith
        | (simp only [posb hm] at e1 e2
           push_cast at e2
           rcases le_or_gt m a with hma | hma
           · have : (m:ℝ) ≤ a := by exact_mod_cast hma
             linarith
           · have : (a:ℝ) + 1 ≤ m := by exact_mod_cast hma
             linarith))

lemma cross {a b c d : ℕ} (hab : a < b) (hcd : c < d) (h1 : R a b) (h2 : R c d)
    (hne : ¬ (a = c ∧ b = d)) (t s : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (heq : seg a b t = seg c d s) :
    (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
  have e1 := congrArg Prod.fst heq
  have e2 := congrArg Prod.snd heq
  simp only [seg_fst, seg_snd] at e1 e2
  rcases kind hab h1 with ⟨rfl, rfl⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨ha, rfl⟩ <;>
    rcases kind hcd h2 with ⟨rfl, rfl⟩ | ⟨rfl, hd⟩ | ⟨rfl, hd⟩ | ⟨hc, rfl⟩
  -- E E
  · exact absurd ⟨rfl, rfl⟩ hne
  -- E A
  · simp only [pos0, pos1, posb hd] at e1 e2
    have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
    have hs : s = 0 := by nlinarith
    subst hs
    exact ⟨Or.inl (by linarith), Or.inl rfl⟩
  -- E B
  · simp only [pos0, pos1, posb hd] at e1 e2
    have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
    have hs : s = 0 := by nlinarith
    subst hs
    exact ⟨Or.inr (by linarith), Or.inl rfl⟩
  -- E C
  · simp only [pos0, pos1, posb hc, posb (show 2 ≤ c + 1 by omega)] at e1 e2
    push_cast at e2
    have hc' : (2:ℝ) ≤ c := by exact_mod_cast hc
    exfalso; linarith
  -- A E
  · simp only [pos0, pos1, posb hb] at e1 e2
    have hb' : (2:ℝ) ≤ b := by exact_mod_cast hb
    have ht : t = 0 := by nlinarith
    subst ht
    exact ⟨Or.inl rfl, Or.inl (by linarith)⟩
  -- A A
  · simp only [pos0, posb hb, posb hd] at e1 e2
    have hts : t = s := by linarith
    subst hts
    have hbd : b ≠ d := fun h => hne ⟨rfl, h⟩
    have hbd' : (b:ℝ) ≠ d := by exact_mod_cast hbd
    have : t * ((b:ℝ) - d) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact ⟨Or.inl h, Or.inl h⟩
    · exact absurd (by linarith) hbd'
  -- A B
  · simp only [pos0, pos1, posb hb, posb hd] at e1 e2
    exact ⟨Or.inr (by linarith), Or.inr (by linarith)⟩
  -- A C
  · simp only [pos0, posb hb, posb hc, posb (show 2 ≤ c + 1 by omega)] at e1 e2
    push_cast at e2
    have ht : t = 1 := by linarith
    subst ht
    refine ⟨Or.inr rfl, ?_⟩
    rcases le_or_gt b c with hbc | hbc
    · have : (b:ℝ) ≤ c := by exact_mod_cast hbc
      left; linarith
    · have : (c:ℝ) + 1 ≤ b := by exact_mod_cast hbc
      right; linarith
  -- B E
  · simp only [pos0, pos1, posb hb] at e1 e2
    have hb' : (2:ℝ) ≤ b := by exact_mod_cast hb
    have ht : t = 0 := by nlinarith
    subst ht
    exact ⟨Or.inl rfl, Or.inr (by linarith)⟩
  -- B A
  · simp only [pos0, pos1, posb hb, posb hd] at e1 e2
    exact ⟨Or.inr (by linarith), Or.inr (by linarith)⟩
  -- B B
  · simp only [pos1, posb hb, posb hd] at e1 e2
    have hts : t = s := by linarith
    subst hts
    have hbd : b ≠ d := fun h => hne ⟨rfl, h⟩
    have hbd' : (b:ℝ) ≠ d := by exact_mod_cast hbd
    have : t * ((b:ℝ) - d) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact ⟨Or.inl h, Or.inl h⟩
    · exact absurd (by linarith) hbd'
  -- B C
  · simp only [pos1, posb hb, posb hc, posb (show 2 ≤ c + 1 by omega)] at e1 e2
    push_cast at e2
    have ht : t = 1 := by linarith
    subst ht
    refine ⟨Or.inr rfl, ?_⟩
    rcases le_or_gt b c with hbc | hbc
    · have : (b:ℝ) ≤ c := by exact_mod_cast hbc
      left; linarith
    · have : (c:ℝ) + 1 ≤ b := by exact_mod_cast hbc
      right; linarith
  -- C E
  · simp only [pos0, pos1, posb ha, posb (show 2 ≤ a + 1 by omega)] at e1 e2
    push_cast at e2
    have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
    exfalso; linarith
  -- C A
  · simp only [pos0, posb hd, posb ha, posb (show 2 ≤ a + 1 by omega)] at e1 e2
    push_cast at e2
    have hs : s = 1 := by linarith
    subst hs
    refine ⟨?_, Or.inr rfl⟩
    rcases le_or_gt d a with hda | hda
    · have : (d:ℝ) ≤ a := by exact_mod_cast hda
      left; linarith
    · have : (a:ℝ) + 1 ≤ d := by exact_mod_cast hda
      right; linarith
  -- C B
  · simp only [pos1, posb hd, posb ha, posb (show 2 ≤ a + 1 by omega)] at e1 e2
    push_cast at e2
    have hs : s = 1 := by linarith
    subst hs
    refine ⟨?_, Or.inr rfl⟩
    rcases le_or_gt d a with hda | hda
    · have : (d:ℝ) ≤ a := by exact_mod_cast hda
      left; linarith
    · have : (a:ℝ) + 1 ≤ d := by exact_mod_cast hda
      right; linarith
  -- C C
  · simp only [posb ha, posb (show 2 ≤ a + 1 by omega), posb hc,
      posb (show 2 ≤ c + 1 by omega)] at e1 e2
    push_cast at e2
    have hac : a ≠ c := fun h => hne ⟨h, by rw [h]⟩
    rcases lt_or_gt_of_ne hac with h | h
    · have : (a:ℝ) + 1 ≤ c := by exact_mod_cast h
      exact ⟨Or.inr (by linarith), Or.inl (by linarith)⟩
    · have : (c:ℝ) + 1 ≤ a := by exact_mod_cast h
      exact ⟨Or.inl (by linarith), Or.inr (by linarith)⟩

end Aux_planarLB

open Aux_planarLB in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  set n := Fintype.card V with hn
  let e : V ≃o Fin n := (Fintype.orderIsoFinOfCardEq V rfl).symm
  let r : V → ℕ := fun v => (e v : ℕ)
  have hr_inj : Function.Injective r := fun u v h => e.injective (Fin.ext h)
  have hr_lt : ∀ u v : V, u < v → r u < r v := fun u v h => e.lt_iff_lt.mpr h
  let L : SimpleGraph V :=
    { Adj := fun u v => R (r u) (r v)
      symm := ⟨fun u v h => by
        change R (r u) (r v) at h
        change R (r v) (r u)
        unfold R at *; omega⟩
      loopless := ⟨fun u h => by
        change R (r u) (r u) at h
        unfold R at h; omega⟩ }
  have hLadj : ∀ u v, L.Adj u v ↔ R (r u) (r v) := fun u v => Iff.rfl
  refine ⟨L, ?_, ?_⟩
  · refine ⟨fun v => pos (r v), fun u v => seg (r u) (r v), ?_, ?_, ?_⟩
    · intro u v h
      exact hr_inj (pos_inj h)
    · intro u v huv hadj
      have hlt := hr_lt u v huv
      have hR : R (r u) (r v) := hadj
      refine ⟨?_, seg_injOn hlt hR, ?_, ?_, ?_⟩
      · apply Continuous.continuousOn
        unfold seg
        fun_prop
      · simp [seg]
      · simp [seg]
      · intro t ht w
        exact seg_avoid hlt hR t ht (r w)
    · intro u v x y huv hxy ha hb hne t ht s hs heq
      have hne' : ¬ (r u = r x ∧ r v = r y) := by
        rintro ⟨h1, h2⟩
        exact hne (by rw [hr_inj h1, hr_inj h2])
      exact cross (hr_lt u v huv) (hr_lt x y hxy) ha hb hne' t s ht.1 ht.2 hs.1 hs.2 heq
  · -- edge count
    let w : ℕ → V := fun m => e.symm ⟨min m (n - 1), by omega⟩
    have hw : ∀ m, m < n → r (w m) = m := by
      intro m hm
      simp only [r, w, OrderIso.apply_symm_apply]
      omega
    let S1 : Set (Sym2 V) := (fun k => s(w 0, w k)) '' Set.Ico 1 n
    let S2 : Set (Sym2 V) := (fun k => s(w 1, w k)) '' Set.Ico 2 n
    let S3 : Set (Sym2 V) := (fun k => s(w k, w (k + 1))) '' Set.Ico 2 (n - 1)
    have hsub : S1 ∪ S2 ∪ S3 ⊆ L.edgeSet := by
      rintro z ((⟨k, ⟨hk1, hk2⟩, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩) | ⟨k, ⟨hk1, hk2⟩, rfl⟩)
      · rw [SimpleGraph.mem_edgeSet, hLadj, hw 0 (by omega), hw k hk2]
        unfold R; omega
      · rw [SimpleGraph.mem_edgeSet, hLadj, hw 1 (by omega), hw k hk2]
        unfold R; omega
      · rw [SimpleGraph.mem_edgeSet, hLadj, hw k (by omega), hw (k + 1) (by omega)]
        unfold R; omega
    have hpair : ∀ a b c d : ℕ, a < n → b < n → c < n → d < n →
        s(w a, w b) = s(w c, w d) → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
      intro a b c d ha hb hc hd h
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        have h1' := congrArg r h1
        have h2' := congrArg r h2
        rw [hw a ha, hw c hc] at h1'
        rw [hw b hb, hw d hd] at h2'
        exact ⟨h1', h2'⟩
      · right
        have h1' := congrArg r h1
        have h2' := congrArg r h2
        rw [hw a ha, hw d hd] at h1'
        rw [hw b hb, hw c hc] at h2'
        exact ⟨h1', h2'⟩
    have hinj1 : Set.InjOn (fun k => s(w 0, w k)) (Set.Ico 1 n) := by
      intro k ⟨hk1, hk2⟩ k' ⟨hk1', hk2'⟩ h
      rcases hpair 0 k 0 k' (by omega) hk2 (by omega) hk2' h with h | h <;> omega
    have hinj2 : Set.InjOn (fun k => s(w 1, w k)) (Set.Ico 2 n) := by
      intro k ⟨hk1, hk2⟩ k' ⟨hk1', hk2'⟩ h
      rcases hpair 1 k 1 k' (by omega) hk2 (by omega) hk2' h with h | h <;> omega
    have hinj3 : Set.InjOn (fun k => s(w k, w (k + 1))) (Set.Ico 2 (n - 1)) := by
      intro k ⟨hk1, hk2⟩ k' ⟨hk1', hk2'⟩ h
      rcases hpair k (k + 1) k' (k' + 1) (by omega) (by omega) (by omega) (by omega) h
        with h | h <;> omega
    have hd12 : Disjoint S1 S2 := by
      rw [Set.disjoint_left]
      rintro z ⟨k, ⟨hk1, hk2⟩, rfl⟩ ⟨k', ⟨hk1', hk2'⟩, h⟩
      rcases hpair 1 k' 0 k (by omega) hk2' (by omega) hk2 h with h | h <;> omega
    have hd3 : Disjoint (S1 ∪ S2) S3 := by
      rw [Set.disjoint_left]
      rintro z (⟨k, ⟨hk1, hk2⟩, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩) ⟨k', ⟨hk1', hk2'⟩, h⟩
      · rcases hpair k' (k' + 1) 0 k (by omega) (by omega) (by omega) hk2 h with h | h <;> omega
      · rcases hpair k' (k' + 1) 1 k (by omega) (by omega) (by omega) hk2 h with h | h <;> omega
    have hc1 : S1.ncard = n - 1 := by rw [hinj1.ncard_image, Set.ncard_Ico_nat]
    have hc2 : S2.ncard = n - 2 := by rw [hinj2.ncard_image, Set.ncard_Ico_nat]
    have hc3 : S3.ncard = n - 1 - 2 := by rw [hinj3.ncard_image, Set.ncard_Ico_nat]
    have hU : (S1 ∪ S2 ∪ S3).ncard = (n - 1) + (n - 2) + (n - 1 - 2) := by
      rw [Set.ncard_union_eq hd3, Set.ncard_union_eq hd12, hc1, hc2, hc3]
    have hle : (S1 ∪ S2 ∪ S3).ncard ≤ L.edgeSet.ncard := Set.ncard_le_ncard hsub
    omega
