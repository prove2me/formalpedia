-- Prove2me | solution 1 for OpenPitMIP.Hourglass.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:24:45.762543+00:00
-- url     : https://prove2.me/submissions/37071e80-b7da-4b8d-8902-1d38e5a27800

import Mathlib
import Definitions.Def_OpenPitMIP_Hourglass_Setting

namespace RRAux_OpenPitMIP_Hourglass_theorem_8

/-- Induction principle along a finite strict order: a property that holds on covering pairs and
composes holds on every related pair. -/
lemma rel_ind {C : Type} [Fintype C] (R : C → C → Prop) (hirr : ∀ a, ¬ R a a)
    (htr : ∀ a b c, R a b → R b c → R a c) (Q : C → C → Prop)
    (hbase : ∀ a b, R a b → (¬ ∃ m, R a m ∧ R m b) → Q a b)
    (hQtr : ∀ a m b, Q a m → Q m b → Q a b) : ∀ a b, R a b → Q a b := by
  classical
  suffices h : ∀ n, ∀ a b,
      (Finset.univ.filter (fun m => R a m ∧ R m b)).card = n → R a b → Q a b by
    intro a b hab; exact h _ a b rfl hab
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab
    by_cases hex : ∃ m, R a m ∧ R m b
    · obtain ⟨m, ham, hmb⟩ := hex
      have h1 : (Finset.univ.filter (fun k => R a k ∧ R k m)).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨m, by simp [ham, hmb], by simp [hirr m]⟩
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          exact ⟨hk.1, htr _ _ _ hk.2 hmb⟩
      have h2 : (Finset.univ.filter (fun k => R m k ∧ R k b)).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨m, by simp [ham, hmb], by simp [hirr m]⟩
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          exact ⟨htr _ _ _ ham hk.1, hk.2⟩
      exact hQtr a m b (ih _ h1 a m rfl ham) (ih _ h2 m b rfl hmb)
    · exact hbase a b hab hex

lemma fin_pos {QS QC U w sA sS sC : ℝ} (hU : U ≤ QS) (hw : w ≤ 1)
    (htot : sA + (sS + sC) ≤ U) :
    (QS + QC - U) * w + sA ≤ (QS - sS) + (w * QC - sC) := by
  have h := mul_nonneg (sub_nonneg.2 hU) (sub_nonneg.2 hw)
  nlinarith [h]

open OpenPitMIP.Hourglass in
lemma mem_blocksOf {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (X : Finset C) (b : B) : b ∈ I.blocksOf X ↔ I.clu b ∈ X := by
  simp [PCPSPC.blocksOf]

open OpenPitMIP.Hourglass in
lemma mem_rcl {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (c c' : C) : c' ∈ I.rcl c ↔ c' = c ∨ I.cprec c c' := by
  simp [PCPSPC.rcl]

open OpenPitMIP.Hourglass in
lemma mem_cl {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (c c' : C) : c' ∈ I.cl c ↔ c' = c ∨ I.cprec c' c := by
  simp [PCPSPC.cl]

end RRAux_OpenPitMIP_Hourglass_theorem_8

open RRAux_OpenPitMIP_Hourglass_theorem_8 in
open OpenPitMIP.Hourglass in
-- Theorem 8 (hourglass cuts), p. 1435.
theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C]
    [DecidableEq B] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (d : D) (t₁ t : Fin T) (ht : t₁ ≤ t)
    (cbar : C) (S : Finset B) (hS : S ⊆ I.blocksOf (I.cl cbar \ {cbar}))
    (hqS : I.Ucum d t₁ t ≤ I.qBlocks S) :
    ∀ (κ : Integrality) (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
      I.Feasible κ x y → I.DestCap y →
        (I.qBlocks (S ∪ I.blocksOf {cbar}) - I.Ucum d t₁ t) * PCPSPC.cum x cbar t
          + ∑ b ∈ I.blocksOf (I.rcl cbar \ {cbar}), I.q b * PCPSPC.ySum y b d t₁ t
        ≤ ∑ b ∈ S ∪ I.blocksOf {cbar},
            I.q b * (PCPSPC.cum x (I.clu b) t - PCPSPC.ySum y b d t₁ t) := by
  intro κ x y hF hcap
  obtain ⟨hxy, hsum1, hprec, _hG, hy0, hint⟩ := hF
  have := hI.strictOrder
  have hirr : ∀ a, ¬ I.cprec a a := fun a => irrefl_of I.cprec a
  have htr : ∀ a b c, I.cprec a b → I.cprec b c → I.cprec a c :=
    fun a b c => trans_of I.cprec
  have hq := hI.q_nonneg
  -- nonnegativity of x
  have hx0 : ∀ c s, 0 ≤ x c s := by
    intro c s
    obtain ⟨b, rfl⟩ := hI.clu_surjective c
    rw [hxy b s]
    exact Finset.sum_nonneg fun d' _ => hy0 b d' s
  have hw0 : ∀ c, 0 ≤ PCPSPC.cum x c t := fun c =>
    Finset.sum_nonneg fun s _ => hx0 c s
  have hw1 : ∀ c, PCPSPC.cum x c t ≤ 1 := by
    intro c
    refine le_trans ?_ (hsum1 c)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun s _ _ => hx0 c s)
  have hys0 : ∀ b, 0 ≤ PCPSPC.ySum y b d t₁ t := fun b =>
    Finset.sum_nonneg fun s _ => hy0 b d s
  have hys_le : ∀ b, PCPSPC.ySum y b d t₁ t ≤ PCPSPC.cum x (I.clu b) t := by
    intro b
    unfold PCPSPC.ySum PCPSPC.cum
    calc ∑ s ∈ Finset.Icc t₁ t, y b d s ≤ ∑ s ∈ Finset.Iic t, y b d s :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun s hs => by simp only [Finset.mem_Icc, Finset.mem_Iic] at hs ⊢; exact hs.2)
            (fun s _ _ => hy0 b d s)
      _ ≤ ∑ s ∈ Finset.Iic t, x (I.clu b) s := Finset.sum_le_sum fun s _ => by
          rw [hxy b s]
          exact Finset.single_le_sum (fun d' _ => hy0 b d' s) (Finset.mem_univ d)
  -- precedence monotonicity of w along the strict order
  have hmono : ∀ a b, I.cprec a b → PCPSPC.cum x b t ≤ PCPSPC.cum x a t :=
    rel_ind I.cprec hirr htr (fun a b => PCPSPC.cum x b t ≤ PCPSPC.cum x a t)
      (fun a b hab hno => hprec b a ⟨hab, hno⟩ t)
      (fun a m b h1 h2 => le_trans h2 h1)
  -- membership facts
  have hR : ∀ b ∈ I.blocksOf (I.rcl cbar \ {cbar}), I.cprec cbar (I.clu b) := by
    intro b hb
    rw [mem_blocksOf, Finset.mem_sdiff, mem_rcl, Finset.mem_singleton] at hb
    rcases hb.1 with h | h
    · exact absurd h hb.2
    · exact h
  have hSm : ∀ b ∈ S, I.cprec (I.clu b) cbar := by
    intro b hb
    have hb' := hS hb
    rw [mem_blocksOf, Finset.mem_sdiff, mem_cl, Finset.mem_singleton] at hb'
    rcases hb'.1 with h | h
    · exact absurd h hb'.2
    · exact h
  have hC : ∀ b ∈ I.blocksOf {cbar}, I.clu b = cbar := by
    intro b hb
    simpa [PCPSPC.blocksOf] using hb
  have d1 : Disjoint S (I.blocksOf {cbar}) := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    have := hSm b hb
    rw [hC b hb'] at this
    exact hirr _ this
  have d2 : Disjoint (I.blocksOf (I.rcl cbar \ {cbar})) (S ∪ I.blocksOf {cbar}) := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    have h1 := hR b hb
    rcases Finset.mem_union.1 hb' with h | h
    · exact hirr _ (htr _ _ _ h1 (hSm b h))
    · rw [hC b h] at h1; exact hirr _ h1
  -- total destination capacity
  have hU : ∑ b, I.q b * PCPSPC.ySum y b d t₁ t ≤ I.Ucum d t₁ t := by
    unfold PCPSPC.ySum PCPSPC.Ucum
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun s _ => hcap d s
  have htot : ∑ b ∈ I.blocksOf (I.rcl cbar \ {cbar}), I.q b * PCPSPC.ySum y b d t₁ t +
      (∑ b ∈ S, I.q b * PCPSPC.ySum y b d t₁ t +
        ∑ b ∈ I.blocksOf {cbar}, I.q b * PCPSPC.ySum y b d t₁ t) ≤ I.Ucum d t₁ t := by
    rw [← Finset.sum_union d1, ← Finset.sum_union d2]
    refine le_trans ?_ hU
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => mul_nonneg (hq b) (hys0 b))
  have hRHS0 : 0 ≤ ∑ b ∈ S ∪ I.blocksOf {cbar},
      I.q b * (PCPSPC.cum x (I.clu b) t - PCPSPC.ySum y b d t₁ t) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (hq b) (sub_nonneg.2 (hys_le b))
  rcases (hw0 cbar).lt_or_eq with hpos | hzero
  · -- w_{c̄,t} > 0: every strict predecessor is fully mined by t
    have hpred : ∀ c', I.cprec c' cbar → PCPSPC.cum x c' t = 1 := by
      cases κ with
      | F =>
        intro c' hc'
        have hne : PCPSPC.cum x cbar t ≠ 0 := ne_of_gt hpos
        obtain ⟨s, hs, hxs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
        have hx1 : x cbar s = 1 := (hint cbar s).resolve_left hxs
        have : x cbar s ≤ PCPSPC.cum x cbar t :=
          Finset.single_le_sum (fun s' _ => hx0 cbar s') hs
        have := hmono c' cbar hc'
        linarith [hw1 c']
      | P =>
        intro c' hc'
        exact rel_ind I.cprec hirr htr
          (fun a b => 0 < PCPSPC.cum x b t → PCPSPC.cum x a t = 1)
          (fun a b hab hno hb => hint b a ⟨hab, hno⟩ t hb)
          (fun a m b h1 h2 hb => h1 (by rw [h2 hb]; exact one_pos)) c' cbar hc' hpos
    have hRHS : ∑ b ∈ S ∪ I.blocksOf {cbar},
        I.q b * (PCPSPC.cum x (I.clu b) t - PCPSPC.ySum y b d t₁ t) =
        (I.qBlocks S - ∑ b ∈ S, I.q b * PCPSPC.ySum y b d t₁ t) +
        (PCPSPC.cum x cbar t * I.qBlocks (I.blocksOf {cbar}) -
          ∑ b ∈ I.blocksOf {cbar}, I.q b * PCPSPC.ySum y b d t₁ t) := by
      rw [Finset.sum_union d1]
      unfold PCPSPC.qBlocks
      rw [Finset.mul_sum]
      congr 1
      · rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [hpred _ (hSm b hb)]; ring
      · rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [hC b hb]; ring
    have hqU : I.qBlocks (S ∪ I.blocksOf {cbar}) =
        I.qBlocks S + I.qBlocks (I.blocksOf {cbar}) := by
      unfold PCPSPC.qBlocks; rw [Finset.sum_union d1]
    rw [hRHS, hqU]
    exact fin_pos hqS (hw1 cbar) htot
  · -- w_{c̄,t} = 0: the successors carry nothing up to t
    have hA : ∑ b ∈ I.blocksOf (I.rcl cbar \ {cbar}), I.q b * PCPSPC.ySum y b d t₁ t ≤ 0 := by
      refine Finset.sum_nonpos fun b hb => ?_
      have h1 := hmono _ _ (hR b hb)
      have h2 := hys_le b
      exact mul_nonpos_of_nonneg_of_nonpos (hq b) (by linarith)
    rw [← hzero, mul_zero, zero_add]
    linarith

#print axioms solution
