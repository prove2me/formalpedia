-- Prove2me | solution 2 for ZeroFreeRRG.Hardcore.potts_positive_zero_free
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:07:22.962646+00:00
-- url     : https://prove2.me/submissions/1ef72d9e-854b-47a5-bca7-ca2ee8c8bdf0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_lemma_4_17
import Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_5_1
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsThresholds
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Definitions.Def_PottsRapidMixing_Ensemble
open scoped Classical
open Set Filter Topology
namespace PottsRapidMixing
private lemma prob_le_one (n d : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    regularProb n d P ≤ 1 := by
  unfold regularProb
  have hcard : (((regularGraphs n d).filter P).card : ℝ) ≤ (regularGraphs n d).card := by
    exact_mod_cast Finset.card_filter_le (regularGraphs n d) P
  by_cases hz : (regularGraphs n d).card = 0
  · simp [hz]
  · have hp : (0:ℝ) < (regularGraphs n d).card := by exact_mod_cast Nat.pos_of_ne_zero hz
    exact (div_le_one hp).2 hcard

private lemma prob_inter_lower (n d : ℕ) (P Q : SimpleGraph (Fin n) → Prop) :
    regularProb n d P + regularProb n d Q - 1 ≤ regularProb n d (fun G => P G ∧ Q G) := by
  let s := regularGraphs n d
  let a := s.filter P
  let b := s.filter Q
  have hunion : a ∪ b ⊆ s := by
    intro x hx
    simp only [Finset.mem_union, a, b, Finset.mem_filter] at hx
    exact hx.elim (fun h => h.1) (fun h => h.1)
  have hinter : a ∩ b = s.filter (fun G => P G ∧ Q G) := by
    ext x
    simp [a, b, and_assoc, and_left_comm, and_comm]
  have hc : a.card + b.card ≤ s.card + (s.filter (fun G => P G ∧ Q G)).card := by
    have h := Finset.card_union_add_card_inter a b
    rw [hinter] at h
    have hu := Finset.card_le_card hunion
    omega
  have hc' : (a.card:ℝ) + b.card ≤ s.card + (s.filter (fun G => P G ∧ Q G)).card := by exact_mod_cast hc
  have hd : (0:ℝ) ≤ s.card := Nat.cast_nonneg _
  have hgoal : (a.card:ℝ) / s.card + (b.card:ℝ) / s.card - 1 ≤
      ((s.filter (fun G => P G ∧ Q G)).card:ℝ) / s.card := by
    by_cases hz : s.card = 0
    · have ha : a.card = 0 := Nat.eq_zero_of_le_zero (le_trans (Finset.card_filter_le s P) (le_of_eq hz))
      have hb : b.card = 0 := Nat.eq_zero_of_le_zero (le_trans (Finset.card_filter_le s Q) (le_of_eq hz))
      simp [hz]
    · have hp : (0:ℝ) < s.card := by exact_mod_cast Nat.pos_of_ne_zero hz
      have hdiv := div_le_div_of_nonneg_right hc' hd
      have hself : (s.card : ℝ) / s.card = 1 := div_self (ne_of_gt hp)
      rw [add_div, add_div, hself] at hdiv
      linarith
  unfold regularProb
  convert hgoal using 1 <;> simp only [s]
  congr 2
  congr 1
  ext x
  simp

private lemma withHighProb_inter (d : ℕ) {P Q : ∀ n, SimpleGraph (Fin n) → Prop}
    (hp : WithHighProb d P) (hq : WithHighProb d Q) :
    WithHighProb d (fun n G => P n G ∧ Q n G) := by
  unfold WithHighProb at *
  have hl := (hp.add hq).sub (tendsto_const_nhds (x := (1:ℝ)))
  have hl' : Tendsto (fun n => regularProb n d (P n) + regularProb n d (Q n) - 1)
      (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (𝓝 1) := by simpa using hl
  exact hl'.squeeze tendsto_const_nhds
    (fun n => prob_inter_lower n d (P n) (Q n))
    (fun n => prob_le_one n d (fun G => P n G ∧ Q n G))
end PottsRapidMixing

namespace PottsRapidMixing
private lemma prob_mono (n d : ℕ) (P Q : SimpleGraph (Fin n) → Prop)
    (h : ∀ G, P G → Q G) : regularProb n d P ≤ regularProb n d Q := by
  unfold regularProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsub : (regularGraphs n d).filter P ⊆ (regularGraphs n d).filter Q := by
    intro G hG
    simp only [Finset.mem_filter] at hG ⊢
    exact ⟨hG.1, h G hG.2⟩
  exact_mod_cast Finset.card_le_card hsub

private lemma withHighProb_mono (d : ℕ) {P Q : ∀ n, SimpleGraph (Fin n) → Prop}
    (hp : WithHighProb d P) (h : ∀ n G, P n G → Q n G) : WithHighProb d Q := by
  unfold WithHighProb at *
  exact hp.squeeze tendsto_const_nhds
    (fun n => prob_mono n d (P n) (Q n) (h n)) (fun n => prob_le_one n d (Q n))

private lemma withHighProb_finite (d : ℕ) {ι : Type*} (s : Finset ι)
    (P : ι → ∀ n, SimpleGraph (Fin n) → Prop)
    (Q : ∀ n, SimpleGraph (Fin n) → Prop)
    (hQ : WithHighProb d Q) (hP : ∀ i ∈ s, WithHighProb d (P i)) :
    WithHighProb d (fun n G => Q n G ∧ ∀ i ∈ s, P i n G) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      apply withHighProb_mono d hQ
      simp
  | @insert a s ha ih =>
      have hs : ∀ i ∈ s, WithHighProb d (P i) := by
        intro i hi
        exact hP i (Finset.mem_insert_of_mem hi)
      have ha' : WithHighProb d (P a) := hP a (Finset.mem_insert_self a s)
      have hi := withHighProb_inter d (ih hs) ha'
      apply withHighProb_mono d hi
      intro n G h
      exact ⟨h.1.1, fun i hi => by
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact h.2
        · exact h.1.2 i hi⟩
end PottsRapidMixing


namespace ZeroFreeRRG.Hardcore

private theorem betaRSB_nonneg (d q : ℕ) : 0 ≤ betaRSB d q := by
  unfold betaRSB
  split_ifs with he
  · exact le_rfl
  · have hne : (pottsWitness d q).Nonempty := Set.nonempty_iff_ne_empty.mpr he
    obtain ⟨x,hx⟩ := hne
    have hb : BddAbove (pottsWitness d q) := ⟨1, fun y hy => hy.2.1.le⟩
    exact le_trans hx.1.le (le_csSup hb hx)

private theorem rs_above_rsb (d q : ℕ) (β : ℝ) (hb : betaRSB d q < β)
    (hb1 : β < 1) : VariationalRS (.potts q) d β := by
  intro ν hν
  by_contra hn
  have hβpos : 0 < β := lt_of_le_of_lt (betaRSB_nonneg d q) hb
  have hm : β ∈ pottsWitness d q := ⟨hβpos,hb1,ν,hν,lt_of_not_ge hn⟩
  have hbounded : BddAbove (pottsWitness d q) := ⟨1, fun x hx => hx.2.1.le⟩
  have hle : β ≤ betaRSB d q := by
    unfold betaRSB
    rw [if_neg (Set.nonempty_iff_ne_empty.mp ⟨β,hm⟩)]
    exact le_csSup hbounded hm
  linarith

private theorem interior_above_rsb (d q : ℕ) (β : ℝ)
    (hb : betaRSB d q < β) (hb1 : β < 1) :
    InteriorVariationalRS (.potts q) d β := by
  let β' := (betaRSB d q + β)/2
  have hb' : betaRSB d q < β' := by dsimp [β']; linarith
  have h'β : β' < β := by dsimp [β']; linarith
  exact ⟨β', (lt_of_le_of_lt (betaRSB_nonneg d q) hb').le, h'β,
    rs_above_rsb d q β' hb' (lt_trans h'β hb1)⟩

theorem _root_.solution (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) (δ : ℝ)
    (hδ : 0 < δ) (hδmax : δ < 1 - betaRSB d q) :
    ∃ η : ℝ, 0 < η ∧
      PottsRapidMixing.WithHighProb d (fun n G =>
        ∀ β ∈ nbhd (realSegment (betaRSB d q + δ) 1) η, pottsZ q G β ≠ 0) := by
  classical
  let a := betaRSB d q + δ
  let K := realSegment a 1
  have ha : 0 < a := by dsimp [a]; linarith [betaRSB_nonneg d q]
  have ha1 : a < 1 := by dsimp [a]; linarith
  have har : betaRSB d q < a := by dsimp [a]; linarith
  have hK : IsCompact K := by
    apply IsCompact.image (isCompact_Icc : IsCompact (Icc a (1:ℝ)))
    exact Complex.continuous_ofReal
  have hlocal : ∀ x : K, ∃ U : Set ℂ, IsOpen U ∧ x.val ∈ U ∧
      PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, pottsZ q G z ≠ 0) := by
    intro x
    obtain ⟨t,ht,heq⟩ := x.property
    change (t : ℂ) = x.val at heq
    rw [← heq]
    have h5 := theorem_5_1 (.potts q) hq d hd
    by_cases ht1 : t = 1
    · rcases h5.2 with ⟨U,hUo,hUmem,hU⟩
      refine ⟨U,hUo,?_,?_⟩
      · simpa [ht1,Model.indepEndpoint] using hUmem
      · simpa [Model.Zgraph] using hU
    · have htpos : 0 < t := lt_of_lt_of_le ha ht.1
      have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      have htr : betaRSB d q < t := lt_of_lt_of_le har ht.1
      have hc := (potts_lemma_4_17 d q hd hq).1 t htpos htlt
        (interior_above_rsb d q t htr htlt)
      rcases h5.1 t ⟨htpos.le, htlt⟩ hc.1 hc.2 with ⟨U,hUo,hUmem,hU⟩
      exact ⟨U,hUo,hUmem,by simpa [Model.Zgraph] using hU⟩
  choose V hVo hVmem hVprob using hlocal
  have hcover : K ⊆ ⋃ x : K, V x := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,hVmem ⟨z,hz⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hVo hcover
  let U : Set ℂ := ⋃ x ∈ s, V x
  have hUo : IsOpen U := by
    apply isOpen_iUnion
    intro x
    apply isOpen_iUnion
    intro hx
    exact hVo x
  obtain ⟨η,hη,hηsub⟩ := hK.exists_cthickening_subset_open hUo hs
  have hone : (1:ℂ) ∈ K := by
    exact ⟨1,⟨ha1.le,le_rfl⟩,by simp⟩
  let x0 : K := ⟨1,hone⟩
  have hprob := PottsRapidMixing.withHighProb_finite d s
    (fun x n G => ∀ z ∈ V x, pottsZ q G z ≠ 0)
    (fun n G => ∀ z ∈ V x0, pottsZ q G z ≠ 0)
    (hVprob x0) (fun x _ => hVprob x)
  refine ⟨η,hη,?_⟩
  apply PottsRapidMixing.withHighProb_mono d hprob
  intro n G hgood α hα
  obtain ⟨w,hw,haw⟩ := hα
  have hthick : α ∈ Metric.cthickening η K := by
    apply Metric.mem_cthickening_of_dist_le α w η K hw
    rw [dist_eq_norm]
    exact haw.le
  have hmem : α ∈ U := hηsub hthick
  simp only [U, mem_iUnion] at hmem
  obtain ⟨x,hx,hαx⟩ := hmem
  exact hgood.2 x hx α hαx
end ZeroFreeRRG.Hardcore
