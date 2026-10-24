-- Prove2me | solution 1 for TreewidthApprox.Pushed.lemma_6_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T14:41:06.950816+00:00
-- url     : https://prove2.me/submissions/6593fa16-9447-4f9c-99be-85d812403c07

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Definitions.Def_TreewidthApprox_Pushed_Setting

set_option autoImplicit false

namespace TwSepAux

open TreewidthApprox.Pushed

section Tree

variable {V T : Type} [Fintype V] [DecidableEq V] [Fintype T] [DecidableEq T]

/-- `P` is a union of branches of the tree `t` at the node `s`. -/
def Closed (t : SimpleGraph T) (s : T) (P : Finset T) : Prop :=
  s ∉ P ∧ ∀ u ∈ P, ∀ w, t.Adj u w → w ≠ s → w ∈ P

/-- Vertices in bags of `P`, minus the bag at `s`. -/
def Scut (Xb : T → Finset V) (s : T) (P : Finset T) : Finset V :=
  P.biUnion Xb \ Xb s

lemma walk_hits {t : SimpleGraph T} {s : T} {P : Finset T} (hc : Closed t s P) :
    ∀ {u w : T} (p : t.Walk u w), u ∈ P → w ∉ P → s ∈ p.support := by
  intro u w p
  induction p with
  | nil => intro hu hw; exact absurd hu hw
  | @cons a b c h p ih =>
    intro ha hc'
    by_cases hb : b = s
    · subst hb
      simp
    · have hbP : b ∈ P := hc.2 a ha b h hb
      have := ih hbP hc'
      simp [this]

lemma walk_adj {t : SimpleGraph T} {s : T} {P : Finset T} (hc : Closed t s P) :
    ∀ {u w : T} (p : t.Walk u w), u ∈ P → w = s → ∃ x ∈ P, t.Adj x s := by
  intro u w p
  induction p with
  | nil => intro hu hw; subst hw; exact absurd hu hc.1
  | @cons a b c h p ih =>
    intro ha hcs
    by_cases hb : b = s
    · subst hb
      exact ⟨a, ha, h⟩
    · exact ih (hc.2 a ha b h hb) hcs

lemma sep_of_cut {G : SimpleGraph V} {t : SimpleGraph T} {Xb : T → Finset V}
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G t Xb) {s : T} {P : Finset T}
    (hc : Closed t s P) :
    IsSeparation G (Scut Xb s P) (Xb s) ((Finset.univ \ Xb s) \ Scut Xb s P) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Finset.disjoint_left]
    intro a ha ha'
    simp [Scut] at ha
    exact ha.2 ha'
  · rw [Finset.disjoint_left]
    intro a ha ha'
    simp at ha'
    exact ha'.2 ha
  · rw [Finset.disjoint_left]
    intro a ha ha'
    simp at ha'
    exact ha'.1 ha
  · ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    tauto
  · intro a ha b hb hab
    simp only [Scut, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and] at ha hb
    obtain ⟨⟨w, hwP, haw⟩, has⟩ := ha
    obtain ⟨hbs, hbS⟩ := hb
    obtain ⟨u, hau, hbu⟩ := htd.2.2.1 a b hab
    by_cases huP : u ∈ P
    · exact hbS ⟨⟨u, huP, hbu⟩, hbs⟩
    · by_cases hus : u = s
      · subst hus; exact has hau
      · obtain ⟨p⟩ := htd.1.connected.preconnected w u
        have hsp : s ∈ p.bypass.support := walk_hits hc p.bypass hwP huP
        have := htd.2.2.2 w s u p.bypass p.bypass_isPath hsp
        exact has (this (Finset.mem_inter.mpr ⟨haw, hau⟩))

lemma tree_sep {G : SimpleGraph V} {t : SimpleGraph T} {Xb : T → Finset V} (k : ℕ)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G t Xb)
    (hw : ∀ s, (Xb s).card ≤ k + 1) :
    ∃ L X R : Finset V, IsSeparation G L X R ∧ X.card ≤ k + 1 ∧
      Fintype.card V ≤ 4 * L.card + 4 * (k + 1) ∧ 4 * L.card ≤ 3 * Fintype.card V := by
  set n := Fintype.card V with hn
  have key : ∀ m : ℕ, ∀ (s : T) (P : Finset T), P.card = m → Closed t s P →
      n ≤ 4 * (Scut Xb s P).card + 4 * (k + 1) →
      ∃ L X R : Finset V, IsSeparation G L X R ∧ X.card ≤ k + 1 ∧
        n ≤ 4 * L.card + 4 * (k + 1) ∧ 4 * L.card ≤ 3 * n := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro s P hPm hc hb
    by_cases h3 : 4 * (Scut Xb s P).card ≤ 3 * n
    · exact ⟨_, _, _, sep_of_cut htd hc, hw s, hb, h3⟩
    push_neg at h3
    -- P is nonempty
    have hPne : P.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp [Scut] at h3
    obtain ⟨u0, hu0⟩ := hPne
    obtain ⟨p0⟩ := htd.1.connected.preconnected u0 s
    obtain ⟨s', hs'P, hs's⟩ := walk_adj hc p0 hu0 rfl
    classical
    set Q := P.filter (fun w => ∃ p : t.Walk s' w, ∀ z ∈ p.support, z ∈ P) with hQ
    have hs'Q : s' ∈ Q := by
      rw [hQ, Finset.mem_filter]
      exact ⟨hs'P, SimpleGraph.Walk.nil, by simpa using hs'P⟩
    by_cases hQP : ∃ w ∈ P, w ∉ Q
    · obtain ⟨w0, hw0P, hw0Q⟩ := hQP
      have hQsub : Q ⊆ P := Finset.filter_subset _ _
      have hcQ : Closed t s Q := by
        refine ⟨fun h => hc.1 (hQsub h), ?_⟩
        intro u hu w huw hws
        rw [hQ, Finset.mem_filter] at hu ⊢
        obtain ⟨huP, p, hp⟩ := hu
        have hwP : w ∈ P := hc.2 u huP w huw hws
        refine ⟨hwP, p.concat huw, ?_⟩
        intro z hz
        rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | hz
        · exact hp z hz
        · rw [hz]; exact hwP
      have hcPQ : Closed t s (P \ Q) := by
        refine ⟨fun h => hc.1 (Finset.mem_sdiff.mp h).1, ?_⟩
        intro u hu w huw hws
        rw [Finset.mem_sdiff] at hu ⊢
        have hwP : w ∈ P := hc.2 u hu.1 w huw hws
        refine ⟨hwP, ?_⟩
        intro hwQ
        apply hu.2
        rw [hQ, Finset.mem_filter] at hwQ ⊢
        obtain ⟨_, p, hp⟩ := hwQ
        refine ⟨hu.1, p.concat huw.symm, ?_⟩
        intro z hz
        rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | hz
        · exact hp z hz
        · rw [hz]; exact hu.1
      have hcardQ : Q.card < m := by
        rw [← hPm]
        exact Finset.card_lt_card ⟨hQsub, fun h => hw0Q (h hw0P)⟩
      have hcardPQ : (P \ Q).card < m := by
        rw [← hPm]
        exact Finset.card_lt_card ⟨Finset.sdiff_subset, fun h => (Finset.mem_sdiff.mp (h hs'P)).2 hs'Q⟩
      have hsub : Scut Xb s P ⊆ Scut Xb s Q ∪ Scut Xb s (P \ Q) := by
        intro v hv
        simp only [Scut, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_union] at hv ⊢
        obtain ⟨⟨w, hwP, hvw⟩, hvs⟩ := hv
        by_cases hwQ : w ∈ Q
        · exact Or.inl ⟨⟨w, hwQ, hvw⟩, hvs⟩
        · exact Or.inr ⟨⟨w, ⟨hwP, hwQ⟩, hvw⟩, hvs⟩
      have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      by_cases hbig : (Scut Xb s P).card ≤ 2 * (Scut Xb s Q).card
      · exact ih _ hcardQ s Q rfl hcQ (by omega)
      · exact ih _ hcardPQ s (P \ Q) rfl hcPQ (by omega)
    · push_neg at hQP
      -- every node of P is reachable from s' inside P
      set P' := P.erase s' with hP'
      have hcP' : Closed t s' P' := by
        refine ⟨Finset.notMem_erase _ _, ?_⟩
        intro u hu w huw hws'
        rw [hP', Finset.mem_erase] at hu
        by_cases hws : w = s
        · exfalso
          subst hws
          have huQ := hQP u hu.2
          rw [hQ, Finset.mem_filter] at huQ
          obtain ⟨_, p, hp⟩ := huQ
          have hsnot : w ∉ p.bypass.support := by
            intro hm
            exact hc.1 (hp w (SimpleGraph.Walk.support_bypass_subset_support p hm))
          have hsne : s' ≠ w := hs's.ne
          have hpath : (SimpleGraph.Walk.cons hs's (SimpleGraph.Walk.cons huw.symm
              SimpleGraph.Walk.nil)).IsPath := by
            simp only [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.isPath_iff_eq_nil,
              SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false, true_and]
            refine ⟨?_, ?_⟩
            · exact fun h => huw.ne h.symm
            · rintro (h | h)
              · exact hsne h
              · exact hu.1 h.symm
          have heq := htd.1.isAcyclic.path_unique ⟨p.bypass, p.bypass_isPath⟩ ⟨_, hpath⟩
          apply hsnot
          rw [show p.bypass = _ from congrArg Subtype.val heq]
          simp
        · rw [hP', Finset.mem_erase]
          exact ⟨hws', hc.2 u hu.2 w huw hws⟩
      have hcardP' : P'.card < m := by
        rw [← hPm, hP']
        exact Finset.card_erase_lt_of_mem hs'P
      have hsub : Scut Xb s P ⊆ Scut Xb s' P' ∪ Xb s' := by
        intro v hv
        simp only [Scut, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_union, hP',
          Finset.mem_erase] at hv ⊢
        obtain ⟨⟨w, hwP, hvw⟩, hvs⟩ := hv
        by_cases hws : w = s'
        · subst hws; exact Or.inr hvw
        · by_cases hv' : v ∈ Xb s'
          · exact Or.inr hv'
          · exact Or.inl ⟨⟨w, ⟨hws, hwP⟩, hvw⟩, hv'⟩
      have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have := hw s'
      exact ih _ hcardP' s' P' rfl hcP' (by omega)
  -- start
  have : Nonempty T := htd.1.connected.nonempty
  obtain s0 : T := Classical.arbitrary T
  have hc0 : Closed t s0 (Finset.univ.erase s0) := by
    refine ⟨Finset.notMem_erase _ _, ?_⟩
    intro u _ w _ hws
    simp [hws]
  have hsub0 : Finset.univ \ Xb s0 ⊆ Scut Xb s0 (Finset.univ.erase s0) := by
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
    obtain ⟨w, hw'⟩ := htd.2.1 v
    simp only [Scut, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ,
      and_true]
    refine ⟨⟨w, ?_, hw'⟩, hv⟩
    rintro rfl
    exact hv hw'
  have hc1 := Finset.card_le_card hsub0
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at hc1
  have := hw s0
  exact key _ s0 _ rfl hc0 (by omega)

end Tree

section Glue

variable {V : Type} [Fintype V] [DecidableEq V]

lemma part_mem {W P₁ P₂ P₃ : Finset V} (h : IsPartition3 W P₁ P₂ P₃) (v : V) :
    (v ∈ W ↔ v ∈ P₁ ∨ v ∈ P₂ ∨ v ∈ P₃) ∧ (v ∈ P₁ → v ∉ P₂) ∧ (v ∈ P₁ → v ∉ P₃) ∧
      (v ∈ P₂ → v ∉ P₃) := by
  obtain ⟨h12, h13, h23, hU⟩ := h
  refine ⟨?_, fun h1 h2 => Finset.disjoint_left.mp h12 h1 h2,
    fun h1 h3 => Finset.disjoint_left.mp h13 h1 h3, fun h2 h3 => Finset.disjoint_left.mp h23 h2 h3⟩
  rw [← hU]
  simp [or_assoc]

lemma part_of_mem {W P₁ P₂ P₃ : Finset V}
    (h : ∀ v, (v ∈ W ↔ v ∈ P₁ ∨ v ∈ P₂ ∨ v ∈ P₃) ∧ (v ∈ P₁ → v ∉ P₂) ∧ (v ∈ P₁ → v ∉ P₃) ∧
      (v ∈ P₂ → v ∉ P₃)) : IsPartition3 W P₁ P₂ P₃ := by
  refine ⟨Finset.disjoint_left.mpr fun {v} h1 h2 => (h v).2.1 h1 h2,
    Finset.disjoint_left.mpr fun {v} h1 h2 => (h v).2.2.1 h1 h2,
    Finset.disjoint_left.mpr fun {v} h1 h2 => (h v).2.2.2 h1 h2, ?_⟩
  ext v
  simp [(h v).1, or_assoc]

lemma sep_swap {G : SimpleGraph V} {L X R : Finset V} (h : IsSeparation G L X R) :
    IsSeparation G R X L := by
  refine ⟨part_of_mem fun v => ?_, fun a ha b hb hab => h.2 b hb a ha hab.symm⟩
  have e := part_mem h.1 v
  simp only [Finset.mem_univ, true_iff] at e ⊢
  tauto

lemma tsep_restrict {G : SimpleGraph V} {L X R A₁ B A₂ : Finset V}
    (hLXR : IsSeparation G L X R) (hsep : IsSeparation G A₁ B A₂) :
    IsTerminalSep G (A₁ ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A₁).card
      (L ∩ (A₁ ∪ (B \ (X ∩ B)))) (X ∩ A₁) (R ∩ (A₁ ∪ (B \ (X ∩ B)))) := by
  refine ⟨part_of_mem fun v => ?_, ?_, ?_, ?_, le_rfl⟩
  · have e := part_mem hLXR.1 v
    have eS := part_mem hsep.1 v
    simp only [Finset.mem_univ, true_iff, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter] at e eS ⊢
    grind
  · intro v hv
    have e := part_mem hLXR.1 v
    simp only [Finset.mem_univ, true_iff, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter] at e hv ⊢
    grind
  · intro v hv
    have e := part_mem hLXR.1 v
    simp only [Finset.mem_univ, true_iff, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter] at e hv ⊢
    grind
  · intro a ha b hb hab
    exact hLXR.2 a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1 hab

lemma glue (G : SimpleGraph V) (k : ℕ) (A₁ B A₂ : Finset V) (hsep : IsSeparation G A₁ B A₂)
    (L X R : Finset V) (hLXR : IsSeparation G L X R) (hX : X.card ≤ k + 1)
    (h1 : Fintype.card V ≤ 8 * (L ∩ (A₁ ∪ B)).card + 4 * (B.card + (k + 1)))
    (h2 : Fintype.card V ≤ 8 * (R ∩ (A₂ ∪ B)).card + 4 * (B.card + (k + 1))) :
    ∃ (TL XB TR : Finset V) (k₁ k₂ : ℕ),
      IsPartition3 B TL XB TR ∧ k₁ + k₂ + XB.card ≤ k + 1 ∧
      (∃ L X R : Finset V, IsTerminalSep G (A₁ ∪ (B \ XB)) TL TR k₁ L X R) ∧
      (∃ L X R : Finset V, IsTerminalSep G (A₂ ∪ (B \ XB)) TL TR k₂ L X R) ∧
      ∀ L₁ X₁ R₁ L₂ X₂ R₂ : Finset V,
        IsLeftPushed G (A₁ ∪ (B \ XB)) TL TR k₁ L₁ X₁ R₁ →
        IsRightPushed G (A₂ ∪ (B \ XB)) TL TR k₂ L₂ X₂ R₂ →
        IsTerminalSep G Finset.univ TL TR (k + 1) (L₁ ∪ TL ∪ L₂) (X₁ ∪ XB ∪ X₂) (R₁ ∪ TR ∪ R₂) ∧
        ((L₁ ∪ TL ∪ L₂).card : ℝ) ≤ 7 / 8 * Fintype.card V + ((B.card : ℝ) + (k + 1)) / 2 ∧
        ((R₁ ∪ TR ∪ R₂).card : ℝ) ≤ 7 / 8 * Fintype.card V + ((B.card : ℝ) + (k + 1)) / 2 := by
  have hT1 := tsep_restrict hLXR hsep
  have hsep' : IsSeparation G A₂ B A₁ := sep_swap hsep
  have hT2 := tsep_restrict hLXR hsep'
  have hpB : IsPartition3 B (L ∩ B) (X ∩ B) (R ∩ B) := by
    refine part_of_mem fun v => ?_
    have e := part_mem hLXR.1 v
    simp only [Finset.mem_univ, true_iff, Finset.mem_inter] at e ⊢
    grind
  have hcardX : (X ∩ A₁).card + (X ∩ A₂).card + (X ∩ B).card ≤ k + 1 := by
    have d12 : Disjoint (X ∩ A₁) (X ∩ A₂) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hsep.1.2.1)
    have d3 : Disjoint (X ∩ A₁ ∪ X ∩ A₂) (X ∩ B) := by
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hsep.1.1),
        Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hsep.1.2.2.1.symm)⟩
    have hsub : X ∩ A₁ ∪ X ∩ A₂ ∪ X ∩ B ⊆ X := by
      intro v hv
      simp only [Finset.mem_union, Finset.mem_inter] at hv
      grind
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d12] at this
    omega
  refine ⟨L ∩ B, X ∩ B, R ∩ B, (X ∩ A₁).card, (X ∩ A₂).card, hpB, hcardX, ⟨_, _, _, hT1⟩,
    ⟨_, _, _, hT2⟩, ?_⟩
  intro L₁ X₁ R₁ L₂ X₂ R₂ hP1 hP2
  have hL1big := hP1.2 _ _ _ hT1
  have hR2big := hP2.2 _ _ _ hT2
  obtain ⟨hp1, hTL1, hTR1, hne1, hc1⟩ := hP1.1
  obtain ⟨hp2, hTL2, hTR2, hne2, hc2⟩ := hP2.1
  have hglue : IsTerminalSep G Finset.univ (L ∩ B) (R ∩ B) (k + 1) (L₁ ∪ (L ∩ B) ∪ L₂)
      (X₁ ∪ (X ∩ B) ∪ X₂) (R₁ ∪ (R ∩ B) ∪ R₂) := by
    refine ⟨part_of_mem fun v => ?_, ?_, ?_, ?_, ?_⟩
    · have e1 := part_mem hp1 v
      have e2 := part_mem hp2 v
      have eS := part_mem hsep.1 v
      have eL := part_mem hLXR.1 v
      have t1 := @hTL1 v
      have t2 := @hTR1 v
      have t3 := @hTL2 v
      have t4 := @hTR2 v
      simp only [Finset.mem_univ, true_iff, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_inter] at e1 e2 eS eL t1 t2 t3 t4 ⊢
      rcases eS.1 with hv | hv | hv
      · have : v ∉ B := fun h => eS.2.1 hv h
        have : v ∉ A₂ := fun h => eS.2.2.1 hv h
        grind
      · have : v ∉ A₁ := fun h => eS.2.1 h hv
        have : v ∉ A₂ := fun h => eS.2.2.2 hv h
        grind
      · have : v ∉ B := fun h => eS.2.2.2 h hv
        have : v ∉ A₁ := fun h => eS.2.2.1 h hv
        grind
    · intro v hv
      simp only [Finset.mem_union]
      exact Or.inl (Or.inr hv)
    · intro v hv
      simp only [Finset.mem_union]
      exact Or.inl (Or.inr hv)
    · intro a ha b hb hab
      have ea1 := part_mem hp1 a
      have ea2 := part_mem hp2 a
      have eb1 := part_mem hp1 b
      have eb2 := part_mem hp2 b
      have ebL := part_mem hLXR.1 b
      have eaL := part_mem hLXR.1 a
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ,
        true_iff] at ea1 ea2 eb1 eb2 ebL eaL
      have ha' : a ∈ L₁ ∨ a ∈ L₂ := by
        simp only [Finset.mem_union] at ha
        rcases ha with (h | h) | h
        · exact Or.inl h
        · exact Or.inl (hTL1 h)
        · exact Or.inr h
      have hb' : b ∈ R₁ ∨ b ∈ R₂ := by
        simp only [Finset.mem_union] at hb
        rcases hb with (h | h) | h
        · exact Or.inl h
        · exact Or.inl (hTR1 h)
        · exact Or.inr h
      have tl1 : a ∈ L ∩ B → a ∈ L₂ := fun h => hTL2 h
      have tr1 : b ∈ R ∩ B → b ∈ R₁ := fun h => hTR1 h
      rcases ha' with ha1 | ha2 <;> rcases hb' with hb1 | hb2
      · exact hne1 a ha1 b hb1 hab
      · -- a ∈ L₁ ⊆ W₁, b ∈ R₂ ⊆ W₂
        have haW : a ∈ A₁ ∨ (a ∈ B ∧ ¬(a ∈ X ∧ a ∈ B)) := ea1.1.mpr (Or.inl ha1)
        have hbW : b ∈ A₂ ∨ (b ∈ B ∧ ¬(b ∈ X ∧ b ∈ B)) := eb2.1.mpr (Or.inr (Or.inr hb2))
        rcases haW with haA | ⟨haB, haX⟩
        · rcases hbW with hbA | ⟨hbB, hbX⟩
          · exact hsep.2 a haA b hbA hab
          · rcases ebL.1 with hbL | hbX' | hbR
            · exact eb2.2.2.1 (hTL2 (Finset.mem_inter.mpr ⟨hbL, hbB⟩)) hb2
            · exact hbX ⟨hbX', hbB⟩
            · exact hne1 a ha1 b (hTR1 (Finset.mem_inter.mpr ⟨hbR, hbB⟩)) hab
        · rcases eaL.1 with haL | haX' | haR
          · exact hne2 a (hTL2 (Finset.mem_inter.mpr ⟨haL, haB⟩)) b hb2 hab
          · exact haX ⟨haX', haB⟩
          · exact ea1.2.2.1 ha1 (hTR1 (Finset.mem_inter.mpr ⟨haR, haB⟩))
      · -- a ∈ L₂ ⊆ W₂, b ∈ R₁ ⊆ W₁
        have haW : a ∈ A₂ ∨ (a ∈ B ∧ ¬(a ∈ X ∧ a ∈ B)) := ea2.1.mpr (Or.inl ha2)
        have hbW : b ∈ A₁ ∨ (b ∈ B ∧ ¬(b ∈ X ∧ b ∈ B)) := eb1.1.mpr (Or.inr (Or.inr hb1))
        rcases haW with haA | ⟨haB, haX⟩
        · rcases hbW with hbA | ⟨hbB, hbX⟩
          · exact hsep.2 b hbA a haA hab.symm
          · rcases ebL.1 with hbL | hbX' | hbR
            · exact eb1.2.2.1 (hTL1 (Finset.mem_inter.mpr ⟨hbL, hbB⟩)) hb1
            · exact hbX ⟨hbX', hbB⟩
            · exact hne2 a ha2 b (hTR2 (Finset.mem_inter.mpr ⟨hbR, hbB⟩)) hab
        · rcases eaL.1 with haL | haX' | haR
          · exact hne1 a (hTL1 (Finset.mem_inter.mpr ⟨haL, haB⟩)) b hb1 hab
          · exact haX ⟨haX', haB⟩
          · exact ea2.2.2.1 ha2 (hTR2 (Finset.mem_inter.mpr ⟨haR, haB⟩))
      · exact hne2 a ha2 b hb2 hab
    · calc (X₁ ∪ (X ∩ B) ∪ X₂).card ≤ (X₁ ∪ (X ∩ B)).card + X₂.card := Finset.card_union_le _ _
        _ ≤ X₁.card + (X ∩ B).card + X₂.card := by
          have := Finset.card_union_le X₁ (X ∩ B); omega
        _ ≤ k + 1 := by omega
  refine ⟨hglue, ?_, ?_⟩
  · have hdis : Disjoint (L₁ ∪ (L ∩ B) ∪ L₂) (R₁ ∪ (R ∩ B) ∪ R₂) := hglue.1.2.1
    have hsum := Finset.card_le_univ (L₁ ∪ (L ∩ B) ∪ L₂ ∪ (R₁ ∪ (R ∩ B) ∪ R₂))
    rw [Finset.card_union_of_disjoint hdis] at hsum
    have hR2 : R₂.card ≤ (R₁ ∪ (R ∩ B) ∪ R₂).card :=
      Finset.card_le_card Finset.subset_union_right
    have hsubR : R ∩ (A₂ ∪ B) ⊆ R ∩ (A₂ ∪ (B \ (X ∩ B))) := by
      intro v hv
      have e := part_mem hLXR.1 v
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ,
        true_iff] at hv e ⊢
      grind
    have hRc := Finset.card_le_card hsubR
    have hnat : 8 * (L₁ ∪ (L ∩ B) ∪ L₂).card ≤ 7 * Fintype.card V + 4 * (B.card + (k + 1)) := by
      omega
    have hreal : (8 * (L₁ ∪ (L ∩ B) ∪ L₂).card : ℝ) ≤
        7 * Fintype.card V + 4 * ((B.card : ℝ) + (k + 1)) := by exact_mod_cast hnat
    linarith
  · have hdis : Disjoint (L₁ ∪ (L ∩ B) ∪ L₂) (R₁ ∪ (R ∩ B) ∪ R₂) := hglue.1.2.1
    have hsum := Finset.card_le_univ (L₁ ∪ (L ∩ B) ∪ L₂ ∪ (R₁ ∪ (R ∩ B) ∪ R₂))
    rw [Finset.card_union_of_disjoint hdis] at hsum
    have hL1 : L₁.card ≤ (L₁ ∪ (L ∩ B) ∪ L₂).card :=
      Finset.card_le_card (Finset.subset_union_left.trans Finset.subset_union_left)
    have hsubL : L ∩ (A₁ ∪ B) ⊆ L ∩ (A₁ ∪ (B \ (X ∩ B))) := by
      intro v hv
      have e := part_mem hLXR.1 v
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ,
        true_iff] at hv e ⊢
      grind
    have hLc := Finset.card_le_card hsubL
    have hnat : 8 * (R₁ ∪ (R ∩ B) ∪ R₂).card ≤ 7 * Fintype.card V + 4 * (B.card + (k + 1)) := by
      omega
    have hreal : (8 * (R₁ ∪ (R ∩ B) ∪ R₂).card : ℝ) ≤
        7 * Fintype.card V + 4 * ((B.card : ℝ) + (k + 1)) := by exact_mod_cast hnat
    linarith

end Glue

end TwSepAux

open TreewidthApprox.Pushed in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (htw : RobertsonSeymour1986.GM5.TreewidthLE G k)
    (A₁ B A₂ : Finset V) (hsep : IsSeparation G A₁ B A₂)
    (hA₁ : (A₁.card : ℝ) ≤ 3 / 4 * Fintype.card V) (hA₂ : (A₂.card : ℝ) ≤ 3 / 4 * Fintype.card V) :
    ∃ (TL XB TR : Finset V) (k₁ k₂ : ℕ),
      IsPartition3 B TL XB TR ∧ k₁ + k₂ + XB.card ≤ k + 1 ∧
      (∃ L X R : Finset V, IsTerminalSep G (A₁ ∪ (B \ XB)) TL TR k₁ L X R) ∧
      (∃ L X R : Finset V, IsTerminalSep G (A₂ ∪ (B \ XB)) TL TR k₂ L X R) ∧
      ∀ L₁ X₁ R₁ L₂ X₂ R₂ : Finset V,
        IsLeftPushed G (A₁ ∪ (B \ XB)) TL TR k₁ L₁ X₁ R₁ →
        IsRightPushed G (A₂ ∪ (B \ XB)) TL TR k₂ L₂ X₂ R₂ →
        IsTerminalSep G Finset.univ TL TR (k + 1) (L₁ ∪ TL ∪ L₂) (X₁ ∪ XB ∪ X₂) (R₁ ∪ TR ∪ R₂) ∧
        ((L₁ ∪ TL ∪ L₂).card : ℝ) ≤ 7 / 8 * Fintype.card V + ((B.card : ℝ) + (k + 1)) / 2 ∧
        ((R₁ ∪ TR ∪ R₂).card : ℝ) ≤ 7 / 8 * Fintype.card V + ((B.card : ℝ) + (k + 1)) / 2 := by
  classical
  obtain ⟨T, hTf, t, Xb, htd, hw⟩ := htw
  obtain ⟨L, X, R, hLXR, hX, hL1, hL2⟩ := TwSepAux.tree_sep k htd hw
  set n := Fintype.card V with hn
  have hA1n : 4 * A₁.card ≤ 3 * n := by
    have : (4 * A₁.card : ℝ) ≤ 3 * n := by linarith
    exact_mod_cast this
  have hA2n : 4 * A₂.card ≤ 3 * n := by
    have : (4 * A₂.card : ℝ) ≤ 3 * n := by linarith
    exact_mod_cast this
  have cover : ∀ S₁ S₂ S₃ : Finset V, (∀ v, v ∈ S₁ ∨ v ∈ S₂ ∨ v ∈ S₃) →
      n ≤ S₁.card + S₂.card + S₃.card := by
    intro S₁ S₂ S₃ h
    have hsub : (Finset.univ : Finset V) ⊆ S₁ ∪ S₂ ∪ S₃ := by
      intro v _
      simp only [Finset.mem_union]
      rcases h v with h | h | h <;> tauto
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have := Finset.card_union_le S₁ S₂
    rw [Finset.card_univ] at *
    omega
  have eS := fun v => (TwSepAux.part_mem hsep.1 v).1
  have eL := fun v => (TwSepAux.part_mem hLXR.1 v).1
  simp only [Finset.mem_univ, true_iff] at eS eL
  -- covering inequalities
  have c1 := cover (A₁ ∪ B) A₂ ∅ (fun v => by
    rcases eS v with h | h | h <;> simp [h])
  have c2 := cover (A₂ ∪ B) A₁ ∅ (fun v => by
    rcases eS v with h | h | h <;> simp [h])
  have c3 := cover L X R (fun v => eL v)
  have c4 := cover (L ∩ (A₁ ∪ B)) (L ∩ (A₂ ∪ B)) (Finset.univ \ L) (fun v => by
    by_cases hv : v ∈ L
    · rcases eS v with h | h | h <;> simp [h, hv]
    · simp [hv])
  have c5 := cover (R ∩ (A₁ ∪ B)) (R ∩ (A₂ ∪ B)) (Finset.univ \ R) (fun v => by
    by_cases hv : v ∈ R
    · rcases eS v with h | h | h <;> simp [h, hv]
    · simp [hv])
  have c6 := cover (L ∩ (A₁ ∪ B)) (R ∩ (A₁ ∪ B)) (X ∪ (Finset.univ \ (A₁ ∪ B))) (fun v => by
    by_cases hv : v ∈ A₁ ∪ B
    · rcases eL v with h | h | h <;> simp [h, hv]
    · simp [hv])
  have c7 := cover (L ∩ (A₂ ∪ B)) (R ∩ (A₂ ∪ B)) (X ∪ (Finset.univ \ (A₂ ∪ B))) (fun v => by
    by_cases hv : v ∈ A₂ ∪ B
    · rcases eL v with h | h | h <;> simp [h, hv]
    · simp [hv])
  have u4 : (Finset.univ \ L).card = n - L.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have u5 : (Finset.univ \ R).card = n - R.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have u6 : (X ∪ (Finset.univ \ (A₁ ∪ B))).card ≤ X.card + (n - (A₁ ∪ B).card) := by
    have := Finset.card_union_le X (Finset.univ \ (A₁ ∪ B))
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at this
    exact this
  have u7 : (X ∪ (Finset.univ \ (A₂ ∪ B))).card ≤ X.card + (n - (A₂ ∪ B).card) := by
    have := Finset.card_union_le X (Finset.univ \ (A₂ ∪ B))
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at this
    exact this
  have hU1 : (A₁ ∪ B).card ≤ n := Finset.card_le_univ _
  have hU2 : (A₂ ∪ B).card ≤ n := Finset.card_le_univ _
  have hLn : L.card ≤ n := Finset.card_le_univ _
  have hRn : R.card ≤ n := Finset.card_le_univ _
  simp only [Finset.card_empty] at c1 c2
  by_cases hopt : n ≤ 8 * (L ∩ (A₁ ∪ B)).card + 4 * (B.card + (k + 1)) ∧
      n ≤ 8 * (R ∩ (A₂ ∪ B)).card + 4 * (B.card + (k + 1))
  · exact TwSepAux.glue G k A₁ B A₂ hsep L X R hLXR hX hopt.1 hopt.2
  · have h1 : n ≤ 8 * (R ∩ (A₁ ∪ B)).card + 4 * (B.card + (k + 1)) := by omega
    have h2 : n ≤ 8 * (L ∩ (A₂ ∪ B)).card + 4 * (B.card + (k + 1)) := by omega
    exact TwSepAux.glue G k A₁ B A₂ hsep R X L (TwSepAux.sep_swap hLXR) hX h1 h2
