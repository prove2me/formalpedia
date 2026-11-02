-- Prove2me | solution 1 for PosetMarginals.Chains.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:46:35.901307+00:00
-- url     : https://prove2.me/submissions/497c0e05-4697-4d1c-ba08-b515a64c5152

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Model
import Definitions.Def_PosetMarginals_Chains_Algorithm

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Classical PosetMarginals.Chains

namespace PMC

section Splice

variable {α : Type*} [PartialOrder α] [Fintype α]

lemma mem_maxChains {C : Finset α} : C ∈ maxChains α ↔ IsMaxChain (· ≤ ·) (C : Set α) := by
  simp [maxChains]

lemma chain_total {C : Finset α} (hC : C ∈ maxChains α) {a b : α} (ha : a ∈ C) (hb : b ∈ C) :
    a ≤ b ∨ b ≤ a := by
  rcases eq_or_ne a b with rfl | hab
  · exact Or.inl le_rfl
  · exact (mem_maxChains.1 hC).1 ha hb hab

lemma mem_of_comparable {C : Finset α} (hC : C ∈ maxChains α) {z : α}
    (hz : ∀ b ∈ C, z ≤ b ∨ b ≤ z) : z ∈ C := by
  have h := mem_maxChains.1 hC
  by_contra hzC
  have hch : IsChain (· ≤ ·) (insert z (C : Set α)) :=
    h.1.insert (fun b hb _ => hz b hb)
  have := h.2 hch (Set.subset_insert _ _)
  have hzin : z ∈ insert z (C : Set α) := Set.mem_insert _ _
  rw [← this] at hzin
  exact hzC hzin

lemma mem_splice {C1 C2 : Finset α} {x z : α} :
    z ∈ splice C1 C2 x ↔ (z ∈ C1 ∧ z ≤ x) ∨ (z ∈ C2 ∧ x ≤ z) := by
  simp [splice]

lemma splice_mem {C1 C2 : Finset α} (h1 : C1 ∈ maxChains α) (h2 : C2 ∈ maxChains α) {x : α}
    (hx1 : x ∈ C1) (hx2 : x ∈ C2) : splice C1 C2 x ∈ maxChains α := by
  rw [mem_maxChains]
  constructor
  · intro a ha b hb _
    simp only [Finset.mem_coe, mem_splice] at ha hb
    rcases ha with ⟨ha1, hax⟩ | ⟨ha2, hxa⟩ <;> rcases hb with ⟨hb1, hbx⟩ | ⟨hb2, hxb⟩
    · exact chain_total h1 ha1 hb1
    · exact Or.inl (hax.trans hxb)
    · exact Or.inr (hbx.trans hxa)
    · exact chain_total h2 ha2 hb2
  · intro t ht hst
    apply Set.Subset.antisymm hst
    intro z hz
    have hcomp : ∀ b ∈ splice C1 C2 x, z ≤ b ∨ b ≤ z := by
      intro b hb
      rcases eq_or_ne z b with rfl | hne
      · exact Or.inl le_rfl
      · exact ht hz (hst (Finset.mem_coe.2 hb)) hne
    have hxs : x ∈ splice C1 C2 x := mem_splice.2 (Or.inl ⟨hx1, le_rfl⟩)
    rcases hcomp x hxs with hzx | hxz
    · have : z ∈ C1 := by
        apply mem_of_comparable h1
        intro b hb
        rcases chain_total h1 hb hx1 with hbx | hxb
        · exact hcomp b (mem_splice.2 (Or.inl ⟨hb, hbx⟩))
        · exact Or.inl (hzx.trans hxb)
      exact Finset.mem_coe.2 (mem_splice.2 (Or.inl ⟨this, hzx⟩))
    · have : z ∈ C2 := by
        apply mem_of_comparable h2
        intro b hb
        rcases chain_total h2 hb hx2 with hbx | hxb
        · exact Or.inr (hbx.trans hxz)
        · exact hcomp b (mem_splice.2 (Or.inr ⟨hb, hxb⟩))
      exact Finset.mem_coe.2 (mem_splice.2 (Or.inr ⟨this, hxz⟩))

lemma sum_lower_upper (f : α → ℝ) (A B : Finset α) (x : α) (hxA : x ∈ A) (hxB : x ∈ B)
    (hA : ∀ z ∈ A, z ≤ x) (hB : ∀ z ∈ B, x ≤ z) :
    ∑ z ∈ A ∪ B, f z = ∑ z ∈ A, f z + ∑ z ∈ B, f z - f x := by
  have hi : A ∩ B = {x} := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact le_antisymm (hA z h1) (hB z h2)
    · rintro rfl; exact ⟨hxA, hxB⟩
  have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  rw [hi, Finset.sum_singleton] at this
  linarith

lemma sum_chain_split (f : α → ℝ) {C : Finset α} (hC : C ∈ maxChains α) {x : α} (hx : x ∈ C) :
    ∑ z ∈ C, f z = ∑ z ∈ C.filter (· ≤ x), f z + ∑ z ∈ C.filter (x ≤ ·), f z - f x := by
  rw [← sum_lower_upper f _ _ x (by simp [hx]) (by simp [hx]) (by simp) (by simp)]
  congr 1
  ext z
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hz
    rcases chain_total hC hz hx with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz

lemma sum_splice_one (f : α → ℝ) (C1 C2 : Finset α) {x : α} (hx1 : x ∈ C1) (hx2 : x ∈ C2) :
    ∑ z ∈ splice C1 C2 x, f z =
      ∑ z ∈ C1.filter (· ≤ x), f z + ∑ z ∈ C2.filter (x ≤ ·), f z - f x := by
  unfold splice
  exact sum_lower_upper f _ _ x (by simp [hx1]) (by simp [hx2]) (by simp) (by simp)

lemma sum_splice (f : α → ℝ) {C1 C2 : Finset α} (h1 : C1 ∈ maxChains α)
    (h2 : C2 ∈ maxChains α) {x : α} (hx1 : x ∈ C1) (hx2 : x ∈ C2) :
    ∑ z ∈ splice C1 C2 x, f z + ∑ z ∈ splice C2 C1 x, f z =
      ∑ z ∈ C1, f z + ∑ z ∈ C2, f z := by
  rw [sum_splice_one f C1 C2 hx1 hx2, sum_splice_one f C2 C1 hx2 hx1,
    sum_chain_split f h1 hx1, sum_chain_split f h2 hx2]
  ring

lemma relGen_lt {C' : Finset (Finset α)} {x y : α} (h : relGen C' x y) (hne : x ≠ y) :
    x < y := by
  rcases h with h | ⟨C, _, _, _, hlt⟩
  · exact absurd h hne
  · exact hlt

/-- Lemma 2, first half: the generated relation is a partial order. -/
lemma isPosetOn_of {X' : Finset α} {C' : Finset (Finset α)} (hC' : C' ⊆ maxChains α)
    (h : PreservesDecomp X' C') : IsPosetOn X' C' := by
  refine ⟨fun x _ => Or.inl rfl, fun x _ y _ hxy hyx => ?_, fun x hx y hy z hz hxy hyz => ?_⟩
  · by_contra hne
    exact lt_asymm (relGen_lt hxy hne) (relGen_lt hyx (Ne.symm hne))
  · rcases hxy with rfl | ⟨C1, hC1, hx1, hy1, hlt1⟩
    · exact hyz
    rcases hyz with rfl | ⟨C2, hC2, hy2, hz2, hlt2⟩
    · exact Or.inr ⟨C1, hC1, hx1, hy1, hlt1⟩
    have hy : y ∈ C1 ∩ C2 ∩ X' := by simp [hy1, hy2, hy]
    refine Or.inr ⟨splice C1 C2 y, (h C1 hC1 C2 hC2 y hy).1, ?_, ?_, hlt1.trans hlt2⟩
    · exact mem_splice.2 (Or.inl ⟨hx1, hlt1.le⟩)
    · exact mem_splice.2 (Or.inr ⟨hz2, hlt2.le⟩)

lemma exists_min_of_chain {C : Finset α} (hC : C ∈ maxChains α) (X : Finset α)
    (hne : (C ∩ X).Nonempty) : ∃ m ∈ C ∩ X, ∀ y ∈ C ∩ X, m ≤ y := by
  obtain ⟨m, hm⟩ := Finset.exists_minimal hne
  refine ⟨m, hm.1, fun y hy => ?_⟩
  rcases chain_total hC (Finset.mem_inter.1 hm.1).1 (Finset.mem_inter.1 hy).1 with h | h
  · exact h
  · exact hm.2 hy h

end Splice

section Alg

variable {α : Type*} [PartialOrder α] [Fintype α]

lemma mem_X (s : AlgState α) {x : α} : x ∈ s.X ↔ 0 < s.ρ x := by
  simp [AlgState.X]

lemma mem_S (s : AlgState α) {x : α} :
    x ∈ s.S ↔ x ∈ s.X ∧ ∀ y ∈ s.X, relGen s.tight y x → y = x := by
  simp only [AlgState.S, Finset.mem_filter]

lemma mem_tight (s : AlgState α) {C : Finset α} : C ∈ s.tight ↔ C ∈ s.chains ∧ s.δ C = 0 := by
  simp only [AlgState.tight, Finset.mem_filter]

lemma mem_slack (s : AlgState α) {C : Finset α} : C ∈ s.slack ↔ C ∈ s.chains ∧ 0 < s.δ C := by
  simp only [AlgState.slack, Finset.mem_filter]

lemma S_sub_X (s : AlgState α) : s.S ⊆ s.X := fun x hx => ((mem_S s).1 hx).1

lemma step_ρ (s : AlgState α) (x : α) :
    s.step.ρ x = s.ρ x - s.w * (if x ∈ s.S then 1 else 0) := rfl

lemma step_δ (s : AlgState α) (C : Finset α) :
    s.step.δ C = s.δ C - (if 2 ≤ (s.S ∩ C).card then s.w * (((s.S ∩ C).card : ℝ) - 1) else 0) :=
  rfl

lemma step_π (s : AlgState α) (C : Finset α) :
    s.step.π C = s.π C - (if (s.S ∩ C).Nonempty then s.w else 0) := rfl

lemma step_prevX (s : AlgState α) : s.step.prevX = s.X := rfl

lemma mem_step_chains (s : AlgState α) {C : Finset α} :
    C ∈ s.step.chains ↔ C ∈ s.chains ∧
      ∃ m ∈ C ∩ s.X, (∀ y ∈ C ∩ s.X, m ≤ y) ∧ m ∈ s.S := by
  simp only [AlgState.step, Finset.mem_filter]

lemma step_chains_sub (s : AlgState α) : s.step.chains ⊆ s.chains :=
  fun C hC => ((mem_step_chains s).1 hC).1

/-- Candidate set of step A7. -/
noncomputable def cands (s : AlgState α) : Finset ℝ :=
  s.S.image s.ρ ∪
    (s.slack.filter (fun C => 2 ≤ (s.S ∩ C).card)).image
      (fun C => s.δ C / (((s.S ∩ C).card : ℝ) - 1))

lemma w_eq (s : AlgState α) :
    s.w = if h : (cands s).Nonempty then (cands s).min' h else 0 := rfl

lemma cands_pos (s : AlgState α) : ∀ v ∈ cands s, 0 < v := by
  intro v hv
  simp only [cands, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hv
  rcases hv with ⟨x, hx, rfl⟩ | ⟨C, ⟨hC, h2⟩, rfl⟩
  · exact (mem_X s).1 (S_sub_X s hx)
  · have hδ : 0 < s.δ C := ((mem_slack s).1 hC).2
    have : (2:ℝ) ≤ (s.S ∩ C).card := by exact_mod_cast h2
    apply div_pos hδ
    linarith

lemma w_nonneg (s : AlgState α) : 0 ≤ s.w := by
  rw [w_eq]
  split_ifs with h
  · exact (cands_pos s _ (Finset.min'_mem _ h)).le
  · exact le_rfl

lemma w_le (s : AlgState α) {v : ℝ} (hv : v ∈ cands s) : s.w ≤ v := by
  rw [w_eq, dif_pos ⟨v, hv⟩]
  exact Finset.min'_le _ _ hv

lemma w_mem (s : AlgState α) (h : (cands s).Nonempty) : s.w ∈ cands s := by
  rw [w_eq, dif_pos h]
  exact Finset.min'_mem _ _

lemma w_le_ρ (s : AlgState α) {x : α} (hx : x ∈ s.S) : s.w ≤ s.ρ x :=
  w_le s (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))

lemma w_mul_le_δ (s : AlgState α) {C : Finset α} (hC : C ∈ s.slack)
    (h2 : 2 ≤ (s.S ∩ C).card) : s.w * (((s.S ∩ C).card : ℝ) - 1) ≤ s.δ C := by
  have hv : s.δ C / (((s.S ∩ C).card : ℝ) - 1) ∈ cands s :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hC, h2⟩))
  have hw := w_le s hv
  have : (2:ℝ) ≤ (s.S ∩ C).card := by exact_mod_cast h2
  have hpos : (0:ℝ) < ((s.S ∩ C).card : ℝ) - 1 := by linarith
  rwa [le_div_iff₀ hpos] at hw

lemma S_nonempty (s : AlgState α) (h : s.X.Nonempty) : s.S.Nonempty := by
  obtain ⟨x, hx⟩ := Finset.exists_minimal h
  refine ⟨x, (mem_S s).2 ⟨hx.1, fun y hy hr => ?_⟩⟩
  by_contra hne
  have hlt := relGen_lt hr hne
  exact absurd (hx.2 hy hlt.le) hlt.not_ge

lemma cands_nonempty (s : AlgState α) (h : s.X.Nonempty) : (cands s).Nonempty := by
  obtain ⟨x, hx⟩ := S_nonempty s h
  exact ⟨_, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)⟩

lemma w_cases (s : AlgState α) (h : s.X.Nonempty) :
    (∃ x ∈ s.S, s.w = s.ρ x) ∨
      (∃ C ∈ s.slack, 2 ≤ (s.S ∩ C).card ∧ s.w = s.δ C / (((s.S ∩ C).card : ℝ) - 1)) := by
  have := w_mem s (cands_nonempty s h)
  simp only [cands, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at this
  rcases this with ⟨x, hx, he⟩ | ⟨C, ⟨hC, h2⟩, he⟩
  · exact Or.inl ⟨x, hx, he.symm⟩
  · exact Or.inr ⟨C, hC, h2, he.symm⟩

/-- Members of `S` are pairwise unrelated along a tight chain. -/
lemma S_tight_le_one (s : AlgState α) (hch : s.chains ⊆ maxChains α) {C : Finset α}
    (hC : C ∈ s.tight) : (s.S ∩ C).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter] at ha hb
  by_contra hne
  have hCm : C ∈ maxChains α := hch ((mem_tight s).1 hC).1
  rcases chain_total hCm ha.2 hb.2 with hab | hba
  · have hlt : a < b := lt_of_le_of_ne hab hne
    have := ((mem_S s).1 hb.1).2 a (S_sub_X s ha.1) (Or.inr ⟨C, hC, ha.2, hb.2, hlt⟩)
    exact hne this
  · have hlt : b < a := lt_of_le_of_ne hba (Ne.symm hne)
    have := ((mem_S s).1 ha.1).2 b (S_sub_X s hb.1) (Or.inr ⟨C, hC, hb.2, ha.2, hlt⟩)
    exact hne this.symm

lemma card_identity (n : ℕ) :
    (n : ℝ) - (if 0 < n then 1 else 0) = (if 2 ≤ n then (n : ℝ) - 1 else 0) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h0 : 0 < n := by omega
    simp [h0, h]

end Alg

section Inv

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- The invariants of Proposition 2, together with basic bookkeeping facts. -/
structure Inv (s : AlgState α) : Prop where
  ρ_nonneg : ∀ x, 0 ≤ s.ρ x
  chains_sub : s.chains ⊆ maxChains α
  X_sub : s.X ⊆ s.prevX
  δ_eq : ∀ C : Finset α, s.δ C = ∑ x ∈ C, s.ρ x - s.π C
  δ_nonneg : ∀ C ∈ s.chains, 0 ≤ s.δ C
  decomp : PreservesDecomp s.prevX s.chains
  cons : ∀ C1 ∈ s.chains, ∀ C2 ∈ s.chains, ∀ x ∈ C1 ∩ C2 ∩ s.prevX,
    s.π C1 + s.π C2 = s.π (splice C1 C2 x) + s.π (splice C2 C1 x)

lemma inv_init (ρ : α → ℝ) (π : Finset α → ℝ) (h : Standing ρ π) : Inv (init ρ π) where
  ρ_nonneg x := (h.1 x).1
  chains_sub := fun C hC => hC
  X_sub := fun x _ => Finset.mem_univ x
  δ_eq C := rfl
  δ_nonneg C hC := by
    show 0 ≤ delta ρ π C
    unfold delta
    linarith [h.2.2.1 C hC]
  decomp := by
    intro C1 hC1 C2 hC2 x hx
    simp only [Finset.mem_inter] at hx
    exact ⟨splice_mem hC1 hC2 hx.1.1 hx.1.2, splice_mem hC2 hC1 hx.1.2 hx.1.1⟩
  cons := by
    intro C1 hC1 C2 hC2 x hx
    exact h.2.2.2 C1 hC1 C2 hC2 x (Finset.mem_inter.1 hx).1

lemma sum_ite_S (s : AlgState α) (C : Finset α) :
    ∑ x ∈ C, s.w * (if x ∈ s.S then (1:ℝ) else 0) = s.w * ((s.S ∩ C).card : ℝ) := by
  rw [← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]

lemma step_δ_eq (s : AlgState α) (hδ : ∀ C : Finset α, s.δ C = ∑ x ∈ C, s.ρ x - s.π C)
    (C : Finset α) : s.step.δ C = ∑ x ∈ C, s.step.ρ x - s.step.π C := by
  simp only [step_δ, step_π, step_ρ]
  rw [Finset.sum_sub_distrib, sum_ite_S, hδ C]
  have hc := card_identity (s.S ∩ C).card
  have hne : (s.S ∩ C).Nonempty ↔ 0 < (s.S ∩ C).card := Finset.card_pos.symm
  by_cases h2 : 2 ≤ (s.S ∩ C).card
  · have h0 : (s.S ∩ C).Nonempty := hne.2 (by omega)
    have h0' : 0 < (s.S ∩ C).card := by omega
    simp only [h2, h0, h0', if_true] at hc ⊢
    linarith
  · simp only [h2, if_false] at hc ⊢
    by_cases h0 : (s.S ∩ C).Nonempty
    · have h0' : 0 < (s.S ∩ C).card := hne.1 h0
      simp only [h0, h0', if_true] at hc ⊢
      have : ((s.S ∩ C).card : ℝ) = 1 := by linarith
      rw [this]; ring
    · have h0' : ¬ 0 < (s.S ∩ C).card := fun h => h0 (hne.2 h)
      simp only [h0, h0', if_false] at hc ⊢
      have : ((s.S ∩ C).card : ℝ) = 0 := by linarith
      rw [this]; ring

/-- Membership of a splice in the next chain family. -/
lemma splice_step_chains' (s : AlgState α) (hI : Inv s) {C1 C2 : Finset α}
    (h1 : C1 ∈ s.step.chains) (h2 : C2 ∈ s.chains) {x : α} (hx : x ∈ C1 ∩ C2 ∩ s.X) :
    splice C1 C2 x ∈ s.step.chains := by
  rw [mem_step_chains] at h1 ⊢
  simp only [Finset.mem_inter] at hx
  have hxp : x ∈ C1 ∩ C2 ∩ s.prevX := by simp [hx.1.1, hx.1.2, hI.X_sub hx.2]
  refine ⟨(hI.decomp C1 h1.1 C2 h2 x hxp).1, ?_⟩
  obtain ⟨m, hm, hmin, hmS⟩ := h1.2
  have hmx : m ≤ x := hmin x (Finset.mem_inter.2 ⟨hx.1.1, hx.2⟩)
  refine ⟨m, ?_, ?_, hmS⟩
  · rw [Finset.mem_inter] at hm ⊢
    exact ⟨mem_splice.2 (Or.inl ⟨hm.1, hmx⟩), hm.2⟩
  · intro y hy
    rw [Finset.mem_inter, mem_splice] at hy
    rcases hy with ⟨⟨hy1, _⟩ | ⟨_, hxy⟩, hyX⟩
    · exact hmin y (Finset.mem_inter.2 ⟨hy1, hyX⟩)
    · exact hmx.trans hxy

lemma splice_step_chains (s : AlgState α) (hI : Inv s) {C1 C2 : Finset α}
    (h1 : C1 ∈ s.step.chains) (h2 : C2 ∈ s.step.chains) {x : α} (hx : x ∈ C1 ∩ C2 ∩ s.X) :
    splice C1 C2 x ∈ s.step.chains :=
  splice_step_chains' s hI h1 (step_chains_sub s h2) hx

lemma step_chains_meet_S (s : AlgState α) {C : Finset α} (hC : C ∈ s.step.chains) :
    (s.S ∩ C).Nonempty := by
  obtain ⟨_, m, hm, _, hmS⟩ := (mem_step_chains s).1 hC
  exact ⟨m, Finset.mem_inter.2 ⟨hmS, (Finset.mem_inter.1 hm).1⟩⟩

lemma inv_step (s : AlgState α) (hI : Inv s) : Inv s.step where
  ρ_nonneg x := by
    rw [step_ρ]
    split_ifs with hx
    · linarith [w_le_ρ s hx]
    · simp [hI.ρ_nonneg x]
  chains_sub := (step_chains_sub s).trans hI.chains_sub
  X_sub := by
    intro x hx
    rw [step_prevX, mem_X]
    rw [mem_X, step_ρ] at hx
    have := w_nonneg s
    split_ifs at hx <;> nlinarith
  δ_eq := step_δ_eq s hI.δ_eq
  δ_nonneg := by
    intro C hC
    have hC0 := step_chains_sub s hC
    have hδ := hI.δ_nonneg C hC0
    rw [step_δ]
    rcases hδ.lt_or_eq with hlt | heq
    · split_ifs with h2
      · linarith [w_mul_le_δ s ((mem_slack s).2 ⟨hC0, hlt⟩) h2]
      · linarith
    · have := S_tight_le_one s hI.chains_sub ((mem_tight s).2 ⟨hC0, heq.symm⟩)
      rw [if_neg (by omega)]
      linarith
  decomp := by
    intro C1 hC1 C2 hC2 x hx
    rw [step_prevX] at hx
    refine ⟨splice_step_chains s hI hC1 hC2 hx, splice_step_chains s hI hC2 hC1 ?_⟩
    simp only [Finset.mem_inter] at hx ⊢
    exact ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
  cons := by
    intro C1 hC1 C2 hC2 x hx
    rw [step_prevX] at hx
    have hx' : x ∈ C2 ∩ C1 ∩ s.X := by
      simp only [Finset.mem_inter] at hx ⊢
      exact ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
    have h12 := splice_step_chains s hI hC1 hC2 hx
    have h21 := splice_step_chains s hI hC2 hC1 hx'
    simp only [step_π, if_pos (step_chains_meet_S s hC1), if_pos (step_chains_meet_S s hC2),
      if_pos (step_chains_meet_S s h12), if_pos (step_chains_meet_S s h21)]
    have hxp : x ∈ C1 ∩ C2 ∩ s.prevX := by
      simp only [Finset.mem_inter] at hx ⊢
      exact ⟨hx.1, hI.X_sub hx.2⟩
    have := hI.cons C1 (step_chains_sub s hC1) C2 (step_chains_sub s hC2) x hxp
    linarith

lemma inv_iter (ρ : α → ℝ) (π : Finset α → ℝ) (h : Standing ρ π) (k : ℕ) :
    Inv (iter ρ π k) := by
  induction k with
  | zero => exact inv_init ρ π h
  | succ k ih => exact inv_step _ ih

/-- The slack identity on the four chains of a splice. -/
lemma δ_splice (s : AlgState α) (hI : Inv s) {C1 C2 : Finset α} (h1 : C1 ∈ s.chains)
    (h2 : C2 ∈ s.chains) {x : α} (hx : x ∈ C1 ∩ C2 ∩ s.prevX) :
    s.δ (splice C1 C2 x) + s.δ (splice C2 C1 x) = s.δ C1 + s.δ C2 := by
  have hx' := hx
  simp only [Finset.mem_inter] at hx'
  have hs := sum_splice s.ρ (hI.chains_sub h1) (hI.chains_sub h2) hx'.1.1 hx'.1.2
  have hc := hI.cons C1 h1 C2 h2 x hx
  rw [hI.δ_eq, hI.δ_eq, hI.δ_eq C1, hI.δ_eq C2]
  linarith

/-- Tight chains are closed under splicing at points of `X`. -/
lemma tight_decomp (s : AlgState α) (hI : Inv s) : PreservesDecomp s.X s.tight := by
  intro C1 hC1 C2 hC2 x hx
  rw [mem_tight] at hC1 hC2
  have hxp : x ∈ C1 ∩ C2 ∩ s.prevX := by
    simp only [Finset.mem_inter] at hx ⊢
    exact ⟨hx.1, hI.X_sub hx.2⟩
  have hd := hI.decomp C1 hC1.1 C2 hC2.1 x hxp
  have he := δ_splice s hI hC1.1 hC2.1 hxp
  have p1 := hI.δ_nonneg _ hd.1
  have p2 := hI.δ_nonneg _ hd.2
  rw [hC1.2, hC2.2] at he
  exact ⟨(mem_tight s).2 ⟨hd.1, by linarith⟩, (mem_tight s).2 ⟨hd.2, by linarith⟩⟩

lemma tight_sub (s : AlgState α) (hI : Inv s) : s.tight ⊆ maxChains α :=
  fun C hC => hI.chains_sub ((mem_tight s).1 hC).1

lemma isPosetOn_tight (s : AlgState α) (hI : Inv s) : IsPosetOn s.X s.tight :=
  isPosetOn_of (tight_sub s hI) (tight_decomp s hI)

end Inv

section L3

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- Descent along tight chains: a tight chain through `x` can be replaced by one whose
minimum in `X` lies in `S`. -/
lemma descent (s : AlgState α) (hI : Inv s) (x : α) (hx : x ∈ s.X) :
    ∀ m : α, ∀ E ∈ s.tight, m ∈ E → m ∈ s.X → x ∈ E → m ≤ x →
      ∃ C2 ∈ s.tight, x ∈ C2 ∧ C2 ∈ s.step.chains := by
  intro m
  induction m using WellFoundedLT.induction with
  | _ m ih =>
  intro E hE hmE hmX hxE hmx
  have hEm : E ∈ maxChains α := tight_sub s hI hE
  obtain ⟨m0, hm0, hmin0⟩ := exists_min_of_chain hEm s.X ⟨m, Finset.mem_inter.2 ⟨hmE, hmX⟩⟩
  have hm0' := Finset.mem_inter.1 hm0
  by_cases hS : m0 ∈ s.S
  · refine ⟨E, hE, hxE, (mem_step_chains s).2 ⟨((mem_tight s).1 hE).1, m0, hm0, hmin0, hS⟩⟩
  · have : ¬ ∀ y ∈ s.X, relGen s.tight y m0 → y = m0 := fun h => hS ((mem_S s).2 ⟨hm0'.2, h⟩)
    push Not at this
    obtain ⟨y, hyX, hrel, hne⟩ := this
    rcases hrel with h | ⟨F, hF, hyF, hm0F, hlt⟩
    · exact absurd h hne
    have hm0m : m0 ≤ m := hmin0 m (Finset.mem_inter.2 ⟨hmE, hmX⟩)
    have hm0x : m0 ≤ x := hmin0 x (Finset.mem_inter.2 ⟨hxE, hx⟩)
    have hdec := tight_decomp s hI F hF E hE m0 (by simp [hm0F, hm0'.1, hm0'.2])
    exact ih y (lt_of_lt_of_le hlt hm0m) (splice F E m0) hdec.1
      (mem_splice.2 (Or.inl ⟨hyF, hlt.le⟩)) hyX (mem_splice.2 (Or.inr ⟨hxE, hm0x⟩))
      (hlt.le.trans hm0x)

lemma exists_dominating_tight (s : AlgState α) (hI : Inv s) {x : α} (hx : x ∈ s.X)
    (hxS : x ∉ s.S) : ∃ C2 ∈ s.tight, x ∈ C2 ∧ C2 ∈ s.step.chains := by
  have : ¬ ∀ y ∈ s.X, relGen s.tight y x → y = x := fun h => hxS ((mem_S s).2 ⟨hx, h⟩)
  push Not at this
  obtain ⟨y, hyX, hrel, hne⟩ := this
  rcases hrel with h | ⟨F, hF, hyF, hxF, hlt⟩
  · exact absurd h hne
  exact descent s hI x hx x F hF hxF hx hxF le_rfl

/-- Lemma 3 for a single state. -/
lemma lemma3_state (s : AlgState α) (hI : Inv s) {C1 : Finset α} (hin : C1 ∈ s.chains)
    (hout : C1 ∉ s.step.chains) (hinter : (C1 ∩ s.X).Nonempty) :
    ∃ C2 ∈ s.step.chains, s.δ C2 ≤ s.δ C1 ∧ C1 ∩ s.X ⊆ C2 ∩ s.X := by
  have hC1m : C1 ∈ maxChains α := hI.chains_sub hin
  obtain ⟨x, hx, hmin⟩ := exists_min_of_chain hC1m s.X hinter
  have hx' := Finset.mem_inter.1 hx
  have hxS : x ∉ s.S := fun h => hout ((mem_step_chains s).2 ⟨hin, x, hx, hmin, h⟩)
  obtain ⟨C2, hC2t, hxC2, hC2s⟩ := exists_dominating_tight s hI hx'.2 hxS
  have hC2 := ((mem_tight s).1 hC2t)
  have hxi : x ∈ C2 ∩ C1 ∩ s.X := by simp [hxC2, hx'.1, hx'.2]
  refine ⟨splice C2 C1 x, splice_step_chains' s hI hC2s hin hxi, ?_, ?_⟩
  · have hxp : x ∈ C2 ∩ C1 ∩ s.prevX := by
      simp [hxC2, hx'.1, hI.X_sub hx'.2]
    have he := δ_splice s hI hC2.1 hin hxp
    have hd := hI.decomp C2 hC2.1 C1 hin x hxp
    have := hI.δ_nonneg _ hd.2
    rw [hC2.2] at he
    linarith
  · intro y hy
    have hy' := Finset.mem_inter.1 hy
    exact Finset.mem_inter.2 ⟨mem_splice.2 (Or.inr ⟨hy'.1, hmin y hy⟩), hy'.2⟩

end L3

section Iter

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- The amount by which `δ_C` drops in one step. -/
noncomputable def dec (s : AlgState α) (C : Finset α) : ℝ :=
  if 2 ≤ (s.S ∩ C).card then s.w * (((s.S ∩ C).card : ℝ) - 1) else 0

lemma step_δ' (s : AlgState α) (C : Finset α) : s.step.δ C = s.δ C - dec s C := rfl

lemma dec_nonneg (s : AlgState α) (C : Finset α) : 0 ≤ dec s C := by
  unfold dec
  split_ifs with h
  · have : (2:ℝ) ≤ (s.S ∩ C).card := by exact_mod_cast h
    exact mul_nonneg (w_nonneg s) (by linarith)
  · exact le_rfl

lemma dec_mono (s : AlgState α) {C C2 : Finset α} (h : (s.S ∩ C).card ≤ (s.S ∩ C2).card) :
    dec s C ≤ dec s C2 := by
  unfold dec
  have hw := w_nonneg s
  have hc : ((s.S ∩ C).card : ℝ) ≤ (s.S ∩ C2).card := by exact_mod_cast h
  split_ifs with h1 h2 h2
  · exact mul_le_mul_of_nonneg_left (by linarith) hw
  · omega
  · have : (2:ℝ) ≤ (s.S ∩ C2).card := by exact_mod_cast h2
    exact mul_nonneg hw (by linarith)
  · exact le_rfl

lemma dec_eq_zero (s : AlgState α) {C : Finset α} (h : (s.S ∩ C).card ≤ 1) : dec s C = 0 := by
  unfold dec
  rw [if_neg (by omega)]

variable (ρ : α → ℝ) (π : Finset α → ℝ)

lemma iter_succ (k : ℕ) : iter ρ π (k + 1) = (iter ρ π k).step := rfl

lemma X_succ_sub (h : Standing ρ π) (k : ℕ) : (iter ρ π (k + 1)).X ⊆ (iter ρ π k).X :=
  (inv_iter ρ π h (k + 1)).X_sub

lemma X_anti (h : Standing ρ π) {k l : ℕ} (hkl : k ≤ l) : (iter ρ π l).X ⊆ (iter ρ π k).X := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact (X_succ_sub ρ π h l).trans ih

lemma chains_anti {k l : ℕ} (hkl : k ≤ l) : (iter ρ π l).chains ⊆ (iter ρ π k).chains := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact (step_chains_sub _).trans ih

lemma δ_tele (C : Finset α) {k l : ℕ} (hkl : k ≤ l) :
    (iter ρ π l).δ C = (iter ρ π k).δ C - ∑ i ∈ Finset.Ico k l, dec (iter ρ π i) C := by
  induction l, hkl using Nat.le_induction with
  | base => simp
  | succ l hkl ih =>
    rw [iter_succ, step_δ', ih, Finset.sum_Ico_succ_top hkl]
    ring

lemma ρ_zero_of_not_mem (h : Standing ρ π) (k : ℕ) {x : α} (hx : x ∉ (iter ρ π k).X) :
    (iter ρ π k).ρ x = 0 := by
  rw [mem_X] at hx
  have := (inv_iter ρ π h k).ρ_nonneg x
  linarith [not_lt.1 hx]

/-- A chain missing `X^k` is untouched from stage `k` on. -/
lemma untouched (h : Standing ρ π) {k l : ℕ} (hkl : k ≤ l) {C : Finset α}
    (hC : C ∩ (iter ρ π k).X = ∅) :
    (iter ρ π l).δ C = (iter ρ π k).δ C ∧ ∑ x ∈ C, (iter ρ π l).ρ x = 0 := by
  constructor
  · rw [δ_tele ρ π C hkl]
    rw [Finset.sum_eq_zero, sub_zero]
    intro i hi
    have hki : k ≤ i := (Finset.mem_Ico.1 hi).1
    apply dec_eq_zero
    have : (iter ρ π i).S ∩ C = ∅ := by
      ext y
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro hyS hyC
      have hyX : y ∈ (iter ρ π k).X := X_anti ρ π h hki (S_sub_X _ hyS)
      have : y ∈ C ∩ (iter ρ π k).X := Finset.mem_inter.2 ⟨hyC, hyX⟩
      rw [hC] at this
      simp at this
    rw [this]; simp
  · apply Finset.sum_eq_zero
    intro x hx
    apply ρ_zero_of_not_mem ρ π h
    intro hxl
    have : x ∈ C ∩ (iter ρ π k).X := Finset.mem_inter.2 ⟨hx, X_anti ρ π h hkl hxl⟩
    rw [hC] at this
    simp at this

/-- Comparison of two chains whose traces on `X^k` are nested. -/
lemma compare (h : Standing ρ π) {k l : ℕ} (hkl : k ≤ l) {C C2 : Finset α}
    (hsub : C ∩ (iter ρ π k).X ⊆ C2 ∩ (iter ρ π k).X) :
    (iter ρ π k).δ C - (iter ρ π k).δ C2 ≤ (iter ρ π l).δ C - (iter ρ π l).δ C2 ∧
      ∑ x ∈ C, (iter ρ π l).ρ x ≤ ∑ x ∈ C2, (iter ρ π l).ρ x := by
  have hsubl : C ∩ (iter ρ π l).X ⊆ C2 ∩ (iter ρ π l).X := by
    intro y hy
    rw [Finset.mem_inter] at hy ⊢
    exact ⟨(Finset.mem_inter.1 (hsub (Finset.mem_inter.2 ⟨hy.1, X_anti ρ π h hkl hy.2⟩))).1,
      hy.2⟩
  constructor
  · rw [δ_tele ρ π C hkl, δ_tele ρ π C2 hkl]
    have : ∑ i ∈ Finset.Ico k l, dec (iter ρ π i) C ≤ ∑ i ∈ Finset.Ico k l, dec (iter ρ π i) C2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply dec_mono
      apply Finset.card_le_card
      intro y hy
      rw [Finset.mem_inter] at hy ⊢
      have hyX : y ∈ (iter ρ π k).X := X_anti ρ π h (Finset.mem_Ico.1 hi).1 (S_sub_X _ hy.1)
      exact ⟨hy.1, (Finset.mem_inter.1 (hsub (Finset.mem_inter.2 ⟨hy.2, hyX⟩))).1⟩
    linarith
  · have hsplit : ∀ D : Finset α, ∑ x ∈ D, (iter ρ π l).ρ x =
        ∑ x ∈ D ∩ (iter ρ π l).X, (iter ρ π l).ρ x := by
      intro D
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro x _ hx
      apply ρ_zero_of_not_mem ρ π h
      intro hxX
      exact hx (Finset.mem_inter.2 ⟨‹x ∈ D›, hxX⟩)
    rw [hsplit C, hsplit C2]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubl
      (fun x _ _ => (inv_iter ρ π h l).ρ_nonneg x)

/-- Every maximal chain has nonnegative slack at any later stage `n`. -/
lemma δ_final_nonneg (h : Standing ρ π) (n : ℕ) :
    ∀ d k, k + d = n → ∀ C ∈ (iter ρ π k).chains, 0 ≤ (iter ρ π n).δ C := by
  intro d
  induction d with
  | zero =>
    intro k hk C hC
    simp at hk
    subst hk
    exact (inv_iter ρ π h k).δ_nonneg C hC
  | succ d ih =>
    intro k hk C hC
    have hkn : k ≤ n := by omega
    by_cases hC1 : C ∈ (iter ρ π (k + 1)).chains
    · exact ih (k + 1) (by omega) C hC1
    by_cases hX : (C ∩ (iter ρ π k).X).Nonempty
    · obtain ⟨C2, hC2, hδ, hsub⟩ :=
        lemma3_state (iter ρ π k) (inv_iter ρ π h k) hC hC1 hX
      have h2 := ih (k + 1) (by omega) C2 hC2
      have := (compare ρ π h hkn hsub).1
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hX
      rw [(untouched ρ π h hkn hX).1]
      exact (inv_iter ρ π h k).δ_nonneg C hC

lemma δ_final_nonneg' (h : Standing ρ π) (n : ℕ) (C : Finset α) (hC : C ∈ maxChains α) :
    0 ≤ (iter ρ π n).δ C :=
  δ_final_nonneg ρ π h n n 0 (by omega) C hC

end Iter

section P4

variable {α : Type*} [PartialOrder α] [Fintype α]
variable (ρ : α → ℝ) (π : Finset α → ℝ)

lemma π_eq (h : Standing ρ π) (l : ℕ) (C : Finset α) :
    (iter ρ π l).π C = ∑ x ∈ C, (iter ρ π l).ρ x - (iter ρ π l).δ C := by
  rw [(inv_iter ρ π h l).δ_eq C]; ring

/-- Domination of the chain targets by chains surviving to stage `k+1` (proof of Prop. 4). -/
lemma π_dom (h : Standing ρ π) (k : ℕ) :
    ∀ d k1, k1 + d = k + 1 → ∀ C ∈ (iter ρ π k1).chains,
      (∃ C' ∈ (iter ρ π (k + 1)).chains,
        (iter ρ π k).π C ≤ (iter ρ π k).π C' ∧ (iter ρ π (k + 1)).π C ≤ (iter ρ π (k + 1)).π C') ∨
      ((iter ρ π k).π C ≤ 0 ∧ (iter ρ π (k + 1)).π C ≤ 0) := by
  intro d
  induction d with
  | zero =>
    intro k1 hk C hC
    simp at hk
    subst hk
    exact Or.inl ⟨C, hC, le_rfl, le_rfl⟩
  | succ d ih =>
    intro k1 hk C hC
    have hk1 : k1 ≤ k := by omega
    by_cases hC1 : C ∈ (iter ρ π (k1 + 1)).chains
    · exact ih (k1 + 1) (by omega) C hC1
    by_cases hX : (C ∩ (iter ρ π k1).X).Nonempty
    · obtain ⟨C2, hC2, hδ, hsub⟩ :=
        lemma3_state (iter ρ π k1) (inv_iter ρ π h k1) hC hC1 hX
      have cmp : ∀ l, k1 ≤ l → (iter ρ π l).π C ≤ (iter ρ π l).π C2 := by
        intro l hl
        have := compare ρ π h hl hsub
        rw [π_eq ρ π h l C, π_eq ρ π h l C2]
        linarith [this.1, this.2]
      have c1 := cmp k hk1
      have c2 := cmp (k + 1) (by omega)
      rcases ih (k1 + 1) (by omega) C2 hC2 with ⟨C', hC', h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨C', hC', c1.trans h1, c2.trans h2⟩
      · exact Or.inr ⟨c1.trans h1, c2.trans h2⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hX
      have hnn := (inv_iter ρ π h k1).δ_nonneg C hC
      have u1 := untouched ρ π h hk1 hX
      have u2 := untouched ρ π h (show k1 ≤ k + 1 by omega) hX
      right
      rw [π_eq ρ π h k C, π_eq ρ π h (k + 1) C, u1.1, u1.2, u2.1, u2.2]
      constructor <;> linarith

/-- The set whose supremum is `maxValue`. -/
def VSet (r : α → ℝ) (p : Finset α → ℝ) : Set ℝ :=
  Set.range r ∪ p '' (maxChains α : Set (Finset α))

lemma VSet_finite (r : α → ℝ) (p : Finset α → ℝ) : (VSet r p).Finite :=
  (Set.finite_range r).union ((maxChains α).finite_toSet.image p)

lemma maxValue_eq (r : α → ℝ) (p : Finset α → ℝ) : maxValue r p = sSup (VSet r p) := rfl

lemma le_maxValue (r : α → ℝ) (p : Finset α → ℝ) {v : ℝ} (hv : v ∈ VSet r p) :
    v ≤ maxValue r p :=
  le_csSup (VSet_finite r p).bddAbove hv

lemma maxValue_eq_of [Nonempty α] (r : α → ℝ) (p : Finset α → ℝ) (c : ℝ)
    (hub : ∀ v ∈ VSet r p, v ≤ c) (hmem : ∃ v ∈ VSet r p, c ≤ v) : maxValue r p = c := by
  obtain ⟨v, hv, hcv⟩ := hmem
  exact le_antisymm (csSup_le ⟨v, hv⟩ hub) (hcv.trans (le_maxValue r p hv))

lemma maxValue_mem [Nonempty α] (r : α → ℝ) (p : Finset α → ℝ) :
    maxValue r p ∈ VSet r p :=
  Set.Nonempty.csSup_mem ⟨r (Classical.arbitrary α), Or.inl ⟨_, rfl⟩⟩ (VSet_finite r p)

lemma ρ_mem_V (r : α → ℝ) (p : Finset α → ℝ) (x : α) : r x ∈ VSet r p := Or.inl ⟨x, rfl⟩

lemma π_mem_V (r : α → ℝ) (p : Finset α → ℝ) {C : Finset α} (hC : C ∈ maxChains α) :
    p C ∈ VSet r p := Or.inr ⟨C, hC, rfl⟩

noncomputable def W (k : ℕ) : ℝ := maxValue (iter ρ π k).ρ (iter ρ π k).π

/-- A non-selected element of `X^k` is dominated by a surviving tight chain. -/
lemma ρ_le_chain (h : Standing ρ π) (k : ℕ) {x : α} (hx : x ∈ (iter ρ π k).X)
    (hxS : x ∉ (iter ρ π k).S) :
    ∃ C2 ∈ (iter ρ π (k + 1)).chains,
      (iter ρ π k).ρ x ≤ (iter ρ π k).π C2 - (iter ρ π k).w := by
  set s := iter ρ π k
  have hI : Inv s := inv_iter ρ π h k
  obtain ⟨C2, hC2t, hxC2, hC2s⟩ := exists_dominating_tight s hI hx hxS
  refine ⟨C2, hC2s, ?_⟩
  obtain ⟨_, m, hm, _, hmS⟩ := (mem_step_chains s).1 hC2s
  have hm' := Finset.mem_inter.1 hm
  have hne : x ≠ m := fun he => hxS (he ▸ hmS)
  have hsum : s.ρ x + s.ρ m ≤ ∑ y ∈ C2, s.ρ y := by
    rw [← Finset.sum_pair hne]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hxC2
      · exact hm'.1
    · intro y _ _; exact hI.ρ_nonneg y
  have hδ := hI.δ_eq C2
  rw [((mem_tight s).1 hC2t).2] at hδ
  have hw := w_le_ρ s hmS
  linarith

lemma W_succ [Nonempty α] (h : Standing ρ π) (k : ℕ) (hX : (iter ρ π k).X.Nonempty) :
    W ρ π (k + 1) = W ρ π k - (iter ρ π k).w := by
  have hdom := π_dom ρ π h k (k + 1) 0 (by omega)
  have hρle := fun (x : α) (hx : x ∈ (iter ρ π k).X) (hxS : x ∉ (iter ρ π k).S) =>
    ρ_le_chain ρ π h k hx hxS
  have hsucc : iter ρ π (k + 1) = (iter ρ π k).step := rfl
  rw [hsucc] at hdom hρle
  set s := iter ρ π k with hs
  have hI : Inv s := inv_iter ρ π h k
  have hw0 := w_nonneg s
  have hWk : ∀ v ∈ VSet s.ρ s.π, v ≤ W ρ π k := fun v hv => le_maxValue _ _ hv
  obtain ⟨s0, hs0⟩ := S_nonempty s hX
  have hws0 : s.w ≤ W ρ π k := (w_le_ρ s hs0).trans (hWk _ (ρ_mem_V _ _ s0))
  have hπ_step : ∀ C ∈ s.step.chains, s.step.π C = s.π C - s.w := by
    intro C hC
    rw [step_π, if_pos (step_chains_meet_S s hC)]
  have hρ_step_nn : ∀ x, 0 ≤ s.step.ρ x := (inv_step s hI).ρ_nonneg
  show maxValue s.step.ρ s.step.π = W ρ π k - s.w
  apply maxValue_eq_of
  · rintro v (⟨x, rfl⟩ | ⟨C, hC, rfl⟩)
    · rw [step_ρ]
      by_cases hxS : x ∈ s.S
      · rw [if_pos hxS]
        have := hWk _ (ρ_mem_V _ _ x)
        linarith
      · rw [if_neg hxS, mul_zero, sub_zero]
        by_cases hxX : x ∈ s.X
        · obtain ⟨C2, hC2, hle⟩ := hρle x hxX hxS
          have := hWk _ (π_mem_V s.ρ s.π (hI.chains_sub (step_chains_sub s hC2)))
          linarith
        · rw [ρ_zero_of_not_mem ρ π h k hxX]
          linarith
    · rcases hdom C hC with ⟨C', hC', _, h2⟩ | ⟨_, h2⟩
      · rw [hπ_step C' hC'] at h2
        have := hWk _ (π_mem_V s.ρ s.π (hI.chains_sub (step_chains_sub s hC')))
        linarith
      · linarith
  · have hmem := maxValue_mem s.ρ s.π
    rcases hmem with ⟨x, hx⟩ | ⟨C, hC, hCe⟩
    · change s.ρ x = W ρ π k at hx
      by_cases hxS : x ∈ s.S
      · refine ⟨s.step.ρ x, ρ_mem_V _ _ x, ?_⟩
        rw [step_ρ, if_pos hxS]
        linarith
      · by_cases hxX : x ∈ s.X
        · obtain ⟨C2, hC2, hle⟩ := hρle x hxX hxS
          refine ⟨s.step.π C2, π_mem_V _ _ (hI.chains_sub (step_chains_sub s hC2)), ?_⟩
          rw [hπ_step C2 hC2]
          linarith
        · refine ⟨s.step.ρ x, ρ_mem_V _ _ x, ?_⟩
          have := hρ_step_nn x
          rw [ρ_zero_of_not_mem ρ π h k hxX] at hx
          linarith
    · change s.π C = W ρ π k at hCe
      rcases hdom C hC with ⟨C', hC', h1, _⟩ | ⟨h1, _⟩
      · refine ⟨s.step.π C', π_mem_V _ _ (hI.chains_sub (step_chains_sub s hC')), ?_⟩
        rw [hπ_step C' hC']
        linarith
      · refine ⟨s.step.ρ (Classical.arbitrary α), ρ_mem_V _ _ _, ?_⟩
        have := hρ_step_nn (Classical.arbitrary α)
        linarith

lemma W_final [Nonempty α] (h : Standing ρ π) (n : ℕ) (hn : (iter ρ π n).X = ∅) :
    W ρ π n = 0 := by
  have hρ0 : ∀ x, (iter ρ π n).ρ x = 0 := fun x =>
    ρ_zero_of_not_mem ρ π h n (by rw [hn]; simp)
  unfold W
  apply maxValue_eq_of
  · rintro v (⟨x, rfl⟩ | ⟨C, hC, rfl⟩)
    · exact (hρ0 x).le
    · rw [π_eq ρ π h n C]
      simp only [hρ0, Finset.sum_const_zero, zero_sub]
      linarith [δ_final_nonneg' ρ π h n C hC]
  · exact ⟨_, ρ_mem_V _ _ (Classical.arbitrary α), (hρ0 _).ge⟩

end P4

end PMC

open PMC in
theorem solution {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α]
    (ρ : α → ℝ) (π : Finset α → ℝ) (h : Standing ρ π)
    (n : ℕ) (hn : (iter ρ π n).X = ∅)
    (hpre : ∀ k < n, (iter ρ π k).X.Nonempty) :
    ∑ k ∈ Finset.range n, (iter ρ π k).w = maxValue ρ π := by
  have hstep : ∀ k ∈ Finset.range n, (iter ρ π k).w = -(W ρ π (k + 1) - W ρ π k) := by
    intro k hk
    rw [W_succ ρ π h k (hpre k (Finset.mem_range.1 hk))]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib, Finset.sum_range_sub,
    W_final ρ π h n hn]
  show -(0 - maxValue ρ π) = maxValue ρ π
  ring
