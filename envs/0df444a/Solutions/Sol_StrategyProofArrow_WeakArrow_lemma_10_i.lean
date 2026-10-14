-- Prove2me | solution 1 for StrategyProofArrow.WeakArrow.lemma_10_i
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:49:50.890169+00:00
-- url     : https://prove2.me/submissions/d3f754c7-fd26-4e4b-a663-27ad2c14b457

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakArrow_Basic



namespace StrategyProofArrow.WeakArrow

open Classical

section G5
variable {ι A : Type*}

theorem g5_refl (R : WeakOrder A) (x : A) : R.rel x x := (R.total x x).elim id id

theorem g5_st_mk {R : WeakOrder A} {x y : A} (h1 : R.rel x y) (h2 : ¬ R.rel y x) :
    R.strict x y := And.intro h1 h2
theorem g5_st_rel {R : WeakOrder A} {x y : A} (h : R.strict x y) : R.rel x y := And.left h
theorem g5_st_nrel {R : WeakOrder A} {x y : A} (h : R.strict x y) : ¬ R.rel y x := And.right h
theorem g5_strict_iff {R : WeakOrder A} {x y : A} : R.strict x y ↔ R.rel x y ∧ ¬ R.rel y x :=
  Iff.rfl

theorem g5_st_irrefl {R : WeakOrder A} {x : A} (h : R.strict x x) : False :=
  (g5_st_nrel h) (g5_st_rel h)

theorem g5_st_trans {R : WeakOrder A} {x y z : A} (h1 : R.strict x y) (h2 : R.strict y z) :
    R.strict x z :=
  g5_st_mk (R.trans _ _ _ (g5_st_rel h1) (g5_st_rel h2))
    (fun h => g5_st_nrel h2 (R.trans _ _ _ h (g5_st_rel h1)))

theorem g5_st_trans_rel {R : WeakOrder A} {x y z : A} (h1 : R.rel x y) (h2 : R.strict y z) :
    R.strict x z :=
  g5_st_mk (R.trans _ _ _ h1 (g5_st_rel h2)) (fun h => g5_st_nrel h2 (R.trans _ _ _ h h1))

theorem g5_rel_of_not_strict {R : WeakOrder A} {x y : A} (h : ¬ R.strict x y) : R.rel y x := by
  rcases R.total y x with h' | h'
  · exact h'
  · by_contra hc; exact h (g5_st_mk h' hc)

def g5Rank (f : A → ℕ) : WeakOrder A where
  rel a b := f b ≤ f a
  total a b := le_total (f b) (f a)
  trans _ _ _ h1 h2 := le_trans h2 h1

@[simp] theorem g5Rank_rel (f : A → ℕ) (a b : A) : (g5Rank f).rel a b ↔ f b ≤ f a := Iff.rfl

@[simp] theorem g5Rank_strict (f : A → ℕ) (a b : A) : (g5Rank f).strict a b ↔ f b < f a := by
  rw [g5_strict_iff, g5Rank_rel, g5Rank_rel]; omega

theorem g5_rank_iff (R : WeakOrder A) (x z : A) (p q : ℕ) (hpq : q < p) :
    ((if R.rel z x then p else q) ≤ (if R.rel x z then p else q) ↔ R.rel x z) := by
  by_cases h1 : R.rel x z <;> by_cases h2 : R.rel z x <;> simp only [h1, h2, if_true, if_false]
  · simp
  · simp; omega
  · simp; omega
  · exact absurd (R.total x z) (by tauto)

theorem g5_psi_pair (R : WeakOrder A) (x y : A) : x ∈ Psi {x, y} R ↔ R.rel x y := by
  constructor
  · rintro ⟨_, h⟩; exact h y (by simp)
  · intro h
    refine ⟨by simp, ?_⟩
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact g5_refl _ _
    · exact h

theorem g5_psi_pair' (R : WeakOrder A) (x y : A) : y ∈ Psi {x, y} R ↔ R.rel y x := by
  rw [Set.pair_comm]; exact g5_psi_pair R y x

theorem g5_psi_congr {W : Set A} {R S : WeakOrder A} (h : AgreeOn W R S) : Psi W R = Psi W S := by
  ext w
  simp only [Psi, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hw, hh⟩; exact ⟨hw, fun y hy => (h w hw y hy).1 (hh y hy)⟩
  · rintro ⟨hw, hh⟩; exact ⟨hw, fun y hy => (h w hw y hy).2 (hh y hy)⟩

theorem g5_agree_pair {R S : WeakOrder A} {x y : A}
    (h1 : R.rel x y ↔ S.rel x y) (h2 : R.rel y x ↔ S.rel y x) : AgreeOn {x, y} R S := by
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  all_goals first
    | exact ⟨fun _ => g5_refl _ _, fun _ => g5_refl _ _⟩
    | exact h1
    | exact h2

theorem g5_pair_of_psi {R S : WeakOrder A} {x y : A} (h : Psi {x, y} R = Psi {x, y} S) :
    (R.rel x y ↔ S.rel x y) ∧ (R.rel y x ↔ S.rel y x) := by
  constructor
  · rw [← g5_psi_pair, ← g5_psi_pair, h]
  · rw [← g5_psi_pair', ← g5_psi_pair', h]

theorem g5_pairIIA {u : WeakProfile ι A → WeakOrder A} (hIIA : IIA u) (x y : A)
    (C D : WeakProfile ι A)
    (h1 : ∀ i, (C i).rel x y ↔ (D i).rel x y) (h2 : ∀ i, (C i).rel y x ↔ (D i).rel y x) :
    (u C).rel x y ↔ (u D).rel x y :=
  (g5_pair_of_psi (hIIA {x, y} C D (fun i => g5_agree_pair (h1 i) (h2 i)))).1

theorem g5_pairIIA_strict {u : WeakProfile ι A → WeakOrder A} (hIIA : IIA u) (x y : A)
    (C D : WeakProfile ι A)
    (h1 : ∀ i, (C i).rel x y ↔ (D i).rel x y) (h2 : ∀ i, (C i).rel y x ↔ (D i).rel y x) :
    (u C).strict x y ↔ (u D).strict x y := by
  rw [g5_strict_iff, g5_strict_iff, g5_pairIIA hIIA x y C D h1 h2, g5_pairIIA hIIA y x C D h2 h1]

variable [DecidableEq A]

noncomputable def g5Canon (x z : A) (R : WeakOrder A) : WeakOrder A :=
  g5Rank (fun a => if a = x then (if R.rel x z then 2 else 1)
    else if a = z then (if R.rel z x then 2 else 1) else 0)

theorem g5Canon_xz {x z : A} (hxz : x ≠ z) (R : WeakOrder A) :
    ((g5Canon x z R).rel x z ↔ R.rel x z) ∧ ((g5Canon x z R).rel z x ↔ R.rel z x) := by
  have hzx : z ≠ x := hxz.symm
  simp only [g5Canon, g5Rank_rel, if_true, hzx, if_false]
  exact ⟨g5_rank_iff R x z 2 1 (by norm_num), g5_rank_iff R z x 2 1 (by norm_num)⟩

theorem g5Canon_off {x z a b : A} (R : WeakOrder A) (ha : a ≠ x) (hb : b ≠ x) :
    ((g5Canon x z R).rel a b ↔ (a = z ∨ b ≠ z)) := by
  simp only [g5Canon, g5Rank_rel, ha, hb, if_false]
  by_cases hza : a = z <;> by_cases hzb : b = z
  · subst hza; subst hzb; simp
  · simp only [hza, hzb, if_true, if_false]; split_ifs <;> simp
  · simp only [hza, hzb, if_true, if_false]; split_ifs <;> simp_all
  · simp [hza, hzb]

theorem g5Canon_xw {x z w : A} (R : WeakOrder A) (h1 : w ≠ x) (h2 : w ≠ z) :
    (g5Canon x z R).strict x w := by
  simp only [g5Canon, g5Rank_strict, h1, h2, if_true, if_false]
  split_ifs <;> omega

/-- Pairwise non-negative response. -/
theorem g5_pnnr [Fintype ι] {u : WeakProfile ι A → WeakOrder A} (hIIA : IIA u) (hNNR : NNR u)
    (x z : A) (hxz : x ≠ z) (C D : WeakProfile ι A)
    (h1 : ∀ i, (C i).rel x z → (D i).rel x z) (h2 : ∀ i, (C i).strict x z → (D i).strict x z) :
    (u C).strict x z → (u D).strict x z := by
  intro hC
  have eC := g5_pairIIA_strict hIIA x z C (fun i => g5Canon x z (C i))
    (fun i => (g5Canon_xz hxz (C i)).1.symm) (fun i => (g5Canon_xz hxz (C i)).2.symm)
  have eD := g5_pairIIA_strict hIIA x z D (fun i => g5Canon x z (D i))
    (fun i => (g5Canon_xz hxz (D i)).1.symm) (fun i => (g5Canon_xz hxz (D i)).2.symm)
  rw [eD]; rw [eC] at hC
  refine hNNR x _ _ ?_ ?_ ?_ z hxz.symm hC
  · intro i a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb
    rw [g5Canon_off _ ha hb, g5Canon_off _ ha hb]
  · intro i y hy h
    by_cases hyz : y = z
    · subst hyz
      exact (g5Canon_xz hxz (D i)).1.2 (h1 i ((g5Canon_xz hxz (C i)).1.1 h))
    · exact g5_st_rel (g5Canon_xw (D i) hy hyz)
  · intro i y hy h
    by_cases hyz : y = z
    · subst hyz
      have hc : (C i).strict x y :=
        g5_st_mk ((g5Canon_xz hxz (C i)).1.1 (g5_st_rel h))
          (fun h' => g5_st_nrel h ((g5Canon_xz hxz (C i)).2.2 h'))
      have hd := h2 i hc
      exact g5_st_mk ((g5Canon_xz hxz (D i)).1.2 (g5_st_rel hd))
          (fun h' => g5_st_nrel hd ((g5Canon_xz hxz (D i)).2.1 h'))
    · exact g5Canon_xw (D i) hy hyz

theorem g5_pareto [Fintype ι] {u : WeakProfile ι A → WeakOrder A} (hCS : CS u) (hIIA : IIA u)
    (hNNR : NNR u) (x y : A) (hxy : x ≠ y) (D : WeakProfile ι A)
    (hD : ∀ i, (D i).strict x y) : (u D).strict x y := by
  obtain ⟨B, hB⟩ := hCS x y hxy
  exact g5_pnnr hIIA hNNR x y hxy B D (fun i _ => g5_st_rel (hD i)) (fun i _ => hD i) hB

theorem g5_bt_rel (Q : StrongOrder A) (R : WeakOrder A) (x y : A) :
    (breakTies Q R).1.rel x y ↔ R.strict x y ∨ (R.rel x y ∧ R.rel y x ∧ Q.1.rel x y) := Iff.rfl

theorem g5_bt_strict_of (Q : StrongOrder A) (R : WeakOrder A) {x y : A} (h : R.strict x y) :
    (breakTies Q R).1.strict x y := by
  refine g5_st_mk ((g5_bt_rel Q R x y).2 (Or.inl h)) ?_
  rw [g5_bt_rel]
  rintro (h' | ⟨h', _, _⟩)
  · exact g5_st_nrel h (g5_st_rel h')
  · exact g5_st_nrel h h'

theorem g5_bt_strict_iff (Q : StrongOrder A) (R : WeakOrder A) (x y : A) :
    (breakTies Q R).1.strict x y ↔
      R.strict x y ∨ (R.rel x y ∧ R.rel y x ∧ Q.1.strict x y) := by
  rw [g5_strict_iff, g5_bt_rel, g5_bt_rel, g5_strict_iff, g5_strict_iff, g5_strict_iff]
  tauto

theorem g5_bt_agree (Q : StrongOrder A) {R S : WeakOrder A} {W : Set A} (h : AgreeOn W R S) :
    AgreeOn W (breakTies Q R).1 (breakTies Q S).1 := by
  intro a ha b hb
  rw [g5_bt_rel, g5_bt_rel, g5_strict_iff, g5_strict_iff, h a ha b hb, h b hb a ha]
theorem g5_wo_ext {R S : WeakOrder A} (h : ∀ a b, R.rel a b ↔ S.rel a b) : R = S := by
  rcases R with ⟨r, _, _⟩
  rcases S with ⟨s, _, _⟩
  have : r = s := funext fun a => funext fun b => propext (h a b)
  subst this; rfl

theorem g5_strong_rel {S : WeakOrder A} (hS : S.IsStrong) (a b : A) :
    S.rel a b ↔ a = b ∨ S.strict a b := by
  constructor
  · intro h
    by_cases hba : S.rel b a
    · exact Or.inl (hS a b h hba)
    · exact Or.inr (g5_st_mk h hba)
  · rintro (rfl | h)
    · exact g5_refl _ _
    · exact g5_st_rel h

theorem g5_lemma_11_core [Fintype ι] (u : WeakProfile ι A → WeakOrder A) (Q : StrongOrder A)
    (hCS : CS u) (hNNR : NNR u) (hIIA : IIA u) :
    (∀ B, (breakTies Q (u B)).1.IsStrong) ∧
      CS (fun B => (breakTies Q (u B)).1) ∧
      NNR (fun B => (breakTies Q (u B)).1) ∧
      IIA (fun B => (breakTies Q (u B)).1) := by
  refine ⟨fun B => (breakTies Q (u B)).2, ?_, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨B, hB⟩ := hCS x y hxy
    exact ⟨B, g5_bt_strict_of Q _ hB⟩
  · intro x C D hag hrel hst z hzx hC
    beta_reduce at hC ⊢
    have hC' := (g5_bt_strict_iff Q (u C) x z).1 hC
    have hDrel : (u D).rel x z := by
      by_contra hn
      have hDs : (u D).strict z x := g5_st_mk ((u D).total x z |>.resolve_left hn) hn
      have hCs : (u C).strict z x := by
        refine g5_pnnr hIIA hNNR z x hzx D C ?_ ?_ hDs
        · intro i hd
          by_contra hc
          have : (C i).strict x z := g5_st_mk ((C i).total x z |>.resolve_right hc) hc
          exact g5_st_nrel (hst i z hzx this) hd
        · intro i hd
          have hc : ¬ (C i).rel x z := fun h => g5_st_nrel hd (hrel i z hzx h)
          exact g5_st_mk ((C i).total x z |>.resolve_left hc) hc
      rcases hC' with hs | ⟨h1, _, _⟩
      · exact g5_st_nrel hs (g5_st_rel hCs)
      · exact g5_st_nrel hCs h1
    rcases hC' with hs | ⟨_, _, hq⟩
    · exact g5_bt_strict_of Q _ (hNNR x C D hag hrel hst z hzx hs)
    · rw [g5_bt_strict_iff]
      by_cases hzx' : (u D).rel z x
      · exact Or.inr ⟨hDrel, hzx', hq⟩
      · exact Or.inl (g5_st_mk hDrel hzx')
  · intro W C D hag
    beta_reduce
    apply g5_psi_congr
    apply g5_bt_agree
    intro a ha b hb
    exact g5_pairIIA hIIA a b C D (fun i => hag i a ha b hb) (fun i => hag i b hb a ha)

theorem g5_lemma_10_i_core [Fintype ι] (u : WeakProfile ι A → WeakOrder A)
    (γ : WeakProfile ι A → StrongProfile ι A) (hγ : IsRegular γ)
    (μ : StrongProfile ι A → StrongOrder A)
    (hIIA : StrictIIA μ) (hCS : StrictCS μ) (hNNR : StrictNNR μ)
    (hu : ∀ B, u B = (μ (γ B)).1) :
    IIA u ∧ CS u ∧ NNR u := by
  obtain ⟨hT, Q, hQ⟩ := hγ
  have char : ∀ (B : WeakProfile ι A) i a b, (γ B i).1.strict a b ↔
      (B i).strict a b ∨ ((B i).rel a b ∧ (B i).rel b a ∧ (Q i).1.strict a b) := by
    intro B i a b
    by_cases h1 : (B i).rel a b <;> by_cases h2 : (B i).rel b a
    · rw [hQ B i a b h1 h2]
      constructor
      · intro h; exact Or.inr ⟨h1, h2, h⟩
      · rintro (h | ⟨_, _, h⟩)
        · exact absurd h2 (g5_st_nrel h)
        · exact h
    · have hs : (B i).strict a b := g5_st_mk h1 h2
      exact ⟨fun _ => Or.inl hs, fun _ => hT B i a b hs⟩
    · have hs : (B i).strict b a := g5_st_mk h2 h1
      have hg := hT B i b a hs
      constructor
      · intro h; exact absurd (g5_st_rel h) (g5_st_nrel hg)
      · rintro (h | ⟨h, _, _⟩)
        · exact absurd (g5_st_rel h) h1
        · exact absurd h h1
    · exact absurd ((B i).total a b) (by tauto)
  have agree : ∀ (C D : WeakProfile ι A) i a b, ((C i).rel a b ↔ (D i).rel a b) →
      ((C i).rel b a ↔ (D i).rel b a) → ((γ C i).1.rel a b ↔ (γ D i).1.rel a b) := by
    intro C D i a b h1 h2
    rw [g5_strong_rel (γ C i).2, g5_strong_rel (γ D i).2, char, char]
    simp only [g5_strict_iff, h1, h2]
  refine ⟨?_, ?_, ?_⟩
  · intro W C D hag
    rw [hu C, hu D]
    apply hIIA
    intro i a ha b hb
    exact agree C D i a b (hag i a ha b hb) (hag i b hb a ha)
  · intro x y hxy
    obtain ⟨B, hB⟩ := hCS x y hxy
    refine ⟨toWeak B, ?_⟩
    rw [hu]
    have key : ∀ i a b, (γ (toWeak B) i).1.rel a b ↔ (B i).1.rel a b := by
      intro i a b
      rw [g5_strong_rel (γ _ i).2, g5_strong_rel (B i).2, char]
      show a = b ∨ ((B i).1.strict a b ∨ ((B i).1.rel a b ∧ (B i).1.rel b a ∧ (Q i).1.strict a b))
        ↔ a = b ∨ (B i).1.strict a b
      constructor
      · rintro (h | h | ⟨h1, h2, _⟩)
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl ((B i).2 a b h1 h2)
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    have := g5_pair_of_psi (hIIA {x, y} (γ (toWeak B)) B
      (fun i a _ b _ => key i a b))
    rw [g5_strict_iff, this.1, this.2]
    exact hB
  · intro x C D hag hrel hst z hzx hC
    rw [hu] at hC ⊢
    have mono : ∀ i y, y ≠ x → (γ C i).1.strict x y → (γ D i).1.strict x y := by
      intro i y hy
      rw [char, char]
      rintro (h | ⟨h1, _, hq⟩)
      · exact Or.inl (hst i y hy h)
      · have hd := hrel i y hy h1
        by_cases h2' : (D i).rel y x
        · exact Or.inr ⟨hd, h2', hq⟩
        · exact Or.inl (g5_st_mk hd h2')
    refine hNNR x (γ C) (γ D) ?_ ?_ ?_ z hzx hC
    · intro i a ha b hb
      exact agree C D i a b (hag i a ha b hb) (hag i b hb a ha)
    · intro i y hy h
      rw [g5_strong_rel (γ C i).2] at h
      rw [g5_strong_rel (γ D i).2]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (mono i y hy h)
    · exact mono

theorem g5_lemma_10_ii_core [Fintype ι] (u : WeakProfile ι A → WeakOrder A)
    (hrange : ∀ B, (u B).IsStrong)
    (hIIA : IIA u) (hCS : CS u) (hNNR : NNR u) :
    ∃ α : WeakProfile ι A → StrongProfile ι A, IsTieBreaking α ∧
      ∃ μ : StrongProfile ι A → StrongOrder A,
        StrictIIA μ ∧ StrictCS μ ∧ StrictNNR μ ∧ ∀ B, u B = (μ (α B)).1 := by
  let α : WeakProfile ι A → StrongProfile ι A := fun B i => breakTies ⟨u B, hrange B⟩ (B i)
  let μ : StrongProfile ι A → StrongOrder A := fun C => ⟨u (toWeak C), hrange _⟩
  have key_strict : ∀ B a b, (u B).strict a b → (u (toWeak (α B))).strict a b := by
    intro B a b h
    have hab : a ≠ b := by rintro rfl; exact g5_st_irrefl h
    refine g5_pnnr hIIA hNNR a b hab B _ ?_ ?_ h
    · intro i hr
      show (breakTies ⟨u B, hrange B⟩ (B i)).1.rel a b
      rw [g5_bt_rel]
      by_cases hba : (B i).rel b a
      · exact Or.inr ⟨hr, hba, g5_st_rel h⟩
      · exact Or.inl (g5_st_mk hr hba)
    · intro i hs
      exact g5_bt_strict_of _ _ hs
  have key : ∀ B, u B = (μ (α B)).1 := by
    intro B
    apply g5_wo_ext
    intro a b
    show (u B).rel a b ↔ (u (toWeak (α B))).rel a b
    by_cases hab : a = b
    · subst hab; exact ⟨fun _ => g5_refl _ _, fun _ => g5_refl _ _⟩
    · by_cases h : (u B).rel a b
      · by_cases h' : (u B).rel b a
        · exact absurd (hrange B a b h h') hab
        · exact ⟨fun _ => g5_st_rel (key_strict B a b (g5_st_mk h h')), fun _ => h⟩
      · have hs : (u B).strict b a := g5_st_mk ((u B).total a b |>.resolve_left h) h
        exact ⟨fun h'' => absurd h'' h, fun h'' => absurd h'' (g5_st_nrel (key_strict B b a hs))⟩
  refine ⟨α, fun B i x y h => g5_bt_strict_of _ _ h, μ, ?_, ?_, ?_, key⟩
  · intro W C D h; exact hIIA W (toWeak C) (toWeak D) h
  · intro x y hxy
    obtain ⟨B, hB⟩ := hCS x y hxy
    refine ⟨α B, ?_⟩
    rw [← key]; exact hB
  · intro x C D h1 h2 h3 z hz hC
    exact hNNR x (toWeak C) (toWeak D) h1 h2 h3 z hz hC

end G5

end StrategyProofArrow.WeakArrow

open StrategyProofArrow.WeakArrow


theorem solution {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : WeakProfile ι A → WeakOrder A) (hrange : ∀ B, (u B).IsStrong)
    (γ : WeakProfile ι A → StrongProfile ι A) (hγ : IsRegular γ)
    (μ : StrongProfile ι A → StrongOrder A)
    (hIIA : StrictIIA μ) (hCS : StrictCS μ) (hNNR : StrictNNR μ)
    (hu : ∀ B, u B = (μ (γ B)).1) :
    IIA u ∧ CS u ∧ NNR u := by
  exact g5_lemma_10_i_core u γ hγ μ hIIA hCS hNNR hu
