-- Prove2me | solution 1 for StrategyProofArrow.Correspondence.cs_of_po
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:53:07.165976+00:00
-- url     : https://prove2.me/submissions/b42bd87a-4c31-40ce-8571-e5b39034771f

import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic



namespace StrategyProofArrow.Correspondence

/-- lift `a` to the top of a strong order -/
def g4lift {A : Type*} (a : A) (R : StrategyProofArrow.Correspondence.StrongOrder A) :
    StrategyProofArrow.Correspondence.StrongOrder A :=
  ⟨{ rel := fun u w => u = a ∨ (w ≠ a ∧ R.1.rel u w)
     total := by
       intro u w
       by_cases hu : u = a
       · exact Or.inl (Or.inl hu)
       · by_cases hw : w = a
         · exact Or.inr (Or.inl hw)
         · rcases R.1.total u w with h | h
           · exact Or.inl (Or.inr ⟨hw, h⟩)
           · exact Or.inr (Or.inr ⟨hu, h⟩)
     trans := by
       rintro u w t (hu | ⟨hw, huw⟩) (hw' | ⟨ht, hwt⟩)
       · exact Or.inl hu
       · exact Or.inl hu
       · exact absurd hw' hw
       · exact Or.inr ⟨ht, R.1.trans _ _ _ huw hwt⟩ },
   by
     rintro u w (hu | ⟨hw, huw⟩) (hw' | ⟨hu', hwu⟩)
     · rw [hu, hw']
     · exact absurd hu hu'
     · exact absurd hw' hw
     · exact R.2 _ _ huw hwu⟩

@[simp] theorem g4lift_rel {A : Type*} (a : A) (R : StrategyProofArrow.Correspondence.StrongOrder A)
    (u w : A) : (g4lift a R).1.rel u w ↔ (u = a ∨ (w ≠ a ∧ R.1.rel u w)) := Iff.rfl

noncomputable def g4Q0 (A : Type*) [Fintype A] : StrategyProofArrow.Correspondence.StrongOrder A :=
  ⟨{ rel := fun u w => ((Fintype.equivFin A) u : ℕ) ≤ (Fintype.equivFin A) w
     total := fun _ _ => le_total _ _
     trans := fun _ _ _ => le_trans },
   fun _ _ h1 h2 => (Fintype.equivFin A).injective (Fin.ext (le_antisymm h1 h2))⟩

noncomputable def g4top2 {A : Type*} [Fintype A] (x y : A) : StrategyProofArrow.Correspondence.StrongOrder A :=
  g4lift x (g4lift y (g4Q0 A))

noncomputable def g4top3 {A : Type*} [Fintype A] (x y z : A) :
    StrategyProofArrow.Correspondence.StrongOrder A :=
  g4lift x (g4lift y (g4lift z (g4Q0 A)))

noncomputable def g4T2 {ι A : Type*} [Fintype A] [DecidableEq ι] (x y : A) (S : Finset ι) :
    StrategyProofArrow.Correspondence.StrongProfile ι A :=
  fun i => if i ∈ S then g4top2 x y else g4top2 y x

theorem g4_strong_rel_iff' {A : Type*} (S : StrategyProofArrow.Correspondence.StrongOrder A) {x y : A}
    (hxy : x ≠ y) : S.1.rel x y ↔ ¬ S.1.rel y x := by
  constructor
  · intro h h'; exact hxy (S.2 x y h h')
  · intro h; exact (S.1.total x y).resolve_right h

section
set_option linter.unusedSectionVars false
variable {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]

theorem g4_mono_step (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν)
    (P : StrategyProofArrow.Correspondence.StrongProfile ι A) (i : ι)
    (c : StrategyProofArrow.Correspondence.StrongOrder A)
    (h : ∀ z, (P i).1.rel (ν P) z → c.1.rel (ν P) z) : ν (Function.update P i c) = ν P := by
  have h1 := hν P i c
  have h2 := hν (Function.update P i c) i (P i)
  simp only [Function.update_idem, Function.update_eq_self, Function.update_self] at h2
  by_contra hne
  have hca : ¬ c.1.rel (ν P) (ν (Function.update P i c)) := by
    intro hc
    exact h2 ⟨hc, fun hc' => hne (c.2 _ _ hc' hc)⟩
  have hPa : ¬ (P i).1.rel (ν P) (ν (Function.update P i c)) := fun hp => hca (h _ hp)
  exact h1 ⟨((P i).1.total _ _).resolve_right hPa, hPa⟩

theorem g4_mono (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν)
    (C C' : StrategyProofArrow.Correspondence.StrongProfile ι A)
    (h : ∀ i z, (C i).1.rel (ν C) z → (C' i).1.rel (ν C) z) : ν C' = ν C := by
  let D : Finset ι → StrategyProofArrow.Correspondence.StrongProfile ι A := fun S j =>
    if j ∈ S then C' j else C j
  have key : ∀ S : Finset ι, ν (D S) = ν C := by
    intro S
    induction S using Finset.induction_on with
    | empty => congr 1
    | insert i S hi ih =>
      have hDi : D S i = C i := by simp [D, hi]
      have hstep := g4_mono_step ν hν (D S) i (C' i) (by
        intro z hz
        rw [hDi, ih] at hz
        rw [ih]
        exact h i z hz)
      rw [← ih, ← hstep]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [D]
      · simp [D, hj]
  have := key Finset.univ
  rw [← this]
  congr 1
  funext j
  simp [D]

theorem g4_unan (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν)
    (C : StrategyProofArrow.Correspondence.StrongProfile ι A) (a w : A)
    (ha : a ∈ Set.range ν) (haw : a ≠ w) (h : ∀ i, (C i).1.strict a w) : ν C ≠ w := by
  obtain ⟨D, hD⟩ := ha
  intro hw
  let E : StrategyProofArrow.Correspondence.StrongProfile ι A := fun i => g4lift a (C i)
  have e1 : ν E = ν C := g4_mono ν hν C E (by
    intro i z hz
    rw [hw] at hz ⊢
    show (g4lift a (C i)).1.rel w z
    rw [g4lift_rel]
    refine Or.inr ⟨?_, hz⟩
    rintro rfl
    exact (h i).2 hz)
  have e2 : ν E = ν D := g4_mono ν hν D E (by
    intro i z _
    rw [hD]
    show (g4lift a (C i)).1.rel a z
    rw [g4lift_rel]
    exact Or.inl rfl)
  apply haw
  rw [← hD, ← e2, e1, hw]

theorem g4_in2 (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν)
    (C : StrategyProofArrow.Correspondence.StrongProfile ι A) (x y : A)
    (hxR : x ∈ Set.range ν)
    (h : ∀ w, w ≠ x → w ≠ y → ∀ i, (C i).1.strict x w) : ν C = x ∨ ν C = y := by
  by_contra hc
  push_neg at hc
  exact g4_unan ν hν C x (ν C) hxR (Ne.symm hc.1) (h _ hc.1 hc.2) rfl

theorem g4_in3 (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν)
    (C : StrategyProofArrow.Correspondence.StrongProfile ι A) (x y z : A)
    (hxR : x ∈ Set.range ν)
    (h : ∀ w, w ≠ x → w ≠ y → w ≠ z → ∀ i, (C i).1.strict x w) :
    ν C = x ∨ ν C = y ∨ ν C = z := by
  by_contra hc
  push_neg at hc
  exact g4_unan ν hν C x (ν C) hxR (Ne.symm hc.1) (h _ hc.1 hc.2.1 hc.2.2) rfl

def g4D (ν : (StrongProfile ι A → A)) (x y : A) (S : Finset ι) : Prop := ν (g4T2 x y S) = x

theorem g4T2_compl (x y : A) (S : Finset ι) : g4T2 x y S = g4T2 y x Sᶜ := by
  funext i
  by_cases hi : i ∈ S <;> simp [g4T2, hi]

theorem g4T2_in2 (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) (S : Finset ι) :
    ν (g4T2 x y S) = x ∨ ν (g4T2 x y S) = y := by
  apply g4_in2 ν hν _ x y hxR
  intro w hwx hwy i
  by_cases hi : i ∈ S <;>
    simp [g4T2, hi, g4top2, StrategyProofArrow.Correspondence.WeakOrder.strict, hwx, hwy, hxy,
      Ne.symm hwx, Ne.symm hwy, Ne.symm hxy]

theorem g4D_compl (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) (S : Finset ι) :
    g4D ν x y S ↔ ¬ g4D ν y x Sᶜ := by
  unfold g4D
  rw [← g4T2_compl]
  rcases g4T2_in2 ν hν x y hxy hxR S with h | h <;> rw [h]
  · simp [hxy]
  · simp [Ne.symm hxy]

theorem g4D_univ (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) : g4D ν x y Finset.univ := by
  unfold g4D
  rcases g4T2_in2 ν hν x y hxy hxR Finset.univ with h | h
  · exact h
  · exfalso
    apply g4_unan ν hν _ x y hxR hxy _ h
    intro i
    simp [g4T2, g4top2, StrategyProofArrow.Correspondence.WeakOrder.strict, hxy, Ne.symm hxy]

theorem g4D_empty (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) (hyR : y ∈ Set.range ν) : ¬ g4D ν x y ∅ := by
  rw [g4D_compl ν hν x y hxy hxR]
  simp only [Finset.compl_empty, not_not]
  exact g4D_univ ν hν y x (Ne.symm hxy) hyR

theorem g4D_mono (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν) (x y : A)
    (S T : Finset ι) (hST : S ⊆ T) (h : g4D ν x y S) : g4D ν x y T := by
  unfold g4D at *
  rw [← h]
  apply g4_mono ν hν
  intro i z hz
  rw [h] at hz ⊢
  by_cases hiT : i ∈ T
  · simp [g4T2, hiT, g4top2]
  · have hiS : i ∉ S := fun hs => hiT (hST hs)
    simpa [g4T2, hiT, hiS] using hz

theorem g4_key2 (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν)
    (C : StrategyProofArrow.Correspondence.StrongProfile ι A) (x y : A) (hx : ν C = x)
    (S : Finset ι) (hS : ∀ i, i ∈ S ↔ (C i).1.rel x y) : g4D ν x y S := by
  unfold g4D
  rw [← hx]
  apply g4_mono ν hν
  intro i z hz
  rw [hx] at hz ⊢
  by_cases hi : i ∈ S
  · simp [g4T2, hi, g4top2]
  · have hn : ¬ (C i).1.rel x y := fun h => hi ((hS i).2 h)
    have hzy : z ≠ y := by rintro rfl; exact hn hz
    simp [g4T2, hi, g4top2, hzy]

theorem g4_rule1 (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν) (x y z : A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxR : x ∈ Set.range ν) (hyR : y ∈ Set.range ν) (hzR : z ∈ Set.range ν)
    (S : Finset ι) (h : g4D ν x y S) : g4D ν x z S := by
  let C : StrategyProofArrow.Correspondence.StrongProfile ι A := fun i =>
    if i ∈ S then g4top3 x y z else g4top3 y z x
  have ho := g4_in3 ν hν C x y z hxR (by
    intro w hwx hwy hwz i
    by_cases hi : i ∈ S <;>
      simp [C, hi, g4top3, StrategyProofArrow.Correspondence.WeakOrder.strict, hwx, hwy, hwz,
        hxy, hxz, hyz, Ne.symm hwx, Ne.symm hwy, Ne.symm hwz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
  rcases ho with ho | ho | ho
  · apply g4_key2 ν hν C x z ho S
    intro i
    by_cases hi : i ∈ S <;>
      simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
  · exfalso
    have := g4_key2 ν hν C y x ho Sᶜ (by
      intro i
      by_cases hi : i ∈ S <;>
        simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
    exact (g4D_compl ν hν x y hxy hxR S).1 h this
  · exfalso
    have := g4_key2 ν hν C z y ho ∅ (by
      intro i
      by_cases hi : i ∈ S <;>
        simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
    exact g4D_empty ν hν z y (Ne.symm hyz) hzR hyR this

theorem g4_rule2 (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν) (x y z : A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxR : x ∈ Set.range ν) (hyR : y ∈ Set.range ν) (hzR : z ∈ Set.range ν)
    (S : Finset ι) (h : g4D ν x y S) : g4D ν z y S := by
  let C : StrategyProofArrow.Correspondence.StrongProfile ι A := fun i =>
    if i ∈ S then g4top3 z x y else g4top3 y z x
  have ho := g4_in3 ν hν C x y z hxR (by
    intro w hwx hwy hwz i
    by_cases hi : i ∈ S <;>
      simp [C, hi, g4top3, StrategyProofArrow.Correspondence.WeakOrder.strict, hwx, hwy, hwz,
        hxy, hxz, hyz, Ne.symm hwx, Ne.symm hwy, Ne.symm hwz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
  rcases ho with ho | ho | ho
  · exfalso
    have := g4_key2 ν hν C x z ho ∅ (by
      intro i
      by_cases hi : i ∈ S <;>
        simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
    exact g4D_empty ν hν x z hxz hxR hzR this
  · exfalso
    have := g4_key2 ν hν C y x ho Sᶜ (by
      intro i
      by_cases hi : i ∈ S <;>
        simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
    exact (g4D_compl ν hν x y hxy hxR S).1 h this
  · apply g4_key2 ν hν C z y ho S
    intro i
    by_cases hi : i ∈ S <;>
      simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]


theorem g4_third (ν : (StrongProfile ι A → A)) (hR : 3 ≤ (Set.range ν).ncard) (x y : A) :
    ∃ z ∈ Set.range ν, z ≠ x ∧ z ≠ y := by
  by_contra hc
  push_neg at hc
  have hsub : Set.range ν ⊆ ({x, y} : Set A) := by
    intro z hz
    by_cases hzx : z = x
    · simp [hzx]
    · simp [hc z hz hzx]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({x, y} : Set A).ncard ≤ 2 := by
    calc ({x, y} : Set A).ncard ≤ ({y} : Set A).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by simp
  omega

def g4Dec (ν : (StrongProfile ι A → A)) (S : Finset ι) : Prop :=
  ∀ u ∈ Set.range ν, ∀ v ∈ Set.range ν, u ≠ v → g4D ν u v S

theorem g4_expand (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν)
    (hR : 3 ≤ (Set.range ν).ncard) (x y : A) (hxy : x ≠ y)
    (hxR : x ∈ Set.range ν) (hyR : y ∈ Set.range ν) (S : Finset ι) (h : g4D ν x y S) :
    g4Dec ν S := by
  have h1 : ∀ v ∈ Set.range ν, v ≠ x → g4D ν x v S := by
    intro v hvR hvx
    by_cases hvy : v = y
    · rw [hvy]; exact h
    · exact g4_rule1 ν hν x y v hxy (Ne.symm hvx) (Ne.symm hvy) hxR hyR hvR S h
  intro u huR v hvR huv
  by_cases hux : u = x
  · rw [hux] at huv ⊢; exact h1 v hvR (Ne.symm huv)
  · by_cases hvx : v = x
    · obtain ⟨w, hwR, hwu, hwx⟩ := g4_third ν hR u x
      have a1 := h1 w hwR hwx
      have a2 := g4_rule2 ν hν x w u (Ne.symm hwx) (Ne.symm hux) hwu hxR hwR huR S a1
      rw [hvx]
      exact g4_rule1 ν hν u w x (Ne.symm hwu) hux hwx huR hwR hxR S a2
    · have a1 := h1 v hvR hvx
      exact g4_rule2 ν hν x v u (Ne.symm hvx) (Ne.symm hux) (Ne.symm huv) hxR hvR huR S a1

theorem g4_contract (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν)
    (hR : 3 ≤ (Set.range ν).ncard) (S1 S2 : Finset ι) (hdisj : Disjoint S1 S2)
    (h : g4Dec ν (S1 ∪ S2)) : g4Dec ν S1 ∨ g4Dec ν S2 := by
  have hne : (Set.range ν).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨x, hxR⟩ := hne
  obtain ⟨y, hyR, hyx, -⟩ := g4_third ν hR x x
  obtain ⟨z, hzR, hzx, hzy⟩ := g4_third ν hR x y
  have hxy : x ≠ y := Ne.symm hyx
  have hxz : x ≠ z := Ne.symm hzx
  have hyz : y ≠ z := Ne.symm hzy
  let C : StrategyProofArrow.Correspondence.StrongProfile ι A := fun i =>
    if i ∈ S1 then g4top3 x y z else if i ∈ S2 then g4top3 z x y else g4top3 y z x
  have hd := h x hxR y hyR hxy
  have ho := g4_in3 ν hν C x y z hxR (by
    intro w hwx hwy hwz i
    by_cases hi : i ∈ S1 <;> by_cases hi2 : i ∈ S2 <;>
      simp [C, hi, hi2, g4top3, StrategyProofArrow.Correspondence.WeakOrder.strict, hwx, hwy, hwz,
        hxy, hxz, hyz, Ne.symm hwx, Ne.symm hwy, Ne.symm hwz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
  have hdis : ∀ i, i ∈ S1 → i ∉ S2 := fun i h1 h2 => Finset.disjoint_left.1 hdisj h1 h2
  rcases ho with ho | ho | ho
  · left
    apply g4_expand ν hν hR x z hxz hxR hzR S1
    apply g4_key2 ν hν C x z ho S1
    intro i
    by_cases hi : i ∈ S1
    · simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
    · by_cases hi2 : i ∈ S2 <;>
        simp [C, hi, hi2, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
  · exfalso
    have := g4_key2 ν hν C y x ho (S1 ∪ S2)ᶜ (by
      intro i
      by_cases hi : i ∈ S1
      · simp [C, hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
      · by_cases hi2 : i ∈ S2 <;>
          simp [C, hi, hi2, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz])
    exact (g4D_compl ν hν x y hxy hxR _).1 hd this
  · right
    apply g4_expand ν hν hR z y (Ne.symm hyz) hzR hyR S2
    apply g4_key2 ν hν C z y ho S2
    intro i
    by_cases hi : i ∈ S1
    · simp [C, hi, hdis i hi, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
    · by_cases hi2 : i ∈ S2 <;>
        simp [C, hi, hi2, g4top3, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]

theorem g4_singleton (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν)
    (hR : 3 ≤ (Set.range ν).ncard) : ∃ j : ι, g4Dec ν {j} := by
  have hne : (Set.range ν).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨x, hxR⟩ := hne
  obtain ⟨y, hyR, hyx, -⟩ := g4_third ν hR x x
  have main : ∀ n, ∀ S : Finset ι, S.card = n → g4Dec ν S → ∃ j : ι, g4Dec ν {j} := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hcard hS
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · rw [Finset.card_eq_zero] at hcard
          subst hcard
          exact absurd (hS x hxR y hyR (Ne.symm hyx)) (g4D_empty ν hν x y (Ne.symm hyx) hxR hyR)
        · obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hcard
          exact ⟨j, hS⟩
      · have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
        obtain ⟨j, hj⟩ := hSne
        have hsplit : S = {j} ∪ S.erase j := by
          rw [Finset.singleton_union, Finset.insert_erase hj]
        have hdisj : Disjoint ({j} : Finset ι) (S.erase j) := by simp
        rw [hsplit] at hS
        rcases g4_contract ν hν hR _ _ hdisj hS with h1 | h2
        · exact ⟨j, h1⟩
        · exact ih (S.erase j).card (by rw [Finset.card_erase_of_mem hj]; omega) _ rfl h2
  exact main _ Finset.univ rfl (fun u hu v hv huv => g4D_univ ν hν u v huv hu)


theorem gs_dict (ν : (StrongProfile ι A → A)) (hν : StrategyProof ν)
    (hp : 3 ≤ (Set.range ν).ncard) :
    ∃ j : ι, ∀ C : StrongProfile ι A, ∀ y ∈ Set.range ν, (C j).1.rel (ν C) y := by
  obtain ⟨j, hj⟩ := g4_singleton ν hν hp
  refine ⟨j, fun C y hyR => ?_⟩
  by_cases hxy : ν C = y
  · rw [hxy]; exact ((C j).1.total y y).elim id id
  · by_contra hn
    classical
    let T : Finset ι := Finset.univ.filter (fun i => (C i).1.rel (ν C) y)
    have hT := g4_key2 ν hν C (ν C) y rfl T (fun i => by simp [T])
    have hjT : j ∉ T := by simp [T, hn]
    have hsub : T ⊆ ({j} : Finset ι)ᶜ := by
      intro i hi
      simp only [Finset.mem_compl, Finset.mem_singleton]
      rintro rfl; exact hjT hi
    have h1 := g4D_mono ν hν _ _ _ _ hsub hT
    have h2 := hj y hyR (ν C) ⟨C, rfl⟩ (Ne.symm hxy)
    exact (g4D_compl ν hν y (ν C) (Ne.symm hxy) hyR {j}).1 h2 h1

end

/-! ## Basic helpers -/

theorem g6_refl {A : Type*} (R : WeakOrder A) (x : A) : R.rel x x := (R.total x x).elim id id

theorem g6_strict_of_rel {A : Type*} (S : StrongOrder A) {x y : A} (hxy : x ≠ y)
    (h : S.1.rel x y) : S.1.strict x y :=
  ⟨h, fun h' => hxy (S.2 x y h h')⟩

theorem g6_exists_top {A : Type*} [Fintype A] [Nonempty A] (R : StrongOrder A) :
    ∃ x, ∀ y, R.1.rel x y := by
  classical
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ
    (fun x => (Finset.univ.filter (fun z => R.1.rel x z)).card) Finset.univ_nonempty
  refine ⟨x, fun y => ?_⟩
  by_contra hxy
  have hyx : R.1.rel y x := (R.1.total x y).resolve_left hxy
  have hsub : Finset.univ.filter (fun z => R.1.rel x z) ⊂
      Finset.univ.filter (fun z => R.1.rel y z) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨y, by simp [g6_refl], by simp [hxy]⟩
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact R.1.trans _ _ _ hyx hz
  have h1 := Finset.card_lt_card hsub
  have h2 := hx y (Finset.mem_univ _)
  omega

noncomputable def g6top {A : Type*} [Fintype A] [Nonempty A] (R : StrongOrder A) : A :=
  Classical.choose (g6_exists_top R)

theorem g6top_spec {A : Type*} [Fintype A] [Nonempty A] (R : StrongOrder A) (y : A) :
    R.1.rel (g6top R) y := Classical.choose_spec (g6_exists_top R) y

theorem g6_psi_univ {A : Type*} (R : StrongOrder A) (a : A) :
    Psi Set.univ R.1 = {a} ↔ ∀ y, R.1.rel a y := by
  constructor
  · intro h y
    have : a ∈ Psi Set.univ R.1 := by rw [h]; rfl
    exact this.2 y trivial
  · intro h
    ext z
    simp only [Psi, Set.mem_univ, true_and, forall_const, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    constructor
    · intro hz; exact R.2 z a (hz a) (h z)
    · rintro rfl; exact h

theorem g6_underlies_iff {ι A : Type*} (u : StrongProfile ι A → StrongOrder A)
    (v : StrongProfile ι A → A) : Underlies u v ↔ ∀ B y, (u B).1.rel (v B) y := by
  unfold Underlies
  exact forall_congr' (fun B => g6_psi_univ (u B) (v B))

theorem g6_mem_psi_pair {A : Type*} (R : WeakOrder A) (x y : A) :
    x ∈ Psi ({x, y} : Set A) R ↔ R.rel x y := by
  simp only [Psi, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
    true_and, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => h.2, fun h => ⟨g6_refl R x, h⟩⟩

theorem g6_agree_pair {A : Type*} (S S' : StrongOrder A) {x y : A} (hxy : x ≠ y)
    (h : S.1.rel x y ↔ S'.1.rel x y) : AgreeOn ({x, y} : Set A) S.1 S'.1 := by
  intro w hw z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw hz
  rcases hw with rfl | rfl <;> rcases hz with rfl | rfl
  · exact ⟨fun _ => g6_refl _ _, fun _ => g6_refl _ _⟩
  · exact h
  · rw [g4_strong_rel_iff' S (Ne.symm hxy), g4_strong_rel_iff' S' (Ne.symm hxy), h]
  · exact ⟨fun _ => g6_refl _ _, fun _ => g6_refl _ _⟩

theorem g6_iia_pair {ι A : Type*} (u : StrongProfile ι A → StrongOrder A) (hiia : IIA u)
    (C D : StrongProfile ι A) {x y : A} (hxy : x ≠ y)
    (h : ∀ i, ((C i).1.rel x y ↔ (D i).1.rel x y)) :
    ((u C).1.rel x y ↔ (u D).1.rel x y) := by
  have := hiia ({x, y} : Set A) C D (fun i => g6_agree_pair (C i) (D i) hxy (h i))
  rw [← g6_mem_psi_pair, ← g6_mem_psi_pair, this]

theorem g6_lift_top {A : Type*} (x : A) (R : StrongOrder A) (y : A) : (g4lift x R).1.rel x y :=
  Or.inl rfl

theorem g6_lift_agree {A : Type*} (x : A) (R : StrongOrder A) :
    AgreeOn ({x}ᶜ : Set A) R.1 (g4lift x R).1 := by
  intro w hw z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw hz
  rw [g4lift_rel]
  simp [hw, hz]

/-! ## The milestones -/

theorem cs_of_po_core {ι A : Type*} [Fintype A]
    (u : StrongProfile ι A → StrongOrder A) (hpo : PO u) : CS u := by
  intro x y hxy
  refine ⟨fun _ => g4lift x (g4Q0 A), hpo _ x y (fun _ => ?_)⟩
  exact g6_strict_of_rel _ hxy (g6_lift_top x _ y)

theorem po_core {ι A : Type*} [Fintype A] [DecidableEq ι] [Nonempty ι]
    (u : StrongProfile ι A → StrongOrder A) (hcs : CS u) (hnnr : NNR u) (hiia : IIA u) :
    PO u := by
  intro B x y hB
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hxy : x ≠ y := by
    intro h; subst h; exact (hB i0).2 (hB i0).1
  obtain ⟨C, hC⟩ := hcs x y hxy
  let D : StrongProfile ι A := fun i => g4lift x (C i)
  have hD : (u D).1.strict x y := by
    refine hnnr x C D (fun i => g6_lift_agree x (C i)) (fun i z _ _ => g6_lift_top x _ z)
      (fun i z hz _ => g6_strict_of_rel _ (Ne.symm hz) (g6_lift_top x _ z)) y (Ne.symm hxy) hC
  have := (g6_iia_pair u hiia B D hxy (fun i => ⟨fun _ => g6_lift_top x _ y,
    fun _ => (hB i).1⟩)).2 hD.1
  exact g6_strict_of_rel _ hxy this

theorem range_of_po {ι A : Type*} [Fintype A]
    (u : StrongProfile ι A → StrongOrder A) (hpo : PO u) (v : StrongProfile ι A → A)
    (hu : Underlies u v) : Set.range v = Set.univ := by
  rw [g6_underlies_iff] at hu
  refine Set.eq_univ_of_forall (fun x => ⟨fun _ => g4lift x (g4Q0 A), ?_⟩)
  by_contra hne
  have h := hpo (fun _ => g4lift x (g4Q0 A)) x (v fun _ => g4lift x (g4Q0 A))
    (fun _ => g6_strict_of_rel _ (Ne.symm hne) (g6_lift_top x _ _))
  exact h.2 (hu _ x)

theorem dict_of_sp {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hm : 3 ≤ Fintype.card A) (v : StrongProfile ι A → A) (hsp : StrategyProof v)
    (hr : Set.range v = Set.univ) : ∃ d : ι, ∀ (B : StrongProfile ι A) y, (B d).1.rel (v B) y := by
  have hp : 3 ≤ (Set.range v).ncard := by
    rw [hr, Set.ncard_univ, Nat.card_eq_fintype_card]; exact hm
  obtain ⟨d, hd⟩ := gs_dict v hsp hp
  exact ⟨d, fun B y => hd B y (by rw [hr]; trivial)⟩

theorem u_eq_dict {ι A : Type*} [Fintype A] (d : ι) (v : StrongProfile ι A → A)
    (hd : ∀ (B : StrongProfile ι A) y, (B d).1.rel (v B) y)
    (u : StrongProfile ι A → StrongOrder A) (hu : Underlies u v) (hiia : IIA u) :
    ∀ B, u B = B d := by
  classical
  rw [g6_underlies_iff] at hu
  have key : ∀ B x y, x ≠ y → (B d).1.rel x y → (u B).1.rel x y := by
    intro B x y hxy hBxy
    let B' : StrongProfile ι A := fun i => if (B i).1.rel x y then g4top2 x y else g4top2 y x
    have hB' : ∀ i, ((B i).1.rel x y ↔ (B' i).1.rel x y) := by
      intro i
      by_cases h : (B i).1.rel x y
      · simp only [B', h, if_true, true_iff]; exact g6_lift_top x _ y
      · simp only [B', h, if_false, false_iff]
        simp [g4top2, hxy, Ne.symm hxy]
    have hv : v B' = x := by
      have h1 := hd B' x
      have hd' : B' d = g4top2 x y := by simp [B', hBxy]
      rw [hd'] at h1
      exact (g4top2 x y).2 _ _ h1 (g6_lift_top x _ _)
    have := hu B' y
    rw [hv] at this
    exact (g6_iia_pair u hiia B B' hxy hB').2 this
  intro B
  apply Subtype.ext
  apply WeakOrder.ext
  funext x y
  apply propext
  by_cases hxy : x = y
  · subst hxy; exact ⟨fun _ => g6_refl _ _, fun _ => g6_refl _ _⟩
  constructor
  · intro h
    by_contra h'
    have := key B y x (Ne.symm hxy) (((B d).1.total x y).resolve_left h')
    exact hxy ((u B).2 x y h this)
  · exact key B x y hxy

theorem lemma_7_core {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : StrongProfile ι A → StrongOrder A) (hcs : CS u) (hnnr : NNR u) (hiia : IIA u) :
    (∃ v : StrongProfile ι A → A, Underlies u v) ∧
      ∀ v : StrongProfile ι A → A, Underlies u v →
        StrategyProof v ∧ Set.range v = Set.univ := by
  haveI : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  refine ⟨⟨fun B => g6top (u B), (g6_underlies_iff _ _).2 (fun B y => g6top_spec _ y)⟩, ?_⟩
  intro v hu
  have hpo := po_core u hcs hnnr hiia
  refine ⟨?_, range_of_po u hpo v hu⟩
  rw [g6_underlies_iff] at hu
  intro B i b ⟨h1, h2⟩
  set x := v (Function.update B i b) with hx
  set y := v B with hy
  have hxy : x ≠ y := by
    intro h; rw [h] at h2; exact h2 (g6_refl _ _)
  have hyx_soc : (u B).1.rel y x := hu B x
  -- in u B, x is not weakly above y
  suffices hsoc : (u B).1.rel x y from hxy ((u B).2 x y hsoc hyx_soc)
  by_cases hb : b.1.rel x y
  · have := hu (Function.update B i b) y
    rw [← hx] at this
    refine (g6_iia_pair u hiia B (Function.update B i b) hxy (fun j => ?_)).2 this
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact ⟨fun _ => hb, fun _ => h1⟩
    · rw [Function.update_of_ne hj]
  · let D : StrongProfile ι A := Function.update B i (g4lift x b)
    have hC : (u (Function.update B i b)).1.strict x y := by
      have := hu (Function.update B i b) y
      rw [← hx] at this
      exact g6_strict_of_rel _ hxy this
    have hD : (u D).1.strict x y := by
      refine hnnr x (Function.update B i b) D (fun j => ?_) (fun j z _ hz => ?_)
        (fun j z hzx hz => ?_) y (Ne.symm hxy) hC
      · by_cases hj : j = i
        · subst hj; simp only [D, Function.update_self]; exact g6_lift_agree x b
        · simp only [D, Function.update_of_ne hj]
          intro w _ z _; exact Iff.rfl
      · by_cases hj : j = i
        · subst hj; simp only [D, Function.update_self]; exact g6_lift_top x _ z
        · simp only [D, Function.update_of_ne hj] at hz ⊢; exact hz
      · by_cases hj : j = i
        · subst hj; simp only [D, Function.update_self]
          exact g6_strict_of_rel _ (Ne.symm hzx) (g6_lift_top x _ z)
        · simp only [D, Function.update_of_ne hj] at hz ⊢; exact hz
    refine (g6_iia_pair u hiia B D hxy (fun j => ?_)).2 hD.1
    by_cases hj : j = i
    · subst hj; simp only [D, Function.update_self]; exact ⟨fun _ => g6_lift_top x _ y, fun _ => h1⟩
    · simp only [D, Function.update_of_ne hj]

theorem dict_iia {ι A : Type*} (d : ι) : IIA (fun B : StrongProfile ι A => B d) := by
  intro W C D h
  ext z
  simp only [Psi, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, hz'⟩; exact ⟨hz, fun y hy => (h d z hz y hy).1 (hz' y hy)⟩
  · rintro ⟨hz, hz'⟩; exact ⟨hz, fun y hy => (h d z hz y hy).2 (hz' y hy)⟩

theorem dict_po {ι A : Type*} (d : ι) : PO (fun B : StrongProfile ι A => B d) :=
  fun _ _ _ h => h d

theorem dict_nnr {ι A : Type*} (d : ι) : NNR (fun B : StrongProfile ι A => B d) :=
  fun _ _ _ _ _ hstr z hz hC => hstr d z hz hC

theorem gibbard_claim_core {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hm : 3 ≤ Fintype.card A)
    (v : StrongProfile ι A → A) (hsp : StrategyProof v) (hrange : Set.range v = Set.univ)
    (Q : StrongOrder A) :
    ∃ μ : StrongProfile ι A → StrongOrder A,
      (∀ B x y, (μ B).1.rel x y ↔ gibbardRel v Q B x y) ∧
      Underlies μ v ∧ PO μ ∧ IIA μ := by
  obtain ⟨d, hd⟩ := dict_of_sp hm v hsp hrange
  refine ⟨fun B => B d, ?_, (g6_underlies_iff _ _).2 hd, dict_po d, dict_iia d⟩
  intro B x y
  unfold gibbardRel
  by_cases hxy : x = y
  · subst hxy; exact ⟨fun _ => Or.inl rfl, fun _ => g6_refl _ _⟩
  simp only [hxy, false_or]
  set w := v (fun i => delta Q x y (B i)) with hw
  have htop := hd (fun i => delta Q x y (B i))
  rw [← hw] at htop
  have hwx := htop x
  have hwy := htop y
  change deltaRel Q.1 (B d).1 x y w x at hwx
  change deltaRel Q.1 (B d).1 x y w y at hwy
  have hwmem : w = x ∨ w = y := by
    unfold deltaRel at hwx
    rcases hwx with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
    · exact h
    · exact h
    · exact absurd (Or.inl rfl) h
  constructor
  · intro h
    rcases hwmem with h' | h'
    · exact h'.symm
    · exfalso
      unfold deltaRel at hwx
      rw [h'] at hwx
      rcases hwx with ⟨-, -, h3⟩ | ⟨-, h3⟩ | ⟨h3, -⟩
      · exact hxy ((B d).2 x y h h3)
      · exact h3 (Or.inl rfl)
      · exact h3 (Or.inr rfl)
  · intro h
    unfold deltaRel at hwy
    rw [← h] at hwy
    rcases hwy with ⟨-, -, h3⟩ | ⟨-, h3⟩ | ⟨h3, -⟩
    · exact h3
    · exact absurd (Or.inr rfl) h3
    · exact absurd (Or.inl rfl) h3

theorem underlying_unique_core {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hm : 3 ≤ Fintype.card A)
    (v : StrongProfile ι A → A) (hsp : StrategyProof v)
    (u u' : StrongProfile ι A → StrongOrder A)
    (hu : Underlies u v) (hpo : PO u) (hiia : IIA u)
    (hu' : Underlies u' v) (hiia' : IIA u') :
    u = u' := by
  obtain ⟨d, hd⟩ := dict_of_sp hm v hsp (range_of_po u hpo v hu)
  funext B
  rw [u_eq_dict d v hd u hu hiia B, u_eq_dict d v hd u' hu' hiia' B]

theorem nnr_of_underlies_core {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hm : 3 ≤ Fintype.card A)
    (v : StrongProfile ι A → A) (hsp : StrategyProof v)
    (u : StrongProfile ι A → StrongOrder A) (hu : Underlies u v) (hpo : PO u) (hiia : IIA u) :
    NNR u := by
  obtain ⟨d, hd⟩ := dict_of_sp hm v hsp (range_of_po u hpo v hu)
  have : u = fun B => B d := funext (u_eq_dict d v hd u hu hiia)
  rw [this]; exact dict_nnr d

theorem lemma_8_core {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : StrongProfile ι A → A) (hsp : StrategyProof v) (hrange : Set.range v = Set.univ) :
    ∃! u : StrongProfile ι A → StrongOrder A, Underlies u v ∧ CS u ∧ NNR u ∧ IIA u := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨d, hd⟩ := dict_of_sp hm v hsp hrange
  refine ⟨fun B => B d, ⟨(g6_underlies_iff _ _).2 hd, cs_of_po_core _ (dict_po d), dict_nnr d,
    dict_iia d⟩, ?_⟩
  rintro u' ⟨hu', hcs', hnnr', hiia'⟩
  exact funext (u_eq_dict d v hd u' hu' hiia')

theorem theorem_2_core {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A) :
    ∃ lam : {v : StrongProfile ι A → A // StrategyProof v ∧ Set.range v = Set.univ} ≃
        {u : StrongProfile ι A → StrongOrder A // CS u ∧ NNR u ∧ IIA u},
      ∀ v, Underlies (lam v).1 v.1 := by
  haveI : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  let F : {v : StrongProfile ι A → A // StrategyProof v ∧ Set.range v = Set.univ} →
      {u : StrongProfile ι A → StrongOrder A // CS u ∧ NNR u ∧ IIA u} := fun v =>
    ⟨Classical.choose (lemma_8_core hn hm v.1 v.2.1 v.2.2).exists,
      (Classical.choose_spec (lemma_8_core hn hm v.1 v.2.1 v.2.2).exists).2⟩
  have hF : ∀ v, Underlies (F v).1 v.1 := fun v =>
    (Classical.choose_spec (lemma_8_core hn hm v.1 v.2.1 v.2.2).exists).1
  let G : {u : StrongProfile ι A → StrongOrder A // CS u ∧ NNR u ∧ IIA u} →
      {v : StrongProfile ι A → A // StrategyProof v ∧ Set.range v = Set.univ} := fun u =>
    ⟨fun B => g6top (u.1 B),
      (lemma_7_core hn hm u.1 u.2.1 u.2.2.1 u.2.2.2).2 _
        ((g6_underlies_iff _ _).2 (fun B y => g6top_spec _ y))⟩
  refine ⟨⟨F, G, ?_, ?_⟩, hF⟩
  · intro v
    apply Subtype.ext
    funext B
    have h1 := (g6_underlies_iff _ _).1 (hF v) B
    show g6top ((F v).1 B) = v.1 B
    exact ((F v).1 B).2 _ _ (g6top_spec _ _) (h1 _)
  · intro u
    apply Subtype.ext
    have hGu : Underlies u.1 (G u).1 := (g6_underlies_iff _ _).2 (fun B y => g6top_spec _ y)
    exact (lemma_8_core hn hm (G u).1 (G u).2.1 (G u).2.2).unique
      ⟨hF (G u), (F (G u)).2⟩ ⟨hGu, u.2⟩

end StrategyProofArrow.Correspondence

open StrategyProofArrow.Correspondence


theorem solution {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : StrongProfile ι A → StrongOrder A) (hpo : PO u) :
    CS u := by
  exact cs_of_po_core u hpo
