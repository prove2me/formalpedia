-- Prove2me | solution 1 for StrategyProofArrow.WeakGS.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:40:12.592199+00:00
-- url     : https://prove2.me/submissions/abe53976-d767-4122-b79f-ba1a15a2b9df

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakGS_Basic



namespace StrategyProofArrow.WeakGS

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

theorem g4_mono_step (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
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

theorem g4_mono (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
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

theorem g4_unan (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
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

theorem g4_in2 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
    (C : StrategyProofArrow.Correspondence.StrongProfile ι A) (x y : A)
    (hxR : x ∈ Set.range ν)
    (h : ∀ w, w ≠ x → w ≠ y → ∀ i, (C i).1.strict x w) : ν C = x ∨ ν C = y := by
  by_contra hc
  push_neg at hc
  exact g4_unan ν hν C x (ν C) hxR (Ne.symm hc.1) (h _ hc.1 hc.2) rfl

theorem g4_in3 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
    (C : StrategyProofArrow.Correspondence.StrongProfile ι A) (x y z : A)
    (hxR : x ∈ Set.range ν)
    (h : ∀ w, w ≠ x → w ≠ y → w ≠ z → ∀ i, (C i).1.strict x w) :
    ν C = x ∨ ν C = y ∨ ν C = z := by
  by_contra hc
  push_neg at hc
  exact g4_unan ν hν C x (ν C) hxR (Ne.symm hc.1) (h _ hc.1 hc.2.1 hc.2.2) rfl

def g4D (ν : StrictVotingProcedure ι A) (x y : A) (S : Finset ι) : Prop := ν (g4T2 x y S) = x

theorem g4T2_compl (x y : A) (S : Finset ι) : g4T2 x y S = g4T2 y x Sᶜ := by
  funext i
  by_cases hi : i ∈ S <;> simp [g4T2, hi]

theorem g4T2_in2 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) (S : Finset ι) :
    ν (g4T2 x y S) = x ∨ ν (g4T2 x y S) = y := by
  apply g4_in2 ν hν _ x y hxR
  intro w hwx hwy i
  by_cases hi : i ∈ S <;>
    simp [g4T2, hi, g4top2, StrategyProofArrow.Correspondence.WeakOrder.strict, hwx, hwy, hxy,
      Ne.symm hwx, Ne.symm hwy, Ne.symm hxy]

theorem g4D_compl (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) (S : Finset ι) :
    g4D ν x y S ↔ ¬ g4D ν y x Sᶜ := by
  unfold g4D
  rw [← g4T2_compl]
  rcases g4T2_in2 ν hν x y hxy hxR S with h | h <;> rw [h]
  · simp [hxy]
  · simp [Ne.symm hxy]

theorem g4D_univ (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) : g4D ν x y Finset.univ := by
  unfold g4D
  rcases g4T2_in2 ν hν x y hxy hxR Finset.univ with h | h
  · exact h
  · exfalso
    apply g4_unan ν hν _ x y hxR hxy _ h
    intro i
    simp [g4T2, g4top2, StrategyProofArrow.Correspondence.WeakOrder.strict, hxy, Ne.symm hxy]

theorem g4D_empty (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y : A)
    (hxy : x ≠ y) (hxR : x ∈ Set.range ν) (hyR : y ∈ Set.range ν) : ¬ g4D ν x y ∅ := by
  rw [g4D_compl ν hν x y hxy hxR]
  simp only [Finset.compl_empty, not_not]
  exact g4D_univ ν hν y x (Ne.symm hxy) hyR

theorem g4D_mono (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y : A)
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

theorem g4_key2 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
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

theorem g4_rule1 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y z : A)
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

theorem g4_rule2 (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν) (x y z : A)
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


theorem g4_third (ν : StrictVotingProcedure ι A) (hR : 3 ≤ (Set.range ν).ncard) (x y : A) :
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

def g4Dec (ν : StrictVotingProcedure ι A) (S : Finset ι) : Prop :=
  ∀ u ∈ Set.range ν, ∀ v ∈ Set.range ν, u ≠ v → g4D ν u v S

theorem g4_expand (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
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

theorem g4_contract (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
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

theorem g4_singleton (ν : StrictVotingProcedure ι A) (hν : StrictStrategyProof ν)
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

theorem theorem_1_core (ν : StrictVotingProcedure ι A)
    (hp : 3 ≤ (Set.range ν).ncard) :
    StrictStrategyProof ν ↔ StrictDictatorial ν := by
  constructor
  · intro hν
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
  · rintro ⟨j, hj⟩ C i c ⟨h1, h2⟩
    have a1 := hj C (ν (Function.update C i c)) ⟨_, rfl⟩
    by_cases hij : i = j
    · subst hij
      exact h2 a1
    · have a2 := hj (Function.update C i c) (ν C) ⟨_, rfl⟩
      rw [Function.update_of_ne (Ne.symm hij)] at a2
      have heq := (C j).2 _ _ a2 (hj C _ ⟨_, rfl⟩)
      rw [heq] at h2
      exact h2 (((C i).1.total _ _).elim id id)

end

end StrategyProofArrow.WeakGS

open StrategyProofArrow.WeakGS


theorem solution {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (ν : StrictVotingProcedure ι A)
    (hp : 3 ≤ (Set.range ν).ncard) :
    StrictStrategyProof ν ↔ StrictDictatorial ν := by
  exact theorem_1_core ν hp
