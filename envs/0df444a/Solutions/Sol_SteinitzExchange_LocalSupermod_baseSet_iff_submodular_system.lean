-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.baseSet_iff_submodular_system
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:54:25.320854+00:00
-- url     : https://prove2.me/submissions/e569cf02-ccc7-4bac-ad7f-4c368623e37c

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal



namespace SteinitzExchange.LocalSupermod

open Finset

theorem aux_bs_chi_apply {V : Type*} [DecidableEq V] (u w : V) :
    chi u w = if w = u then 1 else 0 := by
  unfold chi; simp [Pi.single_apply]

theorem aux_bs_sumOn_ex {V : Type*} [DecidableEq V] (y : V → ℤ) (a b : V) (Z : Finset V) :
    sumOn (y - chi a + chi b) Z = sumOn y Z - (if a ∈ Z then 1 else 0) + (if b ∈ Z then 1 else 0) := by
  unfold sumOn
  simp only [Pi.add_apply, Pi.sub_apply, aux_bs_chi_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq']

theorem aux_bs_dist_lt {V : Type*} [Fintype V] [DecidableEq V] (p q : V → ℤ) (u v : V)
    (hu : q u < p u) (hv : p v < q v) :
    ∑ w, |(p - chi u + chi v) w - q w| < ∑ w, |p w - q w| := by
  have huv : u ≠ v := by rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    simp only [Pi.add_apply, Pi.sub_apply, aux_bs_chi_apply]
    by_cases h1 : w = u
    · subst h1; simp only [if_true, huv, if_false]
      rw [abs_le]; constructor <;> cases abs_cases (p w - q w) <;> omega
    · by_cases h2 : w = v
      · subst h2; simp only [h1, if_true, if_false]
        rw [abs_le]; constructor <;> cases abs_cases (p w - q w) <;> omega
      · simp [h1, h2]
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [Pi.add_apply, Pi.sub_apply, aux_bs_chi_apply, if_true, huv, if_false]
    rw [abs_lt]; constructor <;> cases abs_cases (p u - q u) <;> omega

/-- local optimality -/
theorem aux_bs_LO {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (hB1 : ∀ x ∈ B, ∀ y ∈ B, ∀ u : V, 0 < (x - y) u →
      ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B)
    (y : V → ℤ) (hy : y ∈ B) (X : Finset V)
    (hloc : ∀ a b, a ∉ X → b ∈ X → y - chi a + chi b ∉ B) :
    ∀ z ∈ B, sumOn z X ≤ sumOn y X := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hzS, hzmin⟩ := (B.filter (fun z => sumOn y X < sumOn z X)).exists_min_image
    (fun z => ∑ w, |z w - y w|)
    (by obtain ⟨z, hz, h⟩ := hcon; exact ⟨z, by simp [hz, h]⟩)
  simp only [Finset.mem_filter] at hzS hzmin
  have key : ∀ u v, y u < z u → z v < y v → z - chi u + chi v ∈ B →
      sumOn z X ≤ sumOn (z - chi u + chi v) X → False := by
    intro u v hu hv hB h
    have h1 := hzmin _ ⟨hB, lt_of_lt_of_le hzS.2 h⟩
    have h2 := aux_bs_dist_lt z y u v hu hv
    linarith
  have : ∃ u ∈ X, y u < z u := by
    by_contra h; push Not at h
    have := Finset.sum_le_sum h
    have h2 := hzS.2; unfold sumOn at h2; linarith
  obtain ⟨u, huX, hu⟩ := this
  obtain ⟨v, hv, hz'⟩ := hB1 z hzS.1 y hy u (by simp; linarith)
  simp only [Pi.sub_apply] at hv
  by_cases hvX : v ∈ X
  · exact key u v hu (by linarith) hz' (by rw [aux_bs_sumOn_ex]; simp [huX, hvX])
  · obtain ⟨w, hw, hy'⟩ := hB1 y hy z hzS.1 v (by simp; linarith)
    simp only [Pi.sub_apply] at hw
    by_cases hwX : w ∈ X
    · exact hloc v w hvX hwX hy'
    · obtain ⟨v', hv', hz''⟩ := hB1 z hzS.1 y hy w (by simp; linarith)
      simp only [Pi.sub_apply] at hv'
      exact key w v' (by linarith) (by linarith) hz''
        (by rw [aux_bs_sumOn_ex]; simp only [hwX, if_false]; split_ifs <;> omega)

theorem aux_bs_trans {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (hB1 : ∀ x ∈ B, ∀ y ∈ B, ∀ u : V, 0 < (x - y) u →
      ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B)
    (y : V → ℤ) (hy : y ∈ B) (a b c : V)
    (h1 : y - chi c + chi b ∈ B) (h2 : y - chi a + chi c ∈ B) : y - chi a + chi b ∈ B := by
  by_cases hab : a = b
  · subst hab; simpa using hy
  by_cases hcb : c = b
  · subst hcb; exact h2
  by_cases hca : c = a
  · subst hca; exact h1
  obtain ⟨v, hv, hB⟩ := hB1 _ h1 _ h2 a (by
    simp [aux_bs_chi_apply, hab, Ne.symm hca])
  have hvc : v = c := by
    by_contra hvc
    simp only [Pi.sub_apply, Pi.add_apply, aux_bs_chi_apply, hvc, if_false] at hv
    split_ifs at hv <;> omega
  subst hvc
  convert hB using 1
  funext w
  simp only [Pi.sub_apply, Pi.add_apply, aux_bs_chi_apply]
  split_ifs <;> omega

theorem aux_bs_claimC {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (hB1 : ∀ x ∈ B, ∀ y ∈ B, ∀ u : V, 0 < (x - y) u →
      ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B)
    (hne : B.Nonempty) (x : V → ℤ)
    (hx : ∀ X, sumOn x X ≤ B.sup' hne (fun z => sumOn z X))
    (hxV : sumOn x univ = B.sup' hne (fun z => sumOn z univ)) : x ∈ B := by
  obtain ⟨y, hyB, hymin⟩ := B.exists_min_image (fun y => ∑ w, |y w - x w|) hne
  by_contra hxB
  -- no improving exchange
  have hno : ∀ a b, x a < y a → y b < x b → y - chi a + chi b ∉ B := by
    intro a b ha hb hB
    have h1 := hymin _ hB
    have h2 := aux_bs_dist_lt y x a b ha hb
    linarith
  by_cases hP : ∃ b, y b < x b
  · obtain ⟨b0, hb0⟩ := hP
    let U := univ.filter (fun w => ∃ b, y b < x b ∧ y - chi w + chi b ∈ B)
    have hU : ∀ z ∈ B, sumOn z U ≤ sumOn y U := by
      apply aux_bs_LO B hB1 y hyB U
      intro a b' haU hb'U hB
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at haU hb'U
      obtain ⟨b, hb, hbB⟩ := hb'U
      exact haU ⟨b, hb, aux_bs_trans B hB1 y hyB a b b' hbB hB⟩
    have hfU : B.sup' hne (fun z => sumOn z U) ≤ sumOn y U := Finset.sup'_le _ _ hU
    have hb0U : b0 ∈ U := by
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨b0, hb0, by simpa using hyB⟩
    have hlt : sumOn y U < sumOn x U := by
      unfold sumOn
      apply Finset.sum_lt_sum
      · intro w hw
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨b, hb, hbB⟩ := hw
        by_contra hlt; push Not at hlt
        exact hno w b hlt hb hbB
      · exact ⟨b0, hb0U, hb0⟩
    have := hx U
    linarith
  · push Not at hP
    apply hxB
    have hyV : sumOn y univ ≤ sumOn x univ := by
      rw [hxV]; exact Finset.le_sup' (fun z => sumOn z univ) hyB
    have : x = y := by
      funext w
      by_contra hne'
      have hlt : sumOn x univ < sumOn y univ := by
        unfold sumOn
        apply Finset.sum_lt_sum (fun i _ => hP i)
        exact ⟨w, Finset.mem_univ _, lt_of_le_of_ne (hP w) hne'⟩
      linarith
    rw [this]; exact hyB

theorem aux_bs_union_inter {V : Type*} [DecidableEq V] (x : V → ℤ) (X Y : Finset V) :
    sumOn x (X ∪ Y) + sumOn x (X ∩ Y) = sumOn x X + sumOn x Y := by
  unfold sumOn; exact Finset.sum_union_inter

theorem aux_bs_claimB {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (hB1 : ∀ x ∈ B, ∀ y ∈ B, ∀ u : V, 0 < (x - y) u →
      ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B)
    (hne : B.Nonempty) : IsSubmodular (fun X : Finset V => B.sup' hne (fun z => sumOn z X)) := by
  intro X Y
  obtain ⟨y, hyB, hymax⟩ := B.exists_max_image
    (fun z => sumOn z (X ∪ Y) + sumOn z (X ∩ Y)) hne
  have h1 : ∀ z ∈ B, sumOn z (X ∪ Y) ≤ sumOn y (X ∪ Y) := by
    apply aux_bs_LO B hB1 y hyB
    intro a b ha hb hB
    have := hymax _ hB
    simp only [aux_bs_sumOn_ex] at this
    have ha' : a ∉ X ∩ Y := fun h => ha (Finset.inter_subset_union h)
    simp only [ha, ha', hb, if_true, if_false] at this
    split_ifs at this <;> omega
  have h2 : ∀ z ∈ B, sumOn z (X ∩ Y) ≤ sumOn y (X ∩ Y) := by
    apply aux_bs_LO B hB1 y hyB
    intro a b ha hb hB
    have := hymax _ hB
    simp only [aux_bs_sumOn_ex] at this
    have hb' : b ∈ X ∪ Y := Finset.inter_subset_union hb
    simp only [ha, hb', hb, if_true, if_false] at this
    split_ifs at this <;> omega
  have e1 : B.sup' hne (fun z => sumOn z (X ∪ Y)) ≤ sumOn y (X ∪ Y) := Finset.sup'_le _ _ h1
  have e2 : B.sup' hne (fun z => sumOn z (X ∩ Y)) ≤ sumOn y (X ∩ Y) := Finset.sup'_le _ _ h2
  have e3 : sumOn y X ≤ B.sup' hne (fun z => sumOn z X) := Finset.le_sup' (fun z => sumOn z X) hyB
  have e4 : sumOn y Y ≤ B.sup' hne (fun z => sumOn z Y) := Finset.le_sup' (fun z => sumOn z Y) hyB
  have := aux_bs_union_inter y X Y
  show B.sup' hne (fun z => sumOn z (X ∪ Y)) + B.sup' hne (fun z => sumOn z (X ∩ Y)) ≤
    B.sup' hne (fun z => sumOn z X) + B.sup' hne (fun z => sumOn z Y)
  linarith

theorem aux_bs_fwd {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (hne : B.Nonempty) (hB : IsIntegralBaseSet B) :
    ∀ x : V → ℤ, x ∈ B ↔
      (∀ X : Finset V, sumOn x X ≤ B.sup' hne (fun z => sumOn z X)) ∧
        sumOn x Finset.univ = B.sup' hne (fun z => sumOn z Finset.univ) := by
  intro x
  constructor
  · intro hx
    refine ⟨fun X => Finset.le_sup' (fun z => sumOn z X) hx, ?_⟩
    apply le_antisymm (Finset.le_sup' (fun z => sumOn z Finset.univ) hx)
    apply Finset.sup'_le
    apply aux_bs_LO B hB.2 x hx
    intro a b ha; exact absurd (Finset.mem_univ a) ha
  · rintro ⟨h1, h2⟩
    exact aux_bs_claimC B hB.2 hne x h1 h2

section tight
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem aux_bs_tight_ui (f : Finset V → ℤ) (hf : IsSubmodular f) (x : V → ℤ)
    (hx : ∀ Y, sumOn x Y ≤ f Y) (X Y : Finset V) (hX : sumOn x X = f X) (hY : sumOn x Y = f Y) :
    sumOn x (X ∪ Y) = f (X ∪ Y) ∧ sumOn x (X ∩ Y) = f (X ∩ Y) := by
  have := aux_bs_union_inter x X Y
  have := hf X Y
  have := hx (X ∪ Y)
  have := hx (X ∩ Y)
  constructor <;> linarith

theorem aux_bs_tight_sup {ι : Type*} [DecidableEq ι] (f : Finset V → ℤ) (hf : IsSubmodular f)
    (h0 : f ∅ = 0) (x : V → ℤ)
    (hx : ∀ Y, sumOn x Y ≤ f Y) (s : Finset ι) (F : ι → Finset V)
    (hF : ∀ i ∈ s, sumOn x (F i) = f (F i)) : sumOn x (s.sup F) = f (s.sup F) := by
  induction s using Finset.induction_on with
  | empty => simp [h0, sumOn]
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sup_eq_union]
    exact (aux_bs_tight_ui f hf x hx _ _ (hF a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))).1

theorem aux_bs_tight_inf {ι : Type*} [DecidableEq ι] (f : Finset V → ℤ) (hf : IsSubmodular f)
    (x : V → ℤ) (hx : ∀ Y, sumOn x Y ≤ f Y) (hV : sumOn x Finset.univ = f Finset.univ)
    (s : Finset ι) (F : ι → Finset V)
    (hF : ∀ i ∈ s, sumOn x (F i) = f (F i)) : sumOn x (s.inf F) = f (s.inf F) := by
  induction s using Finset.induction_on with
  | empty => simpa using hV
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.inf_eq_inter]
    exact (aux_bs_tight_ui f hf x hx _ _ (hF a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))).2

end tight

theorem aux_bs_bwd {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (hne : B.Nonempty) (f : Finset V → ℤ) (hf : IsSubmodular f) (h0 : f ∅ = 0)
    (hchar : ∀ x : V → ℤ, x ∈ B ↔
      (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ) :
    IsIntegralBaseSet B := by
  refine ⟨hne, ?_⟩
  intro x hx y hy u hu
  simp only [Pi.sub_apply] at hu
  obtain ⟨hxle, hxV⟩ := (hchar x).1 hx
  obtain ⟨hyle, hyV⟩ := (hchar y).1 hy
  let S := Finset.univ.filter (fun Y : Finset V => sumOn x Y = f Y ∧ u ∉ Y)
  let W := S.sup id
  have hW : sumOn x W = f W :=
    aux_bs_tight_sup f hf h0 x hxle S id (fun i hi => (Finset.mem_filter.1 hi).2.1)
  have huW : u ∉ W := by
    intro h
    obtain ⟨Y, hY, huY⟩ := Finset.mem_sup.1 h
    exact (Finset.mem_filter.1 hY).2.2 huY
  -- find v ∉ W with x v < y v
  have : ∃ v ∈ Wᶜ, x v < y v := by
    by_contra h; push Not at h
    have hlt : sumOn y Wᶜ < sumOn x Wᶜ := by
      unfold sumOn
      apply Finset.sum_lt_sum (fun i hi => h i hi)
      exact ⟨u, Finset.mem_compl.2 huW, by omega⟩
    have c1 : sumOn x Wᶜ + sumOn x W = sumOn x Finset.univ := Finset.sum_compl_add_sum _ _
    have c2 : sumOn y Wᶜ + sumOn y W = sumOn y Finset.univ := Finset.sum_compl_add_sum _ _
    have := hyle W
    linarith
  obtain ⟨v, hvW, hv⟩ := this
  rw [Finset.mem_compl] at hvW
  refine ⟨v, by simp only [Pi.sub_apply]; omega, ?_⟩
  rw [hchar]
  constructor
  · intro Y
    rw [aux_bs_sumOn_ex]
    have := hxle Y
    by_cases hvY : v ∈ Y
    · by_cases huY : u ∈ Y
      · simp only [hvY, huY, if_true]; omega
      · have hnt : sumOn x Y ≠ f Y := by
          intro ht
          have hYS : Y ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, ht, huY⟩
          exact hvW ((Finset.le_sup (f := id) hYS) hvY)
        simp only [hvY, huY, if_true, if_false]; omega
    · simp only [hvY, if_false]; split_ifs <;> omega
  · rw [aux_bs_sumOn_ex]; simp [hxV]

theorem aux_bs_uniq {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (hne : B.Nonempty) (f : Finset V → ℤ) (hf : IsSubmodular f) (h0 : f ∅ = 0)
    (hchar : ∀ x : V → ℤ, x ∈ B ↔
      (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ) :
    ∀ X : Finset V, f X = B.sup' hne (fun x => sumOn x X) := by
  intro X
  apply le_antisymm
  · obtain ⟨x, hxB, hxmax⟩ := B.exists_max_image (fun z => sumOn z X) hne
    obtain ⟨hxle, hxV⟩ := (hchar x).1 hxB
    let T : V → Finset V := fun u =>
      (Finset.univ.filter (fun Y : Finset V => sumOn x Y = f Y ∧ u ∈ Y)).inf id
    have hT : ∀ u, sumOn x (T u) = f (T u) := fun u =>
      aux_bs_tight_inf f hf x hxle hxV _ id (fun i hi => (Finset.mem_filter.1 hi).2.1)
    have huT : ∀ u, u ∈ T u := by
      intro u
      simp only [T]
      rw [Finset.mem_inf]
      intro Y hY; exact (Finset.mem_filter.1 hY).2.2
    have hTX : ∀ u ∈ X, T u ⊆ X := by
      intro u hu w hw
      by_contra hwX
      have hnB : x - chi w + chi u ∉ B := by
        intro hB
        have := hxmax _ hB
        rw [aux_bs_sumOn_ex] at this
        simp only [hwX, hu, if_true, if_false] at this; omega
      rw [hchar] at hnB
      have hVeq : sumOn (x - chi w + chi u) Finset.univ = f Finset.univ := by
        rw [aux_bs_sumOn_ex]; simp [hxV]
      have : ∃ Y, f Y < sumOn (x - chi w + chi u) Y := by
        by_contra h; push Not at h; exact hnB ⟨h, hVeq⟩
      obtain ⟨Y, hY⟩ := this
      rw [aux_bs_sumOn_ex] at hY
      have := hxle Y
      have huY : u ∈ Y := by by_contra h; simp only [h, if_false] at hY; split_ifs at hY <;> omega
      have hwY : w ∉ Y := by intro h; simp only [h, huY, if_true] at hY; omega
      have htY : sumOn x Y = f Y := by
        simp only [huY, hwY, if_true, if_false] at hY; omega
      have hYS : Y ∈ Finset.univ.filter (fun Y : Finset V => sumOn x Y = f Y ∧ u ∈ Y) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, htY, huY⟩
      exact hwY ((Finset.inf_le (f := id) hYS) hw)
    have hXeq : X.sup T = X := by
      apply le_antisymm
      · exact Finset.sup_le hTX
      · intro u hu; exact (Finset.le_sup (f := T) hu) (huT u)
    have htX : sumOn x X = f X := by
      have := aux_bs_tight_sup f hf h0 x hxle X T (fun u _ => hT u)
      rwa [hXeq] at this
    rw [← htX]
    exact Finset.le_sup' (fun z => sumOn z X) hxB
  · exact Finset.sup'_le _ _ (fun z hz => ((hchar z).1 hz).1 X)

theorem aux_bs_compl_sum {V : Type*} [Fintype V] [DecidableEq V] (x : V → ℤ) (X : Finset V) :
    sumOn x Xᶜ = sumOn x Finset.univ - sumOn x X := by
  have : sumOn x Xᶜ + sumOn x X = sumOn x Finset.univ := Finset.sum_compl_add_sum _ _
  linarith

theorem aux_bs_sub_to_sup {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (f : Finset V → ℤ) (hf : IsSubmodular f) (h0 : f ∅ = 0)
    (hchar : ∀ x : V → ℤ, x ∈ B ↔
      (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ) :
    IsSupermodular (fun X => f Finset.univ - f Xᶜ) ∧ (fun X => f Finset.univ - f Xᶜ) ∅ = 0 ∧
      ∀ x : V → ℤ, x ∈ B ↔
        (∀ X : Finset V, (fun X => f Finset.univ - f Xᶜ) X ≤ sumOn x X) ∧
          sumOn x Finset.univ = (fun X => f Finset.univ - f Xᶜ) Finset.univ := by
  refine ⟨?_, by simp, ?_⟩
  · intro X Y
    have := hf Xᶜ Yᶜ
    simp only [Finset.compl_union, Finset.compl_inter] at *
    linarith
  · intro x
    rw [hchar]
    simp only [Finset.compl_univ, h0, sub_zero]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun X => ?_, h2⟩
      have := h1 Xᶜ; rw [aux_bs_compl_sum] at this; linarith
    · rintro ⟨h1, h2⟩
      refine ⟨fun X => ?_, h2⟩
      have := h1 Xᶜ; rw [aux_bs_compl_sum, compl_compl] at this; linarith

theorem aux_bs_sup_to_sub {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (g : Finset V → ℤ) (hg : IsSupermodular g) (h0 : g ∅ = 0)
    (hchar : ∀ x : V → ℤ, x ∈ B ↔
      (∀ X : Finset V, g X ≤ sumOn x X) ∧ sumOn x Finset.univ = g Finset.univ) :
    IsSubmodular (fun X => g Finset.univ - g Xᶜ) ∧ (fun X => g Finset.univ - g Xᶜ) ∅ = 0 ∧
      ∀ x : V → ℤ, x ∈ B ↔
        (∀ X : Finset V, sumOn x X ≤ (fun X => g Finset.univ - g Xᶜ) X) ∧
          sumOn x Finset.univ = (fun X => g Finset.univ - g Xᶜ) Finset.univ := by
  refine ⟨?_, by simp, ?_⟩
  · intro X Y
    have := hg Xᶜ Yᶜ
    simp only [Finset.compl_union, Finset.compl_inter] at *
    linarith
  · intro x
    rw [hchar]
    simp only [Finset.compl_univ, h0, sub_zero]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun X => ?_, h2⟩
      have := h1 Xᶜ; rw [aux_bs_compl_sum] at this; linarith
    · rintro ⟨h1, h2⟩
      refine ⟨fun X => ?_, h2⟩
      have := h1 Xᶜ; rw [aux_bs_compl_sum, compl_compl] at this; linarith

theorem baseSet_core {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty) :
    (IsIntegralBaseSet B ↔
      ∃ f : Finset V → ℤ, IsSubmodular f ∧ f ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ) ∧
    (IsIntegralBaseSet B ↔
      ∃ g : Finset V → ℤ, IsSupermodular g ∧ g ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ sumOn x X) ∧ sumOn x Finset.univ = g Finset.univ) ∧
    (∀ f : Finset V → ℤ, IsSubmodular f → f ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ) →
      ∀ X : Finset V, f X = B.sup' hne (fun x => sumOn x X)) ∧
    (∀ g : Finset V → ℤ, IsSupermodular g → g ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ sumOn x X) ∧ sumOn x Finset.univ = g Finset.univ) →
      ∀ X : Finset V, g X = B.inf' hne (fun x => sumOn x X)) := by
  have P1 : IsIntegralBaseSet B ↔
      ∃ f : Finset V → ℤ, IsSubmodular f ∧ f ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ := by
    constructor
    · intro hB
      refine ⟨fun X => B.sup' hne (fun z => sumOn z X), aux_bs_claimB B hB.2 hne, ?_,
        aux_bs_fwd B hne hB⟩
      simp [sumOn]
    · rintro ⟨f, hf, h0, hchar⟩
      exact aux_bs_bwd B hne f hf h0 hchar
  refine ⟨P1, ?_, fun f hf h0 hchar => aux_bs_uniq B hne f hf h0 hchar, ?_⟩
  · constructor
    · intro hB
      obtain ⟨f, hf, h0, hchar⟩ := P1.1 hB
      exact ⟨_, aux_bs_sub_to_sup B f hf h0 hchar⟩
    · rintro ⟨g, hg, h0, hchar⟩
      exact P1.2 ⟨_, aux_bs_sup_to_sub B g hg h0 hchar⟩
  · intro g hg h0 hchar X
    obtain ⟨hf, hf0, hfchar⟩ := aux_bs_sup_to_sub B g hg h0 hchar
    have hu := aux_bs_uniq B hne _ hf hf0 hfchar Xᶜ
    simp only [compl_compl] at hu
    apply le_antisymm
    · exact Finset.le_inf' _ _ (fun z hz => ((hchar z).1 hz).1 X)
    · obtain ⟨z, hzB, hz⟩ := Finset.exists_mem_eq_sup' hne (fun x => sumOn x Xᶜ)
      rw [hz, aux_bs_compl_sum, ((hchar z).1 hzB).2] at hu
      have : B.inf' hne (fun x => sumOn x X) ≤ sumOn z X := Finset.inf'_le _ hzB
      linarith

end SteinitzExchange.LocalSupermod

open SteinitzExchange.LocalSupermod


theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty) :
    (IsIntegralBaseSet B ↔
      ∃ f : Finset V → ℤ, IsSubmodular f ∧ f ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ) ∧
    (IsIntegralBaseSet B ↔
      ∃ g : Finset V → ℤ, IsSupermodular g ∧ g ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ sumOn x X) ∧ sumOn x Finset.univ = g Finset.univ) ∧
    (∀ f : Finset V → ℤ, IsSubmodular f → f ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ) →
      ∀ X : Finset V, f X = B.sup' hne (fun x => sumOn x X)) ∧
    (∀ g : Finset V → ℤ, IsSupermodular g → g ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ sumOn x X) ∧ sumOn x Finset.univ = g Finset.univ) →
      ∀ X : Finset V, g X = B.inf' hne (fun x => sumOn x X)) := by
  exact baseSet_core B hne
