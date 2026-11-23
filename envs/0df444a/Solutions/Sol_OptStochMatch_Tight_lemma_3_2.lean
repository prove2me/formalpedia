-- Prove2me | solution 1 for OptStochMatch.Tight.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:49:32.463628+00:00
-- url     : https://prove2.me/submissions/414500d6-b14a-489e-905b-e24678d63adb

import Definitions.Def_OptStochMatch_Tight_Basic
import Theorems.Thm_OptStochMatch_Tight_lemma_2_3

namespace AuxLemma32

open Set OptStochMatch.Tight
open scoped NNReal BigOperators

lemma coverRate_empty {m : ℕ} (lam : Ty m → ℝ≥0) : coverRate lam ∅ = 0 := by
  simp [coverRate]

lemma coverRate_submodular {m : ℕ} (lam : Ty m → ℝ≥0) (A B : Finset (Fin m)) :
    coverRate lam (A ∪ B) + coverRate lam (A ∩ B) ≤ coverRate lam A + coverRate lam B := by
  unfold coverRate
  simp_rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  have hnn : 0 ≤ (lam S : ℝ) := NNReal.coe_nonneg (lam S)
  by_cases hA : (S ∩ A).Nonempty <;> by_cases hB : (S ∩ B).Nonempty
  · rw [if_pos hA, if_pos hB]
    split_ifs <;> linarith
  · have hni : ¬ (S ∩ (A ∩ B)).Nonempty := fun ⟨i, hi⟩ =>
      hB ⟨i, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hi).2).2⟩⟩
    rw [if_pos hA, if_neg hB, if_neg hni]
    split_ifs <;> linarith
  · have hni : ¬ (S ∩ (A ∩ B)).Nonempty := fun ⟨i, hi⟩ =>
      hA ⟨i, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hi).2).1⟩⟩
    rw [if_neg hA, if_pos hB, if_neg hni]
    split_ifs <;> linarith
  · have hnu : ¬ (S ∩ (A ∪ B)).Nonempty := by
      rintro ⟨i, hi⟩
      obtain ⟨hiS, hiAB⟩ := Finset.mem_inter.mp hi
      rcases Finset.mem_union.mp hiAB with hiA | hiB
      · exact hA ⟨i, Finset.mem_inter.mpr ⟨hiS, hiA⟩⟩
      · exact hB ⟨i, Finset.mem_inter.mpr ⟨hiS, hiB⟩⟩
    have hni : ¬ (S ∩ (A ∩ B)).Nonempty := fun ⟨i, hi⟩ =>
      hA ⟨i, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hi).2).1⟩⟩
    rw [if_neg hA, if_neg hB, if_neg hnu, if_neg hni]

lemma Plam_compact {m : ℕ} (lam : Ty m → ℝ≥0) : IsCompact (Plam lam) := by
  have h1 : IsClosed {x : Fin m → ℝ | ∀ i, 0 ≤ x i} := by
    have heq : {x : Fin m → ℝ | ∀ i, 0 ≤ x i} = ⋂ i : Fin m, {x | 0 ≤ x i} := by ext x; simp
    rw [heq]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {x : Fin m → ℝ | ∀ A : Finset (Fin m), ∑ i ∈ A, x i ≤ coverRate lam A} := by
    have heq : {x : Fin m → ℝ | ∀ A : Finset (Fin m), ∑ i ∈ A, x i ≤ coverRate lam A} =
        ⋂ A : Finset (Fin m), {x | ∑ i ∈ A, x i ≤ coverRate lam A} := by ext x; simp
    rw [heq]
    exact isClosed_iInter fun A =>
      isClosed_le (continuous_finsetSum A fun i _ => continuous_apply i) continuous_const
  refine (isCompact_Icc : IsCompact (Icc (0 : Fin m → ℝ) (fun i => coverRate lam {i}))).of_isClosed_subset
    (h1.inter h2) ?_
  intro x hx
  refine ⟨hx.1, fun i => ?_⟩
  simpa using hx.2 {i}

lemma zero_mem_Plam {m : ℕ} (lam : Ty m → ℝ≥0) : (0 : Fin m → ℝ) ∈ Plam lam :=
  ⟨fun _ => le_rfl, fun A => by simp [coverRate]; exact Finset.sum_nonneg fun S _ => NNReal.coe_nonneg _⟩

lemma finite_pos_lb {β : Type*} (S : Finset β) (b : β → ℝ) (hb : ∀ j ∈ S, 0 < b j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j ∈ S, ε ≤ b j := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert j S _ ih =>
    obtain ⟨ε, hε, hbound⟩ := ih fun k hk => hb k (Finset.mem_insert_of_mem hk)
    refine ⟨min (b j) ε, lt_min (hb j (Finset.mem_insert_self _ _)) hε, fun k hk => ?_⟩
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound k hk)

lemma sum_update_add {m : ℕ} (x : Fin m → ℝ) (i : Fin m) (ε : ℝ) (A : Finset (Fin m)) :
    ∑ j ∈ A, Function.update x i (x i + ε) j =
      (∑ j ∈ A, x j) + if i ∈ A then ε else 0 := by
  have hy : Function.update x i (x i + ε) = fun j => x j + if j = i then ε else 0 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [hy, Finset.sum_add_distrib]
  simp

lemma optExp_eq_sub_maxDefExp {m : ℕ} (lam : Ty m → ℝ≥0) (z : Fin m → ℝ) (hz : ∀ i, 0 ≤ z i) :
    optExp lam z = ∑ i, z i - maxDefExp lam z := by
  let Feas : Set (Fin m → ℝ) := {x | (∀ i, 0 ≤ x i ∧ x i ≤ z i) ∧ x ∈ Plam lam}
  have hFeas_compact : IsCompact Feas := by
    have hclosed_box : IsClosed {x : Fin m → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ z i} := by
      have heq : {x : Fin m → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ z i} =
          ⋂ i : Fin m, {x | 0 ≤ x i} ∩ {x | x i ≤ z i} := by ext x; simp
      rw [heq]
      exact isClosed_iInter fun i =>
        (isClosed_le continuous_const (continuous_apply i)).inter
          (isClosed_le (continuous_apply i) continuous_const)
    exact (Plam_compact lam).of_isClosed_subset
      (hclosed_box.inter (Plam_compact lam).isClosed) fun x hx => hx.2
  have h0_mem : (0 : Fin m → ℝ) ∈ Feas := ⟨fun i => ⟨le_rfl, hz i⟩, zero_mem_Plam lam⟩
  have hobj_cont : Continuous (fun x : Fin m → ℝ => ∑ i, x i) :=
    continuous_finsetSum _ fun i _ => continuous_apply i
  obtain ⟨x, hxF, hmax_on⟩ := hFeas_compact.exists_isMaxOn ⟨0, h0_mem⟩ hobj_cont.continuousOn
  have hopt_eq : optExp lam z = ∑ i, x i := by
    unfold optExp optExpP
    have hset : {v : ℝ | ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i ∧ y i ≤ z i) ∧ y ∈ Plam lam ∧ v = ∑ i, y i} =
        (fun y : Fin m → ℝ => ∑ i, y i) '' Feas := by
      ext v; simp [Feas, eq_comm, and_assoc]
    rw [hset]
    refine IsGreatest.csSup_eq ⟨⟨x, hxF, rfl⟩, ?_⟩
    rintro v ⟨y, hyF, rfl⟩
    exact hmax_on hyF
  have hxP : x ∈ Plam lam := hxF.2
  have hxz : ∀ i, x i ≤ z i := fun i => (hxF.1 i).2
  have hmax : ∀ y ∈ Plam lam, (∀ i, y i ≤ z i) → ∑ i, y i ≤ ∑ i, x i :=
    fun y hyP hyz => hmax_on ⟨fun i => ⟨hyP.1 i, hyz i⟩, hyP⟩
  have htight_ex : ∀ i, x i < z i → ∃ A : Finset (Fin m), i ∈ A ∧ ∑ j ∈ A, x j = coverRate lam A := by
    intro i hi
    by_contra hnone
    let b : Finset (Fin m) → ℝ := fun A => if i ∈ A then coverRate lam A - ∑ j ∈ A, x j else 1
    have hb : ∀ A ∈ (Finset.univ : Finset (Finset (Fin m))), 0 < b A := by
      intro A _
      dsimp [b]
      split_ifs with hiA
      · refine sub_pos.mpr (lt_of_le_of_ne (hxP.2 A) fun he => hnone ⟨A, hiA, he⟩)
      · exact zero_lt_one
    obtain ⟨δ, hδ, hbound⟩ := finite_pos_lb Finset.univ b hb
    let ε := min δ (z i - x i)
    have hε : 0 < ε := lt_min hδ (sub_pos.mpr hi)
    let y := Function.update x i (x i + ε)
    have hyP : y ∈ Plam lam := by
      refine ⟨fun j => ?_, fun A => ?_⟩
      · by_cases hj : j = i
        · subst hj; simpa [y] using add_nonneg (hxP.1 j) hε.le
        · simpa [y, hj] using hxP.1 j
      · rw [sum_update_add]
        by_cases hiA : i ∈ A
        · rw [if_pos hiA]
          have he : ε ≤ coverRate lam A - ∑ j ∈ A, x j :=
            (min_le_left _ _).trans (by simpa [b, hiA] using hbound A (Finset.mem_univ A))
          linarith
        · rw [if_neg hiA, add_zero]
          exact hxP.2 A
    have hyz : ∀ j, y j ≤ z j := by
      intro j
      by_cases hj : j = i
      · subst hj; simp only [y, Function.update_self]; linarith [min_le_right δ (z j - x j)]
      · simpa [y, hj] using hxz j
    have hm := hmax y hyP hyz
    rw [sum_update_add, if_pos (Finset.mem_univ i)] at hm
    linarith
  have htight_union : ∀ {A B : Finset (Fin m)},
      ∑ j ∈ A, x j = coverRate lam A → ∑ j ∈ B, x j = coverRate lam B →
      ∑ j ∈ A ∪ B, x j = coverRate lam (A ∪ B) := by
    intro A B hA hB
    have hsub := coverRate_submodular lam A B
    have hu := hxP.2 (A ∪ B)
    have hi := hxP.2 (A ∩ B)
    have hm := Finset.sum_union_inter (f := x) (s₁ := A) (s₂ := B)
    linarith
  let TF : Finset (Finset (Fin m)) := Finset.univ.filter fun A => ∑ j ∈ A, x j = coverRate lam A
  let Astar : Finset (Fin m) := TF.biUnion id
  have hAstar_tight : ∑ j ∈ Astar, x j = coverRate lam Astar := by
    suffices hbi : ∀ G : Finset (Finset (Fin m)),
        (∀ A ∈ G, ∑ j ∈ A, x j = coverRate lam A) →
        ∑ j ∈ G.biUnion id, x j = coverRate lam (G.biUnion id) from
      hbi TF fun A hA => (Finset.mem_filter.mp hA).2
    intro G
    induction G using Finset.induction_on with
    | empty => intro _; simp [coverRate_empty]
    | @insert A F _ ih =>
      intro hG
      rw [Finset.biUnion_insert]
      exact htight_union (hG A (Finset.mem_insert_self _ _))
        (ih fun B hB => hG B (Finset.mem_insert_of_mem hB))
  have hAstar_compl : ∀ i, i ∉ Astar → x i = z i := by
    intro i hi
    refine le_antisymm (hxz i) ?_
    by_contra hlt
    obtain ⟨A, hiA, hA⟩ := htight_ex i (lt_of_not_ge hlt)
    exact hi (Finset.mem_biUnion.mpr ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ A, hA⟩, hiA⟩)
  have hupper : ∀ A : Finset (Fin m), ∑ i, x i + defExp lam z A ≤ ∑ i, z i := by
    intro A
    have hsx := Finset.sum_add_sum_compl A x
    have hsz := Finset.sum_add_sum_compl A z
    have hA := hxP.2 A
    have hc : ∑ i ∈ Aᶜ, x i ≤ ∑ i ∈ Aᶜ, z i := Finset.sum_le_sum fun i _ => hxz i
    unfold defExp
    linarith
  have hmax_le : maxDefExp lam z ≤ ∑ i, z i - ∑ i, x i :=
    Finset.sup'_le Finset.univ_nonempty _ fun A _ => by linarith [hupper A]
  have hle_max : ∑ i, z i - ∑ i, x i ≤ maxDefExp lam z := by
    have hc : ∑ i ∈ Astarᶜ, x i = ∑ i ∈ Astarᶜ, z i :=
      Finset.sum_congr rfl fun i hi => hAstar_compl i (Finset.mem_compl.mp hi)
    have hsx := Finset.sum_add_sum_compl Astar x
    have hsz := Finset.sum_add_sum_compl Astar z
    have hdef : defExp lam z Astar ≤ maxDefExp lam z :=
      Finset.le_sup' (defExp lam z) (Finset.mem_univ Astar)
    unfold defExp at hdef
    linarith
  rw [hopt_eq]
  linarith

end AuxLemma32

open scoped NNReal BigOperators
open OptStochMatch.Tight AuxLemma32

theorem solution {m : ℕ} (lam : Ty m → ℝ≥0) :
    (∀ N : Ty m → ℕ, optPois N = (m : ℝ) - (maxDefPois N : ℝ)) ∧
    (∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) → optExp lam z = ∑ i, z i - maxDefExp lam z) := by
  refine ⟨fun N => ?_, fun z hz => optExp_eq_sub_maxDefExp lam z hz⟩
  let lamN : Ty m → ℝ≥0 := fun S => (N S : ℝ≥0)
  let z₁ : Fin m → ℝ := fun _ => 1
  have hset_eq : {v : ℝ | ∃ x : Fin m → Ty m → ℝ,
      (∀ i S, 0 ≤ x i S ∧ x i S ≤ 1) ∧
      (∀ S : Ty m, ∑ i ∈ S, x i S ≤ (N S : ℝ)) ∧
      (∀ i : Fin m, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), x i S ≤ 1) ∧
      v = ∑ S : Ty m, ∑ i ∈ S, x i S} =
    {v : ℝ | ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i ∧ y i ≤ z₁ i) ∧ y ∈ Plam lamN ∧ v = ∑ i, y i} := by
    ext v
    constructor
    · rintro ⟨x, hx01, hcap, hxi, rfl⟩
      let y : Fin m → ℝ := fun i => ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), x i S
      have hy0 : ∀ i, 0 ≤ y i := fun i => Finset.sum_nonneg fun S _ => (hx01 i S).1
      have hyP : y ∈ Plam lamN :=
        (lemma_2_3 lamN y hy0).mpr ⟨x, fun i S => (hx01 i S).1,
          fun S => by simpa [lamN] using hcap S, fun _ => rfl⟩
      have hswap : ∑ S : Ty m, ∑ i ∈ S, x i S = ∑ i : Fin m, y i := by
        dsimp [y]
        trans ∑ S : Ty m, ∑ i : Fin m, if i ∈ S then x i S else 0
        · refine Finset.sum_congr rfl fun S _ => ?_
          have hite := Finset.sum_ite_mem (Finset.univ : Finset (Fin m)) S (fun i => x i S)
          rw [Finset.univ_inter] at hite
          exact hite.symm
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_filter]
      exact ⟨y, fun i => ⟨hy0 i, hxi i⟩, hyP, hswap⟩
    · rintro ⟨y, hy01, hyP, rfl⟩
      obtain ⟨F, hF_nn, hF_cap, hF_sum⟩ := (lemma_2_3 lamN y fun i => (hy01 i).1).mp hyP
      let x : Fin m → Ty m → ℝ := fun i S => if i ∈ S then F i S else 0
      refine ⟨x, ?_, ?_, ?_, ?_⟩
      · intro i S
        dsimp [x]
        by_cases hiS : i ∈ S
        · rw [if_pos hiS]
          refine ⟨hF_nn i S, ?_⟩
          have hle : F i S ≤ y i := by
            rw [← hF_sum i]
            exact Finset.single_le_sum (fun T _ => hF_nn i T)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hiS⟩)
          exact hle.trans (hy01 i).2
        · rw [if_neg hiS]; exact ⟨le_rfl, zero_le_one⟩
      · intro S
        have hS : ∑ i ∈ S, x i S = ∑ i ∈ S, F i S :=
          Finset.sum_congr rfl fun i hiS => by simp [x, hiS]
        rw [hS]
        simpa [lamN] using hF_cap S
      · intro i
        have hi : ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), x i S = y i := by
          rw [← hF_sum i]
          exact Finset.sum_congr rfl fun S hS => by simp [x, (Finset.mem_filter.mp hS).2]
        rw [hi]
        exact (hy01 i).2
      · symm
        trans ∑ S : Ty m, ∑ i : Fin m, if i ∈ S then x i S else 0
        · refine Finset.sum_congr rfl fun S _ => ?_
          have hite := Finset.sum_ite_mem (Finset.univ : Finset (Fin m)) S (fun i => x i S)
          rw [Finset.univ_inter] at hite
          exact hite.symm
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter, ← hF_sum i]
        exact Finset.sum_congr rfl fun S hS => by simp [x, (Finset.mem_filter.mp hS).2]
  have hopt : optPois N = optExp lamN z₁ := by
    unfold optPois optExp optExpP
    rw [hset_eq]
  rw [hopt, optExp_eq_sub_maxDefExp lamN z₁ (fun _ => zero_le_one)]
  have hsum1 : ∑ i : Fin m, z₁ i = (m : ℝ) := by simp [z₁]
  have hdef_eq : ∀ A : Finset (Fin m), defExp lamN z₁ A = (defPois N A : ℝ) := by
    intro A
    unfold defExp defPois coverRate coverCount
    simp [z₁, lamN]
  have hmax_eq : maxDefExp lamN z₁ = (maxDefPois N : ℝ) := by
    unfold maxDefExp maxDefPois
    apply le_antisymm
    · refine Finset.sup'_le Finset.univ_nonempty _ fun A _ => ?_
      rw [hdef_eq A]
      exact Int.cast_le.mpr (Finset.le_sup' (defPois N) (Finset.mem_univ A))
    · obtain ⟨A, hA, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (defPois N)
      rw [heq, ← hdef_eq A]
      exact Finset.le_sup' (defExp lamN z₁) hA
  rw [hsum1, hmax_eq]
