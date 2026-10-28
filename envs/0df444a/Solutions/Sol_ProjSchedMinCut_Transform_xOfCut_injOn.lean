-- Prove2me | solution 1 for ProjSchedMinCut.Transform.xOfCut_injOn
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:49:03.443868+00:00
-- url     : https://prove2.me/submissions/3bc43939-7efd-4e41-ac00-de90b6b0ed0d

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_ProjSchedMinCut_Transform_Setting

open ProjSchedMinCut.Transform
open ProjSchedMinCut.Transform.Instance
open scoped ENNReal

private lemma earliest_nonneg_and_le_latest {n : ℕ} (I : Instance n)
    (hfeas : ∃ S, I.Feasible S) (j : Fin (n + 1)) :
    0 ≤ I.earliest j ∧ I.earliest j ≤ I.latest j := by
  obtain ⟨S, hS⟩ := hfeas
  have hbddBelow : BddBelow (I.startTimes j) := by
    refine ⟨0, ?_⟩
    rintro t ⟨S', hS', rfl⟩
    exact (hS'.2 j).1
  have hbddAbove : BddAbove (I.startTimes j) := by
    refine ⟨I.T, ?_⟩
    rintro t ⟨S', hS', rfl⟩
    have h1 := (hS'.2 j).2
    have h2 : (0 : ℤ) ≤ I.p j := Nat.cast_nonneg _
    omega
  have hmem : S j ∈ I.startTimes j := ⟨S, hS, rfl⟩
  have he : I.earliest j ≤ S j := csInf_le hbddBelow hmem
  have hl : S j ≤ I.latest j := le_csSup hbddAbove hmem
  have h0 : 0 ≤ I.earliest j := by
    refine le_csInf ⟨S j, hmem⟩ ?_
    rintro t ⟨S', hS', rfl⟩
    exact (hS'.2 j).1
  exact ⟨h0, le_trans he hl⟩

private lemma not_inCut_of_cap_top {n : ℕ} (I : Instance n) {X : Set (Node n)}
    (hcap : I.cutCap X < ⊤) {α : Arc n} (hα : α ∈ I.A) (htop : I.cap α = ⊤) :
    ¬ I.InCut X α := by
  classical
  intro hin
  have hmem : α ∈ I.A.filter (fun β => I.InCut X β) :=
    Finset.mem_filter.mpr ⟨hα, hin⟩
  have hle : I.cap α ≤ I.cutCap X :=
    Finset.single_le_sum (fun _ _ => zero_le) hmem
  rw [htop] at hle
  exact not_top_lt (lt_of_le_of_lt hle hcap)

private lemma assign_mem_A_iff {n : ℕ} (I : Instance n) (j : Fin (n + 1)) (t : ℤ) :
    Arc.assign j t ∈ I.A ↔ I.earliest j ≤ t ∧ t ≤ I.latest j := by
  unfold Instance.A
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_Icc, Finset.mem_filter, Arc.assign.injEq,
    reduceCtorEq, and_false, exists_false, or_false]
  constructor
  · rintro ⟨j', t', ht', rfl, rfl⟩
    exact ht'
  · intro ht
    exact ⟨j, t, ht, rfl, rfl⟩

private lemma src_mem_A {n : ℕ} (I : Instance n) (j : Fin (n + 1)) :
    Arc.src j ∈ I.A := by
  unfold Instance.A
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_univ j)))

private lemma snk_mem_A {n : ℕ} (I : Instance n) (j : Fin (n + 1)) :
    Arc.snk j ∈ I.A := by
  unfold Instance.A
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))

private lemma node_v_mem_V {n : ℕ} (I : Instance n) (j : Fin (n + 1)) (t : ℤ)
    (he : I.earliest j ≤ t) (hl : t ≤ I.latest j + 1) :
    Node.v j t ∈ I.V := by
  exact Or.inr ⟨j, t, rfl, he, hl⟩

private lemma propagate_mem_X {n : ℕ} (I : Instance n) {X : Set (Node n)}
    (j : Fin (n + 1)) (tstar : ℤ)
    (hstep : ∀ s, I.earliest j ≤ s → s ≤ I.latest j → s ≠ tstar →
      Node.v j s ∈ X → Node.v j (s + 1) ∈ X)
    (a : ℤ) (k : ℕ) (ha : Node.v j a ∈ X) (hea : I.earliest j ≤ a)
    (hal : a + (k : ℤ) ≤ I.latest j + 1)
    (hne : ∀ s, a ≤ s → s < a + (k : ℤ) → s ≠ tstar) :
    Node.v j (a + (k : ℤ)) ∈ X := by
  induction k with
  | zero =>
    simpa using ha
  | succ k ih =>
    have hal' : a + (k : ℤ) ≤ I.latest j + 1 := by omega
    have hne' : ∀ s, a ≤ s → s < a + (k : ℤ) → s ≠ tstar := by
      intro s hs1 hs2
      exact hne s hs1 (by omega)
    have hk_mem : Node.v j (a + (k : ℤ)) ∈ X := ih hal' hne'
    have hstep_k := hstep (a + (k : ℤ)) (by omega) (by omega)
      (hne (a + (k : ℤ)) (by omega) (by omega)) hk_mem
    have heq : a + (k : ℤ) + 1 = a + ((k + 1 : ℕ) : ℤ) := by omega
    rwa [heq] at hstep_k

private lemma node_v_mem_X_iff {n : ℕ} (I : Instance n) (hfeas : ∃ S, I.Feasible S)
    {X : Set (Node n)} (hncut : I.IsNCut X) (hcap : I.cutCap X < ⊤)
    (j : Fin (n + 1)) {tstar : ℤ}
    (htstar : Arc.assign j tstar ∈ I.A ∧ I.InCut X (Arc.assign j tstar))
    (huniq : ∀ s : ℤ, (Arc.assign j s ∈ I.A ∧ I.InCut X (Arc.assign j s)) → s = tstar)
    {t : ℤ} (he : I.earliest j ≤ t) (hl : t ≤ I.latest j + 1) :
    Node.v j t ∈ X ↔ t ≤ tstar := by
  have ⟨_, hel⟩ := earliest_nonneg_and_le_latest I hfeas j
  have ⟨he_tstar, hl_tstar⟩ := (assign_mem_A_iff I j tstar).mp htstar.1
  have hsrc_not : ¬ I.InCut X (Arc.src j) :=
    not_inCut_of_cap_top I hcap (src_mem_A I j) rfl
  have hearliest_mem : Node.v j (I.earliest j) ∈ X := by
    by_contra hnot
    apply hsrc_not
    exact ⟨hncut.1.2.1, node_v_mem_V I j (I.earliest j) le_rfl (by omega), hnot⟩
  have hsnk_not : ¬ I.InCut X (Arc.snk j) :=
    not_inCut_of_cap_top I hcap (snk_mem_A I j) rfl
  have hlatest_not_mem : Node.v j (I.latest j + 1) ∉ X := by
    intro hmem
    apply hsnk_not
    exact ⟨hmem, Or.inl (Or.inr rfl), hncut.1.2.2⟩
  have hstep : ∀ s, I.earliest j ≤ s → s ≤ I.latest j → s ≠ tstar →
      Node.v j s ∈ X → Node.v j (s + 1) ∈ X := by
    intro s hes hls hne hs_mem
    by_contra hs1_not
    have hA : Arc.assign j s ∈ I.A := (assign_mem_A_iff I j s).mpr ⟨hes, hls⟩
    have hin : I.InCut X (Arc.assign j s) :=
      ⟨hs_mem, node_v_mem_V I j (s + 1) (by omega) (by omega), hs1_not⟩
    exact hne (huniq s ⟨hA, hin⟩)
  constructor
  · intro ht_mem
    by_contra hgt
    have hge : tstar + 1 ≤ t := by omega
    let k : ℕ := (I.latest j + 1 - t).toNat
    have hk_eq : t + (k : ℤ) = I.latest j + 1 := by omega
    have hmem_end : Node.v j (t + (k : ℤ)) ∈ X :=
      propagate_mem_X I j tstar hstep t k ht_mem he (by omega) (by
        intro s hs1 _
        omega)
    rw [hk_eq] at hmem_end
    exact hlatest_not_mem hmem_end
  · intro hle
    let k : ℕ := (t - I.earliest j).toNat
    have hk_eq : I.earliest j + (k : ℤ) = t := by omega
    have hmem_t : Node.v j (I.earliest j + (k : ℤ)) ∈ X :=
      propagate_mem_X I j tstar hstep (I.earliest j) k hearliest_mem le_rfl (by omega) (by
        intro s _ hs2
        omega)
    rwa [hk_eq] at hmem_t

theorem solution {n : ℕ} (I : Instance n) (_hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    Set.InjOn I.xOfCut {X | I.IsNCut X ∧ I.cutCap X < ⊤} := by
  intro X₁ ⟨hncut₁, hcap₁⟩ X₂ ⟨hncut₂, hcap₂⟩ hx
  have hv_iff : ∀ j (t : ℤ), I.earliest j ≤ t → t ≤ I.latest j + 1 →
      (Node.v j t ∈ X₁ ↔ Node.v j t ∈ X₂) := by
    intro j t he hl
    obtain ⟨t₁, ht₁, huniq₁⟩ := hncut₁.2 j
    obtain ⟨t₂, ht₂, huniq₂⟩ := hncut₂.2 j
    have ⟨h0_e, _⟩ := earliest_nonneg_and_le_latest I hfeas j
    have ⟨he_t₁, _⟩ := (assign_mem_A_iff I j t₁).mp ht₁.1
    have ht₁_nonneg : 0 ≤ t₁ := le_trans h0_e he_t₁
    have ht₁_cast : (t₁.toNat : ℤ) = t₁ := Int.toNat_of_nonneg ht₁_nonneg
    have hx₁ : I.xOfCut X₁ j t₁.toNat = 1 := by
      unfold Instance.xOfCut
      rw [ht₁_cast, if_pos ht₁]
    have hx₂ : I.xOfCut X₂ j t₁.toNat = 1 := by
      rw [← hx]
      exact hx₁
    have ht₁_in_X₂ : Arc.assign j t₁ ∈ I.A ∧ I.InCut X₂ (Arc.assign j t₁) := by
      unfold Instance.xOfCut at hx₂
      rw [ht₁_cast] at hx₂
      split_ifs at hx₂ with h
      · exact h
      · exfalso; omega
    have ht₁_eq_t₂ : t₁ = t₂ := huniq₂ t₁ ht₁_in_X₂
    rw [node_v_mem_X_iff I hfeas hncut₁ hcap₁ j ht₁ huniq₁ he hl,
        node_v_mem_X_iff I hfeas hncut₂ hcap₂ j ht₂ huniq₂ he hl,
        ht₁_eq_t₂]
  ext u
  constructor
  · intro hu₁
    rcases hncut₁.1.1 hu₁ with (rfl | rfl) | ⟨j, t, rfl, he, hl⟩
    · exact hncut₂.1.2.1
    · exact absurd hu₁ hncut₁.1.2.2
    · exact (hv_iff j t he hl).mp hu₁
  · intro hu₂
    rcases hncut₂.1.1 hu₂ with (rfl | rfl) | ⟨j, t, rfl, he, hl⟩
    · exact hncut₁.1.2.1
    · exact absurd hu₂ hncut₂.1.2.2
    · exact (hv_iff j t he hl).mpr hu₂
