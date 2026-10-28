-- Prove2me | solution 1 for ProjSchedMinCut.Transform.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:56:47.699016+00:00
-- url     : https://prove2.me/submissions/c0bd7f35-9654-4916-b97b-376dc0ab2a5e

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

private lemma earliest_latest_bounds {n : ℕ} (I : Instance n)
    (hfeas : ∃ S, I.Feasible S) (j : Fin (n + 1)) :
    0 ≤ I.earliest j ∧ I.earliest j ≤ I.latest j ∧ I.latest j ≤ I.T := by
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
  have hT : I.latest j ≤ I.T := by
    refine csSup_le ⟨S j, hmem⟩ ?_
    rintro t ⟨S', hS', rfl⟩
    have h1 := (hS'.2 j).2
    have h2 : (0 : ℤ) ≤ I.p j := Nat.cast_nonneg _
    omega
  exact ⟨h0, le_trans he hl, hT⟩

private lemma earliest_and_latest_lag {n : ℕ} (I : Instance n)
    (hfeas : ∃ S, I.Feasible S) {ij : Fin (n + 1) × Fin (n + 1)} (hij : ij ∈ I.L) :
    I.earliest ij.1 + I.d ij.1 ij.2 ≤ I.earliest ij.2 ∧
      I.latest ij.1 + I.d ij.1 ij.2 ≤ I.latest ij.2 := by
  obtain ⟨S, hS⟩ := hfeas
  have hbddBelow1 : BddBelow (I.startTimes ij.1) := by
    refine ⟨0, ?_⟩
    rintro t ⟨S', hS', rfl⟩
    exact (hS'.2 ij.1).1
  have hbddAbove2 : BddAbove (I.startTimes ij.2) := by
    refine ⟨I.T, ?_⟩
    rintro t ⟨S', hS', rfl⟩
    have h1 := (hS'.2 ij.2).2
    have h2 : (0 : ℤ) ≤ I.p ij.2 := Nat.cast_nonneg _
    omega
  have hne1 : (I.startTimes ij.1).Nonempty := ⟨S ij.1, S, hS, rfl⟩
  have hne2 : (I.startTimes ij.2).Nonempty := ⟨S ij.2, S, hS, rfl⟩
  constructor
  · refine le_csInf hne2 ?_
    rintro t ⟨S', hS', rfl⟩
    have h1 : I.earliest ij.1 ≤ S' ij.1 :=
      csInf_le hbddBelow1 (show S' ij.1 ∈ I.startTimes ij.1 from ⟨S', hS', rfl⟩)
    have h2 := hS'.1 ij hij
    omega
  · have hle : I.latest ij.1 ≤ I.latest ij.2 - I.d ij.1 ij.2 := by
      refine csSup_le hne1 ?_
      rintro t ⟨S', hS', rfl⟩
      have h1 : S' ij.2 ≤ I.latest ij.2 :=
        le_csSup hbddAbove2 (show S' ij.2 ∈ I.startTimes ij.2 from ⟨S', hS', rfl⟩)
      have h2 := hS'.1 ij hij
      omega
    omega

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

private lemma temporal_mem_A {n : ℕ} (I : Instance n) {ij : Fin (n + 1) × Fin (n + 1)}
    (hij : ij ∈ I.L) {t : ℤ}
    (he1 : I.earliest ij.1 + 1 ≤ t) (hl1 : t ≤ I.latest ij.1)
    (he2 : I.earliest ij.2 + 1 ≤ t + I.d ij.1 ij.2) (hl2 : t + I.d ij.1 ij.2 ≤ I.latest ij.2) :
    Arc.temporal ij t ∈ I.A := by
  unfold Instance.A
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  rw [Finset.mem_biUnion]
  refine ⟨ij, hij, Finset.mem_image.mpr ⟨t, ?_, rfl⟩⟩
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨he1, hl1⟩, he2, hl2⟩

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
  have ⟨_, hel, _⟩ := earliest_latest_bounds I hfeas j
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

private lemma finset_sum_ite_eq {α : Type*} [DecidableEq α] (A : Finset α) (a : α) (c : α → ℝ) :
    (∑ s ∈ A, (if s = a then c s else 0)) = if a ∈ A then c a else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert b s hbs ih =>
    rw [Finset.sum_insert hbs, ih]
    by_cases hba : b = a
    · subst hba
      simp [hbs]
    · have hab : a ≠ b := Ne.symm hba
      simp [hba, hab]

private lemma finset_sum_ite_eq_int (A : Finset ℕ) (a : ℕ) :
    (∑ s ∈ A, (if s = a then (1 : ℤ) else 0)) = if a ∈ A then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert b s hbs ih =>
    rw [Finset.sum_insert hbs, ih]
    by_cases hba : b = a
    · subst hba
      simp [hbs]
    · have hab : a ≠ b := Ne.symm hba
      simp [hba, hab]

private lemma ofReal_sum_of_nonneg {α : Type*} {S : Finset α} {f : α → ℝ}
    (hf : ∀ a ∈ S, 0 ≤ f a) :
    ENNReal.ofReal (∑ a ∈ S, f a) = ∑ a ∈ S, ENNReal.ofReal (f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert b s hbs ih =>
    have hb : 0 ≤ f b := hf b (Finset.mem_insert_self b s)
    have hs : ∀ a ∈ s, 0 ≤ f a := fun a ha => hf a (Finset.mem_insert_of_mem ha)
    rw [Finset.sum_insert hbs, Finset.sum_insert hbs,
        ENNReal.ofReal_add hb (Finset.sum_nonneg hs), ih hs]

theorem solution {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    ∀ X, I.IsNCut X → I.cutCap X < ⊤ →
      I.IPFeasible (I.xOfCut X) ∧ I.cutCap X = ENNReal.ofReal (I.cost (I.xOfCut X)) := by
  classical
  intro X hncut hcap
  choose tstar htstar huniq using hncut.2
  have htstar_bounds : ∀ j, I.earliest j ≤ tstar j ∧ tstar j ≤ I.latest j :=
    fun j => (assign_mem_A_iff I j (tstar j)).mp (htstar j).1
  have htstar_nonneg : ∀ j, 0 ≤ tstar j := by
    intro j
    have ⟨h0, _, _⟩ := earliest_latest_bounds I hfeas j
    have ⟨he, _⟩ := htstar_bounds j
    omega
  have htstar_le_T : ∀ j, tstar j ≤ I.T := by
    intro j
    have ⟨_, _, hT⟩ := earliest_latest_bounds I hfeas j
    have ⟨_, hl⟩ := htstar_bounds j
    omega
  have hx_eq : ∀ j (t : ℕ), I.xOfCut X j t = if t = (tstar j).toNat then 1 else 0 := by
    intro j t
    unfold Instance.xOfCut
    have hiff : (Arc.assign j (t : ℤ) ∈ I.A ∧ I.InCut X (Arc.assign j (t : ℤ))) ↔
        t = (tstar j).toNat := by
      constructor
      · intro h
        have heq : (t : ℤ) = tstar j := huniq j (t : ℤ) h
        omega
      · rintro rfl
        have hcast : ((tstar j).toNat : ℤ) = tstar j := Int.toNat_of_nonneg (htstar_nonneg j)
        rw [hcast]
        exact htstar j
    by_cases h : t = (tstar j).toNat
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (mt hiff.mp h), if_neg h]
  have htstar_lag : ∀ ij ∈ I.L, tstar ij.1 + I.d ij.1 ij.2 ≤ tstar ij.2 := by
    intro ij hij
    by_contra hnot
    have ⟨helag, hllag⟩ := earliest_and_latest_lag I hfeas hij
    have ⟨he1, hl1⟩ := htstar_bounds ij.1
    have ⟨he2, hl2⟩ := htstar_bounds ij.2
    let s : ℤ := tstar ij.2 + 1 - I.d ij.1 ij.2
    have hs_mem_A : Arc.temporal ij s ∈ I.A :=
      temporal_mem_A I hij (by omega) (by omega) (by omega) (by omega)
    have hnot_in : ¬ I.InCut X (Arc.temporal ij s) :=
      not_inCut_of_cap_top I hcap hs_mem_A rfl
    apply hnot_in
    dsimp only [Instance.InCut, Instance.tail, Instance.head]
    have hs_in_X : Node.v ij.1 s ∈ X :=
      (node_v_mem_X_iff I hfeas hncut hcap ij.1 (htstar ij.1) (huniq ij.1)
        (by omega) (by omega)).mpr (by omega)
    have hs_head_eq : s + I.d ij.1 ij.2 = tstar ij.2 + 1 := by omega
    rw [hs_head_eq]
    exact ⟨hs_in_X, (htstar ij.2).2.2⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j
    simp_rw [hx_eq j]
    rw [finset_sum_ite_eq_int, if_pos]
    rw [Finset.mem_range]
    have h0 := htstar_nonneg j
    have hT := htstar_le_T j
    omega
  · intro ij hij t _
    simp_rw [hx_eq ij.1, hx_eq ij.2]
    rw [finset_sum_ite_eq_int, finset_sum_ite_eq_int]
    split_ifs with h1 h2
    · exfalso
      rw [Finset.mem_Icc] at h1
      rw [Finset.mem_range] at h2
      have h0_1 := htstar_nonneg ij.1
      have h0_2 := htstar_nonneg ij.2
      have hlag := htstar_lag ij hij
      omega
    · omega
    · omega
    · omega
  · intro j t _
    rw [hx_eq j t]
    split_ifs <;> omega
  · intro j t ht
    rw [hx_eq j t, if_neg]
    have ⟨he, hl⟩ := htstar_bounds j
    have h0 := htstar_nonneg j
    omega
  · have hfilter_eq :
        I.A.filter (fun α => I.InCut X α) = Finset.univ.image (fun j => Arc.assign j (tstar j)) := by
      ext α
      rw [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hαA, hin⟩
        rcases α with ⟨j, t⟩ | ⟨ij, t⟩ | ⟨j⟩ | ⟨j⟩
        · have ht : t = tstar j := huniq j t ⟨hαA, hin⟩
          exact ⟨j, Finset.mem_univ j, by rw [ht]⟩
        · exact absurd hin (not_inCut_of_cap_top I hcap hαA rfl)
        · exact absurd hin (not_inCut_of_cap_top I hcap hαA rfl)
        · exact absurd hin (not_inCut_of_cap_top I hcap hαA rfl)
      · rintro ⟨j, _, rfl⟩
        exact htstar j
    unfold Instance.cutCap
    rw [hfilter_eq, Finset.sum_image]
    · have hcost_eq : I.cost (I.xOfCut X) = ∑ j : Fin (n + 1), I.w j (tstar j).toNat := by
        unfold Instance.cost
        refine Finset.sum_congr rfl fun j _ => ?_
        have hterm : ∀ t : ℕ, I.w j t * (I.xOfCut X j t : ℝ) =
            if t = (tstar j).toNat then I.w j t else 0 := by
          intro t
          rw [hx_eq j t]
          split_ifs <;> simp
        simp_rw [hterm]
        have hr : (tstar j).toNat ∈ Finset.range (I.T + 1) := by
          rw [Finset.mem_range]
          have h0 := htstar_nonneg j
          have hT := htstar_le_T j
          omega
        rw [finset_sum_ite_eq, if_pos hr]
      rw [hcost_eq, ofReal_sum_of_nonneg (fun j _ => hw j (tstar j).toNat)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rfl
    · intro j₁ _ j₂ _ h
      exact (Arc.assign.injEq _ _ _ _ ▸ h).1
