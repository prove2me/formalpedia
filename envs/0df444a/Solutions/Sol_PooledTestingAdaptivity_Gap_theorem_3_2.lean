-- Prove2me | solution 1 for PooledTestingAdaptivity.Gap.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T00:53:28.448194+00:00
-- url     : https://prove2.me/submissions/c3f41989-2fcd-4b53-b946-aba007f38fbd

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_Policies

namespace PooledTestingAdaptivity.Gap

section Helpers

lemma negative_iff {n : ℕ} {t : Finset (Fin n)} {x : Profile n} :
    negative t x = true ↔ ∀ i ∈ t, x i = true := by
  simp [negative]

lemma negative_eq_false_iff {n : ℕ} {t : Finset (Fin n)} {x : Profile n} :
    negative t x = false ↔ ∃ i ∈ t, x i = false := by
  simp [negative]

lemma mem_cleared_iff {n : ℕ} {T : Allocation n} {x : Profile n} {i : Fin n} :
    i ∈ cleared T x ↔ ∃ t ∈ T, negative t x = true ∧ i ∈ t := by
  induction T with
  | nil => simp [cleared]
  | cons t ts ih =>
    simp only [cleared, Finset.mem_union, List.mem_cons]
    constructor
    · rintro (h | h)
      · split_ifs at h with hneg
        · exact ⟨t, Or.inl rfl, hneg, h⟩
        · simp at h
      · rcases ih.mp h with ⟨s, hs, hneg, hi⟩
        exact ⟨s, Or.inr hs, hneg, hi⟩
    · rintro ⟨s, rfl | hs, hneg, hi⟩
      · left; simp [hneg, hi]
      · right; exact ih.mpr ⟨s, hs, hneg, hi⟩

lemma mem_cleared_imp_true {n : ℕ} {T : Allocation n} {x : Profile n} {i : Fin n}
    (h : i ∈ cleared T x) : x i = true := by
  rcases mem_cleared_iff.mp h with ⟨t, _, hneg, hi⟩
  exact negative_iff.mp hneg i hi

lemma refines_nil {n : ℕ} (T : Allocation n) : Refines [] T := by
  induction T with
  | nil => exact Refines.nil
  | cons t ts ih => exact Refines.drop t ih

lemma profileMass_nonneg {n : ℕ} (J : Instance n) (x : Profile n) :
    0 ≤ profileMass J x := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact le_of_lt (J.q_pos i)
  · linarith [J.q_le_one i]

lemma sum_profileMass {n : ℕ} (J : Instance n) :
    ∑ x : Profile n, profileMass J x = 1 := by
  unfold profileMass
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => if b then J.q i else 1 - J.q i)]
  apply Finset.prod_eq_one
  intro i _
  simp [Fintype.sum_bool]

lemma reward_le_sum_u {n : ℕ} (J : Instance n) (T : Allocation n) (x : Profile n) :
    reward J T x ≤ ∑ i : Fin n, J.u i := by
  unfold reward
  exact Finset.sum_le_univ_sum_of_nonneg (fun i => J.u_nonneg i)

lemma staticWelfare_le_sum_u {n : ℕ} (J : Instance n) (T : Allocation n) :
    staticWelfare J T ≤ ∑ i : Fin n, J.u i := by
  unfold staticWelfare expectation
  calc
    ∑ x : Profile n, profileMass J x * reward J T x
      ≤ ∑ x : Profile n, profileMass J x * (∑ i : Fin n, J.u i) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (reward_le_sum_u J T x) (profileMass_nonneg J x)
    _ = (∑ x : Profile n, profileMass J x) * (∑ i : Fin n, J.u i) := by
        rw [← Finset.sum_mul]
    _ = ∑ i : Fin n, J.u i := by
        rw [sum_profileMass J, one_mul]

lemma optStatic_bddAbove {n B : ℕ} {J : Instance n} (F : FeasibleFamily J B) :
    BddAbove {v : ℝ | ∃ T ∈ F.allocations, staticWelfare J T = v} := by
  refine ⟨∑ i : Fin n, J.u i, ?_⟩
  rintro v ⟨T, _, rfl⟩
  exact staticWelfare_le_sum_u J T

lemma run_leaf {n : ℕ} (u : Unit) (x : Profile n) :
    run (.leaf u : Policy n) x = [] := rfl

lemma run_query {n : ℕ} (t : Pool n) (k : Bool → Policy n) (x : Profile n) :
    run (.query t k) x = t.val :: run (k (negative t.val x)) x := rfl

lemma allLabels_mono {Label : Type} {p q : Label → Prop} (hpq : ∀ a, p a → q a) :
    ∀ T : DecisionTree Label, T.allLabels p → T.allLabels q
  | .leaf _, _ => trivial
  | .query t k, ⟨ht, h1, h2⟩ =>
      ⟨hpq t ht, allLabels_mono hpq (k true) h1, allLabels_mono hpq (k false) h2⟩

lemma allLabels_and {Label : Type} {p q : Label → Prop} :
    ∀ T : DecisionTree Label, T.allLabels p → T.allLabels q → T.allLabels (fun a => p a ∧ q a)
  | .leaf _, _, _ => trivial
  | .query t k, ⟨hp, hp1, hp2⟩, ⟨hq, hq1, hq2⟩ =>
      ⟨⟨hp, hq⟩, allLabels_and (k true) hp1 hq1, allLabels_and (k false) hp2 hq2⟩

lemma allLabels_mem_run {n : ℕ} {p : Finset (Fin n) → Prop} :
    ∀ (π : Policy n), π.allLabels (fun s => p s.val) → ∀ (x : Profile n) (t : Finset (Fin n)),
      t ∈ run π x → p t
  | .leaf _, _, _, _, ht => by simp [run_leaf] at ht
  | .query s k, ⟨hs, h1, h2⟩, x, t, ht => by
      rw [run_query, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact hs
      · cases hneg : negative s.val x
        · rw [hneg] at ht; exact allLabels_mem_run (k false) h2 x t ht
        · rw [hneg] at ht; exact allLabels_mem_run (k true) h1 x t ht

end Helpers

/-! ### Section 4.1: Normalization -/

section Normalization

def normAux {n : ℕ} (C : Finset (Fin n)) : Policy n → Policy n
  | .leaf u => .leaf u
  | .query t k =>
      let s := t.val \ C
      if hs : s.Nonempty then
        .query ⟨s, hs⟩ (fun b => if b then normAux (C ∪ s) (k true) else normAux C (k false))
      else
        normAux C (k true)

lemma normAux_allLabels_disjoint {n : ℕ} :
    ∀ (π : Policy n) (C : Finset (Fin n)),
      (normAux C π).allLabels (fun u => Disjoint u.val C)
  | .leaf _, _ => trivial
  | .query t k, C => by
      dsimp [normAux]
      split_ifs with hs
      · refine ⟨Finset.disjoint_left.mpr (fun _ hj => (Finset.mem_sdiff.mp hj).2),
          ?_, normAux_allLabels_disjoint (k false) C⟩
        simp only [ite_true]
        exact allLabels_mono
          (fun (u : Pool n) (hu : Disjoint u.val (C ∪ (t.val \ C))) =>
            hu.mono_right Finset.subset_union_left)
          _ (normAux_allLabels_disjoint (k true) (C ∪ (t.val \ C)))
      · exact normAux_allLabels_disjoint (k true) C

lemma normAux_syntacticallyNormalized {n : ℕ} :
    ∀ (π : Policy n) (C : Finset (Fin n)), SyntacticallyNormalized (normAux C π)
  | .leaf _, _ => trivial
  | .query t k, C => by
      dsimp [normAux]
      split_ifs with hs
      · simp only [SyntacticallyNormalized, ite_true]
        refine ⟨?_, normAux_syntacticallyNormalized (k true) (C ∪ (t.val \ C)),
          normAux_syntacticallyNormalized (k false) C⟩
        exact allLabels_mono
          (fun (u : Pool n) (hu : Disjoint u.val (C ∪ (t.val \ C))) =>
            hu.mono_right Finset.subset_union_right)
          _ (normAux_allLabels_disjoint (k true) (C ∪ (t.val \ C)))
      · exact normAux_syntacticallyNormalized (k true) C

lemma negative_sdiff_eq {n : ℕ} {t C : Finset (Fin n)} {x : Profile n}
    (hC : ∀ j ∈ C, x j = true) :
    negative (t \ C) x = negative t x := by
  apply Bool.eq_iff_iff.mpr
  simp only [negative_iff, Finset.mem_sdiff]
  constructor
  · intro h j hj
    by_cases hjC : j ∈ C
    · exact hC j hjC
    · exact h j ⟨hj, hjC⟩
  · intro h j hj
    exact h j hj.1

lemma normAux_refines {n : ℕ} :
    ∀ (π : Policy n) {C : Finset (Fin n)} {x : Profile n},
      (∀ j ∈ C, x j = true) → Refines (run (normAux C π) x) (run π x)
  | .leaf _, _, _, _ => Refines.nil
  | .query t k, C, x, hC => by
      rw [run_query]
      dsimp [normAux]
      have hneg_eq : negative (t.val \ C) x = negative t.val x := negative_sdiff_eq hC
      split_ifs with hs
      · rw [run_query]
        change Refines ((t.val \ C) :: run (if negative (t.val \ C) x then
            normAux (C ∪ (t.val \ C)) (k true) else normAux C (k false)) x)
          (t.val :: run (k (negative t.val x)) x)
        rw [hneg_eq]
        cases hneg : negative t.val x
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact Refines.keep hs Finset.sdiff_subset (normAux_refines (k false) hC)
        · simp only [↓reduceIte]
          have hCs : ∀ j ∈ C ∪ (t.val \ C), x j = true := by
            intro j hj
            rcases Finset.mem_union.mp hj with hjC | hjs
            · exact hC j hjC
            · exact negative_iff.mp hneg j (Finset.mem_sdiff.mp hjs).1
          exact Refines.keep hs Finset.sdiff_subset (normAux_refines (k true) hCs)
      · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hs
        have hneg : negative t.val x = true :=
          negative_iff.mpr (fun j hj => hC j (hs hj))
        rw [hneg]
        exact Refines.drop t.val (normAux_refines (k true) hC)

lemma normAux_cleared {n : ℕ} :
    ∀ (π : Policy n) {C : Finset (Fin n)} {x : Profile n},
      (∀ j ∈ C, x j = true) →
      C ∪ cleared (run (normAux C π) x) x = C ∪ cleared (run π x) x
  | .leaf _, _, _, _ => rfl
  | .query t k, C, x, hC => by
      rw [run_query]
      dsimp [normAux]
      have hneg_eq : negative (t.val \ C) x = negative t.val x := negative_sdiff_eq hC
      split_ifs with hs
      · rw [run_query]
        change C ∪ cleared ((t.val \ C) :: run (if negative (t.val \ C) x then
            normAux (C ∪ (t.val \ C)) (k true) else normAux C (k false)) x) x =
          C ∪ cleared (t.val :: run (k (negative t.val x)) x) x
        simp only [cleared, hneg_eq]
        cases hneg : negative t.val x
        · simp only [Bool.false_eq_true, ↓reduceIte, Finset.empty_union]
          exact normAux_cleared (k false) hC
        · simp only [↓reduceIte]
          have hCs : ∀ j ∈ C ∪ (t.val \ C), x j = true := by
            intro j hj
            rcases Finset.mem_union.mp hj with hjC | hjs
            · exact hC j hjC
            · exact negative_iff.mp hneg j (Finset.mem_sdiff.mp hjs).1
          calc
            C ∪ ((t.val \ C) ∪ cleared (run (normAux (C ∪ (t.val \ C)) (k true)) x) x)
              = (C ∪ (t.val \ C)) ∪ cleared (run (normAux (C ∪ (t.val \ C)) (k true)) x) x := by
                  rw [Finset.union_assoc]
            _ = (C ∪ (t.val \ C)) ∪ cleared (run (k true) x) x :=
                  normAux_cleared (k true) hCs
            _ = C ∪ (t.val ∪ cleared (run (k true) x) x) := by
                  rw [Finset.union_sdiff_self_eq_union, Finset.union_assoc]
      · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hs
        have hneg : negative t.val x = true :=
          negative_iff.mpr (fun j hj => hC j (hs hj))
        simp only [cleared, hneg, ↓reduceIte]
        calc
          C ∪ cleared (run (normAux C (k true)) x) x
            = C ∪ cleared (run (k true) x) x := normAux_cleared (k true) hC
          _ = (C ∪ t.val) ∪ cleared (run (k true) x) x := by
                rw [Finset.union_eq_left.mpr hs]
          _ = C ∪ (t.val ∪ cleared (run (k true) x) x) := by
                rw [Finset.union_assoc]

def normalize {n : ℕ} (π : Policy n) : Policy n := normAux ∅ π

lemma normalize_syntacticallyNormalized {n : ℕ} (π : Policy n) :
    SyntacticallyNormalized (normalize π) :=
  normAux_syntacticallyNormalized π ∅

lemma normalize_feasible {n B : ℕ} {J : Instance n} {F : FeasibleFamily J B}
    (hF : DownwardClosed F) {π : Policy n} (hπ : Feasible F π) :
    Feasible F (normalize π) := by
  intro x
  exact hF (run π x) (hπ x) _ (normAux_refines π (by simp))

lemma normalize_cleared {n : ℕ} (π : Policy n) (x : Profile n) :
    cleared (run (normalize π) x) x = cleared (run π x) x := by
  unfold normalize
  have h := normAux_cleared π (C := ∅) (x := x) (by simp)
  simpa using h

lemma normalize_dynamicWelfare {n : ℕ} (J : Instance n) (π : Policy n) :
    dynamicWelfare J (normalize π) = dynamicWelfare J π := by
  unfold dynamicWelfare expectation reward
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  rw [normalize_cleared]

end Normalization

/-! ### Half-Thinning and Exact Clearance Probabilities -/

section Thinning

def thinAlloc {n : ℕ} : (P : Allocation n) → (Fin P.length → Finset (Fin n)) → Allocation n
  | [], _ => []
  | t :: ts, masks =>
      let s := t ∩ masks 0
      let rest := thinAlloc ts (fun r => masks r.succ)
      if s.Nonempty then s :: rest else rest

lemma thinAlloc_refines {n : ℕ} :
    ∀ (P : Allocation n) (masks : Fin P.length → Finset (Fin n)),
      Refines (thinAlloc P masks) P
  | [], _ => Refines.nil
  | t :: ts, masks => by
      dsimp [thinAlloc]
      split_ifs with hs
      · exact Refines.keep hs Finset.inter_subset_left (thinAlloc_refines ts _)
      · exact Refines.drop t (thinAlloc_refines ts _)

noncomputable def stepSucc {n : ℕ} (i : Fin n) (t : Finset (Fin n)) (y : Profile n) : ℝ :=
  if i ∈ t ∧ y i = true then
    (1 / 2 : ℝ) ^ (1 + (t.filter (fun j => !y j)).card)
  else
    0

lemma stepSucc_nonneg {n : ℕ} (i : Fin n) (t : Finset (Fin n)) (y : Profile n) :
    0 ≤ stepSucc i t y := by
  unfold stepSucc
  split_ifs
  · positivity
  · rfl

lemma stepSucc_le_one {n : ℕ} (i : Fin n) (t : Finset (Fin n)) (y : Profile n) :
    stepSucc i t y ≤ 1 := by
  unfold stepSucc
  split_ifs
  · exact pow_le_one₀ (by positivity) (by norm_num)
  · norm_num

noncomputable def allocFail {n : ℕ} (i : Fin n) : Allocation n → Profile n → ℝ
  | [], _ => 1
  | t :: ts, y => (1 - stepSucc i t y) * allocFail i ts y

lemma allocFail_nonneg {n : ℕ} (i : Fin n) :
    ∀ (P : Allocation n) (y : Profile n), 0 ≤ allocFail i P y
  | [], _ => zero_le_one
  | t :: ts, y =>
      mul_nonneg (sub_nonneg.mpr (stepSucc_le_one i t y)) (allocFail_nonneg i ts y)

lemma allocFail_le_one {n : ℕ} (i : Fin n) :
    ∀ (P : Allocation n) (y : Profile n), allocFail i P y ≤ 1
  | [], _ => le_rfl
  | t :: ts, y => by
      calc
        (1 - stepSucc i t y) * allocFail i ts y
          ≤ 1 * 1 := mul_le_mul (by linarith [stepSucc_nonneg i t y])
              (allocFail_le_one i ts y) (allocFail_nonneg i ts y) zero_le_one
        _ = 1 := one_mul 1

lemma allocFail_eq_one_of_forall_not_mem {n : ℕ} (i : Fin n) :
    ∀ (P : Allocation n) (y : Profile n), (∀ t ∈ P, i ∉ t) → allocFail i P y = 1
  | [], _, _ => rfl
  | t :: ts, y, h => by
      have hit : i ∉ t := h t List.mem_cons_self
      have hstep : stepSucc i t y = 0 := by simp [stepSucc, hit]
      simp [allocFail, hstep, allocFail_eq_one_of_forall_not_mem i ts y
        (fun s hs => h s (List.mem_cons_of_mem _ hs))]

noncomputable def thinClearProb {n : ℕ} (i : Fin n) (P : Allocation n) (y : Profile n) : ℝ :=
  1 - allocFail i P y

lemma thinClearProb_nonneg {n : ℕ} (i : Fin n) (P : Allocation n) (y : Profile n) :
    0 ≤ thinClearProb i P y :=
  sub_nonneg.mpr (allocFail_le_one i P y)

lemma pow_two_sub_eq {n k : ℕ} (hk : k ≤ n) :
    ((2 : ℝ) ^ (n - k)) = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ k := by
  have h1 : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - k) * (2 : ℝ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have h2 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  calc
    (2 : ℝ) ^ (n - k) = (2 : ℝ) ^ (n - k) * ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) := by
      rw [h2, mul_one]
    _ = ((2 : ℝ) ^ (n - k) * (2 : ℝ) ^ k) * (1 / 2 : ℝ) ^ k := by ring
    _ = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ k := by rw [← h1]

lemma sum_masks_single_fail {n : ℕ} (i : Fin n) (t : Finset (Fin n)) (y : Profile n) :
    (∑ M : Finset (Fin n),
      if i ∈ t ∩ M ∧ negative (t ∩ M) y = true then (0 : ℝ) else 1) =
    (2 : ℝ) ^ n * (1 - stepSucc i t y) := by
  have htot : (∑ _M : Finset (Fin n), (1 : ℝ)) = (2 : ℝ) ^ n := by
    simp [Fintype.card_finset, Fintype.card_fin]
  have hsplit :
      (∑ M : Finset (Fin n), if i ∈ t ∩ M ∧ negative (t ∩ M) y = true then (0 : ℝ) else 1) +
      (∑ M : Finset (Fin n), if i ∈ t ∩ M ∧ negative (t ∩ M) y = true then (1 : ℝ) else 0) =
      (2 : ℝ) ^ n := by
    rw [← Finset.sum_add_distrib, ← htot]
    apply Finset.sum_congr rfl
    intro M _
    split_ifs <;> norm_num
  suffices hsucc :
      (∑ M : Finset (Fin n), if i ∈ t ∩ M ∧ negative (t ∩ M) y = true then (1 : ℝ) else 0) =
      (2 : ℝ) ^ n * stepSucc i t y by
    linarith
  by_cases hiy : i ∈ t ∧ y i = true
  · rcases hiy with ⟨hit, hyi⟩
    let Bad : Finset (Fin n) := t.filter (fun j => !y j)
    have hiBad : i ∉ Bad := by simp [Bad, hyi]
    let Fixed : Finset (Fin n) := insert i Bad
    have hFixed_card : Fixed.card = 1 + Bad.card := by
      rw [Finset.card_insert_of_notMem hiBad, add_comm]
    have hFixed_le : Fixed.card ≤ n := by
      simpa [Fintype.card_fin] using Finset.card_le_univ Fixed
    let Good : Finset (Finset (Fin n)) :=
      Finset.univ.filter (fun M : Finset (Fin n) => i ∈ t ∩ M ∧ negative (t ∩ M) y = true)
    have hsum_eq :
        (∑ M : Finset (Fin n), if i ∈ t ∩ M ∧ negative (t ∩ M) y = true then (1 : ℝ) else 0) =
        (Good.card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [Good]
    let Free : Finset (Fin n) := Finset.univ \ Fixed
    have hcard : Good.card = Free.powerset.card := by
      symm
      apply Finset.card_bij (fun K _ => insert i K)
      · intro K hK
        rw [Finset.mem_powerset] at hK
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Finset.mem_inter.mpr ⟨hit, Finset.mem_insert_self _ _⟩, negative_iff.mpr ?_⟩
        intro j hj
        rcases Finset.mem_inter.mp hj with ⟨hjt, hjins⟩
        rcases Finset.mem_insert.mp hjins with rfl | hjK
        · exact hyi
        · have hjNotFixed : j ∉ Fixed := (Finset.mem_sdiff.mp (hK hjK)).2
          by_contra hjy
          have hjfalse : y j = false := by cases h' : y j <;> simp_all
          apply hjNotFixed
          exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hjt, by simp [hjfalse]⟩)
      · intro K₁ hK₁ K₂ hK₂ heq
        rw [Finset.mem_powerset] at hK₁ hK₂
        have hi₁ : i ∉ K₁ := fun h => (Finset.mem_sdiff.mp (hK₁ h)).2 (Finset.mem_insert_self _ _)
        have hi₂ : i ∉ K₂ := fun h => (Finset.mem_sdiff.mp (hK₂ h)).2 (Finset.mem_insert_self _ _)
        have := congr_arg (fun S => S.erase i) heq
        simpa [Finset.erase_insert hi₁, Finset.erase_insert hi₂] using this
      · intro M hM
        simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
          negative_iff] at hM
        refine ⟨M.erase i, ?_, Finset.insert_erase hM.1.2⟩
        rw [Finset.mem_powerset]
        intro j hj
        rcases Finset.mem_erase.mp hj with ⟨hji, hjM⟩
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ j, ?_⟩
        intro hjFixed
        rcases Finset.mem_insert.mp hjFixed with rfl | hjBad
        · exact hji rfl
        · rcases Finset.mem_filter.mp hjBad with ⟨hjt, hjny⟩
          have hjtrue : y j = true := hM.2 j ⟨hjt, hjM⟩
          simp [hjtrue] at hjny
    have hFree_card : Free.card = n - Fixed.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [hsum_eq, hcard, Finset.card_powerset, hFree_card, Nat.cast_pow, Nat.cast_ofNat]
    rw [pow_two_sub_eq hFixed_le, hFixed_card]
    unfold stepSucc
    rw [if_pos ⟨hit, hyi⟩]
  · have hzero : ∀ M : Finset (Fin n), ¬(i ∈ t ∩ M ∧ negative (t ∩ M) y = true) := by
      rintro M ⟨hiM, hneg⟩
      have hit : i ∈ t := (Finset.mem_inter.mp hiM).1
      have hyi : y i = true := negative_iff.mp hneg i hiM
      exact hiy ⟨hit, hyi⟩
    unfold stepSucc
    rw [if_neg hiy, mul_zero]
    apply Finset.sum_eq_zero
    intro M _
    exact if_neg (hzero M)

lemma mem_cleared_thinAlloc_cons {n : ℕ} (i : Fin n) (t : Finset (Fin n)) (ts : Allocation n)
    (masks : Fin (t :: ts).length → Finset (Fin n)) (y : Profile n) :
    i ∈ cleared (thinAlloc (t :: ts) masks) y ↔
      (i ∈ t ∩ masks 0 ∧ negative (t ∩ masks 0) y = true) ∨
      i ∈ cleared (thinAlloc ts (fun r => masks r.succ)) y := by
  dsimp [thinAlloc]
  split_ifs with hs
  · simp only [cleared, Finset.mem_union]
    split_ifs with hneg
    · simp [hneg]
    · simp [hneg]
  · constructor
    · intro h; exact Or.inr h
    · rintro (⟨hi, _⟩ | h)
      · exact False.elim (hs ⟨i, hi⟩)
      · exact h

lemma sum_masks_fail {n : ℕ} (i : Fin n) :
    ∀ (P : Allocation n) (y : Profile n),
      (∑ masks : Fin P.length → Finset (Fin n),
        if i ∈ cleared (thinAlloc P masks) y then (0 : ℝ) else 1) =
      ((2 : ℝ) ^ n) ^ P.length * allocFail i P y
  | [], y => by
      simp [thinAlloc, cleared, allocFail]
  | t :: ts, y => by
      dsimp only [List.length_cons]
      let e := Fin.consEquiv (fun _ : Fin (ts.length + 1) => Finset (Fin n))
      rw [← e.sum_comp]
      rw [Fintype.sum_prod_type]
      have hcongr :
          ∀ (M : Finset (Fin n)) (masks' : Fin ts.length → Finset (Fin n)),
            (if i ∈ cleared (thinAlloc (t :: ts) (e (M, masks'))) y then (0 : ℝ) else 1) =
            (if i ∈ t ∩ M ∧ negative (t ∩ M) y = true then (0 : ℝ) else 1) *
            (if i ∈ cleared (thinAlloc ts masks') y then (0 : ℝ) else 1) := by
        intro M masks'
        have h0 : e (M, masks') 0 = M := by simp [e]
        have hsucc : (fun r : Fin ts.length => e (M, masks') r.succ) = masks' := by
          ext r; simp [e]
        have hiff : i ∈ cleared (thinAlloc (t :: ts) (e (M, masks'))) y ↔
            (i ∈ t ∩ M ∧ negative (t ∩ M) y = true) ∨ i ∈ cleared (thinAlloc ts masks') y := by
          simpa [h0, hsucc] using mem_cleared_thinAlloc_cons i t ts (e (M, masks')) y
        by_cases hA : i ∈ t ∩ M ∧ negative (t ∩ M) y = true <;>
          by_cases hB : i ∈ cleared (thinAlloc ts masks') y <;>
          simp [hiff, hA, hB]
      simp_rw [hcongr, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [sum_masks_single_fail i t y, sum_masks_fail i ts y]
      simp only [pow_succ, allocFail]
      ring

lemma sum_masks_clear {n : ℕ} (i : Fin n) (P : Allocation n) (y : Profile n) :
    (∑ masks : Fin P.length → Finset (Fin n),
      if i ∈ cleared (thinAlloc P masks) y then (1 : ℝ) else 0) =
    ((2 : ℝ) ^ n) ^ P.length * thinClearProb i P y := by
  have htot :
      (∑ _masks : Fin P.length → Finset (Fin n), (1 : ℝ)) = ((2 : ℝ) ^ n) ^ P.length := by
    simp [Fintype.card_pi, Fintype.card_finset, Fintype.card_fin, Finset.prod_const]
  have hsplit :
      (∑ masks : Fin P.length → Finset (Fin n),
        if i ∈ cleared (thinAlloc P masks) y then (1 : ℝ) else 0) +
      (∑ masks : Fin P.length → Finset (Fin n),
        if i ∈ cleared (thinAlloc P masks) y then (0 : ℝ) else 1) =
      ((2 : ℝ) ^ n) ^ P.length := by
    rw [← Finset.sum_add_distrib, ← htot]
    apply Finset.sum_congr rfl
    intro masks _
    split_ifs <;> norm_num
  have hfail := sum_masks_fail i P y
  unfold thinClearProb
  linarith

end Thinning

/-! ### Sections 4.2 & 4.3: Reduced Normalized Trees and the Failure Invariant -/

section ReducedTree

inductive RTree (n : ℕ) where
  | leaf : RTree n
  | query (A : Finset (Fin n)) (zeroChild posChild : RTree n) : RTree n
  | offer (S : Finset (Fin n)) (cont : RTree n) : RTree n

def RTree.Valid {n : ℕ} : Finset (Fin n) → RTree n → Prop
  | _, .leaf => True
  | F, .query A t0 tp => A ⊆ F ∧ RTree.Valid (F \ A) t0 ∧ RTree.Valid F tp
  | F, .offer S tc => S ⊆ F ∧ RTree.Valid F tc

def allZeroOn {n : ℕ} (A : Finset (Fin n)) (z : Profile n) : Bool :=
  decide (∀ j ∈ A, z j = false)

noncomputable def offerProb {n : ℕ} (S : Finset (Fin n)) (z : Profile n) : ℝ :=
  (1 / 2 : ℝ) ^ (1 + (S.filter (fun j => !z j)).card)

lemma offerProb_nonneg {n : ℕ} (S : Finset (Fin n)) (z : Profile n) :
    0 ≤ offerProb S z := by
  unfold offerProb; positivity

lemma offerProb_le_one {n : ℕ} (S : Finset (Fin n)) (z : Profile n) :
    offerProb S z ≤ 1 := by
  unfold offerProb
  exact pow_le_one₀ (by positivity) (by norm_num)

noncomputable def RTree.IT {n : ℕ} : RTree n → Profile n → ℝ
  | .leaf, _ => 0
  | .query A t0 tp, z => if allZeroOn A z then t0.IT z else tp.IT z
  | .offer S tc, z => if allZeroOn S z then 1 else tc.IT z

noncomputable def RTree.FT {n : ℕ} : RTree n → Profile n → ℝ
  | .leaf, _ => 1
  | .query A t0 tp, z => if allZeroOn A z then t0.FT z else tp.FT z
  | .offer S tc, z =>
      if allZeroOn S z then
        1 - offerProb S z
      else
        (1 - offerProb S z) * tc.FT z

lemma RTree.IT_zero_or_one {n : ℕ} :
    ∀ (T : RTree n) (z : Profile n), T.IT z = 0 ∨ T.IT z = 1
  | .leaf, _ => Or.inl rfl
  | .query A t0 tp, z => by
      dsimp [RTree.IT]
      split_ifs
      · exact t0.IT_zero_or_one z
      · exact tp.IT_zero_or_one z
  | .offer S tc, z => by
      dsimp [RTree.IT]
      split_ifs
      · exact Or.inr rfl
      · exact tc.IT_zero_or_one z

lemma RTree.FT_nonneg {n : ℕ} :
    ∀ (T : RTree n) (z : Profile n), 0 ≤ T.FT z
  | .leaf, _ => zero_le_one
  | .query A t0 tp, z => by
      dsimp [RTree.FT]
      split_ifs
      · exact t0.FT_nonneg z
      · exact tp.FT_nonneg z
  | .offer S tc, z => by
      dsimp [RTree.FT]
      have h1 : 0 ≤ 1 - offerProb S z := sub_nonneg.mpr (offerProb_le_one S z)
      split_ifs
      · exact h1
      · exact mul_nonneg h1 (tc.FT_nonneg z)

lemma RTree.FT_le_one {n : ℕ} :
    ∀ (T : RTree n) (z : Profile n), T.FT z ≤ 1
  | .leaf, _ => le_rfl
  | .query A t0 tp, z => by
      dsimp [RTree.FT]
      split_ifs
      · exact t0.FT_le_one z
      · exact tp.FT_le_one z
  | .offer S tc, z => by
      dsimp [RTree.FT]
      have h0 : 0 ≤ offerProb S z := offerProb_nonneg S z
      split_ifs
      · linarith
      · calc
          (1 - offerProb S z) * tc.FT z
            ≤ 1 * 1 := mul_le_mul (by linarith) (tc.FT_le_one z) (tc.FT_nonneg z) zero_le_one
          _ = 1 := one_mul 1

def IncreasingOn {n : ℕ} (F : Finset (Fin n)) (R : Finset (Profile n)) : Prop :=
  (∀ z ∈ R, ∀ j ∉ F, z j = false) ∧
  (∀ z ∈ R, ∀ z' : Profile n,
    (∀ j ∉ F, z' j = false) → (∀ j ∈ F, z j = true → z' j = true) → z' ∈ R)

lemma increasingOn_filter_zero {n : ℕ} {F A : Finset (Fin n)} {R : Finset (Profile n)}
    (hR : IncreasingOn F R) :
    IncreasingOn (F \ A) (R.filter (fun z => allZeroOn A z = true)) := by
  refine ⟨?_, ?_⟩
  · intro z hz j hj
    rcases Finset.mem_filter.mp hz with ⟨hzR, hzA⟩
    rw [allZeroOn, decide_eq_true_iff] at hzA
    by_cases hjA : j ∈ A
    · exact hzA j hjA
    · exact hR.1 z hzR j (fun hjF => hj (Finset.mem_sdiff.mpr ⟨hjF, hjA⟩))
  · intro z hz z' hz'out hz'mono
    rcases Finset.mem_filter.mp hz with ⟨hzR, hzA⟩
    rw [allZeroOn, decide_eq_true_iff] at hzA
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply hR.2 z hzR z'
      · intro j hjF
        exact hz'out j (fun h => hjF (Finset.mem_sdiff.mp h).1)
      · intro j hjF hzj
        have hjA : j ∉ A := fun h => by rw [hzA j h] at hzj; cases hzj
        exact hz'mono j (Finset.mem_sdiff.mpr ⟨hjF, hjA⟩) hzj
    · rw [allZeroOn, decide_eq_true_iff]
      intro j hjA
      exact hz'out j (fun h => (Finset.mem_sdiff.mp h).2 hjA)

lemma increasingOn_filter_pos {n : ℕ} {F A : Finset (Fin n)} {R : Finset (Profile n)}
    (hAF : A ⊆ F) (hR : IncreasingOn F R) :
    IncreasingOn F (R.filter (fun z => allZeroOn A z = false)) := by
  refine ⟨?_, ?_⟩
  · intro z hz j hj
    exact hR.1 z (Finset.mem_filter.mp hz).1 j hj
  · intro z hz z' hz'out hz'mono
    rcases Finset.mem_filter.mp hz with ⟨hzR, hzA⟩
    refine Finset.mem_filter.mpr ⟨hR.2 z hzR z' hz'out hz'mono, ?_⟩
    rw [allZeroOn, decide_eq_false_iff_not] at hzA ⊢
    intro hall
    apply hzA
    intro j hjA
    by_cases hzj : z j = true
    · have := hz'mono j (hAF hjA) hzj
      rw [hall j hjA] at this; cases this
    · cases h : z j <;> simp_all

lemma card_pos_ge_mul_zero {n : ℕ} {F S : Finset (Fin n)} {R : Finset (Profile n)}
    (hSF : S ⊆ F) (hR : IncreasingOn F R) :
    (R.filter (fun z => allZeroOn S z = true)).card * (2 ^ S.card - 1) ≤
    (R.filter (fun z => allZeroOn S z = false)).card := by
  let Rz := R.filter (fun z => allZeroOn S z = true)
  let Rp := R.filter (fun z => allZeroOn S z = false)
  let NonemptySubs := S.powerset.erase ∅
  have hcard_subs : NonemptySubs.card = 2 ^ S.card - 1 := by
    rw [Finset.card_erase_of_mem (Finset.empty_mem_powerset S), Finset.card_powerset]
  rw [← hcard_subs, ← Finset.card_product]
  let patch : Profile n × Finset (Fin n) → Profile n :=
    fun p j => if j ∈ p.2 then true else p.1 j
  apply Finset.card_le_card_of_injOn patch
  · rintro ⟨z, U⟩ hp
    rcases Finset.mem_product.mp hp with ⟨hz, hU⟩
    rcases Finset.mem_erase.mp hU with ⟨hUne, hUS⟩
    rw [Finset.mem_powerset] at hUS
    rcases Finset.nonempty_iff_ne_empty.mpr hUne with ⟨j₀, hj₀U⟩
    rcases Finset.mem_filter.mp hz with ⟨hzR, _⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply hR.2 z hzR (patch (z, U))
      · intro j hjF
        have hjU : j ∉ U := fun h => hjF (hSF (hUS h))
        simp [patch, hjU, hR.1 z hzR j hjF]
      · intro j _ hzj
        simp [patch, hzj]
    · rw [allZeroOn, decide_eq_false_iff_not]
      intro hall
      have := hall j₀ (hUS hj₀U)
      simp [patch, hj₀U] at this
  · rintro ⟨z₁, U₁⟩ hp₁ ⟨z₂, U₂⟩ hp₂ heq
    rcases Finset.mem_product.mp hp₁ with ⟨hz₁, hU₁⟩
    rcases Finset.mem_product.mp hp₂ with ⟨hz₂, hU₂⟩
    have hU₁S : U₁ ⊆ S := Finset.mem_powerset.mp (Finset.mem_erase.mp hU₁).2
    have hU₂S : U₂ ⊆ S := Finset.mem_powerset.mp (Finset.mem_erase.mp hU₂).2
    have hz₁0 : ∀ j ∈ S, z₁ j = false :=
      decide_eq_true_iff.mp (Finset.mem_filter.mp hz₁).2
    have hz₂0 : ∀ j ∈ S, z₂ j = false :=
      decide_eq_true_iff.mp (Finset.mem_filter.mp hz₂).2
    have hUeq : U₁ = U₂ := by
      ext j
      by_cases hjS : j ∈ S
      · have hj := congr_fun heq j
        simp only [patch, hz₁0 j hjS, hz₂0 j hjS] at hj
        by_cases h1 : j ∈ U₁ <;> by_cases h2 : j ∈ U₂ <;> simp_all
      · constructor <;> intro h <;> exact False.elim (hjS (by first | exact hU₁S h | exact hU₂S h))
    subst hUeq
    congr 1
    ext j
    by_cases hjS : j ∈ S
    · rw [hz₁0 j hjS, hz₂0 j hjS]
    · have hjU : j ∉ U₁ := fun h => hjS (hU₁S h)
      have hj := congr_fun heq j
      simpa [patch, hjU] using hj

theorem failure_invariant {n : ℕ} :
    ∀ (T : RTree n) {F : Finset (Fin n)}, T.Valid F →
      ∀ {R : Finset (Profile n)}, IncreasingOn F R →
      ∑ z ∈ R, T.FT z * (1 + T.IT z) ≤ (R.card : ℝ)
  | .leaf, _, _, R, _ => by
      simp [RTree.FT, RTree.IT]
  | .query A t0 tp, F, ⟨hAF, ht0, htp⟩, R, hR => by
      let R0 := R.filter (fun z => allZeroOn A z = true)
      let Rp := R.filter (fun z => allZeroOn A z = false)
      have hpart : R0 ∪ Rp = R := by
        ext z; simp only [R0, Rp, Finset.mem_union, Finset.mem_filter]
        cases allZeroOn A z <;> simp
      have hdisj : Disjoint R0 Rp :=
        Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by rw [h1] at h2; cases h2)
      have hcard : (R.card : ℝ) = (R0.card : ℝ) + (Rp.card : ℝ) := by
        rw [← hpart, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
      rw [hcard]
      rw [← hpart, Finset.sum_union hdisj]
      have hsum0 :
          ∑ z ∈ R0, (RTree.query A t0 tp).FT z * (1 + (RTree.query A t0 tp).IT z) =
          ∑ z ∈ R0, t0.FT z * (1 + t0.IT z) := by
        apply Finset.sum_congr rfl
        intro z hz
        have hz0 : allZeroOn A z = true := (Finset.mem_filter.mp hz).2
        simp [RTree.FT, RTree.IT, hz0]
      have hsump :
          ∑ z ∈ Rp, (RTree.query A t0 tp).FT z * (1 + (RTree.query A t0 tp).IT z) =
          ∑ z ∈ Rp, tp.FT z * (1 + tp.IT z) := by
        apply Finset.sum_congr rfl
        intro z hz
        have hzp : allZeroOn A z = false := (Finset.mem_filter.mp hz).2
        simp [RTree.FT, RTree.IT, hzp]
      rw [hsum0, hsump]
      exact add_le_add
        (failure_invariant t0 ht0 (increasingOn_filter_zero hR))
        (failure_invariant tp htp (increasingOn_filter_pos hAF hR))
  | .offer S tc, F, ⟨hSF, htc⟩, R, hR => by
      by_cases hS : S = ∅
      · subst hS
        have hterm : ∀ z ∈ R, (RTree.offer ∅ tc).FT z * (1 + (RTree.offer ∅ tc).IT z) = 1 := by
          intro z _
          have hz0 : allZeroOn ∅ z = true := by simp [allZeroOn]
          simp [RTree.FT, RTree.IT, hz0, offerProb]
          norm_num
        rw [Finset.sum_congr rfl hterm]
        simp
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
        have hk_pos : 1 ≤ S.card := Finset.card_pos.mpr hSne
        let k := S.card
        let Rz := R.filter (fun z => allZeroOn S z = true)
        let Rp := R.filter (fun z => allZeroOn S z = false)
        have hpart : Rz ∪ Rp = R := by
          ext z; simp only [Rz, Rp, Finset.mem_union, Finset.mem_filter]
          cases allZeroOn S z <;> simp
        have hdisj : Disjoint Rz Rp :=
          Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by rw [h1] at h2; cases h2)
        have hcard : (R.card : ℝ) = (Rz.card : ℝ) + (Rp.card : ℝ) := by
          rw [← hpart, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
        let p : ℝ := (1 / 2 : ℝ) ^ k
        have hp_nonneg : 0 ≤ p := by positivity
        have hp_le_one : p ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
        have hp_mul : p * (2 : ℝ) ^ k = 1 := by
          dsimp [p]; rw [← mul_pow]; norm_num
        have hsum_z :
            ∑ z ∈ Rz, (RTree.offer S tc).FT z * (1 + (RTree.offer S tc).IT z) =
            (2 - p) * (Rz.card : ℝ) := by
          have hterm : ∀ z ∈ Rz,
              (RTree.offer S tc).FT z * (1 + (RTree.offer S tc).IT z) = 2 - p := by
            intro z hz
            have hz0 : allZeroOn S z = true := (Finset.mem_filter.mp hz).2
            have hfilt : S.filter (fun j => !z j) = S := by
              apply Finset.filter_true_of_mem
              intro j hj
              have := decide_eq_true_iff.mp hz0 j hj
              simp [this]
            simp only [RTree.FT, RTree.IT, hz0, ↓reduceIte, offerProb, hfilt]
            change (1 - (1 / 2 : ℝ) ^ (1 + k)) * (1 + 1) = 2 - (1 / 2 : ℝ) ^ k
            rw [pow_add, pow_one]
            ring
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_comm]
        have hsum_p :
            ∑ z ∈ Rp, (RTree.offer S tc).FT z * (1 + (RTree.offer S tc).IT z) ≤
            (1 - p) * (Rp.card : ℝ) := by
          calc
            ∑ z ∈ Rp, (RTree.offer S tc).FT z * (1 + (RTree.offer S tc).IT z)
              ≤ ∑ z ∈ Rp, (1 - p) * (tc.FT z * (1 + tc.IT z)) := by
                apply Finset.sum_le_sum
                intro z hz
                have hzp : allZeroOn S z = false := (Finset.mem_filter.mp hz).2
                have hnotall : ¬(∀ j ∈ S, z j = false) := decide_eq_false_iff_not.mp hzp
                have hex : ∃ j₀ ∈ S, z j₀ ≠ false := by
                  by_contra h'
                  exact hnotall (fun j hj => by by_contra hne; exact h' ⟨j, hj, hne⟩)
                rcases hex with ⟨j₀, hj₀S, hj₀ne⟩
                have hj₀true : z j₀ = true := by cases h : z j₀ <;> simp_all
                have hsub : S.filter (fun j => !z j) ⊆ S.erase j₀ := by
                  intro j hj
                  rcases Finset.mem_filter.mp hj with ⟨hjS, hzj⟩
                  refine Finset.mem_erase.mpr ⟨?_, hjS⟩
                  rintro rfl
                  simp [hj₀true] at hzj
                have hcard_le : 1 + (S.filter (fun j => !z j)).card ≤ k := by
                  have := Finset.card_le_card hsub
                  rw [Finset.card_erase_of_mem hj₀S] at this
                  omega
                have hprob_ge : p ≤ offerProb S z := by
                  unfold offerProb
                  exact pow_le_pow_of_le_one (by positivity) (by norm_num) hcard_le
                have hnonneg : 0 ≤ tc.FT z * (1 + tc.IT z) := by
                  apply mul_nonneg (tc.FT_nonneg z)
                  rcases tc.IT_zero_or_one z with h | h <;> linarith
                simp only [RTree.FT, RTree.IT, hzp, Bool.false_eq_true, ↓reduceIte, mul_assoc]
                exact mul_le_mul_of_nonneg_right (by linarith) hnonneg
            _ = (1 - p) * ∑ z ∈ Rp, tc.FT z * (1 + tc.IT z) := by rw [← Finset.mul_sum]
            _ ≤ (1 - p) * (Rp.card : ℝ) := by
                apply mul_le_mul_of_nonneg_left
                  (failure_invariant tc htc (increasingOn_filter_pos hSF hR))
                linarith
        have hcomb_nat : Rz.card * (2 ^ k - 1) ≤ Rp.card :=
          card_pos_ge_mul_zero hSF hR
        have h2k_ge : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
        have hcomb_real : (Rz.card : ℝ) * ((2 : ℝ) ^ k - 1) ≤ (Rp.card : ℝ) := by
          have : ((Rz.card * (2 ^ k - 1) : ℕ) : ℝ) ≤ (Rp.card : ℝ) := by exact_mod_cast hcomb_nat
          rwa [Nat.cast_mul, Nat.cast_sub h2k_ge, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at this
        have hslack : p * ((Rz.card : ℝ) * ((2 : ℝ) ^ k - 1) - (Rp.card : ℝ)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hp_nonneg (by linarith)
        have halg :
            (2 - p) * (Rz.card : ℝ) + (1 - p) * (Rp.card : ℝ) =
            ((Rz.card : ℝ) + (Rp.card : ℝ)) +
            p * ((Rz.card : ℝ) * ((2 : ℝ) ^ k - 1) - (Rp.card : ℝ)) := by
          calc
            (2 - p) * (Rz.card : ℝ) + (1 - p) * (Rp.card : ℝ)
              = (Rz.card : ℝ) + (Rp.card : ℝ) + 1 * (Rz.card : ℝ) - p * (Rz.card : ℝ) - p * (Rp.card : ℝ) := by ring
            _ = (Rz.card : ℝ) + (Rp.card : ℝ) + (p * (2 : ℝ) ^ k) * (Rz.card : ℝ) - p * (Rz.card : ℝ) - p * (Rp.card : ℝ) := by
                rw [hp_mul]
            _ = ((Rz.card : ℝ) + (Rp.card : ℝ)) +
                p * ((Rz.card : ℝ) * ((2 : ℝ) ^ k - 1) - (Rp.card : ℝ)) := by ring
        rw [hcard, ← hpart, Finset.sum_union hdisj, hsum_z]
        linarith

def cubeOn {n : ℕ} (E : Finset (Fin n)) : Finset (Profile n) :=
  Finset.univ.filter (fun z : Profile n => ∀ j ∉ E, z j = false)

lemma increasingOn_cubeOn {n : ℕ} (E : Finset (Fin n)) : IncreasingOn E (cubeOn E) := by
  refine ⟨?_, ?_⟩
  · intro z hz j hj
    exact (Finset.mem_filter.mp hz).2 j hj
  · intro _ _ z' hz' _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z', hz'⟩

lemma rtree_stopping_le_twice_success {n : ℕ} {E : Finset (Fin n)} {T : RTree n}
    (hT : T.Valid E) :
    ∑ z ∈ cubeOn E, T.IT z ≤ 2 * ∑ z ∈ cubeOn E, (1 - T.FT z) := by
  have hinv := failure_invariant T hT (increasingOn_cubeOn E)
  have hpt : ∀ z ∈ cubeOn E,
      T.IT z ≤ 2 * (1 - T.FT z) + (T.FT z * (1 + T.IT z) - 1) := by
    intro z _
    have hFle := T.FT_le_one z
    rcases T.IT_zero_or_one z with hI | hI <;> rw [hI] <;> linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hsub :
      ∑ z ∈ cubeOn E, (T.FT z * (1 + T.IT z) - 1) =
      (∑ z ∈ cubeOn E, T.FT z * (1 + T.IT z)) - ((cubeOn E).card : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

end ReducedTree

/-! ### Section 4.4: From the Tree to the Subcube Comparison (Lemma 4.5) -/

section SubcubeComparison

noncomputable def dynInd {n : ℕ} (i : Fin n) (π : Policy n) (x : Profile n) : ℝ :=
  if i ∈ cleared (run π x) x then 1 else 0

def extProfile {n : ℕ} (a : Profile n) (E : Finset (Fin n)) (u : Profile n) : Profile n :=
  fun j => if j ∈ E then u j else a j

def complProfile {n : ℕ} (u : Profile n) : Profile n :=
  fun j => !u j

def xVirt {n : ℕ} (a : Profile n) (E : Finset (Fin n)) (z : Profile n) : Profile n :=
  fun j => if j ∈ E then !z j else a j

def xEval {n : ℕ} (a : Profile n) (E : Finset (Fin n)) (z : Profile n) : Profile n :=
  fun j => if j ∈ E then z j else a j

def buildRTree {n : ℕ} (i : Fin n) (a : Profile n) (E : Finset (Fin n)) : Policy n → RTree n
  | .leaf _ => .leaf
  | .query t k =>
      if decide (∃ j ∈ t.val \ E, a j = false) then
        buildRTree i a E (k false)
      else if i ∈ t.val then
        .offer (t.val ∩ E) (buildRTree i a E (k false))
      else
        .query (t.val ∩ E) (buildRTree i a E (k true)) (buildRTree i a E (k false))

lemma buildRTree_valid_aux {n : ℕ} (i : Fin n) (a : Profile n) (E : Finset (Fin n)) :
    ∀ (π : Policy n) (B : Finset (Fin n)),
      SyntacticallyNormalized π →
      π.allLabels (fun s => Disjoint s.val B) →
      (buildRTree i a E π).Valid (E \ B)
  | .leaf _, _, _, _ => trivial
  | .query t k, B, ⟨hdisj_t, hsn_t, hsn_f⟩, ⟨htB, hall_t, hall_f⟩ => by
      dsimp [buildRTree]
      have hsub : t.val ∩ E ⊆ E \ B := by
        intro j hj
        rcases Finset.mem_inter.mp hj with ⟨hjt, hjE⟩
        exact Finset.mem_sdiff.mpr ⟨hjE, Finset.disjoint_left.mp htB hjt⟩
      split_ifs with hinf hit
      · exact buildRTree_valid_aux i a E (k false) B hsn_f hall_f
      · exact ⟨hsub, buildRTree_valid_aux i a E (k false) B hsn_f hall_f⟩
      · refine ⟨hsub, ?_, buildRTree_valid_aux i a E (k false) B hsn_f hall_f⟩
        have hsdiff : (E \ B) \ (t.val ∩ E) = E \ (B ∪ (t.val ∩ E)) := by
          ext j; simp only [Finset.mem_sdiff, Finset.mem_union, not_or]; tauto
        rw [hsdiff]
        apply buildRTree_valid_aux i a E (k true) (B ∪ (t.val ∩ E)) hsn_t
        exact allLabels_mono
          (fun s (hs : Disjoint s.val B ∧ Disjoint s.val t.val) =>
            Finset.disjoint_union_right.mpr ⟨hs.1, hs.2.mono_right Finset.inter_subset_left⟩)
          _ (allLabels_and (k true) hall_t hdisj_t)

lemma buildRTree_valid {n : ℕ} (i : Fin n) (a : Profile n) (E : Finset (Fin n))
    {π : Policy n} (hπ : SyntacticallyNormalized π) :
    (buildRTree i a E π).Valid E := by
  have h := buildRTree_valid_aux i a E π ∅ hπ (by
    clear hπ
    induction π with
    | leaf _ => trivial
    | query t k ih => exact ⟨Finset.disjoint_empty_right _, ih true, ih false⟩)
  simpa using h

lemma negative_xVirt_eq_allZeroOn {n : ℕ} {t E : Finset (Fin n)} {a z : Profile n}
    (hnoinf : ¬∃ j ∈ t \ E, a j = false) :
    negative t (xVirt a E z) = allZeroOn (t ∩ E) z := by
  apply Bool.eq_iff_iff.mpr
  simp only [negative_iff, allZeroOn, decide_eq_true_iff, Finset.mem_inter, xVirt]
  constructor
  · intro h j ⟨hjt, hjE⟩
    have := h j hjt
    simp [hjE] at this
    exact this
  · intro h j hjt
    by_cases hjE : j ∈ E
    · simp [hjE, h j ⟨hjt, hjE⟩]
    · simp only [hjE, ↓reduceIte]
      by_contra hja
      have hjfalse : a j = false := by cases h' : a j <;> simp_all
      exact hnoinf ⟨j, Finset.mem_sdiff.mpr ⟨hjt, hjE⟩, hjfalse⟩

lemma stepSucc_xEval_eq_offerProb {n : ℕ} {i : Fin n} {t E : Finset (Fin n)} {a z : Profile n}
    (hiE : i ∉ E) (hai : a i = true) (hit : i ∈ t)
    (hnoinf : ¬∃ j ∈ t \ E, a j = false) :
    stepSucc i t (xEval a E z) = offerProb (t ∩ E) z := by
  have hyi : xEval a E z i = true := by simp [xEval, hiE, hai]
  unfold stepSucc offerProb
  rw [if_pos ⟨hit, hyi⟩]
  have hfilt : t.filter (fun j => !xEval a E z j) = (t ∩ E).filter (fun j => !z j) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_inter]
    by_cases hjE : j ∈ E
    · simp [xEval, hjE]
    · constructor
      · rintro ⟨hjt, hja⟩
        have hjfalse : a j = false := by
          simp only [xEval, hjE, ↓reduceIte] at hja
          cases h' : a j <;> simp_all
        exact False.elim (hnoinf ⟨j, Finset.mem_sdiff.mpr ⟨hjt, hjE⟩, hjfalse⟩)
      · rintro ⟨⟨_, hjE'⟩, _⟩
        exact False.elim (hjE hjE')
  rw [hfilt]

lemma buildRTree_IT_eq {n : ℕ} {i : Fin n} {a : Profile n} {E : Finset (Fin n)}
    (hiE : i ∉ E) (hai : a i = true) :
    ∀ (π : Policy n) (z : Profile n),
      (buildRTree i a E π).IT z = dynInd i π (xVirt a E z)
  | .leaf _, z => by
      simp [buildRTree, RTree.IT, dynInd, run_leaf, cleared]
  | .query t k, z => by
      dsimp [buildRTree]
      split_ifs with hinf hit
      · rcases decide_eq_true_iff.mp hinf with ⟨j₀, hj₀, haj₀⟩
        rcases Finset.mem_sdiff.mp hj₀ with ⟨hj₀t, hj₀E⟩
        have hneg : negative t.val (xVirt a E z) = false := by
          rw [negative_eq_false_iff]
          exact ⟨j₀, hj₀t, by simp [xVirt, hj₀E, haj₀]⟩
        rw [buildRTree_IT_eq hiE hai (k false) z]
        simp [dynInd, run_query, hneg, cleared]
      · have hnoinf : ¬∃ j ∈ t.val \ E, a j = false := by simpa using hinf
        have hneg_eq := negative_xVirt_eq_allZeroOn (z := z) hnoinf
        dsimp [RTree.IT]
        cases hz0 : allZeroOn (t.val ∩ E) z
        · have hneg : negative t.val (xVirt a E z) = false := by rw [hneg_eq, hz0]
          simp [dynInd, run_query, hneg, cleared, buildRTree_IT_eq hiE hai (k false) z]
        · have hneg : negative t.val (xVirt a E z) = true := by rw [hneg_eq, hz0]
          simp [dynInd, run_query, hneg, cleared, hit]
      · have hnoinf : ¬∃ j ∈ t.val \ E, a j = false := by simpa using hinf
        have hneg_eq := negative_xVirt_eq_allZeroOn (z := z) hnoinf
        dsimp [RTree.IT]
        cases hz0 : allZeroOn (t.val ∩ E) z
        · have hneg : negative t.val (xVirt a E z) = false := by rw [hneg_eq, hz0]
          simp [dynInd, run_query, hneg, cleared, buildRTree_IT_eq hiE hai (k false) z]
        · have hneg : negative t.val (xVirt a E z) = true := by rw [hneg_eq, hz0]
          simp [dynInd, run_query, hneg, cleared, hit, buildRTree_IT_eq hiE hai (k true) z]

lemma buildRTree_allocFail_le_FT {n : ℕ} {i : Fin n} {a : Profile n} {E : Finset (Fin n)}
    (hiE : i ∉ E) (hai : a i = true) :
    ∀ (π : Policy n) (z : Profile n),
      allocFail i (run π (xVirt a E z)) (xEval a E z) ≤ (buildRTree i a E π).FT z
  | .leaf _, z => by
      simp [buildRTree, RTree.FT, run_leaf, allocFail]
  | .query t k, z => by
      dsimp [buildRTree]
      split_ifs with hinf hit
      · rcases decide_eq_true_iff.mp hinf with ⟨j₀, hj₀, haj₀⟩
        rcases Finset.mem_sdiff.mp hj₀ with ⟨hj₀t, hj₀E⟩
        have hneg : negative t.val (xVirt a E z) = false := by
          rw [negative_eq_false_iff]
          exact ⟨j₀, hj₀t, by simp [xVirt, hj₀E, haj₀]⟩
        rw [run_query, hneg, allocFail]
        calc
          (1 - stepSucc i t.val (xEval a E z)) * allocFail i (run (k false) (xVirt a E z)) (xEval a E z)
            ≤ 1 * allocFail i (run (k false) (xVirt a E z)) (xEval a E z) := by
                apply mul_le_mul_of_nonneg_right
                · linarith [stepSucc_nonneg i t.val (xEval a E z)]
                · exact allocFail_nonneg i _ _
          _ = allocFail i (run (k false) (xVirt a E z)) (xEval a E z) := one_mul _
          _ ≤ (buildRTree i a E (k false)).FT z := buildRTree_allocFail_le_FT hiE hai (k false) z
      · have hnoinf : ¬∃ j ∈ t.val \ E, a j = false := by simpa using hinf
        have hneg_eq := negative_xVirt_eq_allZeroOn (z := z) hnoinf
        have hstep_eq := stepSucc_xEval_eq_offerProb (z := z) hiE hai hit hnoinf
        dsimp [RTree.FT]
        have h1_nonneg : 0 ≤ 1 - offerProb (t.val ∩ E) z :=
          sub_nonneg.mpr (offerProb_le_one _ _)
        cases hz0 : allZeroOn (t.val ∩ E) z
        · have hneg : negative t.val (xVirt a E z) = false := by rw [hneg_eq, hz0]
          rw [run_query, hneg, allocFail, hstep_eq]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact mul_le_mul_of_nonneg_left
            (buildRTree_allocFail_le_FT hiE hai (k false) z) h1_nonneg
        · have hneg : negative t.val (xVirt a E z) = true := by rw [hneg_eq, hz0]
          rw [run_query, hneg, allocFail, hstep_eq]
          simp only [↓reduceIte]
          calc
            (1 - offerProb (t.val ∩ E) z) * allocFail i (run (k true) (xVirt a E z)) (xEval a E z)
              ≤ (1 - offerProb (t.val ∩ E) z) * 1 :=
                  mul_le_mul_of_nonneg_left (allocFail_le_one i _ _) h1_nonneg
            _ = 1 - offerProb (t.val ∩ E) z := mul_one _
      · have hnoinf : ¬∃ j ∈ t.val \ E, a j = false := by simpa using hinf
        have hneg_eq := negative_xVirt_eq_allZeroOn (z := z) hnoinf
        have hstep0 : stepSucc i t.val (xEval a E z) = 0 := by simp [stepSucc, hit]
        dsimp [RTree.FT]
        cases hz0 : allZeroOn (t.val ∩ E) z
        · have hneg : negative t.val (xVirt a E z) = false := by rw [hneg_eq, hz0]
          rw [run_query, hneg, allocFail, hstep0]
          simpa using buildRTree_allocFail_le_FT hiE hai (k false) z
        · have hneg : negative t.val (xVirt a E z) = true := by rw [hneg_eq, hz0]
          rw [run_query, hneg, allocFail, hstep0]
          simpa using buildRTree_allocFail_le_FT hiE hai (k true) z

lemma sum_univ_ext_eq_mul_cubeOn {n : ℕ} (a : Profile n) (E : Finset (Fin n))
    (G : Profile n → Profile n → ℝ) :
    (∑ u : Profile n, G (extProfile a E u) (extProfile a E (complProfile u))) =
    ((cubeOn Eᶜ).card : ℝ) * ∑ z ∈ cubeOn E, G (xVirt a E z) (xEval a E z) := by
  let glue : Profile n × Profile n → Profile n :=
    fun p j => if j ∈ E then !p.1 j else p.2 j
  have hbij :
      ∑ p ∈ cubeOn E ×ˢ cubeOn Eᶜ,
        G (extProfile a E (glue p)) (extProfile a E (complProfile (glue p))) =
      ∑ u : Profile n, G (extProfile a E u) (extProfile a E (complProfile u)) := by
    apply Finset.sum_bij (fun p _ => glue p)
    · intro _ _; exact Finset.mem_univ _
    · rintro ⟨z₁, w₁⟩ hp₁ ⟨z₂, w₂⟩ hp₂ heq
      rcases Finset.mem_product.mp hp₁ with ⟨hz₁, hw₁⟩
      rcases Finset.mem_product.mp hp₂ with ⟨hz₂, hw₂⟩
      have hz₁out := (Finset.mem_filter.mp hz₁).2
      have hz₂out := (Finset.mem_filter.mp hz₂).2
      have hw₁out := (Finset.mem_filter.mp hw₁).2
      have hw₂out := (Finset.mem_filter.mp hw₂).2
      ext j
      · by_cases hjE : j ∈ E
        · have hj := congr_fun heq j
          simp [glue, hjE] at hj
          exact hj
        · rw [hz₁out j hjE, hz₂out j hjE]
      · by_cases hjE : j ∈ E
        · have hjEc : j ∉ Eᶜ := by simp [hjE]
          rw [hw₁out j hjEc, hw₂out j hjEc]
        · have hj := congr_fun heq j
          simpa [glue, hjE] using hj
    · intro u _
      refine ⟨(fun j => if j ∈ E then !u j else false,
               fun j => if j ∈ E then false else u j), ?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          intro j hjE; simp [hjE]
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          intro j hjEc
          have hjE : j ∈ E := by simpa using hjEc
          simp [hjE]
      · ext j
        by_cases hjE : j ∈ E <;> simp [glue, hjE]
    · intros; rfl
  rw [← hbij, Finset.sum_product]
  have hinner : ∀ z ∈ cubeOn E,
      ∑ w ∈ cubeOn Eᶜ,
        G (extProfile a E (glue (z, w))) (extProfile a E (complProfile (glue (z, w)))) =
      ((cubeOn Eᶜ).card : ℝ) * G (xVirt a E z) (xEval a E z) := by
    intro z _
    have h1 : ∀ w, extProfile a E (glue (z, w)) = xVirt a E z := by
      intro w; ext j; by_cases hjE : j ∈ E <;> simp [extProfile, glue, xVirt, hjE]
    have h2 : ∀ w, extProfile a E (complProfile (glue (z, w))) = xEval a E z := by
      intro w; ext j; by_cases hjE : j ∈ E <;> simp [extProfile, complProfile, glue, xEval, hjE]
    simp_rw [h1, h2, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]

lemma subcube_fixed_healthy {n : ℕ} {π : Policy n} (hπ : SyntacticallyNormalized π)
    {E : Finset (Fin n)} {a : Profile n} {i : Fin n}
    (hiE : i ∉ E) (hai : a i = true) :
    (∑ u : Profile n, dynInd i π (extProfile a E u)) ≤
    2 * ∑ u : Profile n, thinClearProb i (run π (extProfile a E u))
      (extProfile a E (complProfile u)) := by
  rw [sum_univ_ext_eq_mul_cubeOn a E (fun x _ => dynInd i π x),
      sum_univ_ext_eq_mul_cubeOn a E (fun x y => thinClearProb i (run π x) y),
      ← mul_assoc, mul_comm (2 : ℝ), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  let T := buildRTree i a E π
  calc
    ∑ z ∈ cubeOn E, dynInd i π (xVirt a E z)
      = ∑ z ∈ cubeOn E, T.IT z := by
          apply Finset.sum_congr rfl
          intro z _
          exact (buildRTree_IT_eq hiE hai π z).symm
    _ ≤ 2 * ∑ z ∈ cubeOn E, (1 - T.FT z) :=
          rtree_stopping_le_twice_success (buildRTree_valid i a E hπ)
    _ ≤ 2 * ∑ z ∈ cubeOn E, thinClearProb i (run π (xVirt a E z)) (xEval a E z) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro z _
          unfold thinClearProb
          linarith [buildRTree_allocFail_le_FT hiE hai π z]

lemma update_same_bool {n : ℕ} (x : Profile n) (i : Fin n) (b : Bool) :
    Function.update x i b i = b := dif_pos rfl

lemma update_noteq_bool {n : ℕ} (x : Profile n) {i j : Fin n} (b : Bool) (h : j ≠ i) :
    Function.update x i b j = x j := dif_neg h

lemma allocFail_update_false_le {n : ℕ} :
    ∀ (π : Policy n), SyntacticallyNormalized π →
      ∀ (i : Fin n) (x y : Profile n),
        allocFail i (run π (Function.update x i false)) y ≤ allocFail i (run π x) y
  | .leaf _, _, _, _, _ => le_rfl
  | .query t k, ⟨hdisj, hsn_t, hsn_f⟩, i, x, y => by
      have h1_nonneg : 0 ≤ 1 - stepSucc i t.val y :=
        sub_nonneg.mpr (stepSucc_le_one i t.val y)
      by_cases hit : i ∈ t.val
      · have hneg0 : negative t.val (Function.update x i false) = false := by
          rw [negative_eq_false_iff]
          exact ⟨i, hit, update_same_bool x i false⟩
        rw [run_query, hneg0, run_query, allocFail, allocFail]
        cases hneg : negative t.val x
        · exact mul_le_mul_of_nonneg_left
            (allocFail_update_false_le (k false) hsn_f i x y) h1_nonneg
        · have hall_not_mem : ∀ s ∈ run (k true) x, i ∉ s := by
            intro s hs hsi
            have hds := allLabels_mem_run (p := fun u => Disjoint u t.val) (k true) hdisj x s hs
            exact Finset.disjoint_left.mp hds hsi hit
          rw [allocFail_eq_one_of_forall_not_mem i (run (k true) x) y hall_not_mem]
          exact mul_le_mul_of_nonneg_left (allocFail_le_one i _ _) h1_nonneg
      · have hneg_eq : negative t.val (Function.update x i false) = negative t.val x := by
          apply Bool.eq_iff_iff.mpr
          simp only [negative_iff]
          constructor <;> intro h j hj
          · have hji : j ≠ i := fun h' => hit (h' ▸ hj)
            simpa [update_noteq_bool x false hji] using h j hj
          · have hji : j ≠ i := fun h' => hit (h' ▸ hj)
            simpa [update_noteq_bool x false hji] using h j hj
        rw [run_query, run_query, hneg_eq, allocFail, allocFail]
        cases negative t.val x
        · exact mul_le_mul_of_nonneg_left
            (allocFail_update_false_le (k false) hsn_f i x y) h1_nonneg
        · exact mul_le_mul_of_nonneg_left
            (allocFail_update_false_le (k true) hsn_t i x y) h1_nonneg

theorem subcube_comparison {n : ℕ} {π : Policy n} (hπ : SyntacticallyNormalized π)
    (E : Finset (Fin n)) (a : Profile n) (i : Fin n) :
    (∑ u : Profile n, dynInd i π (extProfile a E u)) ≤
    2 * ∑ u : Profile n, thinClearProb i (run π (extProfile a E u))
      (extProfile a E (complProfile u)) := by
  by_cases hiE : i ∈ E
  · let E' := E.erase i
    let aH := Function.update a i true
    have hiE' : i ∉ E' := Finset.notMem_erase i E
    have haHi : aH i = true := update_same_bool a i true
    have hface := subcube_fixed_healthy hπ hiE' haHi
    let Ut := Finset.univ.filter (fun u : Profile n => u i = true)
    let Uf := Finset.univ.filter (fun u : Profile n => u i = false)
    have hpart : Ut ∪ Uf = Finset.univ := by
      ext u; simp only [Ut, Uf, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases u i <;> simp
    have hdisj : Disjoint Ut Uf :=
      Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by rw [h1] at h2; cases h2)
    let flip : Profile n → Profile n := fun u => Function.update u i (!u i)
    have hext_flip : ∀ u : Profile n, extProfile aH E' (flip u) = extProfile aH E' u := by
      intro u; ext j
      by_cases hjE' : j ∈ E'
      · have hji : j ≠ i := Finset.ne_of_mem_erase hjE'
        simp [extProfile, hjE', flip, update_noteq_bool u (!u i) hji]
      · simp [extProfile, hjE']
    have hext_compl_flip : ∀ u : Profile n,
        extProfile aH E' (complProfile (flip u)) = extProfile aH E' (complProfile u) := by
      intro u; ext j
      by_cases hjE' : j ∈ E'
      · have hji : j ≠ i := Finset.ne_of_mem_erase hjE'
        simp [extProfile, complProfile, hjE', flip, update_noteq_bool u (!u i) hji]
      · simp [extProfile, hjE']
    have hbij_Ut_Uf : ∀ f : Profile n → ℝ,
        (∀ u, f (flip u) = f u) → ∑ u ∈ Uf, f u = ∑ u ∈ Ut, f u := by
      intro f hf
      symm
      apply Finset.sum_bij (fun u _ => flip u)
      · intro u hu
        have hui : u i = true := (Finset.mem_filter.mp hu).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [flip, hui]⟩
      · intro u₁ _ u₂ _ heq
        ext j
        by_cases hji : j = i
        · subst hji
          have h := congr_fun heq j
          simpa [flip] using h
        · have h := congr_fun heq j
          simpa [flip, update_noteq_bool _ _ hji] using h
      · intro u hu
        have hui : u i = false := (Finset.mem_filter.mp hu).2
        refine ⟨flip u, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          by simp [flip, hui]⟩, ?_⟩
        ext j
        by_cases hji : j = i
        · subst hji; simp [flip, hui]
        · simp [flip, update_noteq_bool _ _ hji]
      · intro u _; exact (hf u).symm
    have hlhs_face :
        (∑ u : Profile n, dynInd i π (extProfile aH E' u)) =
        2 * ∑ u ∈ Ut, dynInd i π (extProfile aH E' u) := by
      rw [← hpart, Finset.sum_union hdisj,
          hbij_Ut_Uf (fun u => dynInd i π (extProfile aH E' u)) (fun u => by rw [hext_flip])]
      ring
    have hrhs_face :
        (∑ u : Profile n, thinClearProb i (run π (extProfile aH E' u))
          (extProfile aH E' (complProfile u))) =
        2 * ∑ u ∈ Uf, thinClearProb i (run π (extProfile aH E' u))
          (extProfile aH E' (complProfile u)) := by
      rw [← hpart, Finset.sum_union hdisj,
          ← hbij_Ut_Uf (fun u => thinClearProb i (run π (extProfile aH E' u))
            (extProfile aH E' (complProfile u))) (fun u => by rw [hext_flip, hext_compl_flip])]
      ring
    have hhalf :
        (∑ u ∈ Ut, dynInd i π (extProfile aH E' u)) ≤
        2 * ∑ u ∈ Uf, thinClearProb i (run π (extProfile aH E' u))
          (extProfile aH E' (complProfile u)) := by
      linarith
    have hlhs_eq :
        (∑ u : Profile n, dynInd i π (extProfile a E u)) =
        ∑ u ∈ Ut, dynInd i π (extProfile aH E' u) := by
      rw [← hpart, Finset.sum_union hdisj]
      have h0 : ∑ u ∈ Uf, dynInd i π (extProfile a E u) = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        have hui : u i = false := (Finset.mem_filter.mp hu).2
        have hxi : extProfile a E u i = false := by simp [extProfile, hiE, hui]
        unfold dynInd
        split_ifs with hcl
        · have := mem_cleared_imp_true hcl
          rw [hxi] at this; cases this
        · rfl
      rw [h0, add_zero]
      apply Finset.sum_congr rfl
      intro u hu
      have hui : u i = true := (Finset.mem_filter.mp hu).2
      congr 1
      ext j
      by_cases hji : j = i
      · subst hji; simp [extProfile, hiE, hui, E', aH, update_same_bool]
      · by_cases hjE : j ∈ E
        · have hjE' : j ∈ E' := Finset.mem_erase.mpr ⟨hji, hjE⟩
          simp [extProfile, hjE, hjE']
        · have hjE' : j ∉ E' := fun h => hjE (Finset.mem_of_mem_erase h)
          simp [extProfile, hjE, hjE', aH, update_noteq_bool a true hji]
    have hrhs_le :
        (∑ u ∈ Uf, thinClearProb i (run π (extProfile aH E' u))
          (extProfile aH E' (complProfile u))) ≤
        ∑ u : Profile n, thinClearProb i (run π (extProfile a E u))
          (extProfile a E (complProfile u)) := by
      rw [← hpart, Finset.sum_union hdisj]
      have hUt_nonneg :
          0 ≤ ∑ u ∈ Ut, thinClearProb i (run π (extProfile a E u))
            (extProfile a E (complProfile u)) :=
        Finset.sum_nonneg (fun u _ => thinClearProb_nonneg _ _ _)
      have hUf_le :
          (∑ u ∈ Uf, thinClearProb i (run π (extProfile aH E' u))
            (extProfile aH E' (complProfile u))) ≤
          ∑ u ∈ Uf, thinClearProb i (run π (extProfile a E u))
            (extProfile a E (complProfile u)) := by
        apply Finset.sum_le_sum
        intro u hu
        have hui : u i = false := (Finset.mem_filter.mp hu).2
        have heval_eq : extProfile a E (complProfile u) = extProfile aH E' (complProfile u) := by
          ext j
          by_cases hji : j = i
          · subst hji; simp [extProfile, complProfile, hiE, hui, E', aH, update_same_bool]
          · by_cases hjE : j ∈ E
            · have hjE' : j ∈ E' := Finset.mem_erase.mpr ⟨hji, hjE⟩
              simp [extProfile, hjE, hjE']
            · have hjE' : j ∉ E' := fun h => hjE (Finset.mem_of_mem_erase h)
              simp [extProfile, hjE, hjE', aH, update_noteq_bool a true hji]
        have hvirt_eq : extProfile a E u = Function.update (extProfile aH E' u) i false := by
          ext j
          by_cases hji : j = i
          · subst hji; simp [extProfile, hiE, hui, update_same_bool]
          · rw [update_noteq_bool _ false hji]
            by_cases hjE : j ∈ E
            · have hjE' : j ∈ E' := Finset.mem_erase.mpr ⟨hji, hjE⟩
              simp [extProfile, hjE, hjE']
            · have hjE' : j ∉ E' := fun h => hjE (Finset.mem_of_mem_erase h)
              simp [extProfile, hjE, hjE', aH, update_noteq_bool a true hji]
        rw [heval_eq, hvirt_eq]
        unfold thinClearProb
        linarith [allocFail_update_false_le π hπ i (extProfile aH E' u)
          (extProfile aH E' (complProfile u))]
      linarith
    linarith
  · cases hai : a i
    · have hlhs0 : ∑ u : Profile n, dynInd i π (extProfile a E u) = 0 := by
        apply Finset.sum_eq_zero
        intro u _
        have hxi : extProfile a E u i = false := by simp [extProfile, hiE, hai]
        unfold dynInd
        split_ifs with hcl
        · have := mem_cleared_imp_true hcl
          rw [hxi] at this; cases this
        · rfl
      rw [hlhs0]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => thinClearProb_nonneg _ _ _))
    · exact subcube_fixed_healthy hπ hiE hai

end SubcubeComparison

/-! ### Section 4.5: Returning to Product Priors (Proposition 4.6) -/

section ProductPriors

def swapL {n : ℕ} (w x y : Profile n) : Profile n :=
  fun j => if w j then y j else x j

def swapR {n : ℕ} (w x y : Profile n) : Profile n :=
  fun j => if w j then x j else y j

lemma profileMass_mul_swap {n : ℕ} (J : Instance n) (w x y : Profile n) :
    profileMass J (swapL w x y) * profileMass J (swapR w x y) =
    profileMass J x * profileMass J y := by
  unfold profileMass
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  dsimp [swapL, swapR]
  by_cases hwj : w j = true <;> simp [hwj, mul_comm]

lemma sum_prod_swap_eq {n : ℕ} (J : Instance n) (w : Profile n)
    (G : Profile n → Profile n → ℝ) :
    (∑ x : Profile n, ∑ y : Profile n,
      profileMass J x * profileMass J y * G (swapL w x y) (swapR w x y)) =
    ∑ x : Profile n, ∑ y : Profile n,
      profileMass J x * profileMass J y * G x y := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let sw : Profile n × Profile n ≃ Profile n × Profile n :=
    { toFun := fun p => (swapL w p.1 p.2, swapR w p.1 p.2)
      invFun := fun p => (swapL w p.1 p.2, swapR w p.1 p.2)
      left_inv := fun ⟨x, y⟩ => by
        ext j <;> (dsimp [swapL, swapR]; cases w j <;> rfl)
      right_inv := fun ⟨x, y⟩ => by
        ext j <;> (dsimp [swapL, swapR]; cases w j <;> rfl) }
  rw [← sw.sum_comp (fun p : Profile n × Profile n =>
    profileMass J p.1 * profileMass J p.2 * G p.1 p.2)]
  apply Finset.sum_congr rfl
  rintro ⟨x, y⟩ _
  simp only [sw, Equiv.coe_fn_mk, profileMass_mul_swap J w x y]

lemma sum_swap_eq_sum_ext {n : ℕ} (x y : Profile n) (G : Profile n → Profile n → ℝ) :
    (∑ w : Profile n, G (swapL w x y) (swapR w x y)) =
    ∑ u : Profile n, G (extProfile x (Finset.univ.filter (fun j => x j ≠ y j)) u)
      (extProfile x (Finset.univ.filter (fun j => x j ≠ y j)) (complProfile u)) := by
  let E := Finset.univ.filter (fun j => x j ≠ y j)
  let φ : Profile n ≃ Profile n :=
    { toFun := fun w j => if x j = y j then w j else if w j then y j else x j
      invFun := fun w j => if x j = y j then w j else if w j then y j else x j
      left_inv := fun w => by
        ext j
        cases hxj : x j <;> cases hyj : y j <;> cases hwj : w j <;> simp_all
      right_inv := fun w => by
        ext j
        cases hxj : x j <;> cases hyj : y j <;> cases hwj : w j <;> simp_all }
  rw [← φ.sum_comp (fun u => G (extProfile x E u) (extProfile x E (complProfile u)))]
  apply Finset.sum_congr rfl
  intro w _
  have h1 : extProfile x E (φ w) = swapL w x y := by
    ext j
    simp only [extProfile, E, Finset.mem_filter, Finset.mem_univ, true_and, φ,
      Equiv.coe_fn_mk, swapL]
    cases hxj : x j <;> cases hyj : y j <;> cases hwj : w j <;> simp_all
  have h2 : extProfile x E (complProfile (φ w)) = swapR w x y := by
    ext j
    simp only [extProfile, complProfile, E, Finset.mem_filter, Finset.mem_univ, true_and, φ,
      Equiv.coe_fn_mk, swapR]
    cases hxj : x j <;> cases hyj : y j <;> cases hwj : w j <;> simp_all
  rw [h1, h2]

theorem prop_4_6 {n : ℕ} (J : Instance n) {π : Policy n} (hπ : SyntacticallyNormalized π)
    (i : Fin n) :
    (∑ x : Profile n, profileMass J x * dynInd i π x) ≤
    2 * ∑ x : Profile n, ∑ y : Profile n,
      profileMass J x * profileMass J y * thinClearProb i (run π x) y := by
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hcard : (∑ _w : Profile n, (1 : ℝ)) = (2 : ℝ) ^ n := by
    simp [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have hlhs :
      (2 : ℝ) ^ n * (∑ x : Profile n, profileMass J x * dynInd i π x) =
      ∑ x : Profile n, ∑ y : Profile n,
        profileMass J x * profileMass J y *
        (∑ w : Profile n, dynInd i π (swapL w x y)) := by
    have hsum_y :
        (∑ x : Profile n, profileMass J x * dynInd i π x) =
        ∑ x : Profile n, ∑ y : Profile n,
          profileMass J x * profileMass J y * dynInd i π x := by
      apply Finset.sum_congr rfl
      intro x _
      calc
        profileMass J x * dynInd i π x
          = profileMass J x * (∑ y : Profile n, profileMass J y) * dynInd i π x := by
              rw [sum_profileMass J, mul_one]
        _ = ∑ y : Profile n, profileMass J x * profileMass J y * dynInd i π x := by
              rw [Finset.mul_sum, Finset.sum_mul]
    calc
      (2 : ℝ) ^ n * (∑ x : Profile n, profileMass J x * dynInd i π x)
        = (∑ _w : Profile n, (1 : ℝ)) *
          (∑ x : Profile n, ∑ y : Profile n, profileMass J x * profileMass J y * dynInd i π x) := by
            rw [hcard, hsum_y]
      _ = ∑ w : Profile n, ∑ x : Profile n, ∑ y : Profile n,
            profileMass J x * profileMass J y * dynInd i π x := by
            rw [Finset.sum_mul]; simp [one_mul]
      _ = ∑ w : Profile n, ∑ x : Profile n, ∑ y : Profile n,
            profileMass J x * profileMass J y * dynInd i π (swapL w x y) := by
            apply Finset.sum_congr rfl
            intro w _
            exact (sum_prod_swap_eq J w (fun x _ => dynInd i π x)).symm
      _ = ∑ x : Profile n, ∑ y : Profile n, ∑ w : Profile n,
            profileMass J x * profileMass J y * dynInd i π (swapL w x y) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro x _
            rw [Finset.sum_comm]
      _ = ∑ x : Profile n, ∑ y : Profile n,
            profileMass J x * profileMass J y *
            (∑ w : Profile n, dynInd i π (swapL w x y)) := by
            apply Finset.sum_congr rfl; intro x _
            apply Finset.sum_congr rfl; intro y _
            rw [← Finset.mul_sum]
  have hrhs :
      (2 : ℝ) ^ n * (∑ x : Profile n, ∑ y : Profile n,
        profileMass J x * profileMass J y * thinClearProb i (run π x) y) =
      ∑ x : Profile n, ∑ y : Profile n,
        profileMass J x * profileMass J y *
        (∑ w : Profile n, thinClearProb i (run π (swapL w x y)) (swapR w x y)) := by
    calc
      (2 : ℝ) ^ n * (∑ x : Profile n, ∑ y : Profile n,
          profileMass J x * profileMass J y * thinClearProb i (run π x) y)
        = (∑ _w : Profile n, (1 : ℝ)) * (∑ x : Profile n, ∑ y : Profile n,
            profileMass J x * profileMass J y * thinClearProb i (run π x) y) := by
            rw [hcard]
      _ = ∑ w : Profile n, ∑ x : Profile n, ∑ y : Profile n,
            profileMass J x * profileMass J y * thinClearProb i (run π x) y := by
            rw [Finset.sum_mul]; simp [one_mul]
      _ = ∑ w : Profile n, ∑ x : Profile n, ∑ y : Profile n,
            profileMass J x * profileMass J y *
            thinClearProb i (run π (swapL w x y)) (swapR w x y) := by
            apply Finset.sum_congr rfl
            intro w _
            exact (sum_prod_swap_eq J w (fun x y => thinClearProb i (run π x) y)).symm
      _ = ∑ x : Profile n, ∑ y : Profile n, ∑ w : Profile n,
            profileMass J x * profileMass J y *
            thinClearProb i (run π (swapL w x y)) (swapR w x y) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro x _
            rw [Finset.sum_comm]
      _ = ∑ x : Profile n, ∑ y : Profile n,
            profileMass J x * profileMass J y *
            (∑ w : Profile n, thinClearProb i (run π (swapL w x y)) (swapR w x y)) := by
            apply Finset.sum_congr rfl; intro x _
            apply Finset.sum_congr rfl; intro y _
            rw [← Finset.mul_sum]
  suffices hmul :
      (2 : ℝ) ^ n * (∑ x : Profile n, profileMass J x * dynInd i π x) ≤
      (2 : ℝ) ^ n * (2 * ∑ x : Profile n, ∑ y : Profile n,
        profileMass J x * profileMass J y * thinClearProb i (run π x) y) by
    exact le_of_mul_le_mul_left hmul h2n_pos
  rw [hlhs, mul_left_comm ((2 : ℝ) ^ n) 2 _, hrhs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  rw [mul_left_comm (2 : ℝ)]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (profileMass_nonneg J x) (profileMass_nonneg J y))
  rw [sum_swap_eq_sum_ext x y (fun a _ => dynInd i π a),
      sum_swap_eq_sum_ext x y (fun a b => thinClearProb i (run π a) b)]
  exact subcube_comparison hπ (Finset.univ.filter (fun j => x j ≠ y j)) x i

end ProductPriors

/-! ### Section 4.6: Completing the Welfare Comparison (Theorem 3.2) -/

section WelfareBound

lemma reward_eq_sum_indicator {n : ℕ} (J : Instance n) (T : Allocation n) (x : Profile n) :
    reward J T x = ∑ i : Fin n, J.u i * (if i ∈ cleared T x then (1 : ℝ) else 0) := by
  unfold reward
  calc
    ∑ i ∈ cleared T x, J.u i
      = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ∈ cleared T x), J.u i := by
          congr 1; ext i; simp
    _ = ∑ i : Fin n, (if i ∈ cleared T x then J.u i else 0) := Finset.sum_filter _ _
    _ = ∑ i : Fin n, J.u i * (if i ∈ cleared T x then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro i _; split_ifs <;> ring

lemma dynamicWelfare_eq_sum_dynInd {n : ℕ} (J : Instance n) (π : Policy n) :
    dynamicWelfare J π =
    ∑ i : Fin n, J.u i * (∑ x : Profile n, profileMass J x * dynInd i π x) := by
  unfold dynamicWelfare expectation dynInd
  calc
    ∑ x : Profile n, profileMass J x * reward J (run π x) x
      = ∑ x : Profile n, ∑ i : Fin n,
          profileMass J x * (J.u i * (if i ∈ cleared (run π x) x then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [reward_eq_sum_indicator, Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ x : Profile n,
          J.u i * (profileMass J x * (if i ∈ cleared (run π x) x then (1 : ℝ) else 0)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro x _; ring
    _ = ∑ i : Fin n, J.u i *
          (∑ x : Profile n, profileMass J x * (if i ∈ cleared (run π x) x then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl; intro i _
        rw [← Finset.mul_sum]

lemma avg_thin_static_le_optStatic {n B : ℕ} {J : Instance n} {F : FeasibleFamily J B}
    (hF : DownwardClosed F) {π : Policy n} (hπ : Feasible F π) :
    (∑ i : Fin n, J.u i * (∑ x : Profile n, ∑ y : Profile n,
      profileMass J x * profileMass J y * thinClearProb i (run π x) y)) ≤
    optStatic F := by
  have hbdd := optStatic_bddAbove F
  have hper_x : ∀ x : Profile n,
      (∑ i : Fin n, J.u i * (∑ y : Profile n,
        profileMass J y * thinClearProb i (run π x) y)) ≤ optStatic F := by
    intro x
    let P := run π x
    let Mcard : ℝ := ((2 : ℝ) ^ n) ^ P.length
    have hMpos : 0 < Mcard := by positivity
    suffices hmul :
        Mcard * (∑ i : Fin n, J.u i * (∑ y : Profile n,
          profileMass J y * thinClearProb i P y)) ≤ Mcard * optStatic F by
      exact le_of_mul_le_mul_left hmul hMpos
    have hlhs :
        (∑ masks : Fin P.length → Finset (Fin n), staticWelfare J (thinAlloc P masks)) =
        Mcard * (∑ i : Fin n, J.u i * (∑ y : Profile n,
          profileMass J y * thinClearProb i P y)) := by
      unfold staticWelfare expectation
      have hexpand : ∀ masks : Fin P.length → Finset (Fin n),
          (∑ y : Profile n, profileMass J y * reward J (thinAlloc P masks) y) =
          ∑ y : Profile n, ∑ i : Fin n,
            J.u i * profileMass J y *
            (if i ∈ cleared (thinAlloc P masks) y then (1 : ℝ) else 0) := by
        intro masks
        apply Finset.sum_congr rfl; intro y _
        rw [reward_eq_sum_indicator, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      simp_rw [hexpand]
      rw [Finset.sum_comm]
      have hswap2 :
          (∑ y : Profile n, ∑ masks : Fin P.length → Finset (Fin n), ∑ i : Fin n,
            J.u i * profileMass J y *
            (if i ∈ cleared (thinAlloc P masks) y then (1 : ℝ) else 0)) =
          ∑ y : Profile n, ∑ i : Fin n,
            J.u i * profileMass J y * (Mcard * thinClearProb i P y) := by
        apply Finset.sum_congr rfl; intro y _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        rw [← Finset.mul_sum, sum_masks_clear i P y]
      rw [hswap2, Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro y _; ring
    rw [← hlhs]
    have hle : ∀ masks : Fin P.length → Finset (Fin n),
        staticWelfare J (thinAlloc P masks) ≤ optStatic F := by
      intro masks
      have hmem : thinAlloc P masks ∈ F.allocations :=
        hF P (hπ x) (thinAlloc P masks) (thinAlloc_refines P masks)
      exact le_csSup hbdd ⟨thinAlloc P masks, hmem, rfl⟩
    have hcard_masks :
        (∑ _masks : Fin P.length → Finset (Fin n), (1 : ℝ)) = Mcard := by
      simp [Mcard, Fintype.card_pi, Fintype.card_finset, Fintype.card_fin, Finset.prod_const]
    calc
      ∑ masks : Fin P.length → Finset (Fin n), staticWelfare J (thinAlloc P masks)
        ≤ ∑ _masks : Fin P.length → Finset (Fin n), optStatic F :=
          Finset.sum_le_sum (fun masks _ => hle masks)
      _ = (∑ _masks : Fin P.length → Finset (Fin n), (1 : ℝ)) * optStatic F := by
          rw [Finset.sum_mul]; simp [one_mul]
      _ = Mcard * optStatic F := by rw [hcard_masks]
  have hrearr :
      (∑ i : Fin n, J.u i * (∑ x : Profile n, ∑ y : Profile n,
        profileMass J x * profileMass J y * thinClearProb i (run π x) y)) =
      ∑ x : Profile n, profileMass J x *
        (∑ i : Fin n, J.u i * (∑ y : Profile n,
          profileMass J y * thinClearProb i (run π x) y)) := by
    have h1 : ∀ i : Fin n,
        J.u i * (∑ x : Profile n, ∑ y : Profile n,
          profileMass J x * profileMass J y * thinClearProb i (run π x) y) =
        ∑ x : Profile n, profileMass J x *
          (J.u i * (∑ y : Profile n, profileMass J y * thinClearProb i (run π x) y)) := by
      intro i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro y _; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    rw [← Finset.mul_sum]
  rw [hrearr]
  calc
    ∑ x : Profile n, profileMass J x *
        (∑ i : Fin n, J.u i * (∑ y : Profile n,
          profileMass J y * thinClearProb i (run π x) y))
      ≤ ∑ x : Profile n, profileMass J x * optStatic F := by
          apply Finset.sum_le_sum; intro x _
          exact mul_le_mul_of_nonneg_left (hper_x x) (profileMass_nonneg J x)
    _ = (∑ x : Profile n, profileMass J x) * optStatic F := by rw [← Finset.sum_mul]
    _ = optStatic F := by rw [sum_profileMass J, one_mul]

lemma dynamicWelfare_le_two_optStatic {n B : ℕ} {J : Instance n} {F : FeasibleFamily J B}
    (hF : DownwardClosed F) {π : Policy n} (hπ : Feasible F π) :
    dynamicWelfare J π ≤ 2 * optStatic F := by
  let π' := normalize π
  have hπ'_feas : Feasible F π' := normalize_feasible hF hπ
  have hπ'_sn : SyntacticallyNormalized π' := normalize_syntacticallyNormalized π
  rw [← normalize_dynamicWelfare J π, dynamicWelfare_eq_sum_dynInd J π']
  calc
    ∑ i : Fin n, J.u i * (∑ x : Profile n, profileMass J x * dynInd i π' x)
      ≤ ∑ i : Fin n, J.u i * (2 * ∑ x : Profile n, ∑ y : Profile n,
          profileMass J x * profileMass J y * thinClearProb i (run π' x) y) := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_left (prop_4_6 J hπ'_sn i) (J.u_nonneg i)
    _ = 2 * (∑ i : Fin n, J.u i * (∑ x : Profile n, ∑ y : Profile n,
          profileMass J x * profileMass J y * thinClearProb i (run π' x) y)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ 2 * optStatic F :=
          mul_le_mul_of_nonneg_left (avg_thin_static_le_optStatic hF hπ'_feas) (by norm_num)

theorem theorem_3_2_aux {n : ℕ} (J : Instance n) (B : ℕ)
    (F : FeasibleFamily J B) (hF : DownwardClosed F) :
    optDynamic F ≤ 2 * optStatic F := by
  unfold optDynamic
  have hleaf_feas : Feasible F (.leaf () : Policy n) := by
    rcases F.nonempty with ⟨T₀, hT₀⟩
    intro x
    rw [run_leaf]
    exact hF T₀ hT₀ [] (refines_nil T₀)
  have hne : {v : ℝ | ∃ π : Policy n, Feasible F π ∧ dynamicWelfare J π = v}.Nonempty :=
    ⟨dynamicWelfare J (.leaf ()), .leaf (), hleaf_feas, rfl⟩
  apply csSup_le hne
  rintro v ⟨π, hπ, rfl⟩
  exact dynamicWelfare_le_two_optStatic hF hπ

end WelfareBound

end PooledTestingAdaptivity.Gap

open PooledTestingAdaptivity.Gap

theorem solution {n : ℕ} (J : Instance n) (B : ℕ)
    (F : FeasibleFamily J B) (hF : DownwardClosed F) :
    optDynamic F ≤ 2 * optStatic F :=
  theorem_3_2_aux J B F hF
