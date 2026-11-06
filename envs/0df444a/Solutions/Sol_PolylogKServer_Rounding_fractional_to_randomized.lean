-- Prove2me | solution 1 for PolylogKServer.Rounding.fractional_to_randomized
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T02:07:46.379987+00:00
-- url     : https://prove2.me/submissions/46d8b888-d3b1-4bbb-adc1-1c1719273ade

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PolylogKServer_Fractional_KServer
import Definitions.Def_PolylogKServer_Rounding_States

/-! Gmove: a balanced state consistent with `x` has balance gap w.r.t. `x'` at most the fractional
movement cost from `x` to `x'`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace R80c9fd83

open Finset PolylogKServer.HST PolylogKServer.Rounding PolylogKServer.Fractional

/-- Affine majorant of the per-node deviation on the two balanced values. -/
theorem affine_majorant (a b : ℝ) : ∃ α β : ℝ, α * a + β ≤ |b - a| ∧
    ∀ m : ℕ, ((m : ℤ) = ⌊a⌋ ∨ (m : ℤ) = ⌈a⌉) →
      min |(m : ℝ) - ⌊b⌋| |(m : ℝ) - ⌈b⌉| ≤ α * m + β := by
  have hfa : ⌊a⌋ ≤ ⌈a⌉ := Int.floor_le_ceil a
  have hca : ⌈a⌉ ≤ ⌊a⌋ + 1 := Int.ceil_le_floor_add_one a
  have hfb : ⌊b⌋ ≤ ⌈b⌉ := Int.floor_le_ceil b
  have hcb : ⌈b⌉ ≤ ⌊b⌋ + 1 := Int.ceil_le_floor_add_one b
  have hb1 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
  have hb2 : b ≤ (⌈b⌉ : ℝ) := Int.le_ceil b
  have ha1 : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
  have ha2 : a ≤ (⌈a⌉ : ℝ) := Int.le_ceil a
  by_cases c1 : ⌈b⌉ ≤ ⌊a⌋
  · refine ⟨1, -(⌈b⌉ : ℝ), ?_, ?_⟩
    · have := le_abs_self (a - b)
      rw [abs_sub_comm] at this
      linarith
    · intro m hm
      have hm' : ⌈b⌉ ≤ (m : ℤ) := by rcases hm with h | h <;> omega
      have hm'' : (⌈b⌉ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm'
      refine (min_le_right _ _).trans (le_of_eq ?_)
      rw [abs_of_nonneg (by linarith)]
      ring
  by_cases c2 : ⌈a⌉ ≤ ⌊b⌋
  · refine ⟨-1, (⌊b⌋ : ℝ), ?_, ?_⟩
    · have := le_abs_self (b - a)
      linarith
    · intro m hm
      have hm' : (m : ℤ) ≤ ⌊b⌋ := by rcases hm with h | h <;> omega
      have hm'' : (m : ℝ) ≤ (⌊b⌋ : ℝ) := by exact_mod_cast hm'
      refine (min_le_left _ _).trans (le_of_eq ?_)
      rw [abs_of_nonpos (by linarith)]
      ring
  · refine ⟨0, 0, by simp, ?_⟩
    intro m hm
    push_neg at c1 c2
    rcases hm with h | h
    · have e : (m : ℤ) = ⌊b⌋ := by omega
      have e' : (m : ℝ) = (⌊b⌋ : ℝ) := by exact_mod_cast e
      refine (min_le_left _ _).trans (le_of_eq ?_)
      rw [e', sub_self, abs_zero]; ring
    · have e : (m : ℤ) = ⌈b⌉ := by omega
      have e' : (m : ℝ) = (⌈b⌉ : ℝ) := by exact_mod_cast e
      refine (min_le_right _ _).trans (le_of_eq ?_)
      rw [e', sub_self, abs_zero]; ring

variable {V : Type} [Fintype V] [DecidableEq V]

open Classical in
theorem countBelow_eq (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (C : Finset M)
    (p : V) : (countBelow T e C p : ℝ) = ∑ m ∈ C, if T.IsAnc p (e m : V) then (1 : ℝ) else 0 := by
  unfold countBelow
  rw [Finset.card_filter]
  push_cast
  rfl

/-- Averaging the subtree counts of a consistent state gives the subtree mass. -/
theorem count_avg (T : WTree V) {k : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    (e : M ≃ T.Leaf) (x : M → ℝ) (S : KConfig k M → ℝ) (hc : Consistent S x) (p : V) :
    ∑ C, S C * (countBelow T e C.1 p : ℝ) = massBelow T e x p := by
  classical
  simp_rw [countBelow_eq]
  have h1 : ∀ C : KConfig k M, S C * ∑ m ∈ C.1, (if T.IsAnc p (e m : V) then (1 : ℝ) else 0) =
      ∑ m, (if T.IsAnc p (e m : V) then (1 : ℝ) else 0) * (if m ∈ C.1 then S C else 0) := by
    intro C
    rw [Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ C.1)]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [if_pos hm]; ring
    · intro m _ hm
      rw [if_neg hm, mul_zero]
  simp_rw [h1]
  rw [Finset.sum_comm]
  unfold massBelow
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.mul_sum, ← Finset.sum_filter, hc m]
  split_ifs <;> simp

theorem massBelow_eq_subtreeMass (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf)
    (x : M → ℝ) (p : V) : massBelow T e x p = subtreeMass T e x p := rfl

/-- **Gmove.** -/
theorem gmove (T : WTree V) {k : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    (e : M ≃ T.Leaf) (x x' : M → ℝ) (S : KConfig k M → ℝ) (hS : IsKState S)
    (hc : Consistent S x) (hb : Balanced T e x S) :
    balanceGap T e S x' ≤ fracMoveCost T e x x' := by
  unfold balanceGap fracMoveCost
  apply Finset.sum_le_sum
  intro p hp
  have hp' : p ≠ T.root := (Finset.mem_filter.1 hp).2
  apply mul_le_mul_of_nonneg_left _ (T.W_pos p hp').le
  obtain ⟨α, β, h1, h2⟩ := affine_majorant (massBelow T e x p) (massBelow T e x' p)
  calc ∑ C, S C * min |(countBelow T e C.1 p : ℝ) - ⌊massBelow T e x' p⌋|
          |(countBelow T e C.1 p : ℝ) - ⌈massBelow T e x' p⌉|
        ≤ ∑ C, S C * (α * (countBelow T e C.1 p : ℝ) + β) := by
          apply Finset.sum_le_sum
          intro C _
          by_cases hSC : S C = 0
          · rw [hSC, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (h2 _ (hb C hSC p)) (hS.1 C)
    _ = α * ∑ C, S C * (countBelow T e C.1 p : ℝ) + β * ∑ C, S C := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro C _
          ring
    _ = α * massBelow T e x p + β := by rw [count_avg T e x S hc p, hS.2, mul_one]
    _ ≤ |massBelow T e x' p - massBelow T e x p| := h1
    _ = |subtreeMass T e x' p - subtreeMass T e x p| := rfl

section Match

variable {k : ℕ} {M : Type} [MetricSpace M]

/-- A labelling of a configuration. -/
theorem exists_label (C : KConfig k M) :
    ∃ a : Fin k → M, Function.Injective a ∧ ∀ m, m ∈ C.1 ↔ ∃ i, a i = m := by
  classical
  let e := C.1.equivFin
  refine ⟨fun i => (e.symm (Fin.cast C.2.symm i)).1, ?_, ?_⟩
  · intro i j h
    have h' := Subtype.ext h
    have := e.symm.injective h'
    exact Fin.cast_injective _ this
  · intro m
    constructor
    · intro hm
      refine ⟨Fin.cast C.2 (e ⟨m, hm⟩), ?_⟩
      simp
    · rintro ⟨i, rfl⟩
      exact (e.symm (Fin.cast C.2.symm i)).2

theorem matchCost_nonneg (C C' : KConfig k M) : 0 ≤ matchCost C C' := by
  unfold matchCost
  apply Real.sInf_nonneg
  rintro c ⟨a, b, -, -, -, -, rfl⟩
  exact Finset.sum_nonneg fun i _ => dist_nonneg

theorem matchCost_le (C C' : KConfig k M) (a b : Fin k → M)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hia : ∀ m, m ∈ C.1 ↔ ∃ i, a i = m) (hib : ∀ m, m ∈ C'.1 ↔ ∃ i, b i = m) :
    matchCost C C' ≤ ∑ i, dist (a i) (b i) := by
  classical
  unfold matchCost
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨a', b', -, -, -, -, rfl⟩
    exact Finset.sum_nonneg fun i _ => dist_nonneg
  · refine ⟨a, b, ha, hb, ?_, ?_, rfl⟩
    · ext m; simp only [Finset.mem_image, Finset.mem_univ, true_and]; exact (hia m).symm
    · ext m; simp only [Finset.mem_image, Finset.mem_univ, true_and]; exact (hib m).symm

theorem matchCost_self (C : KConfig k M) : matchCost C C = 0 := by
  obtain ⟨a, ha, hia⟩ := exists_label C
  have h := matchCost_le C C a a ha ha hia hia
  simp only [dist_self, Finset.sum_const_zero] at h
  exact le_antisymm h (matchCost_nonneg C C)

/-- Membership form of an element of the matchCost set. -/
theorem mem_of_image {C : KConfig k M} {a : Fin k → M} [DecidableEq M]
    (h : Finset.univ.image a = C.1) : ∀ m, m ∈ C.1 ↔ ∃ i, a i = m := by
  intro m; rw [← h]; simp

/-- Key step of the triangle inequality: compose two labelled matchings. -/
theorem matchCost_le_add_of (C1 C2 C3 : KConfig k M) (a1 b1 a2 b2 : Fin k → M)
    (ha1 : Function.Injective a1) (hb1 : Function.Injective b1)
    (ha2 : Function.Injective a2) (hb2 : Function.Injective b2)
    (h1 : ∀ m, m ∈ C1.1 ↔ ∃ i, a1 i = m) (h2 : ∀ m, m ∈ C2.1 ↔ ∃ i, b1 i = m)
    (h2' : ∀ m, m ∈ C2.1 ↔ ∃ i, a2 i = m) (h3 : ∀ m, m ∈ C3.1 ↔ ∃ i, b2 i = m) :
    matchCost C1 C3 ≤ ∑ i, dist (a1 i) (b1 i) + ∑ i, dist (a2 i) (b2 i) := by
  have hex : ∀ i, ∃ j, a2 j = b1 i := fun i => (h2' (b1 i)).1 ((h2 (b1 i)).2 ⟨i, rfl⟩)
  choose π hπ using hex
  have hπi : Function.Injective π := by
    intro i j h
    apply hb1
    rw [← hπ i, ← hπ j, h]
  have hπb : Function.Bijective π := (Finite.injective_iff_bijective).1 hπi
  let eπ := Equiv.ofBijective π hπb
  have hb : Function.Injective (fun i => b2 (π i)) := hb2.comp hπi
  have hib : ∀ m, m ∈ C3.1 ↔ ∃ i, b2 (π i) = m := by
    intro m
    rw [h3 m]
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨i, hi⟩ := hπb.2 j
      exact ⟨i, by rw [hi]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨π i, rfl⟩
  calc matchCost C1 C3 ≤ ∑ i, dist (a1 i) (b2 (π i)) := matchCost_le C1 C3 a1 _ ha1 hb h1 hib
    _ ≤ ∑ i, (dist (a1 i) (b1 i) + dist (b1 i) (b2 (π i))) :=
        Finset.sum_le_sum fun i _ => dist_triangle _ _ _
    _ = ∑ i, dist (a1 i) (b1 i) + ∑ i, dist (a2 (π i)) (b2 (π i)) := by
        rw [Finset.sum_add_distrib]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [hπ i]
    _ = ∑ i, dist (a1 i) (b1 i) + ∑ i, dist (a2 i) (b2 i) := by
        congr 1
        exact Equiv.sum_comp eπ (fun j => dist (a2 j) (b2 j))

theorem matchCost_triangle (C1 C2 C3 : KConfig k M) :
    matchCost C1 C3 ≤ matchCost C1 C2 + matchCost C2 C3 := by
  classical
  have key : ∀ a1 b1 : Fin k → M, Function.Injective a1 → Function.Injective b1 →
      Finset.univ.image a1 = C1.1 → Finset.univ.image b1 = C2.1 →
      ∀ a2 b2 : Fin k → M, Function.Injective a2 → Function.Injective b2 →
      Finset.univ.image a2 = C2.1 → Finset.univ.image b2 = C3.1 →
      matchCost C1 C3 ≤ ∑ i, dist (a1 i) (b1 i) + ∑ i, dist (a2 i) (b2 i) :=
    fun a1 b1 ha1 hb1 e1 f1 a2 b2 ha2 hb2 e2 f2 =>
      matchCost_le_add_of C1 C2 C3 a1 b1 a2 b2 ha1 hb1 ha2 hb2 (mem_of_image e1)
        (mem_of_image f1) (mem_of_image e2) (mem_of_image f2)
  obtain ⟨l1, hl1, hm1⟩ := exists_label C1
  obtain ⟨l2, hl2, hm2⟩ := exists_label C2
  obtain ⟨l3, hl3, hm3⟩ := exists_label C3
  have img : ∀ (C : KConfig k M) (l : Fin k → M), (∀ m, m ∈ C.1 ↔ ∃ i, l i = m) →
      Finset.univ.image l = C.1 := by
    intro C l h; ext m; simp only [Finset.mem_image, Finset.mem_univ, true_and]; exact (h m).symm
  -- matchCost C1 C3 - matchCost C2 C3 ≤ every element of the C1,C2 set
  have step1 : ∀ a1 b1 : Fin k → M, Function.Injective a1 → Function.Injective b1 →
      Finset.univ.image a1 = C1.1 → Finset.univ.image b1 = C2.1 →
      matchCost C1 C3 - ∑ i, dist (a1 i) (b1 i) ≤ matchCost C2 C3 := by
    intro a1 b1 ha1 hb1 e1 f1
    show _ ≤ sInf _
    apply le_csInf
    · exact ⟨_, l2, l3, hl2, hl3, img C2 l2 hm2, img C3 l3 hm3, rfl⟩
    · rintro c ⟨a2, b2, ha2, hb2, e2, f2, rfl⟩
      have := key a1 b1 ha1 hb1 e1 f1 a2 b2 ha2 hb2 e2 f2
      linarith
  have step2 : matchCost C1 C3 - matchCost C2 C3 ≤ matchCost C1 C2 := by
    show _ ≤ sInf _
    apply le_csInf
    · exact ⟨_, l1, l2, hl1, hl2, img C1 l1 hm1, img C2 l2 hm2, rfl⟩
    · rintro c ⟨a1, b1, ha1, hb1, e1, f1, rfl⟩
      have := step1 a1 b1 ha1 hb1 e1 f1
      linarith
  linarith

end Match

section Transport

variable {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]

theorem transportCost_nonneg (S S' : KConfig k M → ℝ) : 0 ≤ transportCost S S' := by
  unfold transportCost
  apply Real.sInf_nonneg
  rintro c ⟨q, hq, rfl⟩
  exact Finset.sum_nonneg fun z _ => mul_nonneg (hq.1 z) (matchCost_nonneg _ _)

theorem transportCost_le (S S' : KConfig k M → ℝ) (q : KConfig k M × KConfig k M → ℝ)
    (hq : IsCoupling S S' q) : transportCost S S' ≤ ∑ z, q z * matchCost z.1 z.2 := by
  unfold transportCost
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨q', hq', rfl⟩
    exact Finset.sum_nonneg fun z _ => mul_nonneg (hq'.1 z) (matchCost_nonneg _ _)
  · exact ⟨q, hq, rfl⟩

/-- The diagonal coupling. -/
theorem isCoupling_diag (S : KConfig k M → ℝ) (hS : ∀ C, 0 ≤ S C) :
    IsCoupling S S (fun z => if z.1 = z.2 then S z.1 else 0) := by
  refine ⟨fun z => ?_, fun C => ?_, fun C' => ?_⟩
  · show 0 ≤ (if z.1 = z.2 then S z.1 else 0)
    split_ifs
    · exact hS _
    · exact le_rfl
  · simp
  · simp

theorem transportCost_self (S : KConfig k M → ℝ) (hS : ∀ C, 0 ≤ S C) :
    transportCost S S = 0 := by
  apply le_antisymm _ (transportCost_nonneg S S)
  refine (transportCost_le S S _ (isCoupling_diag S hS)).trans (le_of_eq ?_)
  apply Finset.sum_eq_zero
  intro z _
  split_ifs with h
  · rw [h, matchCost_self, mul_zero]
  · rw [zero_mul]

/-- The product coupling of two states. -/
theorem isCoupling_prod (S S' : KConfig k M → ℝ) (hS : IsKState S) (hS' : IsKState S') :
    IsCoupling S S' (fun z => S z.1 * S' z.2) := by
  refine ⟨fun z => mul_nonneg (hS.1 _) (hS'.1 _), fun C => ?_, fun C' => ?_⟩
  · simp only; rw [← Finset.mul_sum, hS'.2, mul_one]
  · simp only; rw [← Finset.sum_mul, hS.2, one_mul]

theorem coupling_zero_left {S S' : KConfig k M → ℝ} {q : KConfig k M × KConfig k M → ℝ}
    (hq : IsCoupling S S' q) {C : KConfig k M} (h : S C = 0) (C' : KConfig k M) :
    q (C, C') = 0 := by
  have h1 := hq.2.1 C
  rw [h] at h1
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hq.1 _)).1 h1 C' (Finset.mem_univ _)

theorem coupling_zero_right {S S' : KConfig k M → ℝ} {q : KConfig k M × KConfig k M → ℝ}
    (hq : IsCoupling S S' q) {C' : KConfig k M} (h : S' C' = 0) (C : KConfig k M) :
    q (C, C') = 0 := by
  have h1 := hq.2.2 C'
  rw [h] at h1
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hq.1 _)).1 h1 C (Finset.mem_univ _)

/-- Gluing weight. -/
noncomputable def glueW (S2 : KConfig k M → ℝ) (q12 q23 : KConfig k M × KConfig k M → ℝ)
    (C C' C'' : KConfig k M) : ℝ :=
  q12 (C, C') * q23 (C', C'') / S2 C'

theorem glue_row {S1 S2 S3 : KConfig k M → ℝ} {q12 q23 : KConfig k M × KConfig k M → ℝ}
    (h12 : IsCoupling S1 S2 q12) (h23 : IsCoupling S2 S3 q23) (C C' : KConfig k M) :
    ∑ C'', glueW S2 q12 q23 C C' C'' = q12 (C, C') := by
  unfold glueW
  simp_rw [mul_div_right_comm]
  rw [← Finset.mul_sum, h23.2.1 C']
  by_cases h : S2 C' = 0
  · rw [coupling_zero_right h12 h C, zero_div, zero_mul]
  · rw [div_mul_cancel₀ _ h]

theorem glue_col {S1 S2 S3 : KConfig k M → ℝ} {q12 q23 : KConfig k M × KConfig k M → ℝ}
    (h12 : IsCoupling S1 S2 q12) (h23 : IsCoupling S2 S3 q23) (C' C'' : KConfig k M) :
    ∑ C, glueW S2 q12 q23 C C' C'' = q23 (C', C'') := by
  unfold glueW
  rw [← Finset.sum_div, ← Finset.sum_mul, h12.2.2 C']
  by_cases h : S2 C' = 0
  · rw [coupling_zero_left h23 h C'', mul_zero, zero_div]
  · rw [mul_div_assoc]; field_simp

theorem glueW_nonneg {S1 S2 S3 : KConfig k M → ℝ} {q12 q23 : KConfig k M × KConfig k M → ℝ}
    (h12 : IsCoupling S1 S2 q12) (h23 : IsCoupling S2 S3 q23) (hS2 : ∀ C, 0 ≤ S2 C)
    (C C' C'' : KConfig k M) : 0 ≤ glueW S2 q12 q23 C C' C'' :=
  div_nonneg (mul_nonneg (h12.1 _) (h23.1 _)) (hS2 _)

theorem isCoupling_glue {S1 S2 S3 : KConfig k M → ℝ} {q12 q23 : KConfig k M × KConfig k M → ℝ}
    (h12 : IsCoupling S1 S2 q12) (h23 : IsCoupling S2 S3 q23) (hS2 : ∀ C, 0 ≤ S2 C) :
    IsCoupling S1 S3 (fun z => ∑ C', glueW S2 q12 q23 z.1 C' z.2) := by
  refine ⟨fun z => Finset.sum_nonneg fun C' _ => glueW_nonneg h12 h23 hS2 _ _ _,
    fun C => ?_, fun C'' => ?_⟩
  · simp only
    rw [Finset.sum_comm]
    simp_rw [glue_row h12 h23]
    exact h12.2.1 C
  · simp only
    rw [Finset.sum_comm]
    simp_rw [glue_col h12 h23]
    exact h23.2.2 C''

theorem glue_cost_le {S1 S2 S3 : KConfig k M → ℝ} {q12 q23 : KConfig k M × KConfig k M → ℝ}
    (h12 : IsCoupling S1 S2 q12) (h23 : IsCoupling S2 S3 q23) (hS2 : ∀ C, 0 ≤ S2 C) :
    ∑ z : KConfig k M × KConfig k M, (∑ C', glueW S2 q12 q23 z.1 C' z.2) * matchCost z.1 z.2 ≤
      ∑ z, q12 z * matchCost z.1 z.2 + ∑ z, q23 z * matchCost z.1 z.2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only
  set w := glueW S2 q12 q23 with hw
  calc ∑ C, ∑ C'', (∑ C', w C C' C'') * matchCost C C''
      ≤ ∑ C, ∑ C'', ∑ C', w C C' C'' * (matchCost C C' + matchCost C' C'') := by
        apply Finset.sum_le_sum; intro C _
        apply Finset.sum_le_sum; intro C'' _
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum; intro C' _
        exact mul_le_mul_of_nonneg_left (matchCost_triangle C C' C'')
          (glueW_nonneg h12 h23 hS2 _ _ _)
    _ = ∑ C, ∑ C'', ∑ C', w C C' C'' * matchCost C C' +
          ∑ C, ∑ C'', ∑ C', w C C' C'' * matchCost C' C'' := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro C _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro C'' _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro C' _
        ring
    _ = ∑ C, ∑ C', q12 (C, C') * matchCost C C' + ∑ C', ∑ C'', q23 (C', C'') * matchCost C' C'' := by
        congr 1
        · apply Finset.sum_congr rfl; intro C _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro C' _
          rw [← Finset.sum_mul, glue_row h12 h23]
        · rw [Finset.sum_congr rfl (fun C _ => Finset.sum_comm), Finset.sum_comm]
          apply Finset.sum_congr rfl; intro C' _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro C'' _
          rw [← Finset.sum_mul, glue_col h12 h23]
    _ = ∑ C, ∑ C', q12 (C, C') * matchCost C C' + ∑ C', ∑ C'', q23 (C', C'') * matchCost C' C'' := rfl

theorem transportCost_triangle (S1 S2 S3 : KConfig k M → ℝ) (h1 : IsKState S1)
    (h2 : IsKState S2) (h3 : IsKState S3) :
    transportCost S1 S3 ≤ transportCost S1 S2 + transportCost S2 S3 := by
  have key : ∀ q12, IsCoupling S1 S2 q12 → ∀ q23, IsCoupling S2 S3 q23 →
      transportCost S1 S3 ≤ ∑ z, q12 z * matchCost z.1 z.2 + ∑ z, q23 z * matchCost z.1 z.2 :=
    fun q12 h12 q23 h23 =>
      (transportCost_le _ _ _ (isCoupling_glue h12 h23 h2.1)).trans (glue_cost_le h12 h23 h2.1)
  have step1 : ∀ q12, IsCoupling S1 S2 q12 →
      transportCost S1 S3 - ∑ z, q12 z * matchCost z.1 z.2 ≤ transportCost S2 S3 := by
    intro q12 h12
    rw [show transportCost S2 S3 = sInf {c : ℝ | ∃ q, IsCoupling S2 S3 q ∧
      c = ∑ z, q z * matchCost z.1 z.2} from rfl]
    apply le_csInf
    · exact ⟨_, _, isCoupling_prod S2 S3 h2 h3, rfl⟩
    · rintro c ⟨q23, h23, rfl⟩
      have := key q12 h12 q23 h23
      linarith
  have step2 : transportCost S1 S3 - transportCost S2 S3 ≤ transportCost S1 S2 := by
    rw [show transportCost S1 S2 = sInf {c : ℝ | ∃ q, IsCoupling S1 S2 q ∧
      c = ∑ z, q z * matchCost z.1 z.2} from rfl]
    apply le_csInf
    · exact ⟨_, _, isCoupling_prod S1 S2 h1 h2, rfl⟩
    · rintro c ⟨q12, h12, rfl⟩
      have := step1 q12 h12
      linarith
  linarith

end Transport
section TreeR

variable {V : Type} [Fintype V] [DecidableEq V]

theorem t_depth_parent (T : WTree V) (v : V) : T.depth (T.parent v) = T.depth v - 1 := by
  by_cases hv : v = T.root
  · subst hv; rw [T.parent_root, T.depth_root]
  · have := T.depth_parent v hv; omega

theorem t_depth_iter (T : WTree V) (v : V) (i : ℕ) :
    T.depth (T.parent^[i] v) = T.depth v - i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', t_depth_parent, ih]; omega

theorem t_eq_root_of_depth (T : WTree V) {v : V} (h : T.depth v = 0) : v = T.root := by
  by_contra hv; have := T.depth_parent v hv; omega

theorem t_iter_depth (T : WTree V) (v : V) : T.parent^[T.depth v] v = T.root :=
  t_eq_root_of_depth T (by rw [t_depth_iter]; omega)

theorem t_iter_root (T : WTree V) (i : ℕ) : T.parent^[i] T.root = T.root :=
  Function.iterate_fixed T.parent_root i

theorem t_anc_eq (T : WTree V) {a v : V} (h : T.IsAnc a v) :
    a = T.parent^[T.depth v - T.depth a] v := by
  obtain ⟨i, rfl⟩ := h
  rw [t_depth_iter]
  by_cases hi : i ≤ T.depth v
  · congr 1; omega
  · have h1 : T.parent^[i] v = T.root := by
      have : i = (i - T.depth v) + T.depth v := by omega
      rw [this, Function.iterate_add_apply, t_iter_depth, t_iter_root]
    rw [h1]
    have : T.depth v - (T.depth v - i) = T.depth v := by omega
    rw [this, t_iter_depth]

theorem t_anc_depth_le (T : WTree V) {a v : V} (h : T.IsAnc a v) : T.depth a ≤ T.depth v := by
  obtain ⟨i, rfl⟩ := h; rw [t_depth_iter]; omega

theorem t_iter_ge (T : WTree V) (v : V) {i : ℕ} (hi : T.depth v ≤ i) :
    T.parent^[i] v = T.root := by
  have : i = (i - T.depth v) + T.depth v := by omega
  rw [this, Function.iterate_add_apply, t_iter_depth, t_iter_root]

theorem t_anc_of_depth (T : WTree V) {a b w : V} (ha : T.IsAnc a w) (hb : T.IsAnc b w)
    (hd : T.depth a ≤ T.depth b) : T.IsAnc a b := by
  obtain ⟨i, rfl⟩ := hb
  obtain ⟨j, rfl⟩ := ha
  rw [t_depth_iter, t_depth_iter] at hd
  by_cases hij : i ≤ j
  · exact ⟨j - i, by rw [← Function.iterate_add_apply]; congr 1; omega⟩
  · refine ⟨0, ?_⟩
    simp only [Function.iterate_zero, id]
    rw [t_iter_ge T w (show T.depth w ≤ i by omega), t_iter_ge T w (show T.depth w ≤ j by omega)]

theorem t_anc_unique (T : WTree V) {a b w : V} (ha : T.IsAnc a w) (hb : T.IsAnc b w)
    (hd : T.depth a = T.depth b) : a = b := by
  rw [t_anc_eq T ha, t_anc_eq T hb, hd]

theorem t_anc_refl (T : WTree V) (v : V) : T.IsAnc v v := ⟨0, rfl⟩

theorem t_anc_trans (T : WTree V) {a b c : V} (h1 : T.IsAnc a b) (h2 : T.IsAnc b c) :
    T.IsAnc a c := by
  obtain ⟨i, rfl⟩ := h1; obtain ⟨j, rfl⟩ := h2
  exact ⟨i + j, by rw [Function.iterate_add_apply]⟩

theorem t_anc_parent_self (T : WTree V) (v : V) : T.IsAnc (T.parent v) v := ⟨1, rfl⟩

theorem t_anc_antisymm (T : WTree V) {a b : V} (h1 : T.IsAnc a b) (h2 : T.IsAnc b a) :
    a = b :=
  t_anc_unique T h1 (t_anc_refl T b) (le_antisymm (t_anc_depth_le T h1) (t_anc_depth_le T h2))

theorem t_child_depth (T : WTree V) {u p : V} (hu : u ≠ T.root) (hp : T.parent u = p) :
    T.depth u = T.depth p + 1 := by rw [← hp]; exact (T.depth_parent u hu).symm

theorem t_depth_lt (T : WTree V) {a v : V} (h : T.IsAnc a v) (hne : v ≠ a) :
    T.depth a < T.depth v := by
  rcases lt_or_eq_of_le (t_anc_depth_le T h) with h' | h'
  · exact h'
  · exact absurd (t_anc_unique T h (t_anc_refl T v) h').symm hne

/-- For `w` strictly below `p`, the child of `p` towards `w`. -/
theorem t_exists_child (T : WTree V) {p w : V} (h : T.IsAnc p w) (hne : w ≠ p) :
    ∃ u, u ≠ T.root ∧ T.parent u = p ∧ T.IsAnc u w := by
  have hd := t_depth_lt T h hne
  refine ⟨T.parent^[T.depth w - T.depth p - 1] w, ?_, ?_, ⟨_, rfl⟩⟩
  · intro hr
    have := congrArg T.depth hr
    rw [t_depth_iter, T.depth_root] at this; omega
  · rw [← Function.iterate_succ_apply' T.parent]
    conv_rhs => rw [t_anc_eq T h]
    congr 1; omega

/-- The children of `p`. -/
def ch (T : WTree V) (p : V) : Finset V := univ.filter (fun u => u ≠ T.root ∧ T.parent u = p)

theorem mem_ch (T : WTree V) {p u : V} : u ∈ ch T p ↔ u ≠ T.root ∧ T.parent u = p := by
  simp [ch]

theorem t_leaf_anc (T : WTree V) {c w : V} (hc : T.IsLeaf c) (h : T.IsAnc c w) : w = c := by
  by_contra hne
  obtain ⟨u, hu, hpu, -⟩ := t_exists_child T h hne
  exact hc u hu hpu

theorem t_anc_of_child (T : WTree V) {p u w : V} (hu : u ∈ ch T p) (h : T.IsAnc u w) :
    T.IsAnc p w := by
  rw [mem_ch] at hu
  rw [← hu.2]; exact t_anc_trans T (t_anc_parent_self T u) h

theorem t_child_unique (T : WTree V) {p u u' w : V} (hu : u ∈ ch T p) (hu' : u' ∈ ch T p)
    (h : T.IsAnc u w) (h' : T.IsAnc u' w) : u = u' := by
  rw [mem_ch] at hu hu'
  refine t_anc_unique T h h' ?_
  rw [t_child_depth T hu.1 hu.2, t_child_depth T hu'.1 hu'.2]

theorem ind_split (T : WTree V) {p w : V} (hw : w ≠ p) (f : ℝ) :
    (open Classical in if T.IsAnc p w then f else 0) =
      ∑ u ∈ ch T p, (open Classical in if T.IsAnc u w then f else 0) := by
  classical
  by_cases h : T.IsAnc p w
  · obtain ⟨u0, hu0, hp0, ha0⟩ := t_exists_child T h hw
    have hu0' : u0 ∈ ch T p := (mem_ch T).2 ⟨hu0, hp0⟩
    rw [if_pos h, Finset.sum_eq_single u0]
    · rw [if_pos ha0]
    · intro u hu hne; rw [if_neg]; intro ha; exact hne (t_child_unique T hu hu0' ha ha0)
    · intro h; exact absurd hu0' h
  · rw [if_neg h]; symm
    apply Finset.sum_eq_zero; intro u hu; rw [if_neg]; intro ha; exact h (t_anc_of_child T hu ha)

theorem leaf_ne (T : WTree V) {M : Type} (e : M ≃ T.Leaf) {p : V} (hp : ¬ T.IsLeaf p) (m : M) :
    (e m : V) ≠ p := by
  intro h; exact hp (h ▸ (e m).2)

theorem count_split (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (C : Finset M)
    {p : V} (hp : ¬ T.IsLeaf p) :
    (countBelow T e C p : ℝ) = ∑ u ∈ ch T p, (countBelow T e C u : ℝ) := by
  rw [countBelow_eq]
  simp_rw [countBelow_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  exact ind_split T (leaf_ne T e hp m) 1

theorem count_split_int (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (C : Finset M)
    {p : V} (hp : ¬ T.IsLeaf p) :
    (countBelow T e C p : ℤ) = ∑ u ∈ ch T p, (countBelow T e C u : ℤ) := by
  have := count_split T e C hp
  exact_mod_cast this

theorem mass_split (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (x : M → ℝ)
    {p : V} (hp : ¬ T.IsLeaf p) :
    massBelow T e x p = ∑ u ∈ ch T p, massBelow T e x u := by
  unfold massBelow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  exact ind_split T (leaf_ne T e hp m) (x m)

theorem sum_floor_le {ι : Type} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ⌊f i⌋ ≤ ⌊∑ i ∈ s, f i⌋ := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha]
  exact (add_le_add le_rfl ih).trans (Int.le_floor_add _ _)

theorem ceil_le_sum_ceil {ι : Type} (s : Finset ι) (f : ι → ℝ) :
    ⌈∑ i ∈ s, f i⌉ ≤ ∑ i ∈ s, ⌈f i⌉ := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha]
  exact (Int.ceil_add_le _ _).trans (add_le_add le_rfl ih)

theorem count_pos_exists (T : WTree V) {M : Type} (e : M ≃ T.Leaf) (C : Finset M) (c : V)
    (h : 0 < countBelow T e C c) : ∃ m ∈ C, T.IsAnc c (e m) := by
  classical
  unfold countBelow at h
  obtain ⟨m, hm⟩ := Finset.card_pos.1 h
  rw [Finset.mem_filter] at hm
  exact ⟨m, hm.1, hm.2⟩

theorem mass_nonneg (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (x : M → ℝ)
    (hx : ∀ m, 0 ≤ x m) (c : V) : 0 ≤ massBelow T e x c := by
  unfold massBelow
  exact Finset.sum_nonneg fun m _ => by split_ifs; exacts [hx m, le_rfl]

/-- Leaf of the leaf set. -/
theorem mass_leaf (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (x : M → ℝ)
    (m0 : M) : massBelow T e x (e m0) = x m0 := by
  classical
  unfold massBelow
  rw [Finset.sum_eq_single m0]
  · rw [if_pos (t_anc_refl T _)]
  · intro m _ hm
    rw [if_neg]
    intro ha
    have := t_leaf_anc T (e m0).2 ha
    exact hm (e.injective (Subtype.ext this))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem count_leaf_zero (T : WTree V) {M : Type} (e : M ≃ T.Leaf) (C : Finset M)
    (m0 : M) (h : countBelow T e C (e m0) = 0) : m0 ∉ C := by
  classical
  intro hm
  unfold countBelow at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  exact h hm (t_anc_refl T _)

/-- Greedy removal descent: below a node with more servers than the floor of its mass, there
is a server whose whole path stays strictly above the floors. -/
theorem rem_exists (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (x : M → ℝ)
    (hx : ∀ m, 0 ≤ x m) (C : Finset M) (c : V)
    (hc : ⌊massBelow T e x c⌋ < (countBelow T e C c : ℤ)) :
    ∃ m ∈ C, T.IsAnc c (e m) ∧ ∀ v, T.IsAnc c v → T.IsAnc v (e m) →
      ⌊massBelow T e x v⌋ < (countBelow T e C v : ℤ) := by
  classical
  suffices H : ∀ n : ℕ, ∀ c : V, Finset.univ.sup T.depth - T.depth c ≤ n →
      ⌊massBelow T e x c⌋ < (countBelow T e C c : ℤ) →
      ∃ m ∈ C, T.IsAnc c (e m) ∧ ∀ v, T.IsAnc c v → T.IsAnc v (e m) →
        ⌊massBelow T e x v⌋ < (countBelow T e C v : ℤ) from H _ c le_rfl hc
  have leafcase : ∀ c : V, T.IsLeaf c → ⌊massBelow T e x c⌋ < (countBelow T e C c : ℤ) →
      ∃ m ∈ C, T.IsAnc c (e m) ∧ ∀ v, T.IsAnc c v → T.IsAnc v (e m) →
        ⌊massBelow T e x v⌋ < (countBelow T e C v : ℤ) := by
    intro c hl hc
    have h0 : 0 ≤ ⌊massBelow T e x c⌋ := Int.floor_nonneg.2 (mass_nonneg T e x hx c)
    obtain ⟨m, hm, ha⟩ := count_pos_exists T e C c (by omega)
    refine ⟨m, hm, ha, fun v h1 h2 => ?_⟩
    have hmc := t_leaf_anc T hl ha
    rw [hmc] at h2
    rw [t_anc_antisymm T h2 h1]; exact hc
  intro n
  induction n with
  | zero =>
    intro c hn hc
    by_cases hl : T.IsLeaf c
    · exact leafcase c hl hc
    · exfalso
      unfold WTree.IsLeaf at hl; push Not at hl
      obtain ⟨u, hu, hpu⟩ := hl
      have h1 := t_child_depth T hu hpu
      have h2 : T.depth u ≤ Finset.univ.sup T.depth := Finset.le_sup (Finset.mem_univ u)
      omega
  | succ n ih =>
    intro c hn hc
    by_cases hl : T.IsLeaf c
    · exact leafcase c hl hc
    · have hs : ∑ u ∈ ch T c, ⌊massBelow T e x u⌋ < ∑ u ∈ ch T c, (countBelow T e C u : ℤ) := by
        rw [← count_split_int T e C hl]
        refine lt_of_le_of_lt ?_ hc
        rw [mass_split T e x hl]
        exact sum_floor_le _ _
      obtain ⟨u, hu, hlt⟩ := Finset.exists_lt_of_sum_lt hs
      have hu' := (mem_ch T).1 hu
      have hdu := t_child_depth T hu'.1 hu'.2
      obtain ⟨m, hm, ha, hp⟩ := ih u (by omega) hlt
      refine ⟨m, hm, t_anc_of_child T hu ha, fun v h1 h2 => ?_⟩
      by_cases hvc : v = c
      · rw [hvc]; exact hc
      · have := t_depth_lt T h1 hvc
        exact hp v (t_anc_of_depth T ha h2 (by omega)) h2

/-- Greedy insertion descent (masses at most one per point). -/
theorem ins_exists (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (x : M → ℝ)
    (hx1 : ∀ m, x m ≤ 1) (C : Finset M) (c : V)
    (hc : (countBelow T e C c : ℤ) < ⌈massBelow T e x c⌉) :
    ∃ m, m ∉ C ∧ T.IsAnc c (e m) ∧ ∀ v, T.IsAnc c v → T.IsAnc v (e m) →
      (countBelow T e C v : ℤ) < ⌈massBelow T e x v⌉ := by
  classical
  suffices H : ∀ n : ℕ, ∀ c : V, Finset.univ.sup T.depth - T.depth c ≤ n →
      (countBelow T e C c : ℤ) < ⌈massBelow T e x c⌉ →
      ∃ m, m ∉ C ∧ T.IsAnc c (e m) ∧ ∀ v, T.IsAnc c v → T.IsAnc v (e m) →
        (countBelow T e C v : ℤ) < ⌈massBelow T e x v⌉ from H _ c le_rfl hc
  have leafcase : ∀ c : V, T.IsLeaf c → (countBelow T e C c : ℤ) < ⌈massBelow T e x c⌉ →
      ∃ m, m ∉ C ∧ T.IsAnc c (e m) ∧ ∀ v, T.IsAnc c v → T.IsAnc v (e m) →
        (countBelow T e C v : ℤ) < ⌈massBelow T e x v⌉ := by
    intro c hl hc
    set m0 := e.symm ⟨c, hl⟩ with hm0
    have he : (e m0 : V) = c := by rw [hm0, Equiv.apply_symm_apply]
    have hmass : massBelow T e x c = x m0 := by rw [← he]; exact mass_leaf T e x m0
    have h1 : ⌈massBelow T e x c⌉ ≤ 1 := by
      rw [hmass]; exact Int.ceil_le.2 (by exact_mod_cast hx1 m0)
    have hz : countBelow T e C (e m0) = 0 := by rw [he]; omega
    refine ⟨m0, count_leaf_zero T e C m0 hz, he ▸ t_anc_refl T _, fun v h1 h2 => ?_⟩
    rw [he] at h2
    rw [t_anc_antisymm T h2 h1]; exact hc
  intro n
  induction n with
  | zero =>
    intro c hn hc
    by_cases hl : T.IsLeaf c
    · exact leafcase c hl hc
    · exfalso
      unfold WTree.IsLeaf at hl; push Not at hl
      obtain ⟨u, hu, hpu⟩ := hl
      have h1 := t_child_depth T hu hpu
      have h2 : T.depth u ≤ Finset.univ.sup T.depth := Finset.le_sup (Finset.mem_univ u)
      omega
  | succ n ih =>
    intro c hn hc
    by_cases hl : T.IsLeaf c
    · exact leafcase c hl hc
    · have hs : ∑ u ∈ ch T c, (countBelow T e C u : ℤ) < ∑ u ∈ ch T c, ⌈massBelow T e x u⌉ := by
        rw [← count_split_int T e C hl]
        refine lt_of_lt_of_le hc ?_
        rw [mass_split T e x hl]
        exact ceil_le_sum_ceil _ _
      obtain ⟨u, hu, hlt⟩ := Finset.exists_lt_of_sum_lt hs
      have hu' := (mem_ch T).1 hu
      have hdu := t_child_depth T hu'.1 hu'.2
      obtain ⟨m, hm, ha, hp⟩ := ih u (by omega) hlt
      refine ⟨m, hm, t_anc_of_child T hu ha, fun v h1 h2 => ?_⟩
      by_cases hvc : v = c
      · rw [hvc]; exact hc
      · have := t_depth_lt T h1 hvc
        exact hp v (t_anc_of_depth T ha h2 (by omega)) h2

end TreeR

section MoveR

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Move one server from `m1` to `m2` (identity if the move is not possible). -/
def mvK {k : ℕ} {M : Type} [DecidableEq M] (C : KConfig k M) (m1 m2 : M) : KConfig k M :=
  if h : m1 ∈ C.1 ∧ m2 ∉ C.1 then
    ⟨insert m2 (C.1.erase m1), by
      rw [Finset.card_insert_of_notMem (fun h' => h.2 (Finset.mem_of_mem_erase h')),
        Finset.card_erase_of_mem h.1, C.2]
      have : 0 < k := C.2 ▸ Finset.card_pos.2 ⟨m1, h.1⟩
      omega⟩
  else C

theorem mvK_val {k : ℕ} {M : Type} [DecidableEq M] (C : KConfig k M) {m1 m2 : M}
    (h1 : m1 ∈ C.1) (h2 : m2 ∉ C.1) : (mvK C m1 m2).1 = insert m2 (C.1.erase m1) := by
  unfold mvK; rw [dif_pos ⟨h1, h2⟩]

theorem count_mv (T : WTree V) {M : Type} [Fintype M] [DecidableEq M] (e : M ≃ T.Leaf) (C : Finset M)
    {m1 m2 : M} (h1 : m1 ∈ C) (h2 : m2 ∉ C) (v : V) :
    (countBelow T e (insert m2 (C.erase m1)) v : ℝ) = (countBelow T e C v : ℝ)
      - (open Classical in if T.IsAnc v (e m1) then 1 else 0)
      + (open Classical in if T.IsAnc v (e m2) then 1 else 0) := by
  rw [countBelow_eq, countBelow_eq,
    Finset.sum_insert (fun h' => h2 (Finset.mem_of_mem_erase h')), Finset.sum_erase_eq_sub h1]
  ring

/-- The tree earthmover functional between two configurations. -/
noncomputable def emd (T : WTree V) {M : Type} (e : M ≃ T.Leaf) (C C' : Finset M) : ℝ :=
  ∑ x ∈ univ.filter (fun x => x ≠ T.root),
    T.W x * |(countBelow T e C' x : ℝ) - (countBelow T e C x : ℝ)|

theorem emd_nonneg (T : WTree V) {M : Type} (e : M ≃ T.Leaf) (C C' : Finset M) :
    0 ≤ emd T e C C' := by
  unfold emd
  exact Finset.sum_nonneg fun x hx =>
    mul_nonneg (T.W_pos x (Finset.mem_filter.1 hx).2).le (abs_nonneg _)

theorem emd_self (T : WTree V) {M : Type} (e : M ≃ T.Leaf) (C : Finset M) :
    emd T e C C = 0 := by
  unfold emd; simp

theorem treeDist_mv (T : WTree V) {M : Type} [Fintype M] [DecidableEq M] (e : M ≃ T.Leaf) (C : Finset M)
    {m1 m2 : M} (h1 : m1 ∈ C) (h2 : m2 ∉ C) :
    T.treeDist (e m1) (e m2) = emd T e C (insert m2 (C.erase m1)) := by
  classical
  unfold WTree.treeDist emd
  apply Finset.sum_congr rfl
  intro x _
  rw [count_mv T e C h1 h2 x]
  by_cases a : T.IsAnc x (e m1) <;> by_cases b : T.IsAnc x (e m2) <;> simp [a, b]

theorem matchCost_mv {k : ℕ} {M : Type} [MetricSpace M] [DecidableEq M] (C : KConfig k M)
    {m1 m2 : M} (h1 : m1 ∈ C.1) (h2 : m2 ∉ C.1) : matchCost C (mvK C m1 m2) ≤ dist m1 m2 := by
  classical
  obtain ⟨a, ha, hia⟩ := exists_label C
  obtain ⟨i0, hi0⟩ := (hia m1).1 h1
  let b : Fin k → M := Function.update a i0 m2
  have hb_ne : ∀ i, i ≠ i0 → b i = a i := fun i hi => Function.update_of_ne hi _ _
  have hb0 : b i0 = m2 := Function.update_self _ _ _
  have hbinj : Function.Injective b := by
    intro i j hij
    by_cases hi : i = i0 <;> by_cases hj : j = i0
    · rw [hi, hj]
    · exfalso; rw [hi, hb0, hb_ne j hj] at hij; exact h2 ((hia _).2 ⟨j, hij.symm⟩)
    · exfalso; rw [hj, hb0, hb_ne i hi] at hij; exact h2 ((hia _).2 ⟨i, hij⟩)
    · rw [hb_ne i hi, hb_ne j hj] at hij; exact ha hij
  have hib : ∀ m, m ∈ (mvK C m1 m2).1 ↔ ∃ i, b i = m := by
    intro m
    rw [mvK_val C h1 h2, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨hne, hm⟩)
      · exact ⟨i0, hb0⟩
      · obtain ⟨i, rfl⟩ := (hia _).1 hm
        refine ⟨i, hb_ne i ?_⟩
        rintro rfl; exact hne hi0
    · rintro ⟨i, rfl⟩
      by_cases hi : i = i0
      · left; rw [hi, hb0]
      · right; rw [hb_ne i hi]
        refine ⟨fun h => hi (ha (h.trans hi0.symm)), (hia _).2 ⟨i, rfl⟩⟩
  refine (matchCost_le C _ a b ha hbinj hia hib).trans (le_of_eq ?_)
  rw [Finset.sum_eq_single i0]
  · rw [hi0, hb0]
  · intro i _ hi; rw [hb_ne i hi, dist_self]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The cost of a single move is at most its tree earthmover functional. -/
theorem matchCost_mv_le_emd (T : WTree V) {k : ℕ} {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M]
    (e : M ≃ T.Leaf) (hM : T.IsLeafMetric M e) (C : KConfig k M) {m1 m2 : M}
    (h1 : m1 ∈ C.1) (h2 : m2 ∉ C.1) :
    matchCost C (mvK C m1 m2) ≤ emd T e C.1 (mvK C m1 m2).1 := by
  rw [mvK_val C h1 h2, ← treeDist_mv T e C.1 h1 h2, ← hM]
  exact matchCost_mv C h1 h2

/-- The deviation of an integer count from the box `{⌊t⌋, ⌈t⌉}`. -/
noncomputable def devR (t n : ℝ) : ℝ := min |n - ⌊t⌋| |n - ⌈t⌉|

theorem devR_nonneg (t n : ℝ) : 0 ≤ devR t n := le_min (abs_nonneg _) (abs_nonneg _)

theorem devR_dec (t : ℝ) (n : ℤ) (h : ⌊t⌋ < n) : devR t ((n : ℝ) - 1) ≤ devR t n := by
  unfold devR
  have hc1 : (⌈t⌉ : ℝ) ≤ ⌊t⌋ + 1 := by exact_mod_cast Int.ceil_le_floor_add_one t
  have hn : (⌊t⌋ : ℝ) + 1 ≤ n := by exact_mod_cast h
  calc min |(n : ℝ) - 1 - ⌊t⌋| |(n : ℝ) - 1 - ⌈t⌉| ≤ |(n : ℝ) - 1 - ⌊t⌋| := min_le_left _ _
    _ = n - 1 - ⌊t⌋ := abs_of_nonneg (by linarith)
    _ ≤ _ := le_min (by rw [abs_of_nonneg (by linarith)]; linarith)
        (by rw [abs_of_nonneg (by linarith)]; linarith)

theorem devR_inc (t : ℝ) (n : ℤ) (h : n < ⌈t⌉) : devR t ((n : ℝ) + 1) ≤ devR t n := by
  unfold devR
  have hc1 : (⌈t⌉ : ℝ) ≤ ⌊t⌋ + 1 := by exact_mod_cast Int.ceil_le_floor_add_one t
  have hn : (n : ℝ) + 1 ≤ ⌈t⌉ := by exact_mod_cast h
  calc min |(n : ℝ) + 1 - ⌊t⌋| |(n : ℝ) + 1 - ⌈t⌉| ≤ |(n : ℝ) + 1 - ⌈t⌉| := min_le_right _ _
    _ = ⌈t⌉ - n - 1 := by rw [abs_of_nonpos (by linarith)]; ring
    _ ≤ _ := le_min (by rw [abs_of_nonpos (by linarith)]; linarith)
        (by rw [abs_of_nonpos (by linarith)]; linarith)

end MoveR

section LegalR

variable {V : Type} [Fintype V] [DecidableEq V]
variable {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]

/-- Subtree count of a configuration, as a real number. -/
noncomputable def nC (T : WTree V) (e : M ≃ T.Leaf) (v : V) (C : KConfig k M) : ℝ :=
  (countBelow T e C.1 v : ℝ)

/-- A legal greedy move inside the subtree of `p`: one server leaves the subtree of the child `c`
along a path staying above the floors, one enters the subtree of another child `d` along a path
staying below the ceilings (floors/ceilings of the target masses `massBelow y`). -/
def LegalMv (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (p : V) (C C' : KConfig k M) : Prop :=
  ∃ m1 m2 c d, m1 ∈ C.1 ∧ m2 ∉ C.1 ∧ c ∈ ch T p ∧ d ∈ ch T p ∧ c ≠ d ∧
    T.IsAnc c (e m1) ∧ T.IsAnc d (e m2) ∧
    (∀ v, T.IsAnc c v → T.IsAnc v (e m1) →
      ⌊massBelow T e y v⌋ < (countBelow T e C.1 v : ℤ)) ∧
    (∀ v, T.IsAnc d v → T.IsAnc v (e m2) →
      (countBelow T e C.1 v : ℤ) < ⌈massBelow T e y v⌉) ∧
    C' = mvK C m1 m2

theorem anc_iff_of_not_below (T : WTree V) {p v w1 w2 : V} (h1 : T.IsAnc p w1)
    (h2 : T.IsAnc p w2) (hv : ¬ (T.IsAnc p v ∧ v ≠ p)) :
    T.IsAnc v w1 → T.IsAnc v w2 := by
  intro ha
  by_cases hd : T.depth v ≤ T.depth p
  · exact t_anc_trans T (t_anc_of_depth T ha h1 hd) h2
  · exfalso
    have hpv := t_anc_of_depth T h1 ha (by omega)
    refine hv ⟨hpv, ?_⟩
    rintro rfl; omega

theorem legal_outside (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) {p : V}
    {C C' : KConfig k M} (h : LegalMv T e y p C C') {v : V} (hv : ¬ (T.IsAnc p v ∧ v ≠ p)) :
    nC T e v C' = nC T e v C := by
  classical
  obtain ⟨m1, m2, c, d, hm1, hm2, hc, hd, -, ha1, ha2, -, -, rfl⟩ := h
  have hp1 := t_anc_of_child T hc ha1
  have hp2 := t_anc_of_child T hd ha2
  unfold nC
  rw [mvK_val C hm1 hm2, count_mv T e C.1 hm1 hm2 v]
  have hiff : T.IsAnc v (e m1) ↔ T.IsAnc v (e m2) :=
    ⟨anc_iff_of_not_below T hp1 hp2 hv, anc_iff_of_not_below T hp2 hp1 hv⟩
  by_cases a : T.IsAnc v (e m1)
  · rw [if_pos a, if_pos (hiff.1 a)]; ring
  · rw [if_neg a, if_neg (fun h => a (hiff.2 h))]; ring

theorem legal_dev (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) {p : V}
    {C C' : KConfig k M} (h : LegalMv T e y p C C') {v : V} (hv : T.IsAnc p v ∧ v ≠ p) :
    devR (massBelow T e y v) (nC T e v C') ≤ devR (massBelow T e y v) (nC T e v C) := by
  classical
  obtain ⟨m1, m2, c, d, hm1, hm2, hc, hd, hcd, ha1, ha2, hp1, hp2, rfl⟩ := h
  obtain ⟨u, hu0, hpu, hau⟩ := t_exists_child T hv.1 hv.2
  have hu : u ∈ ch T p := (mem_ch T).2 ⟨hu0, hpu⟩
  unfold nC
  rw [mvK_val C hm1 hm2, count_mv T e C.1 hm1 hm2 v]
  by_cases a1 : T.IsAnc v (e m1) <;> by_cases a2 : T.IsAnc v (e m2)
  · exfalso
    have e1 := t_child_unique T hu hc (t_anc_trans T hau a1) ha1
    have e2 := t_child_unique T hu hd (t_anc_trans T hau a2) ha2
    exact hcd (e1.symm.trans e2)
  · rw [if_pos a1, if_neg a2]
    have e1 := t_child_unique T hu hc (t_anc_trans T hau a1) ha1
    have hlt := hp1 v (e1 ▸ hau) a1
    have := devR_dec (massBelow T e y v) _ hlt
    simp only [Int.cast_natCast] at this
    simpa using this
  · rw [if_neg a1, if_pos a2]
    have e2 := t_child_unique T hu hd (t_anc_trans T hau a2) ha2
    have hlt := hp2 v (e2 ▸ hau) a2
    have := devR_inc (massBelow T e y v) _ hlt
    simp only [Int.cast_natCast] at this
    simpa using this
  · rw [if_neg a1, if_neg a2]; simp

theorem ind_sum_le_one (T : WTree V) {p w : V} (hw : w ≠ p) :
    ∑ u ∈ ch T p, (open Classical in if T.IsAnc u w then (1 : ℝ) else 0) ≤ 1 := by
  classical
  rw [← ind_split T hw 1]
  split_ifs <;> norm_num

theorem legal_children (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) {p : V}
    {C C' : KConfig k M} (h : LegalMv T e y p C C') :
    ∑ u ∈ ch T p, |nC T e u C' - nC T e u C| ≤ 2 := by
  classical
  obtain ⟨m1, m2, c, d, hm1, hm2, hc, hd, hcd, ha1, ha2, -, -, rfl⟩ := h
  have hne1 : (e m1 : V) ≠ p := fun h' => by
    have := (mem_ch T).1 hc
    have h3 := t_child_depth T this.1 this.2
    have h4 := t_anc_depth_le T ha1
    rw [h'] at h4; omega
  have hne2 : (e m2 : V) ≠ p := fun h' => by
    have := (mem_ch T).1 hd
    have h3 := t_child_depth T this.1 this.2
    have h4 := t_anc_depth_le T ha2
    rw [h'] at h4; omega
  unfold nC
  have hb : ∀ u, |(countBelow T e (mvK C m1 m2).1 u : ℝ) - countBelow T e C.1 u| ≤
      (open Classical in if T.IsAnc u (e m1) then (1 : ℝ) else 0) +
      (open Classical in if T.IsAnc u (e m2) then (1 : ℝ) else 0) := by
    intro u
    rw [mvK_val C hm1 hm2, count_mv T e C.1 hm1 hm2 u]
    split_ifs <;> norm_num
  calc ∑ u ∈ ch T p, |(countBelow T e (mvK C m1 m2).1 u : ℝ) - countBelow T e C.1 u|
      ≤ ∑ u ∈ ch T p, ((open Classical in if T.IsAnc u (e m1) then (1 : ℝ) else 0) +
      (open Classical in if T.IsAnc u (e m2) then (1 : ℝ) else 0)) := Finset.sum_le_sum fun u _ => hb u
    _ ≤ 2 := by
      rw [Finset.sum_add_distrib]
      linarith [ind_sum_le_one T hne1, ind_sum_le_one T hne2]

end LegalR

section KernelR

variable {V : Type} [Fintype V] [DecidableEq V]
variable {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]

/-- Expectation under a mass function. -/
noncomputable def Ex (S f : KConfig k M → ℝ) : ℝ := ∑ C, S C * f C

/-- Pushforward of a mass function through a kernel. -/
noncomputable def push (S : KConfig k M → ℝ) (K : KConfig k M → KConfig k M → ℝ) :
    KConfig k M → ℝ :=
  fun C' => ∑ C, S C * K C C'

/-- Off-diagonal part of a kernel. -/
noncomputable def offK (K : KConfig k M → KConfig k M → ℝ) (C C' : KConfig k M) : ℝ :=
  if C' = C then 0 else K C C'

/-- Expected number of moves. -/
noncomputable def moveMass (S : KConfig k M → ℝ) (K : KConfig k M → KConfig k M → ℝ) : ℝ :=
  ∑ C, S C * ∑ C', offK K C C'

theorem root_anc' (T : WTree V) (v : V) : T.IsAnc T.root v := ⟨_, t_iter_depth T v⟩

open Classical in
/-- Nodes strictly below the children of `p`. -/
noncomputable def dpSet (T : WTree V) (p : V) : Finset V :=
  univ.filter (fun v => T.IsAnc p v ∧ v ≠ p ∧ v ∉ ch T p)

theorem push_isKState (S : KConfig k M → ℝ) (K : KConfig k M → KConfig k M → ℝ)
    (hS : IsKState S) (hK0 : ∀ C C', 0 ≤ K C C') (hK1 : ∀ C, ∑ C', K C C' = 1) :
    IsKState (push S K) := by
  refine ⟨fun C' => Finset.sum_nonneg fun C _ => mul_nonneg (hS.1 C) (hK0 C C'), ?_⟩
  unfold push
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hK1, mul_one]
  exact hS.2

theorem moveMass_nonneg (S : KConfig k M → ℝ) (K : KConfig k M → KConfig k M → ℝ)
    (hS : ∀ C, 0 ≤ S C) (hK0 : ∀ C C', 0 ≤ K C C') : 0 ≤ moveMass S K := by
  unfold moveMass offK
  exact Finset.sum_nonneg fun C _ => mul_nonneg (hS C)
    (Finset.sum_nonneg fun C' _ => by split_ifs; exacts [le_rfl, hK0 C C'])

theorem Ex_push_sub (S : KConfig k M → ℝ) (K : KConfig k M → KConfig k M → ℝ)
    (hK1 : ∀ C, ∑ C', K C C' = 1) (f : KConfig k M → ℝ) :
    Ex (push S K) f - Ex S f = ∑ C, S C * ∑ C', offK K C C' * (f C' - f C) := by
  unfold Ex push
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro C _
  have h1 : ∑ C', offK K C C' * (f C' - f C) = ∑ C', K C C' * (f C' - f C) := by
    apply Finset.sum_congr rfl; intro C' _
    unfold offK; split_ifs with h
    · rw [h]; ring
    · rfl
  have h2 : ∑ C', K C C' * (f C' - f C) = ∑ C', K C C' * f C' - (∑ C', K C C') * f C := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intros; ring
  rw [h1, h2, hK1 C, one_mul, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intros; ring

theorem moved_le (S : KConfig k M → ℝ) (K : KConfig k M → KConfig k M → ℝ)
    (hS : ∀ C, 0 ≤ S C) (hK0 : ∀ C C', 0 ≤ K C C') (g : KConfig k M → KConfig k M → ℝ)
    (β : ℝ) (hg : ∀ C C', K C C' ≠ 0 → C' ≠ C → g C C' ≤ β) :
    ∑ C, S C * ∑ C', offK K C C' * g C C' ≤ β * moveMass S K := by
  unfold moveMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro C _
  have h1 : ∑ C', offK K C C' * g C C' ≤ ∑ C', β * offK K C C' := by
    apply Finset.sum_le_sum; intro C' _
    unfold offK
    split_ifs with hc
    · simp
    · by_cases hk : K C C' = 0
      · rw [hk]; simp
      · have := mul_le_mul_of_nonneg_left (hg C C' hk hc) (hK0 C C'); linarith
  rw [← Finset.mul_sum] at h1
  calc S C * _ ≤ S C * (β * ∑ C', offK K C C') := mul_le_mul_of_nonneg_left h1 (hS C)
    _ = β * (S C * ∑ C', offK K C C') := by ring

theorem Ex_push_le (S : KConfig k M → ℝ) (K : KConfig k M → KConfig k M → ℝ)
    (hS : ∀ C, 0 ≤ S C) (hK0 : ∀ C C', 0 ≤ K C C') (hK1 : ∀ C, ∑ C', K C C' = 1)
    (f : KConfig k M → ℝ) (β : ℝ) (hf : ∀ C C', K C C' ≠ 0 → C' ≠ C → f C' - f C ≤ β) :
    Ex (push S K) f ≤ Ex S f + β * moveMass S K := by
  have h := Ex_push_sub S K hK1 f
  have h2 := moved_le S K hS hK0 (fun C C' => f C' - f C) β hf
  linarith

theorem Ex_push_abs (S : KConfig k M → ℝ) (K : KConfig k M → KConfig k M → ℝ)
    (hS : ∀ C, 0 ≤ S C) (hK0 : ∀ C C', 0 ≤ K C C') (hK1 : ∀ C, ∑ C', K C C' = 1)
    (f : KConfig k M → ℝ) :
    |Ex (push S K) f - Ex S f| ≤ ∑ C, S C * ∑ C', offK K C C' * |f C' - f C| := by
  rw [Ex_push_sub S K hK1 f]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun C _ => ?_)
  rw [abs_mul, abs_of_nonneg (hS C)]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun C' _ => ?_)) (hS C)
  have : 0 ≤ offK K C C' := by unfold offK; split_ifs; exacts [le_rfl, hK0 C C']
  rw [abs_mul, abs_of_nonneg this]

theorem swap3 (D : Finset V) (w : V → ℝ) (S : KConfig k M → ℝ)
    (Kd : KConfig k M → KConfig k M → ℝ) (g : V → KConfig k M → KConfig k M → ℝ) :
    ∑ v ∈ D, w v * ∑ C, S C * ∑ C', Kd C C' * g v C C' =
      ∑ C, S C * ∑ C', Kd C C' * ∑ v ∈ D, w v * g v C C' := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro C _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro C' _
  apply Finset.sum_congr rfl; intro v _
  ring

/-- Certificate for a randomized transformation inside the subtree of `p`, with move mass `μ`. -/
def Rel (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (p : V) (A B : ℝ)
    (S S' : KConfig k M → ℝ) (μ : ℝ) : Prop :=
  IsKState S' ∧ 0 ≤ μ ∧ transportCost S S' ≤ A * μ ∧
  (∀ v, Ex S' (fun C => devR (massBelow T e y v) (nC T e v C)) ≤
      Ex S (fun C => devR (massBelow T e y v) (nC T e v C))) ∧
  (∑ v ∈ dpSet T p, T.W v * |Ex S' (nC T e v) - massBelow T e y v|) ≤
      (∑ v ∈ dpSet T p, T.W v * |Ex S (nC T e v) - massBelow T e y v|) + B * μ ∧
  (∑ u ∈ ch T p, |Ex S' (nC T e u) - Ex S (nC T e u)|) ≤ 2 * μ ∧
  (∀ v, ¬ (T.IsAnc p v ∧ v ≠ p) → Ex S' (nC T e v) = Ex S (nC T e v)) ∧
  (∀ C', S' C' ≠ 0 → ∃ C, S C ≠ 0 ∧ ∀ v, ¬ (T.IsAnc p v ∧ v ≠ p) → nC T e v C' = nC T e v C)

theorem rel_kernel (T : WTree V) (e : M ≃ T.Leaf) (hM : T.IsLeafMetric M e) (y : M → ℝ)
    (p : V) (A B : ℝ) (S : KConfig k M → ℝ) (hS : IsKState S)
    (K : KConfig k M → KConfig k M → ℝ) (hK0 : ∀ C C', 0 ≤ K C C')
    (hK1 : ∀ C, ∑ C', K C C' = 1)
    (hKL : ∀ C C' : KConfig k M, K C C' ≠ 0 → C' ≠ C → LegalMv T e y p C C')
    (hA : ∀ C C' : KConfig k M, LegalMv T e y p C C' → emd T e C.1 C'.1 ≤ A)
    (hB : ∀ C C' : KConfig k M, LegalMv T e y p C C' →
      ∑ v ∈ dpSet T p, T.W v * |nC T e v C' - nC T e v C| ≤ B) :
    Rel T e y p A B S (push S K) (moveMass S K) := by
  classical
  have hS0 := hS.1
  refine ⟨push_isKState S K hS hK0 hK1, moveMass_nonneg S K hS0 hK0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    let q : KConfig k M × KConfig k M → ℝ := fun z => S z.1 * K z.1 z.2
    have hq : IsCoupling S (push S K) q := by
      refine ⟨fun z => mul_nonneg (hS0 _) (hK0 _ _), fun C => ?_, fun C' => rfl⟩
      simp only [q]; rw [← Finset.mul_sum, hK1, mul_one]
    refine (transportCost_le S _ q hq).trans ?_
    rw [Fintype.sum_prod_type]
    have hrw : ∀ C, ∑ C', q (C, C') * matchCost (C, C').1 (C, C').2 =
        S C * ∑ C', offK K C C' * matchCost C C' := by
      intro C
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro C' _
      simp only [q, offK]
      split_ifs with h
      · rw [h, matchCost_self]; ring
      · ring
    simp_rw [hrw]
    refine moved_le S K hS0 hK0 _ A fun C C' hk hc => ?_
    obtain ⟨m1, m2, c, d, hm1, hm2, -, -, -, -, -, -, -, rfl⟩ := hKL C C' hk hc
    exact (matchCost_mv_le_emd T e hM C hm1 hm2).trans
      (hA C _ (hKL C _ hk hc))
  · -- dev
    intro v
    by_cases hv : T.IsAnc p v ∧ v ≠ p
    · have := Ex_push_le S K hS0 hK0 hK1 (fun C => devR (massBelow T e y v) (nC T e v C)) 0
        (fun C C' hk hc => by
          have := legal_dev T e y (hKL C C' hk hc) hv
          linarith)
      linarith
    · have := Ex_push_le S K hS0 hK0 hK1 (fun C => devR (massBelow T e y v) (nC T e v C)) 0
        (fun C C' hk hc => by
          have h := legal_outside T e y (hKL C C' hk hc) hv
          simp only [h, sub_self, le_refl])
      linarith
  · -- deep errors
    have h1 : ∀ v ∈ dpSet T p, T.W v * |Ex (push S K) (nC T e v) - massBelow T e y v| ≤
        T.W v * |Ex S (nC T e v) - massBelow T e y v| +
        T.W v * ∑ C, S C * ∑ C', offK K C C' * |nC T e v C' - nC T e v C| := by
      intro v hv
      have hW : 0 ≤ T.W v := by
        have hv' := (Finset.mem_filter.1 hv).2
        refine (T.W_pos v ?_).le
        intro hr; rw [hr] at hv'
        exact hv'.2.1 (t_anc_antisymm T hv'.1 (root_anc' T p)).symm
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hW
      have := Ex_push_abs S K hS0 hK0 hK1 (nC T e v)
      have h3 := abs_sub_le (Ex (push S K) (nC T e v)) (Ex S (nC T e v)) (massBelow T e y v)
      linarith
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add le_rfl ?_
    rw [swap3 (dpSet T p) T.W S (offK K) (fun v C C' => |nC T e v C' - nC T e v C|)]
    exact moved_le S K hS0 hK0 _ B fun C C' hk hc => hB C C' (hKL C C' hk hc)
  · -- children
    have h1 : ∀ u ∈ ch T p, |Ex (push S K) (nC T e u) - Ex S (nC T e u)| ≤
        1 * ∑ C, S C * ∑ C', offK K C C' * |nC T e u C' - nC T e u C| := by
      intro u _; rw [one_mul]; exact Ex_push_abs S K hS0 hK0 hK1 (nC T e u)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [swap3 (ch T p) (fun _ => 1) S (offK K) (fun v C C' => |nC T e v C' - nC T e v C|)]
    refine moved_le S K hS0 hK0 _ 2 fun C C' hk hc => ?_
    simp only [one_mul]
    exact legal_children T e y (hKL C C' hk hc)
  · -- outside means
    intro v hv
    have h := Ex_push_sub S K hK1 (nC T e v)
    have h0 : ∑ C, S C * ∑ C', offK K C C' * (nC T e v C' - nC T e v C) = 0 := by
      apply Finset.sum_eq_zero; intro C _
      rw [Finset.sum_eq_zero, mul_zero]; intro C' _
      unfold offK
      split_ifs with hc
      · rw [zero_mul]
      · by_cases hk : K C C' = 0
        · rw [hk, zero_mul]
        · rw [legal_outside T e y (hKL C C' hk hc) hv, sub_self, mul_zero]
    linarith
  · -- support
    intro C' hC'
    obtain ⟨C, -, hC⟩ := Finset.exists_ne_zero_of_sum_ne_zero hC'
    refine ⟨C, left_ne_zero_of_mul hC, fun v hv => ?_⟩
    by_cases hc : C' = C
    · rw [hc]
    · exact legal_outside T e y (hKL C C' (right_ne_zero_of_mul hC) hc) hv

theorem rel_comp (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (p : V) (A B : ℝ)
    (S1 S2 S3 : KConfig k M → ℝ) (μ1 μ2 : ℝ) (h1 : IsKState S1)
    (r1 : Rel T e y p A B S1 S2 μ1) (r2 : Rel T e y p A B S2 S3 μ2) :
    Rel T e y p A B S1 S3 (μ1 + μ2) := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, h1'⟩ := r1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, h2'⟩ := r2
  refine ⟨a2, by linarith, ?_, fun v => (d2 v).trans (d1 v), by linarith, ?_,
    fun v hv => (g2 v hv).trans (g1 v hv), ?_⟩
  · have := transportCost_triangle S1 S2 S3 h1 a1 a2
    nlinarith
  · have : ∀ u ∈ ch T p, |Ex S3 (nC T e u) - Ex S1 (nC T e u)| ≤
        |Ex S3 (nC T e u) - Ex S2 (nC T e u)| + |Ex S2 (nC T e u) - Ex S1 (nC T e u)| :=
      fun u _ => abs_sub_le _ _ _
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_add_distrib]; linarith
  · intro C3 hC3
    obtain ⟨C2, hC2, hv2⟩ := h2' C3 hC3
    obtain ⟨C1, hC1, hv1⟩ := h1' C2 hC2
    exact ⟨C1, hC1, fun v hv => (hv2 v hv).trans (hv1 v hv)⟩

end KernelR

section HstR

variable {V : Type} [Fintype V] [DecidableEq V]
variable {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]

/-- In a σ-HST, the edge weights along an ancestor chain at depths ≥ d0 sum to a geometric bound. -/
theorem chain_sum_le (T : WTree V) (σ L : ℝ) (hσ : 1 < σ) (hL : 0 < L)
    (hW : ∀ v, v ≠ T.root → T.W v = L / σ ^ (T.depth v - 1)) (w : V) (d0 : ℕ) (hd0 : 1 ≤ d0)
    (F : Finset V) (hF : ∀ x ∈ F, T.IsAnc x w ∧ d0 ≤ T.depth x) :
    ∑ x ∈ F, T.W x ≤ L * σ * ((1 / σ) ^ d0 / (1 - 1 / σ)) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hterm : ∀ x ∈ F, T.W x = L * σ * (1 / σ) ^ (T.depth x) := by
    intro x hx
    have hd := (hF x hx).2
    have hxr : x ≠ T.root := by intro hr; rw [hr, T.depth_root] at hd; omega
    rw [hW x hxr]
    obtain ⟨j, hj⟩ : ∃ j, T.depth x = j + 1 := ⟨T.depth x - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel, one_div_pow, pow_succ]
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have hinj : Set.InjOn T.depth F := by
    intro a ha b hb hab
    exact t_anc_unique T (hF a ha).1 (hF b hb).1 hab
  rw [← Finset.sum_image (g := T.depth) (f := fun j => L * σ * (1 / σ) ^ j) hinj]
  have hsub : F.image T.depth ⊆ Finset.Ico d0 (T.depth w + 1) := by
    intro j hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hj
    rw [Finset.mem_Ico]
    exact ⟨(hF x hx).2, Nat.lt_succ_of_le (t_anc_depth_le T (hF x hx).1)⟩
  have hnn : ∀ j ∈ Finset.Ico d0 (T.depth w + 1), j ∉ F.image T.depth →
      0 ≤ L * σ * (1 / σ) ^ j := fun j _ _ => by positivity
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact geom_sum_Ico_le_of_lt_one (by positivity) (by rw [div_lt_one hσ0]; exact hσ)

/-- Pointwise bound of the count change of a legal move. -/
theorem legal_pt (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) {p : V} {C C' : KConfig k M}
    (h : LegalMv T e y p C C') :
    ∃ w1 w2 : V, ∀ x, |nC T e x C' - nC T e x C| ≤
      (open Classical in if T.IsAnc x w1 ∧ (T.IsAnc p x ∧ x ≠ p) then (1 : ℝ) else 0) +
      (open Classical in if T.IsAnc x w2 ∧ (T.IsAnc p x ∧ x ≠ p) then (1 : ℝ) else 0) := by
  classical
  have h0 := h
  obtain ⟨m1, m2, c, d, hm1, hm2, -, -, -, -, -, -, -, rfl⟩ := h
  refine ⟨e m1, e m2, fun x => ?_⟩
  by_cases hx : T.IsAnc p x ∧ x ≠ p
  · unfold nC
    rw [mvK_val C hm1 hm2, count_mv T e C.1 hm1 hm2 x]
    by_cases a : T.IsAnc x (e m1) <;> by_cases b : T.IsAnc x (e m2)
    · rw [if_pos a, if_pos b, if_pos ⟨a, hx⟩, if_pos ⟨b, hx⟩]; norm_num
    · rw [if_pos a, if_neg b, if_pos ⟨a, hx⟩, if_neg (fun h => b h.1)]; norm_num
    · rw [if_neg a, if_pos b, if_neg (fun h => a h.1), if_pos ⟨b, hx⟩]; norm_num
    · rw [if_neg a, if_neg b, if_neg (fun h => a h.1), if_neg (fun h => b h.1)]; norm_num
  · rw [legal_outside T e y h0 hx, sub_self, abs_zero,
      if_neg (fun h => hx h.2), if_neg (fun h => hx h.2)]
    norm_num

theorem sum_ind_eq (R : Finset V) (f : V → ℝ) (P : V → Prop) [DecidablePred P] :
    ∑ x ∈ R, f x * (if P x then (1 : ℝ) else 0) = ∑ x ∈ R.filter P, f x := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro x _
  split_ifs <;> simp

/-- Weighted count change over a set `R` of nodes whose members strictly below `p` sit at depth
`≥ d0`. -/
theorem legal_weighted_le (T : WTree V) (σ L : ℝ) (hσ : 1 < σ) (hL : 0 < L)
    (hW : ∀ v, v ≠ T.root → T.W v = L / σ ^ (T.depth v - 1)) (e : M ≃ T.Leaf) (y : M → ℝ)
    {p : V} {C C' : KConfig k M} (h : LegalMv T e y p C C') (R : Finset V) (d0 : ℕ)
    (hd0 : 1 ≤ d0) (hR : ∀ x ∈ R, T.IsAnc p x ∧ x ≠ p → d0 ≤ T.depth x)
    (hRW : ∀ x ∈ R, 0 ≤ T.W x) :
    ∑ x ∈ R, T.W x * |nC T e x C' - nC T e x C| ≤
      2 * (L * σ * ((1 / σ) ^ d0 / (1 - 1 / σ))) := by
  classical
  obtain ⟨w1, w2, hpt⟩ := legal_pt T e y h
  have h1 : ∑ x ∈ R, T.W x * |nC T e x C' - nC T e x C| ≤
      ∑ x ∈ R, T.W x * (if T.IsAnc x w1 ∧ (T.IsAnc p x ∧ x ≠ p) then (1 : ℝ) else 0) +
      ∑ x ∈ R, T.W x * (if T.IsAnc x w2 ∧ (T.IsAnc p x ∧ x ≠ p) then (1 : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hRW x hx)
    convert hpt x using 2
  refine h1.trans ?_
  rw [sum_ind_eq, sum_ind_eq, two_mul]
  refine add_le_add (chain_sum_le T σ L hσ hL hW w1 d0 hd0 _ fun x hx => ?_)
    (chain_sum_le T σ L hσ hL hW w2 d0 hd0 _ fun x hx => ?_)
  · rw [Finset.mem_filter] at hx; exact ⟨hx.2.1, hR x hx.1 hx.2.2⟩
  · rw [Finset.mem_filter] at hx; exact ⟨hx.2.1, hR x hx.1 hx.2.2⟩

theorem legal_emd_le (T : WTree V) (σ L : ℝ) (hσ : 1 < σ) (hL : 0 < L)
    (hW : ∀ v, v ≠ T.root → T.W v = L / σ ^ (T.depth v - 1)) (e : M ≃ T.Leaf) (y : M → ℝ)
    {p : V} {C C' : KConfig k M} (h : LegalMv T e y p C C') :
    emd T e C.1 C'.1 ≤ 2 * (L * σ * ((1 / σ) ^ (T.depth p + 1) / (1 - 1 / σ))) := by
  unfold emd
  exact legal_weighted_le T σ L hσ hL hW e y h _ (T.depth p + 1) (by omega)
    (fun x _ hx => t_depth_lt T hx.1 hx.2)
    (fun x hx => (T.W_pos x (Finset.mem_filter.1 hx).2).le)

theorem dpSet_depth (T : WTree V) {p x : V} (hx : x ∈ dpSet T p) :
    T.depth p + 2 ≤ T.depth x := by
  classical
  unfold dpSet at hx
  rw [Finset.mem_filter] at hx
  obtain ⟨-, ha, hne, hch⟩ := hx
  have hlt := t_depth_lt T ha hne
  by_contra hcon
  apply hch
  rw [mem_ch]
  have hxr : x ≠ T.root := by intro hr; rw [hr, T.depth_root] at hlt; omega
  refine ⟨hxr, ?_⟩
  have := t_anc_eq T ha
  rw [show T.depth x - T.depth p = 1 by omega] at this
  exact this.symm

theorem legal_deep_le (T : WTree V) (σ L : ℝ) (hσ : 1 < σ) (hL : 0 < L)
    (hW : ∀ v, v ≠ T.root → T.W v = L / σ ^ (T.depth v - 1)) (e : M ≃ T.Leaf) (y : M → ℝ)
    {p : V} {C C' : KConfig k M} (h : LegalMv T e y p C C') :
    ∑ v ∈ dpSet T p, T.W v * |nC T e v C' - nC T e v C| ≤
      2 * (L * σ * ((1 / σ) ^ (T.depth p + 2) / (1 - 1 / σ))) := by
  refine legal_weighted_le T σ L hσ hL hW e y h _ (T.depth p + 2) (by omega)
    (fun x hx _ => dpSet_depth T hx) (fun x hx => ?_)
  have := dpSet_depth T hx
  exact (T.W_pos x (by intro hr; rw [hr, T.depth_root] at this; omega)).le

end HstR

section ProjR

variable {V : Type} [Fintype V] [DecidableEq V]
variable {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]

/-- The integer `n` lies between the floor and the ceiling of `t`. -/
def BoxZ (t : ℝ) (n : ℤ) : Prop := ⌊t⌋ ≤ n ∧ n ≤ ⌈t⌉

theorem devR_zero_of_box (t : ℝ) (n : ℤ) (h : BoxZ t n) : devR t n = 0 := by
  have hc1 : ⌈t⌉ ≤ ⌊t⌋ + 1 := Int.ceil_le_floor_add_one t
  unfold devR
  rcases (show n = ⌊t⌋ ∨ n = ⌈t⌉ by unfold BoxZ at h; omega) with h' | h'
  · rw [h', sub_self, abs_zero]; exact min_eq_left (abs_nonneg _)
  · rw [h', sub_self, abs_zero]; exact min_eq_right (abs_nonneg _)

theorem box_of_devR_zero (t : ℝ) (n : ℤ) (h : devR t n = 0) : BoxZ t n := by
  have hc1 : ⌈t⌉ ≤ ⌊t⌋ + 1 := Int.ceil_le_floor_add_one t
  have hfc : ⌊t⌋ ≤ ⌈t⌉ := Int.floor_le_ceil t
  unfold devR at h
  rcases min_choice |(n : ℝ) - ⌊t⌋| |(n : ℝ) - ⌈t⌉| with h' | h' <;> rw [h'] at h
  · have h2 : (n : ℝ) = ⌊t⌋ := by rw [abs_eq_zero, sub_eq_zero] at h; exact h
    have : n = ⌊t⌋ := by exact_mod_cast h2
    unfold BoxZ; omega
  · have h2 : (n : ℝ) = ⌈t⌉ := by rw [abs_eq_zero, sub_eq_zero] at h; exact h
    have : n = ⌈t⌉ := by exact_mod_cast h2
    unfold BoxZ; omega

theorem devR_dec_strict (t : ℝ) (n : ℤ) (h : ⌈t⌉ < n) :
    devR t ((n : ℝ) - 1) ≤ devR t n - 1 := by
  unfold devR
  have hfc : (⌊t⌋ : ℝ) ≤ ⌈t⌉ := by exact_mod_cast Int.floor_le_ceil t
  have hn : (⌈t⌉ : ℝ) + 1 ≤ n := by exact_mod_cast h
  have h1 : min |(n : ℝ) - 1 - ⌊t⌋| |(n : ℝ) - 1 - ⌈t⌉| ≤ n - 1 - ⌈t⌉ :=
    (min_le_right _ _).trans (le_of_eq (abs_of_nonneg (by linarith)))
  have h2 : (n : ℝ) - ⌈t⌉ ≤ min |(n : ℝ) - ⌊t⌋| |(n : ℝ) - ⌈t⌉| :=
    le_min ((by linarith : (n : ℝ) - ⌈t⌉ ≤ n - ⌊t⌋).trans (le_abs_self _)) (le_abs_self _)
  linarith

theorem devR_inc_strict (t : ℝ) (n : ℤ) (h : n < ⌊t⌋) :
    devR t ((n : ℝ) + 1) ≤ devR t n - 1 := by
  unfold devR
  have hfc : (⌊t⌋ : ℝ) ≤ ⌈t⌉ := by exact_mod_cast Int.floor_le_ceil t
  have hn : (n : ℝ) + 1 ≤ ⌊t⌋ := by exact_mod_cast h
  have h1 : min |(n : ℝ) + 1 - ⌊t⌋| |(n : ℝ) + 1 - ⌈t⌉| ≤ ⌊t⌋ - n - 1 :=
    (min_le_left _ _).trans (le_of_eq (by rw [abs_of_nonpos (by linarith)]; ring))
  have h2 : (⌊t⌋ : ℝ) - n ≤ min |(n : ℝ) - ⌊t⌋| |(n : ℝ) - ⌈t⌉| :=
    le_min (by rw [abs_of_nonpos (by linarith)]; linarith)
      (by rw [abs_of_nonpos (by linarith)]; linarith)
  linarith

/-- Total deviation of the children of `p` from their boxes. -/
noncomputable def childDev (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (p : V)
    (C : KConfig k M) : ℝ :=
  ∑ u ∈ ch T p, devR (massBelow T e y u) (nC T e u C)

/-- All children of `p` are in their boxes. -/
def ChBox (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (p : V) (C : KConfig k M) : Prop :=
  ∀ u ∈ ch T p, BoxZ (massBelow T e y u) (countBelow T e C.1 u)

theorem childDev_nonneg (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (p : V)
    (C : KConfig k M) : 0 ≤ childDev T e y p C :=
  Finset.sum_nonneg fun _ _ => devR_nonneg _ _

theorem childDev_zero_of_box (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (p : V)
    (C : KConfig k M) (h : ChBox T e y p C) : childDev T e y p C = 0 := by
  unfold childDev
  refine Finset.sum_eq_zero fun u hu => ?_
  have := devR_zero_of_box _ _ (h u hu)
  unfold nC
  simpa using this

theorem box_of_childDev_le (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (p : V)
    (C : KConfig k M) (h : childDev T e y p C ≤ 0) : ChBox T e y p C := by
  intro u hu
  have h0 : childDev T e y p C = 0 := le_antisymm h (childDev_nonneg T e y p C)
  unfold childDev at h0
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => devR_nonneg _ _)).1 h0 u hu
  apply box_of_devR_zero
  unfold nC at this
  simpa using this

/-- One improving legal move between two given children. -/
theorem fin_move (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (hy0 : ∀ m, 0 ≤ y m)
    (hy1 : ∀ m, y m ≤ 1) (p : V) (C : KConfig k M) {c d : V} (hc : c ∈ ch T p)
    (hd : d ∈ ch T p) (hcd : c ≠ d)
    (hc1 : ⌊massBelow T e y c⌋ < (countBelow T e C.1 c : ℤ))
    (hd1 : (countBelow T e C.1 d : ℤ) < ⌈massBelow T e y d⌉)
    (hstr : devR (massBelow T e y c) (nC T e c C - 1) ≤ devR (massBelow T e y c) (nC T e c C) - 1 ∨
      devR (massBelow T e y d) (nC T e d C + 1) ≤ devR (massBelow T e y d) (nC T e d C) - 1) :
    ∃ C', LegalMv T e y p C C' ∧ childDev T e y p C' ≤ childDev T e y p C - 1 := by
  classical
  obtain ⟨m1, hm1, ha1, hp1⟩ := rem_exists T e y hy0 C.1 c hc1
  obtain ⟨m2, hm2, ha2, hp2⟩ := ins_exists T e y hy1 C.1 d hd1
  have hL : LegalMv T e y p C (mvK C m1 m2) :=
    ⟨m1, m2, c, d, hm1, hm2, hc, hd, hcd, ha1, ha2, hp1, hp2, rfl⟩
  refine ⟨mvK C m1 m2, hL, ?_⟩
  have hdev : ∀ u ∈ ch T p, devR (massBelow T e y u) (nC T e u (mvK C m1 m2)) ≤
      devR (massBelow T e y u) (nC T e u C) := by
    intro u hu
    have hu' := (mem_ch T).1 hu
    refine legal_dev T e y hL ⟨hu'.2 ▸ t_anc_parent_self T u, ?_⟩
    intro h; rw [h] at hu'
    have := t_child_depth T hu'.1 hu'.2; omega
  have nc : nC T e c (mvK C m1 m2) = nC T e c C - 1 := by
    unfold nC
    rw [mvK_val C hm1 hm2, count_mv T e C.1 hm1 hm2 c, if_pos ha1, if_neg]
    · ring
    · intro h; exact hcd (t_child_unique T hc hd h ha2)
  have nd : nC T e d (mvK C m1 m2) = nC T e d C + 1 := by
    unfold nC
    rw [mvK_val C hm1 hm2, count_mv T e C.1 hm1 hm2 d, if_pos ha2, if_neg]
    · ring
    · intro h; exact hcd (t_child_unique T hc hd ha1 h)
  unfold childDev
  rcases hstr with hs | hs
  · rw [← Finset.add_sum_erase _ _ hc, ← Finset.add_sum_erase _ _ hc, nc]
    have := Finset.sum_le_sum (s := (ch T p).erase c) fun u hu => hdev u (Finset.mem_of_mem_erase hu)
    linarith
  · rw [← Finset.add_sum_erase _ _ hd, ← Finset.add_sum_erase _ _ hd, nd]
    have := Finset.sum_le_sum (s := (ch T p).erase d) fun u hu => hdev u (Finset.mem_of_mem_erase hu)
    linarith

theorem proj1_exists (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (hy0 : ∀ m, 0 ≤ y m)
    (hy1 : ∀ m, y m ≤ 1) (p : V) (C : KConfig k M)
    (hp : BoxZ (massBelow T e y p) (countBelow T e C.1 p)) (hnb : ¬ ChBox T e y p C) :
    ∃ C', LegalMv T e y p C C' ∧ childDev T e y p C' ≤ childDev T e y p C - 1 := by
  classical
  unfold ChBox at hnb
  push Not at hnb
  obtain ⟨u0, hu0, hb0⟩ := hnb
  have hpl : ¬ T.IsLeaf p := fun hl => by
    have := (mem_ch T).1 hu0; exact hl u0 this.1 this.2
  have hsum := count_split_int T e C.1 hpl
  have hms := mass_split T e y hpl
  have hfl := sum_floor_le (ch T p) (fun u => massBelow T e y u)
  have hcl := ceil_le_sum_ceil (ch T p) (fun u => massBelow T e y u)
  rw [← hms] at hfl hcl
  unfold BoxZ at hb0 hp
  have hfc0 := Int.floor_le_ceil (massBelow T e y u0)
  by_cases hf : ⌊massBelow T e y u0⌋ ≤ (countBelow T e C.1 u0 : ℤ)
  · have hgt : ⌈massBelow T e y u0⌉ < (countBelow T e C.1 u0 : ℤ) := by
      by_contra h; exact hb0 ⟨hf, not_lt.1 h⟩
    obtain ⟨d, hd, hdlt⟩ : ∃ d ∈ ch T p, (countBelow T e C.1 d : ℤ) < ⌈massBelow T e y d⌉ := by
      by_contra hcon
      push Not at hcon
      have := Finset.sum_lt_sum hcon ⟨u0, hu0, hgt⟩
      omega
    have hne : u0 ≠ d := by rintro rfl; omega
    refine fin_move T e y hy0 hy1 p C hu0 hd hne (by omega) hdlt (Or.inl ?_)
    have := devR_dec_strict (massBelow T e y u0) _ hgt
    unfold nC; push_cast at this; exact this
  · have hlt : (countBelow T e C.1 u0 : ℤ) < ⌊massBelow T e y u0⌋ := not_le.1 hf
    obtain ⟨c, hc, hclt⟩ : ∃ c ∈ ch T p, ⌊massBelow T e y c⌋ < (countBelow T e C.1 c : ℤ) := by
      by_contra hcon
      push Not at hcon
      have := Finset.sum_lt_sum hcon ⟨u0, hu0, hlt⟩
      omega
    have hne : c ≠ u0 := by rintro rfl; omega
    refine fin_move T e y hy0 hy1 p C hc hu0 hne hclt (by omega) (Or.inr ?_)
    have := devR_inc_strict (massBelow T e y u0) _ hlt
    unfold nC; push_cast at this; exact this

theorem rel_refl (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ)
    (p : V) (A B : ℝ) (S : KConfig k M → ℝ) (hS : IsKState S) : Rel T e y p A B S S 0 := by
  refine ⟨hS, le_rfl, ?_, fun v => le_rfl, by simp, by simp, fun v _ => rfl,
    fun C' h => ⟨C', h, fun _ _ => rfl⟩⟩
  rw [transportCost_self S hS.1, mul_zero]

theorem proj_all (T : WTree V) (e : M ≃ T.Leaf) (hM : T.IsLeafMetric M e) (y : M → ℝ)
    (hy0 : ∀ m, 0 ≤ y m) (hy1 : ∀ m, y m ≤ 1) (p : V) (A B : ℝ)
    (hA : ∀ C C' : KConfig k M, LegalMv T e y p C C' → emd T e C.1 C'.1 ≤ A)
    (hB : ∀ C C' : KConfig k M, LegalMv T e y p C C' →
      ∑ v ∈ dpSet T p, T.W v * |nC T e v C' - nC T e v C| ≤ B) :
    ∀ N : ℕ, ∀ S : KConfig k M → ℝ, IsKState S →
      (∀ C, S C ≠ 0 → BoxZ (massBelow T e y p) (countBelow T e C.1 p)) →
      (∀ C, S C ≠ 0 → childDev T e y p C ≤ N) →
      ∃ S' μ, Rel T e y p A B S S' μ ∧ μ ≤ Ex S (childDev T e y p) ∧
        ∀ C', S' C' ≠ 0 → ChBox T e y p C' := by
  classical
  let f : KConfig k M → KConfig k M := fun C =>
    if h : BoxZ (massBelow T e y p) (countBelow T e C.1 p) ∧ ¬ ChBox T e y p C then
      Classical.choose (proj1_exists T e y hy0 hy1 p C h.1 h.2) else C
  have hf1 : ∀ C, (BoxZ (massBelow T e y p) (countBelow T e C.1 p) ∧ ¬ ChBox T e y p C) →
      LegalMv T e y p C (f C) ∧ childDev T e y p (f C) ≤ childDev T e y p C - 1 := by
    intro C h
    have := Classical.choose_spec (proj1_exists T e y hy0 hy1 p C h.1 h.2)
    simp only [f, dif_pos h]; exact this
  have hf2 : ∀ C, ¬ (BoxZ (massBelow T e y p) (countBelow T e C.1 p) ∧ ¬ ChBox T e y p C) →
      f C = C := by
    intro C h; simp only [f, dif_neg h]
  let K : KConfig k M → KConfig k M → ℝ := fun C C' => if C' = f C then 1 else 0
  have hK0 : ∀ C C', 0 ≤ K C C' := fun C C' => by simp only [K]; split_ifs <;> norm_num
  have hK1 : ∀ C, ∑ C', K C C' = 1 := fun C => by simp [K]
  have hKf : ∀ C C', K C C' ≠ 0 → C' = f C := fun C C' h => by
    by_contra h'; exact h (by simp only [K]; rw [if_neg h'])
  have hmove : ∀ C C', K C C' ≠ 0 → C' ≠ C →
      LegalMv T e y p C C' ∧ childDev T e y p C' ≤ childDev T e y p C - 1 := by
    intro C C' hk hc
    have e1 := hKf C C' hk
    by_cases h : BoxZ (massBelow T e y p) (countBelow T e C.1 p) ∧ ¬ ChBox T e y p C
    · rw [e1]; exact hf1 C h
    · exact absurd (e1.trans (hf2 C h)) hc
  intro N
  induction N with
  | zero =>
    intro S hS hbox hN
    refine ⟨S, 0, rel_refl T e y p A B S hS, ?_,
      fun C' hC' => box_of_childDev_le T e y p C' (by simpa using hN C' hC')⟩
    unfold Ex
    exact Finset.sum_nonneg fun C _ => mul_nonneg (hS.1 C) (childDev_nonneg T e y p C)
  | succ N ih =>
    intro S hS hbox hN
    have r1 := rel_kernel T e hM y p A B S hS K hK0 hK1
      (fun C C' hk hc => (hmove C C' hk hc).1) hA hB
    have hdec := Ex_push_le S K hS.1 hK0 hK1 (childDev T e y p) (-1)
      (fun C C' hk hc => by linarith [(hmove C C' hk hc).2])
    have hsupp : ∀ C', push S K C' ≠ 0 → ∃ C, S C ≠ 0 ∧ K C C' ≠ 0 := by
      intro C' h
      obtain ⟨C, -, hC⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      exact ⟨C, left_ne_zero_of_mul hC, right_ne_zero_of_mul hC⟩
    have hbox1 : ∀ C', push S K C' ≠ 0 →
        BoxZ (massBelow T e y p) (countBelow T e C'.1 p) := by
      intro C' h
      obtain ⟨C, hC, hcnt⟩ := r1.2.2.2.2.2.2.2 C' h
      have := hcnt p (fun h => h.2 rfl)
      unfold nC at this
      have h2 : countBelow T e C'.1 p = countBelow T e C.1 p := by exact_mod_cast this
      rw [h2]; exact hbox C hC
    have hN1 : ∀ C', push S K C' ≠ 0 → childDev T e y p C' ≤ N := by
      intro C' h
      obtain ⟨C, hC, hk⟩ := hsupp C' h
      have hNC := hN C hC
      push_cast at hNC
      by_cases hb : ChBox T e y p C'
      · rw [childDev_zero_of_box T e y p C' hb]; positivity
      · by_cases hc : C' = C
        · exfalso
          rw [hc] at hb hk
          have h' := hf1 C ⟨hbox C hC, hb⟩
          have e1 := hKf C C hk
          rw [← e1] at h'
          linarith [h'.2]
        · linarith [(hmove C C' hk hc).2]
    obtain ⟨S2, μ2, r2, hμ2, hb2⟩ := ih (push S K) r1.1 hbox1 hN1
    refine ⟨S2, moveMass S K + μ2, rel_comp T e y p A B S _ S2 _ _ hS r1 r2, ?_, hb2⟩
    linarith

end ProjR
section RRR

variable {V : Type} [Fintype V] [DecidableEq V]
variable {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]

/-- Count strictly above the floor of the target mass. -/
abbrev hiP (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (u : V) (C : KConfig k M) : Prop :=
  ⌊massBelow T e y u⌋ < (countBelow T e C.1 u : ℤ)

/-- Count strictly below the ceiling of the target mass. -/
abbrev loP (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (u : V) (C : KConfig k M) : Prop :=
  (countBelow T e C.1 u : ℤ) < ⌈massBelow T e y u⌉

abbrev hlP (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (c d : V) (C : KConfig k M) : Prop :=
  hiP T e y c C ∧ loP T e y d C

abbrev hhP (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (c d : V) (C : KConfig k M) : Prop :=
  hiP T e y c C ∧ hiP T e y d C

abbrev llP (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (c d : V) (C : KConfig k M) : Prop :=
  loP T e y c C ∧ loP T e y d C

theorem not_hi_lo (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (u : V) (C : KConfig k M) :
    ¬ (hiP T e y u C ∧ loP T e y u C) := by
  rintro ⟨h1, h2⟩
  have := Int.ceil_le_floor_add_one (massBelow T e y u)
  simp only [hiP, loP] at h1 h2
  omega

/-- A legal move between two distinct children, with its effect on the children's counts. -/
theorem mv2 (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (hy0 : ∀ m, 0 ≤ y m)
    (hy1 : ∀ m, y m ≤ 1) (p : V) (C : KConfig k M) {c d : V} (hc : c ∈ ch T p)
    (hd : d ∈ ch T p) (hcd : c ≠ d)
    (hc1 : hiP T e y c C) (hd1 : loP T e y d C) :
    ∃ C', LegalMv T e y p C C' ∧ ∀ u ∈ ch T p,
      nC T e u C' = nC T e u C - (if u = c then 1 else 0) + (if u = d then 1 else 0) := by
  classical
  obtain ⟨m1, hm1, ha1, hp1⟩ := rem_exists T e y hy0 C.1 c hc1
  obtain ⟨m2, hm2, ha2, hp2⟩ := ins_exists T e y hy1 C.1 d hd1
  refine ⟨mvK C m1 m2, ⟨m1, m2, c, d, hm1, hm2, hc, hd, hcd, ha1, ha2, hp1, hp2, rfl⟩, ?_⟩
  intro u hu
  unfold nC
  rw [mvK_val C hm1 hm2, count_mv T e C.1 hm1 hm2 u]
  have e1 : T.IsAnc u (e m1) ↔ u = c :=
    ⟨fun h => t_child_unique T hu hc h ha1, fun h => h ▸ ha1⟩
  have e2 : T.IsAnc u (e m2) ↔ u = d :=
    ⟨fun h => t_child_unique T hu hd h ha2, fun h => h ▸ ha2⟩
  by_cases h1 : u = c <;> by_cases h2 : u = d
  · exact absurd (h1.symm.trans h2) hcd
  · rw [if_pos (e1.2 h1), if_neg (fun h => h2 (e2.1 h)), if_pos h1, if_neg h2]
  · rw [if_neg (fun h => h1 (e1.1 h)), if_pos (e2.2 h2), if_neg h1, if_pos h2]
  · rw [if_neg (fun h => h1 (e1.1 h)), if_neg (fun h => h2 (e2.1 h)), if_neg h1, if_neg h2]

/-- A move from a high child to a low child keeps every child in its box. -/
theorem chbox_mv (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (p : V) {C C' : KConfig k M}
    {c d : V} (hcd : c ≠ d) (hb : ChBox T e y p C) (h1 : hiP T e y c C) (h2 : loP T e y d C)
    (hn : ∀ u ∈ ch T p, nC T e u C' = nC T e u C - (if u = c then 1 else 0) +
      (if u = d then 1 else 0)) :
    ChBox T e y p C' := by
  intro u hu
  have h := hn u hu
  have hbu := hb u hu
  unfold BoxZ at hbu ⊢
  unfold nC at h
  simp only [hiP, loP] at h1 h2
  by_cases huc : u = c
  · subst huc
    rw [if_pos rfl, if_neg hcd] at h
    have h' : (countBelow T e C'.1 u : ℤ) = countBelow T e C.1 u - 1 := by
      have : (countBelow T e C'.1 u : ℝ) = (countBelow T e C.1 u : ℝ) - 1 := by linarith
      exact_mod_cast this
    omega
  · by_cases hud : u = d
    · subst hud
      rw [if_neg huc, if_pos rfl] at h
      have h' : (countBelow T e C'.1 u : ℤ) = countBelow T e C.1 u + 1 := by
        have : (countBelow T e C'.1 u : ℝ) = (countBelow T e C.1 u : ℝ) + 1 := by linarith
        exact_mod_cast this
      omega
    · rw [if_neg huc, if_neg hud] at h
      have h' : countBelow T e C'.1 u = countBelow T e C.1 u := by
        have : (countBelow T e C'.1 u : ℝ) = (countBelow T e C.1 u : ℝ) := by linarith
        exact_mod_cast this
      rw [h']; exact hbu

/-- Pairing lemma: a both-high configuration and a both-low configuration (same box at `p`)
admit a child that is high in the second and low in the first. -/
theorem ex_e (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (p : V) {C1 C2 : KConfig k M}
    {c d : V} (hc : c ∈ ch T p) (hd : d ∈ ch T p) (hcd : c ≠ d)
    (hp1 : BoxZ (massBelow T e y p) (countBelow T e C1.1 p))
    (hp2 : BoxZ (massBelow T e y p) (countBelow T e C2.1 p))
    (hb1 : ChBox T e y p C1) (hb2 : ChBox T e y p C2)
    (y1 : hhP T e y c d C1) (z2 : llP T e y c d C2) :
    ∃ u ∈ ch T p, hiP T e y u C2 ∧ loP T e y u C1 := by
  by_contra hcon
  push Not at hcon
  have hpl : ¬ T.IsLeaf p := fun hl => by
    have := (mem_ch T).1 hc; exact hl c this.1 this.2
  obtain ⟨y1c, y1d⟩ := y1
  obtain ⟨z2c, z2d⟩ := z2
  simp only [hiP, loP] at y1c y1d z2c z2d
  have key : ∀ u ∈ ch T p, (countBelow T e C2.1 u : ℤ) + (if u = c then 1 else 0) +
      (if u = d then 1 else 0) ≤ countBelow T e C1.1 u := by
    intro u hu
    have b1 := hb1 u hu
    have b2 := hb2 u hu
    have hfc := Int.ceil_le_floor_add_one (massBelow T e y u)
    unfold BoxZ at b1 b2
    by_cases huc : u = c
    · subst huc
      rw [if_pos rfl, if_neg hcd]
      omega
    · by_cases hud : u = d
      · subst hud
        rw [if_neg huc, if_pos rfl]
        omega
      · rw [if_neg huc, if_neg hud]
        have hh := hcon u hu
        by_cases h2 : ⌊massBelow T e y u⌋ < (countBelow T e C2.1 u : ℤ)
        · have h1 := hh h2
          omega
        · omega
  have hsum := Finset.sum_le_sum key
  have e1 : ∑ u ∈ ch T p, (if u = c then (1 : ℤ) else 0) = 1 := by simp [hc]
  have e2 : ∑ u ∈ ch T p, (if u = d then (1 : ℤ) else 0) = 1 := by simp [hd]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2,
    ← count_split_int T e C2.1 hpl, ← count_split_int T e C1.1 hpl] at hsum
  unfold BoxZ at hp1 hp2
  have := Int.ceil_le_floor_add_one (massBelow T e y p)
  omega

/-- Kernel given by a stay weight and finitely many weighted targets. -/
noncomputable def KW (w0 : KConfig k M → ℝ) (wt : KConfig k M → KConfig k M → ℝ)
    (G : KConfig k M → KConfig k M → KConfig k M) (C C' : KConfig k M) : ℝ :=
  (if C' = C then w0 C else 0) + ∑ C2, if C' = G C C2 then wt C C2 else 0

theorem KW_nonneg (w0 : KConfig k M → ℝ) (wt : KConfig k M → KConfig k M → ℝ)
    (G : KConfig k M → KConfig k M → KConfig k M) (hw0 : ∀ C, 0 ≤ w0 C)
    (hwt : ∀ C C2, 0 ≤ wt C C2) (C C' : KConfig k M) : 0 ≤ KW w0 wt G C C' := by
  unfold KW
  refine add_nonneg ?_ (Finset.sum_nonneg fun C2 _ => ?_)
  · split_ifs
    · exact hw0 C
    · exact le_rfl
  · split_ifs
    · exact hwt C C2
    · exact le_rfl

theorem KW_f (w0 : KConfig k M → ℝ) (wt : KConfig k M → KConfig k M → ℝ)
    (G : KConfig k M → KConfig k M → KConfig k M) (C : KConfig k M) (f : KConfig k M → ℝ) :
    ∑ C', KW w0 wt G C C' * f C' = w0 C * f C + ∑ C2, wt C C2 * f (G C C2) := by
  unfold KW
  simp_rw [add_mul, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp

theorem KW_row (w0 : KConfig k M → ℝ) (wt : KConfig k M → KConfig k M → ℝ)
    (G : KConfig k M → KConfig k M → KConfig k M) (C : KConfig k M) :
    ∑ C', KW w0 wt G C C' = w0 C + ∑ C2, wt C C2 := by
  have := KW_f w0 wt G C (fun _ => 1)
  simpa using this

theorem Ex_push_KW (w0 : KConfig k M → ℝ) (wt : KConfig k M → KConfig k M → ℝ)
    (G : KConfig k M → KConfig k M → KConfig k M) (S f : KConfig k M → ℝ) :
    Ex (push S (KW w0 wt G)) f =
      ∑ C, S C * (w0 C * f C + ∑ C2, wt C C2 * f (G C C2)) := by
  unfold Ex push
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro C _
  rw [← KW_f w0 wt G C f, Finset.mul_sum]
  apply Finset.sum_congr rfl; intros; ring

theorem moveMass_KW_le (w0 : KConfig k M → ℝ) (wt : KConfig k M → KConfig k M → ℝ)
    (G : KConfig k M → KConfig k M → KConfig k M) (S : KConfig k M → ℝ)
    (hS : ∀ C, 0 ≤ S C) (hwt : ∀ C C2, 0 ≤ wt C C2) :
    moveMass S (KW w0 wt G) ≤ ∑ C, S C * ∑ C2, wt C C2 := by
  unfold moveMass
  apply Finset.sum_le_sum; intro C _
  apply mul_le_mul_of_nonneg_left _ (hS C)
  have h : ∀ C', offK (KW w0 wt G) C C' ≤ ∑ C2, if C' = G C C2 then wt C C2 else 0 := by
    intro C'
    unfold offK KW
    by_cases hc : C' = C
    · rw [if_pos hc]
      exact Finset.sum_nonneg fun C2 _ => by
        split_ifs
        · exact hwt C C2
        · exact le_rfl
    · rw [if_neg hc, if_neg hc, zero_add]
  refine (Finset.sum_le_sum fun C' _ => h C').trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  simp

theorem KW_legal (w0 : KConfig k M → ℝ) (wt : KConfig k M → KConfig k M → ℝ)
    (G : KConfig k M → KConfig k M → KConfig k M) {C C' : KConfig k M}
    (h : KW w0 wt G C C' ≠ 0) (hc : C' ≠ C) : ∃ C2, wt C C2 ≠ 0 ∧ C' = G C C2 := by
  unfold KW at h
  rw [if_neg hc, zero_add] at h
  obtain ⟨C2, -, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hg : C' = G C C2
  · rw [if_pos hg] at h2; exact ⟨C2, h2, hg⟩
  · rw [if_neg hg] at h2; exact absurd rfl h2

theorem Ex_mono' (S f g : KConfig k M → ℝ) (hS : ∀ C, 0 ≤ S C)
    (h : ∀ C, S C ≠ 0 → f C ≤ g C) : Ex S f ≤ Ex S g := by
  unfold Ex
  apply Finset.sum_le_sum; intro C _
  by_cases hC : S C = 0
  · rw [hC]; simp
  · exact mul_le_mul_of_nonneg_left (h C hC) (hS C)

theorem Ex_const' (S : KConfig k M → ℝ) (hS : ∑ C, S C = 1) (a : ℝ) :
    Ex S (fun _ => a) = a := by
  unfold Ex
  rw [← Finset.sum_mul, hS, one_mul]

theorem Ex_two (S : KConfig k M → ℝ) (hS : ∑ C, S C = 1) (a s : ℝ)
    (P Q : KConfig k M → Prop) [DecidablePred P] [DecidablePred Q] :
    Ex S (fun C => a + s * ((if P C then 1 else 0) + (if Q C then 1 else 0))) =
      a + s * ((∑ C, if P C then S C else 0) + ∑ C, if Q C then S C else 0) := by
  unfold Ex
  rw [Finset.sum_congr rfl (fun C _ => show S C * (a + s * ((if P C then (1 : ℝ) else 0) +
      (if Q C then 1 else 0))) = S C * a + s * ((if P C then S C else 0) +
      (if Q C then S C else 0)) by split_ifs <;> ring)]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hS, one_mul, ← Finset.mul_sum,
    Finset.sum_add_distrib]

theorem transfer (T : WTree V) (e : M ≃ T.Leaf) (hM : T.IsLeafMetric M e) (y : M → ℝ)
    (hy0 : ∀ m, 0 ≤ y m) (hy1 : ∀ m, y m ≤ 1) (p : V) (A B : ℝ)
    (hA : ∀ C C' : KConfig k M, LegalMv T e y p C C' → emd T e C.1 C'.1 ≤ A)
    (hB : ∀ C C' : KConfig k M, LegalMv T e y p C C' →
      ∑ v ∈ dpSet T p, T.W v * |nC T e v C' - nC T e v C| ≤ B)
    (S : KConfig k M → ℝ) (hS : IsKState S)
    (hsup : ∀ C, S C ≠ 0 → BoxZ (massBelow T e y p) (countBelow T e C.1 p) ∧ ChBox T e y p C)
    {c d : V} (hc : c ∈ ch T p) (hd : d ∈ ch T p) (hcd : c ≠ d) (ε : ℝ) (hε : 0 < ε)
    (hεc : ε ≤ Ex S (nC T e c) - massBelow T e y c)
    (hεd : ε ≤ massBelow T e y d - Ex S (nC T e d)) :
    ∃ S' μ, Rel T e y p A B S S' μ ∧ μ ≤ 2 * ε ∧
      (∀ C', S' C' ≠ 0 → BoxZ (massBelow T e y p) (countBelow T e C'.1 p) ∧
        ChBox T e y p C') ∧
      ∀ u ∈ ch T p, Ex S' (nC T e u) =
        Ex S (nC T e u) - (if u = c then ε else 0) + (if u = d then ε else 0) := by
  have hS0 := hS.1
  have hS1 := hS.2
  have flc : ⌊massBelow T e y c⌋ < ⌈massBelow T e y c⌉ := by
    by_contra h
    push Not at h
    have : Ex S (nC T e c) ≤ Ex S (fun _ => massBelow T e y c) := by
      refine Ex_mono' S _ _ hS0 fun C hC => ?_
      have hb := (hsup C hC).2 c hc
      unfold BoxZ at hb
      have h1 : (countBelow T e C.1 c : ℤ) ≤ ⌊massBelow T e y c⌋ := hb.2.trans h
      have h2 : ((countBelow T e C.1 c : ℤ) : ℝ) ≤ (⌊massBelow T e y c⌋ : ℝ) := by
        exact_mod_cast h1
      show (countBelow T e C.1 c : ℝ) ≤ massBelow T e y c
      push_cast at h2
      linarith [Int.floor_le (massBelow T e y c)]
    rw [Ex_const' S hS1] at this
    linarith
  have fld : ⌊massBelow T e y d⌋ < ⌈massBelow T e y d⌉ := by
    by_contra h
    push Not at h
    have : Ex S (fun _ => massBelow T e y d) ≤ Ex S (nC T e d) := by
      refine Ex_mono' S _ _ hS0 fun C hC => ?_
      have hb := (hsup C hC).2 d hd
      unfold BoxZ at hb
      have h1 : ⌈massBelow T e y d⌉ ≤ (countBelow T e C.1 d : ℤ) := h.trans hb.1
      have h2 : (⌈massBelow T e y d⌉ : ℝ) ≤ ((countBelow T e C.1 d : ℤ) : ℝ) := by
        exact_mod_cast h1
      show massBelow T e y d ≤ (countBelow T e C.1 d : ℝ)
      push_cast at h2
      linarith [Int.le_ceil (massBelow T e y d)]
    rw [Ex_const' S hS1] at this
    linarith
  obtain ⟨mA, hmA⟩ : ∃ m : ℝ, m = ∑ C, if hlP T e y c d C then S C else 0 := ⟨_, rfl⟩
  obtain ⟨mB, hmB⟩ : ∃ m : ℝ, m = ∑ C, if hhP T e y c d C then S C else 0 := ⟨_, rfl⟩
  obtain ⟨mZ, hmZ⟩ : ∃ m : ℝ, m = ∑ C, if llP T e y c d C then S C else 0 := ⟨_, rfl⟩
  have mA0 : 0 ≤ mA := by
    rw [hmA]; exact Finset.sum_nonneg fun C _ => by split_ifs; exacts [hS0 C, le_rfl]
  have mB0 : 0 ≤ mB := by
    rw [hmB]; exact Finset.sum_nonneg fun C _ => by split_ifs; exacts [hS0 C, le_rfl]
  have mZ0 : 0 ≤ mZ := by
    rw [hmZ]; exact Finset.sum_nonneg fun C _ => by split_ifs; exacts [hS0 C, le_rfl]
  have hcb : Ex S (nC T e c) ≤ ((⌊massBelow T e y c⌋ : ℤ) : ℝ) + 1 * (mA + mB) := by
    rw [hmA, hmB]
    refine (Ex_mono' S _ _ hS0 fun C hC => ?_).trans
      (le_of_eq (Ex_two S hS1 ((⌊massBelow T e y c⌋ : ℤ) : ℝ) 1 (hlP T e y c d) (hhP T e y c d)))
    have hbc := (hsup C hC).2 c hc
    have hbd := (hsup C hC).2 d hd
    unfold BoxZ at hbc hbd
    have hfc := Int.ceil_le_floor_add_one (massBelow T e y c)
    have i1 : (0 : ℝ) ≤ if hlP T e y c d C then 1 else 0 := by split_ifs <;> norm_num
    have i2 : (0 : ℝ) ≤ if hhP T e y c d C then 1 else 0 := by split_ifs <;> norm_num
    show (countBelow T e C.1 c : ℝ) ≤ ((⌊massBelow T e y c⌋ : ℤ) : ℝ) + 1 *
      ((if hlP T e y c d C then 1 else 0) + (if hhP T e y c d C then 1 else 0))
    by_cases h1 : hiP T e y c C
    · have hle : (countBelow T e C.1 c : ℤ) ≤ ⌊massBelow T e y c⌋ + 1 := by omega
      have hle' : (countBelow T e C.1 c : ℝ) ≤ ((⌊massBelow T e y c⌋ : ℤ) : ℝ) + 1 := by
        exact_mod_cast hle
      by_cases h2 : loP T e y d C
      · rw [if_pos (show hlP T e y c d C from ⟨h1, h2⟩)]; linarith
      · have h3 : hiP T e y d C := by simp only [hiP, loP] at h2 ⊢; omega
        rw [if_pos (show hhP T e y c d C from ⟨h1, h3⟩)]; linarith
    · have hle : (countBelow T e C.1 c : ℤ) ≤ ⌊massBelow T e y c⌋ := by
        simp only [hiP] at h1; omega
      have hle' : (countBelow T e C.1 c : ℝ) ≤ ((⌊massBelow T e y c⌋ : ℤ) : ℝ) := by
        exact_mod_cast hle
      linarith
  have hdb : ((⌈massBelow T e y d⌉ : ℤ) : ℝ) + (-1) * (mA + mZ) ≤ Ex S (nC T e d) := by
    rw [hmA, hmZ]
    refine (le_of_eq (Ex_two S hS1 ((⌈massBelow T e y d⌉ : ℤ) : ℝ) (-1) (hlP T e y c d)
      (llP T e y c d)).symm).trans (Ex_mono' S _ _ hS0 fun C hC => ?_)
    have hbc := (hsup C hC).2 c hc
    have hbd := (hsup C hC).2 d hd
    unfold BoxZ at hbc hbd
    have hfd := Int.ceil_le_floor_add_one (massBelow T e y d)
    have i1 : (0 : ℝ) ≤ if hlP T e y c d C then 1 else 0 := by split_ifs <;> norm_num
    have i2 : (0 : ℝ) ≤ if llP T e y c d C then 1 else 0 := by split_ifs <;> norm_num
    show ((⌈massBelow T e y d⌉ : ℤ) : ℝ) + (-1) *
      ((if hlP T e y c d C then 1 else 0) + (if llP T e y c d C then 1 else 0)) ≤
        (countBelow T e C.1 d : ℝ)
    by_cases h2 : loP T e y d C
    · have hge : ⌈massBelow T e y d⌉ - 1 ≤ (countBelow T e C.1 d : ℤ) := by omega
      have hge' : ((⌈massBelow T e y d⌉ : ℤ) : ℝ) - 1 ≤ (countBelow T e C.1 d : ℝ) := by
        exact_mod_cast hge
      by_cases h1 : hiP T e y c C
      · rw [if_pos (show hlP T e y c d C from ⟨h1, h2⟩)]; linarith
      · have h3 : loP T e y c C := by simp only [hiP, loP] at h1 ⊢; omega
        rw [if_pos (show llP T e y c d C from ⟨h3, h2⟩)]; linarith
    · have hge : ⌈massBelow T e y d⌉ ≤ (countBelow T e C.1 d : ℤ) := by
        simp only [loP] at h2; omega
      have hge' : ((⌈massBelow T e y d⌉ : ℤ) : ℝ) ≤ (countBelow T e C.1 d : ℝ) := by
        exact_mod_cast hge
      linarith
  have hεB : ε ≤ mA + mB := by have := Int.floor_le (massBelow T e y c); linarith
  have hεZ : ε ≤ mA + mZ := by have := Int.le_ceil (massBelow T e y d); linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min ε mA := ⟨_, rfl⟩
  have ha1 : a ≤ ε := by rw [ha]; exact min_le_left _ _
  have ha2 : a ≤ mA := by rw [ha]; exact min_le_right _ _
  have ha0 : 0 ≤ a := by rw [ha]; exact le_min hε.le mA0
  obtain ⟨ε', hε'⟩ : ∃ x : ℝ, x = ε - a := ⟨_, rfl⟩
  have he0 : 0 ≤ ε' := by linarith
  have heB : ε' ≤ mB := by
    rcases le_total ε mA with h | h
    · rw [min_eq_left h] at ha; linarith
    · rw [min_eq_right h] at ha; linarith
  have heZ : ε' ≤ mZ := by
    rcases le_total ε mA with h | h
    · rw [min_eq_left h] at ha; linarith
    · rw [min_eq_right h] at ha; linarith
  obtain ⟨κ, hκ⟩ : ∃ x : ℝ, x = ε' / (mB * mZ) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact div_nonneg he0 (mul_nonneg mB0 mZ0)
  have hkB : κ * mZ = ε' / mB ∧ κ * mB = ε' / mZ ∧ κ * mB * mZ = ε' := by
    rcases eq_or_lt_of_le he0 with h | h
    · rw [hκ, ← h]; simp
    · have h1 : mB ≠ 0 := by linarith
      have h2 : mZ ≠ 0 := by linarith
      rw [hκ]; refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring
  have haA : a / mA * mA = a := by
    rcases eq_or_lt_of_le mA0 with h | h
    · rw [← h] at ha2 ⊢; rw [mul_zero]; linarith
    · have := h.ne'; field_simp
  have nXY : ∀ C : KConfig k M, ¬ (hlP T e y c d C ∧ hhP T e y c d C) := fun C h =>
    not_hi_lo T e y d C ⟨h.2.2, h.1.2⟩
  have nXZ : ∀ C : KConfig k M, ¬ (hlP T e y c d C ∧ llP T e y c d C) := fun C h =>
    not_hi_lo T e y c C ⟨h.1.1, h.2.1⟩
  have nYZ : ∀ C : KConfig k M, ¬ (hhP T e y c d C ∧ llP T e y c d C) := fun C h =>
    not_hi_lo T e y c C ⟨h.1.1, h.2.1⟩
  have hXm : ∀ C : KConfig k M, ∃ C', hlP T e y c d C → LegalMv T e y p C C' ∧
      ∀ u ∈ ch T p, nC T e u C' = nC T e u C - (if u = c then 1 else 0) +
        (if u = d then 1 else 0) := by
    intro C
    by_cases h : hlP T e y c d C
    · obtain ⟨C', h1, h2⟩ := mv2 T e y hy0 hy1 p C hc hd hcd h.1 h.2
      exact ⟨C', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨C, fun h' => absurd h' h⟩
  choose gX hgX using hXm
  have hPm : ∀ C1 C2 : KConfig k M, ∃ u : V, ∃ C' C'' : KConfig k M,
      ((S C1 ≠ 0 ∧ S C2 ≠ 0 ∧ hhP T e y c d C1 ∧ llP T e y c d C2) →
        (LegalMv T e y p C1 C' ∧ ChBox T e y p C' ∧ ∀ w ∈ ch T p, nC T e w C' =
          nC T e w C1 - (if w = c then 1 else 0) + (if w = u then 1 else 0)) ∧
        (LegalMv T e y p C2 C'' ∧ ChBox T e y p C'' ∧ ∀ w ∈ ch T p, nC T e w C'' =
          nC T e w C2 - (if w = u then 1 else 0) + (if w = d then 1 else 0))) ∧
      (¬ (S C1 ≠ 0 ∧ S C2 ≠ 0 ∧ hhP T e y c d C1 ∧ llP T e y c d C2) →
        C' = C1 ∧ C'' = C2) := by
    intro C1 C2
    by_cases hP : S C1 ≠ 0 ∧ S C2 ≠ 0 ∧ hhP T e y c d C1 ∧ llP T e y c d C2
    · obtain ⟨hs1, hs2, hy, hz⟩ := hP
      obtain ⟨bp1, bc1⟩ := hsup C1 hs1
      obtain ⟨bp2, bc2⟩ := hsup C2 hs2
      obtain ⟨u, hu, hu2, hu1⟩ := ex_e T e y p hc hd hcd bp1 bp2 bc1 bc2 hy hz
      have huc : c ≠ u := fun h => not_hi_lo T e y c C1 ⟨hy.1, by rw [h]; exact hu1⟩
      have hud : u ≠ d := fun h => not_hi_lo T e y d C2 ⟨by rw [← h]; exact hu2, hz.2⟩
      obtain ⟨C', hL1, hf1⟩ := mv2 T e y hy0 hy1 p C1 hc hu huc hy.1 hu1
      obtain ⟨C'', hL2, hf2⟩ := mv2 T e y hy0 hy1 p C2 hu hd hud hu2 hz.2
      exact ⟨u, C', C'', fun _ => ⟨⟨hL1, chbox_mv T e y p huc bc1 hy.1 hu1 hf1, hf1⟩,
        ⟨hL2, chbox_mv T e y p hud bc2 hu2 hz.2 hf2, hf2⟩⟩,
        fun h => absurd ⟨hs1, hs2, hy, hz⟩ h⟩
    · exact ⟨c, C1, C2, fun h => absurd h hP, fun _ => ⟨rfl, rfl⟩⟩
  choose ee g1 g2 hg using hPm
  obtain ⟨w0, hw0⟩ : ∃ f : KConfig k M → ℝ, ∀ C, f C =
      if hlP T e y c d C then 1 - a / mA else if hhP T e y c d C then 1 - ε' / mB
      else if llP T e y c d C then 1 - ε' / mZ else 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨wt, hwt⟩ : ∃ f : KConfig k M → KConfig k M → ℝ, ∀ C C2, f C C2 =
      if hlP T e y c d C then a / mA * S C2
      else if hhP T e y c d C then (if llP T e y c d C2 then κ * S C2 else 0)
      else if llP T e y c d C then (if hhP T e y c d C2 then κ * S C2 else 0) else 0 :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ f : KConfig k M → KConfig k M → KConfig k M, ∀ C C2, f C C2 =
      if hlP T e y c d C then gX C else if hhP T e y c d C then g1 C C2
      else if llP T e y c d C then g2 C2 C else C := ⟨_, fun _ _ => rfl⟩
  have r1 : a / mA ≤ 1 := div_le_one_of_le₀ ha2 mA0
  have r2 : ε' / mB ≤ 1 := div_le_one_of_le₀ heB mB0
  have r3 : ε' / mZ ≤ 1 := div_le_one_of_le₀ heZ mZ0
  have hw0n : ∀ C, 0 ≤ w0 C := fun C => by rw [hw0]; split_ifs <;> linarith
  have hwtn : ∀ C C2, 0 ≤ wt C C2 := fun C C2 => by
    rw [hwt]
    split_ifs <;> first | exact le_rfl | exact mul_nonneg hκ0 (hS0 C2) |
      exact mul_nonneg (div_nonneg ha0 mA0) (hS0 C2)
  have hsA : ∑ C2, a / mA * S C2 = a / mA := by rw [← Finset.mul_sum, hS1, mul_one]
  have hsZ : ∑ C2, (if llP T e y c d C2 then κ * S C2 else 0) = κ * mZ := by
    rw [hmZ, Finset.mul_sum]; exact Finset.sum_congr rfl fun C2 _ => by split_ifs <;> ring
  have hsB : ∑ C2, (if hhP T e y c d C2 then κ * S C2 else 0) = κ * mB := by
    rw [hmB, Finset.mul_sum]; exact Finset.sum_congr rfl fun C2 _ => by split_ifs <;> ring
  have hrowsum : ∀ C, ∑ C2, wt C C2 = (if hlP T e y c d C then a / mA else
      if hhP T e y c d C then κ * mZ else if llP T e y c d C then κ * mB else 0) := by
    intro C
    simp_rw [hwt C]
    by_cases hX : hlP T e y c d C
    · simp only [if_pos hX]; exact hsA
    · by_cases hY : hhP T e y c d C
      · simp only [if_neg hX, if_pos hY]; exact hsZ
      · by_cases hZ : llP T e y c d C
        · simp only [if_neg hX, if_neg hY, if_pos hZ]; exact hsB
        · simp only [if_neg hX, if_neg hY, if_neg hZ]; simp
  have hrow1 : ∀ C, w0 C + ∑ C2, wt C C2 = 1 := by
    intro C
    rw [hrowsum, hw0]
    split_ifs <;> linarith [hkB.1, hkB.2.1]
  have hK0 := KW_nonneg w0 wt G hw0n hwtn
  have hK1 : ∀ C, ∑ C', KW w0 wt G C C' = 1 := fun C => by rw [KW_row]; exact hrow1 C
  have hKL : ∀ C C', KW w0 wt G C C' ≠ 0 → C' ≠ C → LegalMv T e y p C C' := by
    intro C C' hk hne
    obtain ⟨C2, -, rfl⟩ := KW_legal w0 wt G hk hne
    rw [hG] at hne ⊢
    by_cases hX : hlP T e y c d C
    · rw [if_pos hX] at hne ⊢; exact (hgX C hX).1
    · rw [if_neg hX] at hne ⊢
      by_cases hY : hhP T e y c d C
      · rw [if_pos hY] at hne ⊢
        by_cases hP : S C ≠ 0 ∧ S C2 ≠ 0 ∧ hhP T e y c d C ∧ llP T e y c d C2
        · exact ((hg C C2).1 hP).1.1
        · exact absurd ((hg C C2).2 hP).1 hne
      · rw [if_neg hY] at hne ⊢
        by_cases hZ : llP T e y c d C
        · rw [if_pos hZ] at hne ⊢
          by_cases hP : S C2 ≠ 0 ∧ S C ≠ 0 ∧ hhP T e y c d C2 ∧ llP T e y c d C
          · exact ((hg C2 C).1 hP).2.1
          · exact absurd ((hg C2 C).2 hP).2 hne
        · rw [if_neg hZ] at hne; exact absurd rfl hne
  have r := rel_kernel T e hM y p A B S hS (KW w0 wt G) hK0 hK1 hKL hA hB
  have hsupp' : ∀ C', push S (KW w0 wt G) C' ≠ 0 →
      BoxZ (massBelow T e y p) (countBelow T e C'.1 p) ∧ ChBox T e y p C' := by
    intro C' h
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC, hcnt⟩ := r.2.2.2.2.2.2.2 C' h
      have := hcnt p (fun h => h.2 rfl)
      unfold nC at this
      have h2 : countBelow T e C'.1 p = countBelow T e C.1 p := by exact_mod_cast this
      rw [h2]; exact (hsup C hC).1
    · obtain ⟨C, -, hC⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have hSC := left_ne_zero_of_mul hC
      have hk := right_ne_zero_of_mul hC
      by_cases hne : C' = C
      · rw [hne]; exact (hsup C hSC).2
      obtain ⟨C2, -, rfl⟩ := KW_legal w0 wt G hk hne
      rw [hG] at hne ⊢
      by_cases hX : hlP T e y c d C
      · rw [if_pos hX]; exact chbox_mv T e y p hcd (hsup C hSC).2 hX.1 hX.2 (hgX C hX).2
      · rw [if_neg hX] at hne ⊢
        by_cases hY : hhP T e y c d C
        · rw [if_pos hY] at hne ⊢
          by_cases hP : S C ≠ 0 ∧ S C2 ≠ 0 ∧ hhP T e y c d C ∧ llP T e y c d C2
          · exact ((hg C C2).1 hP).1.2.1
          · exact absurd ((hg C C2).2 hP).1 hne
        · rw [if_neg hY] at hne ⊢
          by_cases hZ : llP T e y c d C
          · rw [if_pos hZ] at hne ⊢
            by_cases hP : S C2 ≠ 0 ∧ S C ≠ 0 ∧ hhP T e y c d C2 ∧ llP T e y c d C
            · exact ((hg C2 C).1 hP).2.2.1
            · exact absurd ((hg C2 C).2 hP).2 hne
          · rw [if_neg hZ] at hne; exact absurd rfl hne
  have hμ : moveMass S (KW w0 wt G) ≤ 2 * ε := by
    refine (moveMass_KW_le w0 wt G S hS0 hwtn).trans ?_
    have hpc : ∀ C, S C * ∑ C2, wt C C2 = (if hlP T e y c d C then S C else 0) * (a / mA) +
        (if hhP T e y c d C then S C else 0) * (κ * mZ) +
        (if llP T e y c d C then S C else 0) * (κ * mB) := by
      intro C
      rw [hrowsum C]
      by_cases hX : hlP T e y c d C
      · simp only [if_pos hX, if_neg (fun h => nXY C ⟨hX, h⟩), if_neg (fun h => nXZ C ⟨hX, h⟩)]
        ring
      · by_cases hY : hhP T e y c d C
        · simp only [if_neg hX, if_pos hY, if_neg (fun h => nYZ C ⟨hY, h⟩)]; ring
        · by_cases hZ : llP T e y c d C
          · simp only [if_neg hX, if_neg hY, if_pos hZ]; ring
          · simp only [if_neg hX, if_neg hY, if_neg hZ]; ring
    rw [Finset.sum_congr rfl fun C _ => hpc C, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← hmA, ← hmB, ← hmZ]
    have e1 : mA * (a / mA) = a := by rw [mul_comm]; exact haA
    have e2 : mB * (κ * mZ) = ε' := by rw [← hkB.2.2]; ring
    have e3 : mZ * (κ * mB) = ε' := by rw [← hkB.2.2]; ring
    rw [e1, e2, e3]; linarith
  have hEx : ∀ u ∈ ch T p, Ex (push S (KW w0 wt G)) (nC T e u) =
      Ex S (nC T e u) - (if u = c then ε else 0) + (if u = d then ε else 0) := by
    intro u hu
    obtain ⟨Dc, hDc⟩ : ∃ x : ℝ, x = -(if u = c then (1 : ℝ) else 0) + (if u = d then 1 else 0) :=
      ⟨_, rfl⟩
    obtain ⟨bX, hbX⟩ : ∃ f : KConfig k M → KConfig k M → ℝ, ∀ C C2, f C C2 =
        if hlP T e y c d C then a / mA * S C2 * Dc else 0 := ⟨_, fun _ _ => rfl⟩
    obtain ⟨bY, hbY⟩ : ∃ f : KConfig k M → KConfig k M → ℝ, ∀ C C2, f C C2 =
        if hhP T e y c d C ∧ llP T e y c d C2 then
          κ * S C2 * (-(if u = c then (1 : ℝ) else 0) + (if u = ee C C2 then 1 else 0)) else 0 :=
      ⟨_, fun _ _ => rfl⟩
    obtain ⟨bZ, hbZ⟩ : ∃ f : KConfig k M → KConfig k M → ℝ, ∀ C C2, f C C2 =
        if llP T e y c d C ∧ hhP T e y c d C2 then
          κ * S C2 * (-(if u = ee C2 C then (1 : ℝ) else 0) + (if u = d then 1 else 0)) else 0 :=
      ⟨_, fun _ _ => rfl⟩
    have hpt : ∀ C C2, S C ≠ 0 → wt C C2 * nC T e u (G C C2) =
        wt C C2 * nC T e u C + (bX C C2 + bY C C2 + bZ C C2) := by
      intro C C2 hSC
      rw [hwt C C2, hG C C2, hbX C C2, hbY C C2, hbZ C C2]
      by_cases hX : hlP T e y c d C
      · have nY : ¬ (hhP T e y c d C ∧ llP T e y c d C2) := fun h => nXY C ⟨hX, h.1⟩
        have nZ : ¬ (llP T e y c d C ∧ hhP T e y c d C2) := fun h => nXZ C ⟨hX, h.1⟩
        simp only [if_pos hX, if_neg nY, if_neg nZ]
        rw [(hgX C hX).2 u hu, hDc]; ring
      · simp only [if_neg hX]
        by_cases hY : hhP T e y c d C
        · have nZ : ¬ (llP T e y c d C ∧ hhP T e y c d C2) := fun h => nYZ C ⟨hY, h.1⟩
          simp only [if_pos hY, if_neg nZ]
          by_cases hZ2 : llP T e y c d C2
          · simp only [if_pos hZ2,
              if_pos (show hhP T e y c d C ∧ llP T e y c d C2 from ⟨hY, hZ2⟩)]
            by_cases hS2 : S C2 = 0
            · rw [hS2]; ring
            · rw [((hg C C2).1 ⟨hSC, hS2, hY, hZ2⟩).1.2.2 u hu]; ring
          · simp only [if_neg hZ2,
              if_neg (fun h : hhP T e y c d C ∧ llP T e y c d C2 => hZ2 h.2)]; ring
        · simp only [if_neg hY, if_neg (fun h : hhP T e y c d C ∧ llP T e y c d C2 => hY h.1)]
          by_cases hZ : llP T e y c d C
          · simp only [if_pos hZ]
            by_cases hY2 : hhP T e y c d C2
            · simp only [if_pos hY2,
                if_pos (show llP T e y c d C ∧ hhP T e y c d C2 from ⟨hZ, hY2⟩)]
              by_cases hS2 : S C2 = 0
              · rw [hS2]; ring
              · rw [((hg C2 C).1 ⟨hS2, hSC, hY2, hZ⟩).2.2.2 u hu]; ring
            · simp only [if_neg hY2,
                if_neg (fun h : llP T e y c d C ∧ hhP T e y c d C2 => hY2 h.2)]; ring
          · simp only [if_neg hZ,
              if_neg (fun h : llP T e y c d C ∧ hhP T e y c d C2 => hZ h.1)]; ring
    rw [Ex_push_KW]
    have step1 : ∀ C, S C * (w0 C * nC T e u C + ∑ C2, wt C C2 * nC T e u (G C C2)) =
        S C * nC T e u C + (S C * ∑ C2, bX C C2 + (S C * ∑ C2, bY C C2 +
          S C * ∑ C2, bZ C C2)) := by
      intro C
      by_cases hSC : S C = 0
      · rw [hSC]; ring
      · rw [Finset.sum_congr rfl (fun C2 _ => hpt C C2 hSC), Finset.sum_add_distrib,
          ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hw : w0 C = 1 - ∑ C2, wt C C2 := by linarith [hrow1 C]
        rw [hw]; ring
    rw [Finset.sum_congr rfl fun C _ => step1 C, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    have sX : ∑ C, S C * ∑ C2, bX C C2 = a * Dc := by
      have h1 : ∀ C, S C * ∑ C2, bX C C2 = (if hlP T e y c d C then S C else 0) * (a / mA * Dc) := by
        intro C
        simp_rw [hbX C]
        split_ifs
        · rw [show ∑ C2, a / mA * S C2 * Dc = a / mA * Dc * ∑ C2, S C2 by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hS1]; ring
        · simp
      rw [Finset.sum_congr rfl fun C _ => h1 C, ← Finset.sum_mul, ← hmA,
        show mA * (a / mA * Dc) = a / mA * mA * Dc by ring, haA]
    have sYZ : ∑ C, S C * ∑ C2, bY C C2 + ∑ C, S C * ∑ C2, bZ C C2 = ε' * Dc := by
      have e1 : ∑ C, S C * ∑ C2, bZ C C2 = ∑ C, ∑ C2, S C2 * bZ C2 C := by
        simp_rw [Finset.mul_sum]; exact Finset.sum_comm
      rw [e1]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      have h2 : ∀ C C2, S C * bY C C2 + S C2 * bZ C2 C = (if hhP T e y c d C then S C else 0) *
          (if llP T e y c d C2 then S C2 else 0) * (κ * Dc) := by
        intro C C2
        rw [hbY, hbZ]
        by_cases h1 : hhP T e y c d C
        · by_cases h2 : llP T e y c d C2
          · have q1 : hhP T e y c d C ∧ llP T e y c d C2 := ⟨h1, h2⟩
            have q2 : llP T e y c d C2 ∧ hhP T e y c d C := ⟨h2, h1⟩
            rw [if_pos q1, if_pos q2, if_pos h1, if_pos h2, hDc]; ring
          · have q1 : ¬ (hhP T e y c d C ∧ llP T e y c d C2) := fun h => h2 h.2
            have q2 : ¬ (llP T e y c d C2 ∧ hhP T e y c d C) := fun h => h2 h.1
            rw [if_neg q1, if_neg q2, if_neg h2]; ring
        · have q1 : ¬ (hhP T e y c d C ∧ llP T e y c d C2) := fun h => h1 h.1
          have q2 : ¬ (llP T e y c d C2 ∧ hhP T e y c d C) := fun h => h1 h.2
          rw [if_neg q1, if_neg q2, if_neg h1]; ring
      rw [Finset.sum_congr rfl fun C _ => (Finset.sum_add_distrib).symm.trans
        (Finset.sum_congr rfl fun C2 _ => h2 C C2)]
      rw [show (∑ C, ∑ C2, (if hhP T e y c d C then S C else 0) *
          (if llP T e y c d C2 then S C2 else 0) * (κ * Dc)) =
          (∑ C, if hhP T e y c d C then S C else 0) *
          (∑ C2, if llP T e y c d C2 then S C2 else 0) * (κ * Dc) by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun C _ => by rw [Finset.sum_mul]]
      rw [← hmB, ← hmZ, show mB * mZ * (κ * Dc) = κ * mB * mZ * Dc by ring, hkB.2.2]
    have fin : a * Dc + ε' * Dc = -(if u = c then ε else 0) + (if u = d then ε else 0) := by
      rw [hDc, hε']; split_ifs <;> ring
    have hE : Ex S (nC T e u) = ∑ C, S C * nC T e u C := rfl
    rw [hE]
    linarith [sX, sYZ, fin]
  exact ⟨push S (KW w0 wt G), moveMass S (KW w0 wt G), r, hμ, hsupp', hEx⟩

theorem exists_pos_neg (s : Finset V) (f : V → ℝ) (hs : ∑ u ∈ s, f u = 0) {u0 : V}
    (hu0 : u0 ∈ s) (h0 : f u0 ≠ 0) : ∃ c ∈ s, ∃ d ∈ s, 0 < f c ∧ f d < 0 := by
  rcases lt_or_gt_of_ne h0 with h | h
  · by_contra hcon
    have hall : ∀ c ∈ s, f c ≤ (fun _ => (0 : ℝ)) c := fun c hc => by
      by_contra h'
      exact hcon ⟨c, hc, u0, hu0, lt_of_not_ge h', h⟩
    have := Finset.sum_lt_sum hall ⟨u0, hu0, h⟩
    simp only [Finset.sum_const_zero] at this
    linarith
  · by_contra hcon
    have hall : ∀ d ∈ s, (fun _ => (0 : ℝ)) d ≤ f d := fun d hd => by
      by_contra h'
      exact hcon ⟨u0, hu0, d, hd, h, lt_of_not_ge h'⟩
    have := Finset.sum_lt_sum hall ⟨u0, hu0, h⟩
    simp only [Finset.sum_const_zero] at this
    linarith

/-- Mean fixing at `p`: with every child box-valued and the children's means summing to the
right total, legal moves make every child mean exact at move mass at most the total error. -/
theorem rr_all (T : WTree V) (e : M ≃ T.Leaf) (hM : T.IsLeafMetric M e) (y : M → ℝ)
    (hy0 : ∀ m, 0 ≤ y m) (hy1 : ∀ m, y m ≤ 1) (p : V) (A B : ℝ)
    (hA : ∀ C C' : KConfig k M, LegalMv T e y p C C' → emd T e C.1 C'.1 ≤ A)
    (hB : ∀ C C' : KConfig k M, LegalMv T e y p C C' →
      ∑ v ∈ dpSet T p, T.W v * |nC T e v C' - nC T e v C| ≤ B) :
    ∀ N : ℕ, ∀ F : Finset V, F.card ≤ N → ∀ S : KConfig k M → ℝ, IsKState S →
      (∀ C, S C ≠ 0 → BoxZ (massBelow T e y p) (countBelow T e C.1 p) ∧ ChBox T e y p C) →
      (∑ u ∈ ch T p, Ex S (nC T e u) = ∑ u ∈ ch T p, massBelow T e y u) →
      (∀ u ∈ ch T p, u ∉ F → Ex S (nC T e u) = massBelow T e y u) →
      ∃ S' μ, Rel T e y p A B S S' μ ∧
        μ ≤ ∑ u ∈ ch T p, |Ex S (nC T e u) - massBelow T e y u| ∧
        (∀ C', S' C' ≠ 0 → BoxZ (massBelow T e y p) (countBelow T e C'.1 p) ∧
          ChBox T e y p C') ∧
        ∀ u ∈ ch T p, Ex S' (nC T e u) = massBelow T e y u := by
  intro N
  induction N with
  | zero =>
    intro F hF S hS hsup _ hex
    have hF0 : F = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hF)
    exact ⟨S, 0, rel_refl T e y p A B S hS, Finset.sum_nonneg fun _ _ => abs_nonneg _, hsup,
      fun u hu => hex u hu (by simp [hF0])⟩
  | succ N ih =>
    intro F hF S hS hsup hsum hex
    by_cases hall : ∀ u ∈ ch T p, Ex S (nC T e u) = massBelow T e y u
    · exact ⟨S, 0, rel_refl T e y p A B S hS, Finset.sum_nonneg fun _ _ => abs_nonneg _,
        hsup, hall⟩
    push Not at hall
    obtain ⟨u0, hu0, hne⟩ := hall
    have hs0 : ∑ u ∈ ch T p, (Ex S (nC T e u) - massBelow T e y u) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    obtain ⟨c, hc, d, hd, hcpos, hdneg⟩ :=
      exists_pos_neg (ch T p) _ hs0 hu0 (sub_ne_zero.2 hne)
    have hcd : c ≠ d := by rintro rfl; linarith
    obtain ⟨ε, hεdef⟩ : ∃ x : ℝ, x = min (Ex S (nC T e c) - massBelow T e y c)
        (massBelow T e y d - Ex S (nC T e d)) := ⟨_, rfl⟩
    have hε : 0 < ε := by rw [hεdef]; exact lt_min hcpos (by linarith)
    have hεc : ε ≤ Ex S (nC T e c) - massBelow T e y c := by rw [hεdef]; exact min_le_left _ _
    have hεd : ε ≤ massBelow T e y d - Ex S (nC T e d) := by rw [hεdef]; exact min_le_right _ _
    obtain ⟨S1, μ1, r1, hμ1, hsup1, hex1⟩ :=
      transfer T e hM y hy0 hy1 p A B hA hB S hS hsup hc hd hcd ε hε hεc hεd
    have e1 : ∑ u ∈ ch T p, (if u = c then ε else 0) = ε := by simp [hc]
    have e2 : ∑ u ∈ ch T p, (if u = d then ε else 0) = ε := by simp [hd]
    have hsum1 : ∑ u ∈ ch T p, Ex S1 (nC T e u) = ∑ u ∈ ch T p, massBelow T e y u := by
      rw [Finset.sum_congr rfl hex1, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, e1, e2]
      ring
    have hcF : c ∈ F := by
      by_contra h; have := hex c hc h; linarith
    have hdF : d ∈ F := by
      by_contra h; have := hex d hd h; linarith
    obtain ⟨w, hwF, hex1'⟩ : ∃ w ∈ F, ∀ u ∈ ch T p, u ∉ F.erase w →
        Ex S1 (nC T e u) = massBelow T e y u := by
      rcases le_total (Ex S (nC T e c) - massBelow T e y c)
          (massBelow T e y d - Ex S (nC T e d)) with h | h
      · refine ⟨c, hcF, fun u hu hnot => ?_⟩
        rw [hex1 u hu]
        by_cases huc : u = c
        · rw [huc, if_pos rfl, if_neg hcd, hεdef, min_eq_left h]; ring
        · have huF : u ∉ F := fun h' => hnot (Finset.mem_erase.2 ⟨huc, h'⟩)
          have := hex u hu huF
          have hud : u ≠ d := by rintro rfl; linarith
          rw [if_neg huc, if_neg hud, this]; ring
      · refine ⟨d, hdF, fun u hu hnot => ?_⟩
        rw [hex1 u hu]
        by_cases hud : u = d
        · rw [hud, if_neg (Ne.symm hcd), if_pos rfl, hεdef, min_eq_right h]; ring
        · have huF : u ∉ F := fun h' => hnot (Finset.mem_erase.2 ⟨hud, h'⟩)
          have := hex u hu huF
          have huc : u ≠ c := by rintro rfl; linarith
          rw [if_neg huc, if_neg hud, this]; ring
    have hcard : (F.erase w).card ≤ N := by
      rw [Finset.card_erase_of_mem hwF]; omega
    obtain ⟨S2, μ2, r2, hμ2, hsup2, hex2⟩ := ih (F.erase w) hcard S1 r1.1 hsup1 hsum1 hex1'
    refine ⟨S2, μ1 + μ2, rel_comp T e y p A B S S1 S2 μ1 μ2 hS r1 r2, ?_, hsup2, hex2⟩
    have hpt : ∀ u ∈ ch T p, |Ex S1 (nC T e u) - massBelow T e y u| =
        |Ex S (nC T e u) - massBelow T e y u| -
          ((if u = c then ε else 0) + (if u = d then ε else 0)) := by
      intro u hu
      rw [hex1 u hu]
      by_cases huc : u = c
      · rw [huc, if_pos rfl, if_neg hcd]
        rw [show Ex S (nC T e c) - ε + 0 - massBelow T e y c =
          Ex S (nC T e c) - massBelow T e y c - ε by ring]
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Ex S (nC T e c) - massBelow T e y c - ε),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ Ex S (nC T e c) - massBelow T e y c)]
        ring
      · by_cases hud : u = d
        · rw [hud, if_neg (Ne.symm hcd), if_pos rfl]
          rw [show Ex S (nC T e d) - 0 + ε - massBelow T e y d =
            Ex S (nC T e d) - massBelow T e y d + ε by ring]
          rw [abs_of_nonpos (by linarith : Ex S (nC T e d) - massBelow T e y d + ε ≤ 0),
            abs_of_nonpos (by linarith : Ex S (nC T e d) - massBelow T e y d ≤ 0)]
          ring
        · simp only [if_neg huc, if_neg hud, sub_zero, add_zero]
    have habs : ∑ u ∈ ch T p, |Ex S1 (nC T e u) - massBelow T e y u| =
        ∑ u ∈ ch T p, |Ex S (nC T e u) - massBelow T e y u| - 2 * ε := by
      rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib, e1, e2]
      ring
    linarith

end RRR

section Assembly

/-- The generalized rebalancing statement (core obligation GR). Lemma 25 is the case x' = x. -/
def GR (σ C : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
  ∀ (M : Type) [MetricSpace M] [Fintype M] [DecidableEq M] (e : M ≃ T.Leaf),
    T.IsLeafMetric M e →
  ∀ (k : ℕ) (x x' : M → ℝ) (S : KConfig k M → ℝ), IsFracState k x → IsFracState k x' →
    IsKState S → Consistent S x →
    ∃ S' : KConfig k M → ℝ, IsKState S' ∧ Consistent S' x' ∧ Balanced T e x' S' ∧
      transportCost S S' ≤ C * (balanceGap T e S x' + fracMoveCost T e x x')

/-- Iterate a step function along consecutive entries of a list. -/
noncomputable def iterL {α β : Type} (step : α → β → β → α) (a0 : α) (l : List β) (d : β) :
    ℕ → α
  | 0 => a0
  | t + 1 => step (iterL step a0 l d t) (l.getD t d) (l.getD (t + 1) d)

/-- Iterate a step function along a sequence. -/
noncomputable def iterS {α β : Type} (step : α → β → β → α) (a0 : α) (xs : ℕ → β) : ℕ → α
  | 0 => a0
  | t + 1 => step (iterS step a0 xs t) (xs t) (xs (t + 1))

theorem getD_range_map {β : Type} (xs : ℕ → β) (d : β) (n i : ℕ) (h : i < n) :
    ((List.range n).map xs).getD i d = xs i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem iterL_range {α β : Type} (step : α → β → β → α) (a0 : α) (xs : ℕ → β) (d : β)
    (n : ℕ) : ∀ t, t < n → iterL step a0 ((List.range n).map xs) d t = iterS step a0 xs t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    simp only [iterL, iterS]
    rw [ih (by omega), getD_range_map xs d n t (by omega),
      getD_range_map xs d n (t + 1) ht]

variable {V : Type} [Fintype V] [DecidableEq V]

theorem pure_isKState {k : ℕ} {M : Type} [Fintype M] [DecidableEq M] (C₀ : KConfig k M) :
    IsKState (pureState C₀) := by
  refine ⟨fun C => ?_, ?_⟩
  · unfold pureState; split_ifs <;> norm_num
  · unfold pureState; simp

theorem pure_consistent {k : ℕ} {M : Type} [Fintype M] [DecidableEq M] (C₀ : KConfig k M) :
    Consistent (pureState C₀) (fun m => if m ∈ C₀.1 then 1 else 0) := by
  intro i
  rw [Finset.sum_filter, Finset.sum_eq_single C₀]
  · simp [pureState]
  · intro b _ hb; simp [pureState, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem pure_balanced (T : WTree V) {k : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    (e : M ≃ T.Leaf) (C₀ : KConfig k M) :
    Balanced T e (fun m => if m ∈ C₀.1 then 1 else 0) (pureState C₀) := by
  classical
  intro C hC p
  have hC' : C = C₀ := by
    by_contra h; exact hC (by simp [pureState, h])
  subst hC'
  left
  have hm : massBelow T e (fun m => if m ∈ C.1 then (1 : ℝ) else 0) p =
      (countBelow T e C.1 p : ℝ) := by
    rw [countBelow_eq]
    unfold massBelow
    rw [← Finset.sum_subset (Finset.subset_univ C.1)]
    · apply Finset.sum_congr rfl
      intro m hm
      simp [hm]
    · intro m _ hm
      simp [hm]
  rw [hm, Int.floor_natCast]

/-- **Assembly24**: GR gives Theorem 24 with constant 2C. -/
theorem online_of_GR (σ C : ℝ) (hC : 0 < C) (h : GR σ C) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M] [DecidableEq M] (e : M ≃ T.Leaf),
        T.IsLeafMetric M e →
      ∀ (k : ℕ) (C₀ : KConfig k M),
        ∃ P : List (M → ℝ) → (KConfig k M → ℝ),
          ∀ xs : ℕ → M → ℝ, (∀ t, IsFracState k (xs t)) →
            xs 0 = (fun m => if m ∈ C₀.1 then 1 else 0) →
            P [xs 0] = pureState C₀ ∧
            (∀ t, IsKState (P ((List.range (t + 1)).map xs)) ∧
              Consistent (P ((List.range (t + 1)).map xs)) (xs t)) ∧
            ∀ t, transportCost (P ((List.range (t + 1)).map xs))
                (P ((List.range (t + 2)).map xs)) ≤
              (2 * C) * fracMoveCost T e (xs t) (xs (t + 1)) := by
  intro V _ _ T hT M _ _ _ e hM k C₀
  classical
  let step : (KConfig k M → ℝ) → (M → ℝ) → (M → ℝ) → (KConfig k M → ℝ) := fun S x x' =>
    if hh : IsFracState k x ∧ IsFracState k x' ∧ IsKState S ∧ Consistent S x then
      Classical.choose (h V T hT M e hM k x x' S hh.1 hh.2.1 hh.2.2.1 hh.2.2.2) else S
  have step_spec : ∀ S x x', IsFracState k x → IsFracState k x' → IsKState S →
      Consistent S x → IsKState (step S x x') ∧ Consistent (step S x x') x' ∧
        Balanced T e x' (step S x x') ∧
        transportCost S (step S x x') ≤ C * (balanceGap T e S x' + fracMoveCost T e x x') := by
    intro S x x' h1 h2 h3 h4
    have hh : IsFracState k x ∧ IsFracState k x' ∧ IsKState S ∧ Consistent S x :=
      ⟨h1, h2, h3, h4⟩
    simp only [step, dif_pos hh]
    exact Classical.choose_spec (h V T hT M e hM k x x' S h1 h2 h3 h4)
  refine ⟨fun l => iterL step (pureState C₀) l 0 (l.length - 1), ?_⟩
  intro xs hxs h0
  have hP : ∀ n t, n = t + 1 → iterL step (pureState C₀) ((List.range n).map xs) 0
      (((List.range n).map xs).length - 1) = iterS step (pureState C₀) xs t := by
    intro n t hn
    subst hn
    simp only [List.length_map, List.length_range, Nat.add_sub_cancel]
    exact iterL_range step _ xs 0 (t + 1) t (by omega)
  have inv : ∀ t, IsKState (iterS step (pureState C₀) xs t) ∧
      Consistent (iterS step (pureState C₀) xs t) (xs t) ∧
      Balanced T e (xs t) (iterS step (pureState C₀) xs t) := by
    intro t
    induction t with
    | zero =>
      simp only [iterS]
      rw [h0]
      exact ⟨pure_isKState C₀, pure_consistent C₀, pure_balanced T e C₀⟩
    | succ t ih =>
      simp only [iterS]
      obtain ⟨a, b, c, -⟩ := step_spec _ (xs t) (xs (t + 1)) (hxs t) (hxs (t + 1)) ih.1 ih.2.1
      exact ⟨a, b, c⟩
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro t
    beta_reduce
    rw [hP (t + 1) t rfl]
    exact ⟨(inv t).1, (inv t).2.1⟩
  · intro t
    beta_reduce
    rw [hP (t + 1) t rfl, hP (t + 2) (t + 1) rfl]
    simp only [iterS]
    obtain ⟨-, -, -, hcost⟩ := step_spec _ (xs t) (xs (t + 1)) (hxs t) (hxs (t + 1))
      (inv t).1 (inv t).2.1
    have hg := gmove T e (xs t) (xs (t + 1)) _ (inv t).1 (inv t).2.1 (inv t).2.2
    calc _ ≤ C * (balanceGap T e (iterS step (pureState C₀) xs t) (xs (t + 1)) +
          fracMoveCost T e (xs t) (xs (t + 1))) := hcost
      _ ≤ C * (fracMoveCost T e (xs t) (xs (t + 1)) + fracMoveCost T e (xs t) (xs (t + 1))) := by
          apply mul_le_mul_of_nonneg_left _ hC.le; linarith
      _ = (2 * C) * fracMoveCost T e (xs t) (xs (t + 1)) := by ring

open PolylogKServer.Fractional in
/-- Theorem 24 from the core obligation GR. -/
theorem online_rounding_of (hGR : ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧ GR σ C) :
    ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M] [DecidableEq M] (e : M ≃ T.Leaf),
        T.IsLeafMetric M e →
      ∀ (k : ℕ) (C₀ : KConfig k M),
        ∃ P : List (M → ℝ) → (KConfig k M → ℝ),
          ∀ xs : ℕ → M → ℝ, (∀ t, IsFracState k (xs t)) →
            xs 0 = (fun m => if m ∈ C₀.1 then 1 else 0) →
            P [xs 0] = pureState C₀ ∧
            (∀ t, IsKState (P ((List.range (t + 1)).map xs)) ∧
              Consistent (P ((List.range (t + 1)).map xs)) (xs t)) ∧
            ∀ t, transportCost (P ((List.range (t + 1)).map xs))
                (P ((List.range (t + 2)).map xs)) ≤
              C * fracMoveCost T e (xs t) (xs (t + 1)) := by
  intro σ hσ
  obtain ⟨C, hC, h⟩ := hGR σ hσ
  exact ⟨2 * C, by positivity, online_of_GR σ C hC h⟩

/-- Lemma 25 from the core obligation GR (case x' = x). -/
theorem rebalance_of (hGR : ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧ GR σ C) :
    ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M] [DecidableEq M] (e : M ≃ T.Leaf),
        T.IsLeafMetric M e →
      ∀ (k : ℕ) (x : M → ℝ) (S : KConfig k M → ℝ),
        IsFracState k x → IsKState S → Consistent S x →
        ∃ S' : KConfig k M → ℝ, IsKState S' ∧ Consistent S' x ∧ Balanced T e x S' ∧
          transportCost S S' ≤ C * balanceGap T e S x := by
  intro σ hσ
  obtain ⟨C, hC, h⟩ := hGR σ hσ
  refine ⟨C, hC, ?_⟩
  intro V _ _ T hT M _ _ _ e hM k x S hx hS hc
  obtain ⟨S', a, b, c, d⟩ := h V T hT M e hM k x x S hx hx hS hc
  refine ⟨S', a, b, c, ?_⟩
  have h0 : fracMoveCost T e x x = 0 := by unfold fracMoveCost; simp
  rwa [h0, add_zero] at d

end Assembly

end R80c9fd83

namespace R80c9fd83

open Finset PolylogKServer.HST PolylogKServer.Rounding PolylogKServer.Fractional

section GRR

variable {V : Type} [Fintype V] [DecidableEq V]
variable {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]

theorem Ex_sum_ch (T : WTree V) (e : M ≃ T.Leaf) (S : KConfig k M → ℝ) {p : V}
    (hp : ¬ T.IsLeaf p) : Ex S (nC T e p) = ∑ u ∈ ch T p, Ex S (nC T e u) := by
  unfold Ex
  rw [Finset.sum_congr rfl fun C _ => show S C * nC T e p C = ∑ u ∈ ch T p, S C * nC T e u C by
    unfold nC; rw [count_split T e C.1 hp, Finset.mul_sum]]
  exact Finset.sum_comm

theorem Ex_childDev (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (S : KConfig k M → ℝ) (p : V) :
    Ex S (childDev T e y p) =
      ∑ u ∈ ch T p, Ex S (fun C => devR (massBelow T e y u) (nC T e u C)) := by
  unfold Ex childDev
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- One node of the top-down pass: projection, then mean fixing. -/
theorem step_node (T : WTree V) (e : M ≃ T.Leaf) (hM : T.IsLeafMetric M e) (y : M → ℝ)
    (hy0 : ∀ m, 0 ≤ y m) (hy1 : ∀ m, y m ≤ 1) (p : V) (hp : ¬ T.IsLeaf p) (A B : ℝ)
    (hA : ∀ C C' : KConfig k M, LegalMv T e y p C C' → emd T e C.1 C'.1 ≤ A)
    (hB : ∀ C C' : KConfig k M, LegalMv T e y p C C' →
      ∑ v ∈ dpSet T p, T.W v * |nC T e v C' - nC T e v C| ≤ B)
    (S : KConfig k M → ℝ) (hS : IsKState S)
    (hbox : ∀ C, S C ≠ 0 → BoxZ (massBelow T e y p) (countBelow T e C.1 p))
    (hmean : Ex S (nC T e p) = massBelow T e y p) :
    ∃ S' μ, Rel T e y p A B S S' μ ∧
      μ ≤ 3 * Ex S (childDev T e y p) + ∑ u ∈ ch T p, |Ex S (nC T e u) - massBelow T e y u| ∧
      (∀ C', S' C' ≠ 0 → ∀ u ∈ ch T p, BoxZ (massBelow T e y u) (countBelow T e C'.1 u)) ∧
      ∀ u ∈ ch T p, Ex S' (nC T e u) = massBelow T e y u := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ C, S C ≠ 0 → childDev T e y p C ≤ N := by
    refine ⟨⌈∑ C : KConfig k M, childDev T e y p C⌉₊, fun C _ => ?_⟩
    exact (Finset.single_le_sum (fun (C : KConfig k M) _ => childDev_nonneg T e y p C)
      (Finset.mem_univ C)).trans (Nat.le_ceil _)
  obtain ⟨S1, μ1, r1, hμ1, hb1⟩ := proj_all T e hM y hy0 hy1 p A B hA hB N S hS hbox hN
  have hsup1 : ∀ C', S1 C' ≠ 0 →
      BoxZ (massBelow T e y p) (countBelow T e C'.1 p) ∧ ChBox T e y p C' := by
    intro C' h
    refine ⟨?_, hb1 C' h⟩
    obtain ⟨C, hC, hcnt⟩ := r1.2.2.2.2.2.2.2 C' h
    have := hcnt p (fun h => h.2 rfl)
    unfold nC at this
    have h2 : countBelow T e C'.1 p = countBelow T e C.1 p := by exact_mod_cast this
    rw [h2]; exact hbox C hC
  have hsum1 : ∑ u ∈ ch T p, Ex S1 (nC T e u) = ∑ u ∈ ch T p, massBelow T e y u := by
    rw [← Ex_sum_ch T e S1 hp, r1.2.2.2.2.2.2.1 p (fun h => h.2 rfl), hmean,
      mass_split T e y hp]
  obtain ⟨S2, μ2, r2, hμ2, hsup2, hex2⟩ := rr_all T e hM y hy0 hy1 p A B hA hB
    (ch T p).card (ch T p) le_rfl S1 r1.1 hsup1 hsum1 (fun u hu h => absurd hu h)
  refine ⟨S2, μ1 + μ2, rel_comp T e y p A B S S1 S2 μ1 μ2 hS r1 r2, ?_,
    fun C' h => (hsup2 C' h).2, hex2⟩
  have h6 := r1.2.2.2.2.2.1
  have : ∑ u ∈ ch T p, |Ex S1 (nC T e u) - massBelow T e y u| ≤
      ∑ u ∈ ch T p, |Ex S (nC T e u) - massBelow T e y u| +
        ∑ u ∈ ch T p, |Ex S1 (nC T e u) - Ex S (nC T e u)| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun u _ => by
      have := abs_sub_le (Ex S1 (nC T e u)) (Ex S (nC T e u)) (massBelow T e y u)
      linarith
  linarith

/-- The potential of the not-yet-done nodes. -/
noncomputable def Phi (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (D : Finset V)
    (S : KConfig k M → ℝ) : ℝ :=
  ∑ v ∈ univ.filter (fun v => v ∉ D), T.W v *
    (3 * Ex S (fun C => devR (massBelow T e y v) (nC T e v C)) +
      |Ex S (nC T e v) - massBelow T e y v|)

theorem phi_step (T : WTree V) (e : M ≃ T.Leaf) (y : M → ℝ) (p : V) (A B Wc κ : ℝ)
    (hκ : 0 ≤ κ) (hWc : 0 ≤ Wc) (hch : ∀ u ∈ ch T p, T.W u = Wc) (hAB : A ≤ κ * (Wc - B))
    (D : Finset V) (hroot : T.root ∈ D) (hD : ∀ v, T.IsAnc p v → v ≠ p → v ∉ D)
    (S S' : KConfig k M → ℝ) (μ : ℝ) (r : Rel T e y p A B S S' μ)
    (hμ : μ ≤ 3 * Ex S (childDev T e y p) +
      ∑ u ∈ ch T p, |Ex S (nC T e u) - massBelow T e y u|) :
    transportCost S S' ≤ κ * (Phi T e y D S - Phi T e y (D ∪ ch T p) S') := by
  classical
  obtain ⟨-, hμ0, hcost, hdev, hdeep, -, hout, -⟩ := r
  have hchanc : ∀ u ∈ ch T p, T.IsAnc p u ∧ u ≠ p := by
    intro u hu
    have hu' := (mem_ch T).1 hu
    refine ⟨hu'.2 ▸ t_anc_parent_self T u, ?_⟩
    intro h; rw [h] at hu'
    have := t_child_depth T hu'.1 hu'.2; omega
  have hset : univ.filter (fun v => v ∉ D) =
      ch T p ∪ univ.filter (fun v => v ∉ D ∪ ch T p) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_or]
    constructor
    · intro h
      by_cases hv : v ∈ ch T p
      · exact Or.inl hv
      · exact Or.inr ⟨h, hv⟩
    · rintro (h | ⟨h, -⟩)
      · exact hD v (hchanc v h).1 (hchanc v h).2
      · exact h
  have hdisj : Disjoint (ch T p) (univ.filter (fun v => v ∉ D ∪ ch T p)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_or] at hv'
    exact hv'.2 hv
  have hsplit : Phi T e y D S = ∑ u ∈ ch T p, T.W u *
      (3 * Ex S (fun C => devR (massBelow T e y u) (nC T e u C)) +
        |Ex S (nC T e u) - massBelow T e y u|) + Phi T e y (D ∪ ch T p) S := by
    unfold Phi
    rw [hset, Finset.sum_union hdisj]
  have hchsum : ∑ u ∈ ch T p, T.W u *
      (3 * Ex S (fun C => devR (massBelow T e y u) (nC T e u C)) +
        |Ex S (nC T e u) - massBelow T e y u|) =
      Wc * (3 * Ex S (childDev T e y p) +
        ∑ u ∈ ch T p, |Ex S (nC T e u) - massBelow T e y u|) := by
    have h1 : ∀ u ∈ ch T p, T.W u *
        (3 * Ex S (fun C => devR (massBelow T e y u) (nC T e u C)) +
          |Ex S (nC T e u) - massBelow T e y u|) =
        Wc * (3 * Ex S (fun C => devR (massBelow T e y u) (nC T e u C)) +
          |Ex S (nC T e u) - massBelow T e y u|) := fun u hu => by rw [hch u hu]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
      Ex_childDev]
  have hsub : ∀ v ∈ dpSet T p, v ∈ univ.filter (fun v => v ∉ D ∪ ch T p) := by
    intro v hv
    have hv' := (Finset.mem_filter.1 hv).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_or]
    exact ⟨hD v hv'.1 hv'.2.1, hv'.2.2⟩
  have hpt : ∀ v ∈ univ.filter (fun v => v ∉ D ∪ ch T p),
      T.W v * (3 * Ex S' (fun C => devR (massBelow T e y v) (nC T e v C)) +
        |Ex S' (nC T e v) - massBelow T e y v|) ≤
      T.W v * (3 * Ex S (fun C => devR (massBelow T e y v) (nC T e v C)) +
        |Ex S (nC T e v) - massBelow T e y v|) +
      (if v ∈ dpSet T p then T.W v * |Ex S' (nC T e v) - massBelow T e y v| -
        T.W v * |Ex S (nC T e v) - massBelow T e y v| else 0) := by
    intro v hv
    have hv' : v ∉ D ∧ v ∉ ch T p := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_or]
        using hv
    have hW : 0 ≤ T.W v := (T.W_pos v (fun h => hv'.1 (h ▸ hroot))).le
    have hd := mul_le_mul_of_nonneg_left (hdev v) hW
    by_cases hdp : v ∈ dpSet T p
    · rw [if_pos hdp]; linarith
    · rw [if_neg hdp]
      have hno : ¬ (T.IsAnc p v ∧ v ≠ p) := by
        rintro ⟨h1, h2⟩
        exact hdp (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2, hv'.2⟩)
      rw [hout v hno]; linarith
  have hU : Phi T e y (D ∪ ch T p) S' ≤ Phi T e y (D ∪ ch T p) S + B * μ := by
    unfold Phi
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter]
    have hf : (univ.filter (fun v => v ∉ D ∪ ch T p)).filter (fun v => v ∈ dpSet T p) =
        dpSet T p := by
      ext v; rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hsub v h, h⟩⟩
    rw [hf, Finset.sum_sub_distrib]
    linarith [hdeep]
  have hkey : Wc * (3 * Ex S (childDev T e y p) +
      ∑ u ∈ ch T p, |Ex S (nC T e u) - massBelow T e y u|) - B * μ ≤
      Phi T e y D S - Phi T e y (D ∪ ch T p) S' := by
    rw [hsplit, hchsum]; linarith
  have h1 : A * μ ≤ κ * (Wc - B) * μ := mul_le_mul_of_nonneg_right hAB hμ0
  have h2 : Wc * μ ≤ Wc * (3 * Ex S (childDev T e y p) +
      ∑ u ∈ ch T p, |Ex S (nC T e u) - massBelow T e y u|) := mul_le_mul_of_nonneg_left hμ hWc
  have h3 : κ * (Wc * μ - B * μ) ≤ κ * (Phi T e y D S - Phi T e y (D ∪ ch T p) S') :=
    mul_le_mul_of_nonneg_left (by linarith) hκ
  calc transportCost S S' ≤ A * μ := hcost
    _ ≤ κ * (Wc - B) * μ := h1
    _ = κ * (Wc * μ - B * μ) := by ring
    _ ≤ _ := h3

/-- Top-down induction over an ancestor-closed, sibling-closed done set. -/
theorem top_ind (T : WTree V) (e : M ≃ T.Leaf) (hM : T.IsLeafMetric M e) (y : M → ℝ)
    (hy0 : ∀ m, 0 ≤ y m) (hy1 : ∀ m, y m ≤ 1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hAB : ∀ p, ¬ T.IsLeaf p → ∃ A B Wc : ℝ, 0 ≤ Wc ∧ (∀ u ∈ ch T p, T.W u = Wc) ∧
      A ≤ κ * (Wc - B) ∧
      (∀ C C' : KConfig k M, LegalMv T e y p C C' → emd T e C.1 C'.1 ≤ A) ∧
      (∀ C C' : KConfig k M, LegalMv T e y p C C' →
        ∑ v ∈ dpSet T p, T.W v * |nC T e v C' - nC T e v C| ≤ B)) :
    ∀ n : ℕ, ∀ D : Finset V, (univ.filter (fun v => v ∉ D)).card ≤ n → T.root ∈ D →
      (∀ v ∈ D, T.parent v ∈ D) →
      (∀ u u', T.parent u = T.parent u' → u ≠ T.root → u' ≠ T.root → u ∈ D → u' ∈ D) →
      ∀ S : KConfig k M → ℝ, IsKState S →
      (∀ v ∈ D, (∀ C, S C ≠ 0 → BoxZ (massBelow T e y v) (countBelow T e C.1 v)) ∧
        Ex S (nC T e v) = massBelow T e y v) →
      ∃ S' : KConfig k M → ℝ, IsKState S' ∧
        (∀ v, (∀ C, S' C ≠ 0 → BoxZ (massBelow T e y v) (countBelow T e C.1 v)) ∧
          Ex S' (nC T e v) = massBelow T e y v) ∧
        transportCost S S' ≤ κ * Phi T e y D S := by
  have hfin : ∀ D : Finset V, ∀ S : KConfig k M → ℝ, IsKState S → (∀ v, v ∈ D) →
      (∀ v ∈ D, (∀ C, S C ≠ 0 → BoxZ (massBelow T e y v) (countBelow T e C.1 v)) ∧
        Ex S (nC T e v) = massBelow T e y v) →
      ∃ S' : KConfig k M → ℝ, IsKState S' ∧
        (∀ v, (∀ C, S' C ≠ 0 → BoxZ (massBelow T e y v) (countBelow T e C.1 v)) ∧
          Ex S' (nC T e v) = massBelow T e y v) ∧
        transportCost S S' ≤ κ * Phi T e y D S := by
    intro D S hS hall hdone
    refine ⟨S, hS, fun v => hdone v (hall v), ?_⟩
    have h0 : Phi T e y D S = 0 :=
      Finset.sum_eq_zero fun v hv => absurd (hall v) (Finset.mem_filter.1 hv).2
    rw [transportCost_self S hS.1, h0, mul_zero]
  intro n
  induction n with
  | zero =>
    intro D hcard _ _ _ S hS hdone
    refine hfin D S hS (fun v => ?_) hdone
    by_contra hv
    have hmem : v ∈ univ.filter (fun v => v ∉ D) := Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩
    have := Finset.card_pos.2 ⟨v, hmem⟩
    omega
  | succ n ih =>
    intro D hcard hroot hpar hsib S hS hdone
    by_cases hall : ∀ v, v ∈ D
    · exact hfin D S hS hall hdone
    push Not at hall
    obtain ⟨v0, hv0⟩ := hall
    obtain ⟨v, hvD, hvmin⟩ := Finset.exists_min_image (univ.filter (fun v => v ∉ D)) T.depth
      ⟨v0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv0⟩⟩
    have hv : v ∉ D := (Finset.mem_filter.1 hvD).2
    have hvr : v ≠ T.root := fun h => hv (h ▸ hroot)
    obtain ⟨p, hpdef⟩ : ∃ p, p = T.parent v := ⟨_, rfl⟩
    have hpD : p ∈ D := by
      by_contra hp
      have h1 := hvmin p (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩)
      have h2 := t_depth_parent T v
      have h3 : T.depth v ≠ 0 := fun h0 => hvr (t_eq_root_of_depth T h0)
      rw [hpdef] at h1
      omega
    have hvch : v ∈ ch T p := (mem_ch T).2 ⟨hvr, hpdef.symm⟩
    have hpl : ¬ T.IsLeaf p := fun hl => hl v hvr hpdef.symm
    have hchD : ∀ u ∈ ch T p, u ∉ D := fun u hu huD =>
      hv (hsib u v (((mem_ch T).1 hu).2.trans hpdef) ((mem_ch T).1 hu).1 hvr huD)
    have hiter : ∀ i : ℕ, ∀ w, w ∈ D → T.parent^[i] w ∈ D := by
      intro i
      induction i with
      | zero => intro w hw; exact hw
      | succ i ihi =>
        intro w hw; rw [Function.iterate_succ_apply]; exact ihi _ (hpar w hw)
    have hD : ∀ w, T.IsAnc p w → w ≠ p → w ∉ D := by
      intro w hpw hne hwD
      obtain ⟨u, hur, hup, ⟨i, hi⟩⟩ := t_exists_child T hpw hne
      exact hchD u ((mem_ch T).2 ⟨hur, hup⟩) (hi ▸ hiter i w hwD)
    obtain ⟨A, B, Wc, hWc, hch, hAB', hA, hB⟩ := hAB p hpl
    obtain ⟨hboxp, hmeanp⟩ := hdone p hpD
    obtain ⟨S1, μ, r, hμ, hcb, hex⟩ :=
      step_node T e hM y hy0 hy1 p hpl A B hA hB S hS hboxp hmeanp
    have hcost1 := phi_step T e y p A B Wc κ hκ hWc hch hAB' D hroot hD S S1 μ r hμ
    have hcard' : (univ.filter (fun v => v ∉ D ∪ ch T p)).card ≤ n := by
      have hsub : univ.filter (fun v => v ∉ D ∪ ch T p) ⊂ univ.filter (fun v => v ∉ D) := by
        refine (Finset.ssubset_iff_of_subset (fun w hw => ?_)).2 ⟨v, hvD, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            not_or] at hw ⊢
          exact hw.1
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_or,
            not_and, not_not]
          exact fun _ => hvch
      have := Finset.card_lt_card hsub
      omega
    have hroot' : T.root ∈ D ∪ ch T p := Finset.mem_union_left _ hroot
    have hpar' : ∀ w ∈ D ∪ ch T p, T.parent w ∈ D ∪ ch T p := by
      intro w hw
      rcases Finset.mem_union.1 hw with h | h
      · exact Finset.mem_union_left _ (hpar w h)
      · rw [((mem_ch T).1 h).2]; exact Finset.mem_union_left _ hpD
    have hsib' : ∀ u u', T.parent u = T.parent u' → u ≠ T.root → u' ≠ T.root →
        u ∈ D ∪ ch T p → u' ∈ D ∪ ch T p := by
      intro u u' hpu hu hu' h
      rcases Finset.mem_union.1 h with h | h
      · exact Finset.mem_union_left _ (hsib u u' hpu hu hu' h)
      · exact Finset.mem_union_right _ ((mem_ch T).2 ⟨hu', hpu.symm.trans ((mem_ch T).1 h).2⟩)
    have hdone' : ∀ w ∈ D ∪ ch T p,
        (∀ C, S1 C ≠ 0 → BoxZ (massBelow T e y w) (countBelow T e C.1 w)) ∧
        Ex S1 (nC T e w) = massBelow T e y w := by
      intro w hw
      rcases Finset.mem_union.1 hw with h | h
      · have hno : ¬ (T.IsAnc p w ∧ w ≠ p) := fun hh => hD w hh.1 hh.2 h
        refine ⟨fun C hC => ?_, ?_⟩
        · obtain ⟨C0, hC0, hcnt⟩ := r.2.2.2.2.2.2.2 C hC
          have := hcnt w hno
          unfold nC at this
          have h2 : countBelow T e C.1 w = countBelow T e C0.1 w := by exact_mod_cast this
          rw [h2]; exact (hdone w h).1 C0 hC0
        · rw [r.2.2.2.2.2.2.1 w hno]; exact (hdone w h).2
      · exact ⟨fun C hC => hcb C hC w h, hex w h⟩
    obtain ⟨S2, hS2, hdone2, hcost2⟩ :=
      ih (D ∪ ch T p) hcard' hroot' hpar' hsib' S1 r.1 hdone'
    refine ⟨S2, hS2, hdone2, ?_⟩
    have := transportCost_triangle S S1 S2 hS r.1 hS2
    linarith

theorem mass_root (T : WTree V) (e : M ≃ T.Leaf) (z : M → ℝ) :
    massBelow T e z T.root = ∑ m, z m := by
  classical
  unfold massBelow
  exact Finset.sum_congr rfl fun m _ => if_pos (root_anc' T _)

theorem count_root (T : WTree V) (e : M ≃ T.Leaf) (C : Finset M) :
    countBelow T e C T.root = C.card := by
  classical
  unfold countBelow
  rw [Finset.filter_true_of_mem fun m _ => root_anc' T _]

theorem count_leaf (T : WTree V) (e : M ≃ T.Leaf) (C : Finset M) (i : M) :
    (countBelow T e C (e i) : ℝ) = if i ∈ C then 1 else 0 := by
  classical
  rw [countBelow_eq]
  have h : ∀ m ∈ C, (if T.IsAnc (e i : V) (e m : V) then (1 : ℝ) else 0) =
      if m = i then 1 else 0 := by
    intro m _
    by_cases hm : m = i
    · rw [hm, if_pos (t_anc_refl T _), if_pos rfl]
    · rw [if_neg hm, if_neg]
      intro ha
      exact hm (e.injective (Subtype.ext (t_leaf_anc T (e i).2 ha)))
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq]

end GRR

theorem gr_holds (σ : ℝ) (hσ : 3 < σ) : GR σ (3 * (2 * σ / (σ - 3))) := by
  intro V _ _ T hT M _ _ _ e hM k x x' S hx hx' hS hcons
  obtain ⟨L, hL, hW⟩ := hT
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 2 * σ / (σ - 3) := ⟨_, rfl⟩
  rw [← hκdef]
  have hs3 : 0 < σ - 3 := by linarith
  have hκ : 0 ≤ κ := by rw [hκdef]; exact div_nonneg (by linarith) hs3.le
  have hy0 : ∀ m, 0 ≤ x' m := fun m => (hx'.1 m).1
  have hy1 : ∀ m, x' m ≤ 1 := fun m => (hx'.1 m).2
  have hAB : ∀ p, ¬ T.IsLeaf p → ∃ A B Wc : ℝ, 0 ≤ Wc ∧ (∀ u ∈ ch T p, T.W u = Wc) ∧
      A ≤ κ * (Wc - B) ∧
      (∀ C C' : KConfig k M, LegalMv T e x' p C C' → emd T e C.1 C'.1 ≤ A) ∧
      (∀ C C' : KConfig k M, LegalMv T e x' p C C' →
        ∑ v ∈ dpSet T p, T.W v * |nC T e v C' - nC T e v C| ≤ B) := by
    intro p _
    refine ⟨2 * (L * σ * ((1 / σ) ^ (T.depth p + 1) / (1 - 1 / σ))),
      2 * (L * σ * ((1 / σ) ^ (T.depth p + 2) / (1 - 1 / σ))), L / σ ^ T.depth p,
      div_nonneg hL.le (pow_nonneg (by linarith) _), ?_, ?_,
      fun C C' h => legal_emd_le T σ L (by linarith) hL hW e x' h,
      fun C C' h => legal_deep_le T σ L (by linarith) hL hW e x' h⟩
    · intro u hu
      have hu' := (mem_ch T).1 hu
      rw [hW u hu'.1, t_child_depth T hu'.1 hu'.2]
      simp
    · have hσ0 : σ ≠ 0 := by linarith
      have hσ1 : σ - 1 ≠ 0 := by linarith
      have hσ3 : σ - 3 ≠ 0 := by linarith
      have e1 : (1 / σ) ^ (T.depth p + 1) = (1 / σ) ^ (T.depth p) / σ := by
        rw [pow_succ]; ring
      have e2 : (1 / σ) ^ (T.depth p + 2) = (1 / σ) ^ (T.depth p) / σ ^ 2 := by
        rw [pow_add]; ring
      have e3 : L / σ ^ T.depth p = L * (1 / σ) ^ (T.depth p) := by
        rw [one_div_pow]; ring
      rw [e1, e2, e3, hκdef]
      generalize (1 / σ) ^ (T.depth p) = q
      apply le_of_eq
      field_simp
      ring
  have hdone0 : ∀ v ∈ ({T.root} : Finset V),
      (∀ C, S C ≠ 0 → BoxZ (massBelow T e x' v) (countBelow T e C.1 v)) ∧
        Ex S (nC T e v) = massBelow T e x' v := by
    intro v hv
    rw [Finset.mem_singleton] at hv
    subst hv
    have hm : massBelow T e x' T.root = k := by rw [mass_root, hx'.2]
    refine ⟨fun C _ => ?_, ?_⟩
    · rw [hm, count_root T e C.1, C.2]
      unfold BoxZ
      simp
    · rw [hm]
      show ∑ C, S C * (countBelow T e C.1 T.root : ℝ) = k
      rw [count_avg T e x S hcons, mass_root, hx.2]
  obtain ⟨S', hS', hdone, hcost⟩ := top_ind T e hM x' hy0 hy1 κ hκ hAB (Fintype.card V)
    {T.root} (Finset.card_le_univ _) (Finset.mem_singleton_self _)
    (fun v hv => by
      rw [Finset.mem_singleton] at hv ⊢
      rw [hv, T.parent_root])
    (fun u u' _ hu _ h => absurd (Finset.mem_singleton.1 h) hu)
    S hS hdone0
  have hPhi : Phi T e x' {T.root} S = 3 * balanceGap T e S x' + fracMoveCost T e x x' := by
    unfold Phi balanceGap fracMoveCost
    have hf : (univ.filter (fun v => v ∉ ({T.root} : Finset V))) =
        univ.filter (fun v => v ≠ T.root) := by
      ext v; simp
    rw [hf, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    have h1 : Ex S (nC T e v) = massBelow T e x v := count_avg T e x S hcons v
    rw [h1, abs_sub_comm (massBelow T e x v)]
    simp only [Ex, devR, nC, massBelow_eq_subtreeMass]
    ring
  have hF : 0 ≤ fracMoveCost T e x x' := by
    unfold fracMoveCost
    exact Finset.sum_nonneg fun v hv =>
      mul_nonneg (T.W_pos v (Finset.mem_filter.1 hv).2).le (abs_nonneg _)
  refine ⟨S', hS', ?_, ?_, ?_⟩
  · intro i
    have h := (hdone (e i : V)).2
    rw [mass_leaf] at h
    rw [Finset.sum_filter, ← h]
    unfold Ex
    exact Finset.sum_congr rfl fun C _ => by
      unfold nC; rw [count_leaf T e C.1 i]; split_ifs <;> ring
  · intro C hC p
    have hb := (hdone p).1 C hC
    unfold BoxZ at hb
    have := Int.ceil_le_floor_add_one (massBelow T e x' p)
    omega
  · rw [hPhi] at hcost
    have := mul_nonneg hκ hF
    nlinarith

theorem gr_all : ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧ GR σ C := fun σ hσ =>
  ⟨3 * (2 * σ / (σ - 3)), mul_pos (by norm_num) (div_pos (by linarith) (by linarith)),
    gr_holds σ (by linarith)⟩

end R80c9fd83

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace K1c810f69

open MeasureTheory ProbabilityTheory Finset
open PolylogKServer.HST PolylogKServer.Rounding PolylogKServer.Fractional

/-! ## Part 1: inverse-CDF sampling on a finite type -/

noncomputable def cum (v : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ range j, v i

theorem cum_succ (v : ℕ → ℝ) (j : ℕ) : cum v (j + 1) = cum v j + v j :=
  Finset.sum_range_succ _ _

theorem cum_zero (v : ℕ → ℝ) : cum v 0 = 0 := by simp [cum]

theorem cum_mono (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) {a b : ℕ} (h : a ≤ b) : cum v a ≤ cum v b :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun i _ _ => hv i)

theorem cum_unique (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) (u : ℝ) {a b : ℕ}
    (ha : cum v a ≤ u ∧ u < cum v (a + 1)) (hb : cum v b ≤ u ∧ u < cum v (b + 1)) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · have := cum_mono v hv (show a + 1 ≤ b by omega); linarith [ha.2, hb.1]
  · exact h
  · have := cum_mono v hv (show b + 1 ≤ a by omega); linarith [ha.1, hb.2]

noncomputable def pickF (v : ℕ → ℝ) (n : ℕ) (j0 : Fin n) (u : ℝ) : Fin n := by
  classical
  exact if h : ∃ j : Fin n, cum v (j : ℕ) ≤ u ∧ u < cum v ((j : ℕ) + 1) then h.choose else j0

theorem pickF_eq_of (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) (n : ℕ) (j0 : Fin n) (u : ℝ) (j : Fin n)
    (h : cum v (j : ℕ) ≤ u ∧ u < cum v ((j : ℕ) + 1)) : pickF v n j0 u = j := by
  have hex : ∃ j : Fin n, cum v (j : ℕ) ≤ u ∧ u < cum v ((j : ℕ) + 1) := ⟨j, h⟩
  unfold pickF
  rw [dif_pos hex]
  exact Fin.ext (cum_unique v hv u hex.choose_spec h)

theorem pickF_of_not (v : ℕ → ℝ) (n : ℕ) (j0 : Fin n) (u : ℝ)
    (h : ¬ ∃ j : Fin n, cum v (j : ℕ) ≤ u ∧ u < cum v ((j : ℕ) + 1)) : pickF v n j0 u = j0 := by
  unfold pickF
  rw [dif_neg h]

theorem exists_of_lt_one (v : ℕ → ℝ) (n : ℕ) (hn : cum v n = 1) (hn0 : 0 < n) (u : ℝ)
    (h0 : 0 ≤ u) (h1 : u < 1) : ∃ j : Fin n, cum v (j : ℕ) ≤ u ∧ u < cum v ((j : ℕ) + 1) := by
  classical
  have hex : ∃ m, u < cum v (m + 1) := ⟨n - 1, by rw [Nat.sub_add_cancel hn0]; linarith⟩
  obtain ⟨m, hm, hmin⟩ : ∃ m, u < cum v (m + 1) ∧ ∀ m' < m, ¬ u < cum v (m' + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m' h => Nat.find_min hex h⟩
  have hmn : m < n := by
    by_contra hc
    exact hmin (n - 1) (by omega) (by rw [Nat.sub_add_cancel hn0]; linarith)
  refine ⟨⟨m, hmn⟩, ?_, hm⟩
  cases m with
  | zero => simp only [cum_zero]; exact h0
  | succ m' =>
    have := hmin m' (Nat.lt_succ_self m')
    push_neg at this
    exact this

theorem sample_exists {Y : Type} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (w : Y → ℝ) (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1) :
    ∃ s : unitInterval → Y, Measurable s ∧ (∀ u, 0 < w (s u)) ∧
      ∀ y, volume (s ⁻¹' {y}) = ENNReal.ofReal (w y) := by
  classical
  set n := Fintype.card Y with hn_def
  let e : Y ≃ Fin n := Fintype.equivFin Y
  let v : ℕ → ℝ := fun i => if h : i < n then w (e.symm ⟨i, h⟩) else 0
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i; simp only [v]; split_ifs
    · exact hw0 _
    · exact le_refl 0
  have hvj : ∀ j : Fin n, v j = w (e.symm j) := by
    intro j; simp only [v, dif_pos j.isLt]
  have hsumw : ∑ j : Fin n, v j = 1 := by
    rw [← hw1, ← e.symm.sum_comp w]
    exact Finset.sum_congr rfl (fun j _ => hvj j)
  have hcn : cum v n = 1 := by
    rw [cum, ← hsumw]
    exact (Fin.sum_univ_eq_sum_range (fun i => v i) n).symm
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin n, 0 < v j0 := by
    by_contra hc
    push_neg at hc
    have : ∑ j : Fin n, v j ≤ 0 := Finset.sum_nonpos (fun j _ => hc j)
    linarith
  have hn0 : 0 < n := j0.pos
  let s : unitInterval → Y := fun u => e.symm (pickF v n j0 (u : ℝ))
  let Int : Fin n → Set unitInterval := fun j =>
    {u | cum v (j : ℕ) ≤ (u : ℝ) ∧ (u : ℝ) < cum v ((j : ℕ) + 1)}
  let E : Set unitInterval := {u | ¬ ∃ j : Fin n, cum v (j : ℕ) ≤ (u : ℝ) ∧ (u : ℝ) < cum v ((j : ℕ) + 1)}
  have hIntM : ∀ j, MeasurableSet (Int j) := fun j =>
    (measurableSet_le measurable_const measurable_subtype_coe).inter
      (measurableSet_lt measurable_subtype_coe measurable_const)
  have hEM : MeasurableSet E := by
    have : E = ⋂ j : Fin n, (Int j)ᶜ := by
      ext u; simp only [E, Int, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff, not_exists]
    rw [this]; exact MeasurableSet.iInter (fun j => (hIntM j).compl)
  have hpre : ∀ y, s ⁻¹' {y} = Int (e y) ∪ (E ∩ {_u | j0 = e y}) := by
    intro y; ext u
    simp only [s, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq, Int, E]
    rw [Equiv.symm_apply_eq]
    constructor
    · intro h
      by_cases hx : ∃ j : Fin n, cum v (j : ℕ) ≤ (u : ℝ) ∧ (u : ℝ) < cum v ((j : ℕ) + 1)
      · left
        obtain ⟨j, hj⟩ := hx
        rw [pickF_eq_of v hv0 n j0 _ j hj] at h
        rw [← h]; exact hj
      · right
        rw [pickF_of_not v n j0 _ hx] at h
        exact ⟨hx, h⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact pickF_eq_of v hv0 n j0 _ _ h
      · rw [pickF_of_not v n j0 _ h1]; exact h2
  have hENull : volume E = 0 := by
    apply measure_mono_null (t := {(1 : unitInterval)}) _ (measure_singleton _)
    intro u hu
    simp only [Set.mem_singleton_iff]
    by_contra hne
    have hlt : (u : ℝ) < 1 := by
      rcases lt_or_eq_of_le u.2.2 with h | h
      · exact h
      · exact absurd (Subtype.ext h) hne
    exact hu (exists_of_lt_one v n hcn hn0 u u.2.1 hlt)
  have hIntV : ∀ j : Fin n, volume (Int j) = ENNReal.ofReal (v j) := by
    intro j
    have h0 : 0 ≤ cum v (j : ℕ) := by rw [← cum_zero v]; exact cum_mono v hv0 (Nat.zero_le _)
    have h1 : cum v ((j : ℕ) + 1) ≤ 1 := by
      rw [← hcn]; exact cum_mono v hv0 (by have := j.isLt; omega)
    have himg : Subtype.val '' Int j = Set.Ico (cum v (j : ℕ)) (cum v ((j : ℕ) + 1)) := by
      ext x; constructor
      · rintro ⟨u, hu, rfl⟩; exact hu
      · intro hx
        exact ⟨⟨x, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩, hx, rfl⟩
    rw [unitInterval.volume_apply, himg, Real.volume_Ico, cum_succ]
    congr 1; ring
  refine ⟨s, ?_, ?_, ?_⟩
  · apply measurable_to_countable'
    intro y; rw [hpre y]
    exact (hIntM _).union (hEM.inter (MeasurableSet.const _))
  · intro u
    show 0 < w (e.symm (pickF v n j0 (u : ℝ)))
    rw [← hvj]
    by_cases hx : ∃ j : Fin n, cum v (j : ℕ) ≤ (u : ℝ) ∧ (u : ℝ) < cum v ((j : ℕ) + 1)
    · obtain ⟨j, hj⟩ := hx
      rw [pickF_eq_of v hv0 n j0 _ j hj]
      have := hj.2; rw [cum_succ] at this; linarith [hj.1]
    · rw [pickF_of_not v n j0 _ hx]; exact hj0
  · intro y
    rw [hpre y]
    apply le_antisymm
    · calc volume (Int (e y) ∪ (E ∩ {_u | j0 = e y}))
          ≤ volume (Int (e y)) + volume (E ∩ {_u | j0 = e y}) := measure_union_le _ _
        _ ≤ volume (Int (e y)) + 0 := by
            gcongr; exact le_of_eq (measure_mono_null Set.inter_subset_left hENull)
        _ = ENNReal.ofReal (w y) := by rw [add_zero, hIntV, hvj, e.symm_apply_apply]
    · calc ENNReal.ofReal (w y) = volume (Int (e y)) := by rw [hIntV, hvj, e.symm_apply_apply]
        _ ≤ _ := measure_mono Set.subset_union_left

theorem lintegral_fin {Y : Type} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (s : unitInterval → Y) (hs : Measurable s) (g : Y → ENNReal) :
    ∫⁻ u, g (s u) = ∑ y, volume (s ⁻¹' {y}) * g y := by
  classical
  have hsplit : ∀ u, g (s u) = ∑ y, (s ⁻¹' {y}).indicator (fun _ => g y) u := by
    intro u
    rw [Finset.sum_eq_single (s u)]
    · simp [Set.indicator_apply]
    · intro y _ hy; simp [Set.indicator_apply, Ne.symm hy]
    · simp
  simp_rw [hsplit]
  rw [lintegral_finsetSum _ (fun y _ => measurable_const.indicator (hs (measurableSet_singleton y)))]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [lintegral_indicator_const (hs (measurableSet_singleton y)), mul_comm]

/-! ## Part 2: coins and a history-driven chain -/

abbrev Coins := ℕ → unitInterval

noncomputable abbrev μC : Measure Coins :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

section Chain

variable {Y : Type} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] {M : Type}

noncomputable def go (y0 : Y) (f : List M → M → Y → unitInterval → Y) : List M → Coins → Y
  | [], _ => y0
  | r :: rl, ω => f rl.reverse r (go y0 f rl ω) (ω rl.length)

noncomputable def Zc (y0 : Y) (f : List M → M → Y → unitInterval → Y) (l : List M)
    (ω : Coins) : Y :=
  go y0 f l.reverse ω

theorem Zc_nil (y0 : Y) (f : List M → M → Y → unitInterval → Y) (ω : Coins) :
    Zc y0 f [] ω = y0 := rfl

theorem Zc_snoc (y0 : Y) (f : List M → M → Y → unitInterval → Y) (l : List M) (r : M)
    (ω : Coins) : Zc y0 f (l ++ [r]) ω = f l r (Zc y0 f l ω) (ω l.length) := by
  simp [Zc, go]

theorem go_meas (y0 : Y) (f : List M → M → Y → unitInterval → Y)
    (hf : ∀ l r y, Measurable (f l r y)) : ∀ rl : List M, Measurable (go y0 f rl)
  | [] => measurable_const
  | r :: rl => by
    have h1 := go_meas y0 f hf rl
    have hg : Measurable (fun p : Y × unitInterval => f rl.reverse r p.1 p.2) :=
      measurable_from_prod_countable_right (fun y => hf _ _ y)
    exact hg.comp (h1.prodMk (measurable_pi_apply rl.length))

theorem go_dep (y0 : Y) (f : List M → M → Y → unitInterval → Y) :
    ∀ (rl : List M) (ω ω' : Coins), (∀ i < rl.length, ω i = ω' i) → go y0 f rl ω = go y0 f rl ω'
  | [], _, _, _ => rfl
  | r :: rl, ω, ω', h => by
    simp only [go]
    rw [go_dep y0 f rl ω ω' (fun i hi => h i (by simp; omega)), h rl.length (by simp)]

theorem Zc_meas (y0 : Y) (f : List M → M → Y → unitInterval → Y)
    (hf : ∀ l r y, Measurable (f l r y)) (l : List M) : Measurable (Zc y0 f l) :=
  go_meas y0 f hf l.reverse

theorem Zc_dep (y0 : Y) (f : List M → M → Y → unitInterval → Y) (l : List M) (ω ω' : Coins)
    (h : ∀ i < l.length, ω i = ω' i) : Zc y0 f l ω = Zc y0 f l ω' :=
  go_dep y0 f l.reverse ω ω' (by simpa using h)

end Chain

/-- The key independence step: a functional of the first `n` coins is independent of coin `n`. -/
theorem indep_step {Y : Type} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (n : ℕ) (G : Coins → Y) (hG : Measurable G)
    (hdep : ∀ ω ω' : Coins, (∀ i < n, ω i = ω' i) → G ω = G ω')
    (H : Y → unitInterval → ENNReal) (hH : ∀ y, Measurable (H y)) :
    ∫⁻ ω, H (G ω) (ω n) ∂μC = ∑ y, μC {ω | G ω = y} * ∫⁻ u, H y u := by
  classical
  have hsplit : ∀ ω : Coins, H (G ω) (ω n) =
      ∑ y, (if G ω = y then (1 : ENNReal) else 0) * H y (ω n) := by
    intro ω
    rw [Finset.sum_eq_single (G ω)]
    · simp
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  simp_rw [hsplit]
  rw [lintegral_finsetSum]
  · refine Finset.sum_congr rfl (fun y _ => ?_)
    have hind : iIndepFun (fun i (ω : Coins) => ω i) μC :=
      iIndepFun_infinitePi (P := fun _ : ℕ => (volume : Measure unitInterval))
        (X := fun _ (x : unitInterval) => x) (fun _ => measurable_id)
    have hdisj : Disjoint (Finset.range n) ({n} : Finset ℕ) := by simp
    have hAB := hind.indepFun_finset (Finset.range n) {n} hdisj (fun i => measurable_pi_apply i)
    let ext : (↥(Finset.range n) → unitInterval) → Coins := fun a i =>
      if h : i ∈ Finset.range n then a ⟨i, h⟩ else 0
    have hext : Measurable ext := by
      apply measurable_pi_lambda
      intro i
      by_cases h : i ∈ Finset.range n
      · simp only [ext, dif_pos h]; exact measurable_pi_apply _
      · simp only [ext, dif_neg h]; exact measurable_const
    let φ : (↥(Finset.range n) → unitInterval) → ENNReal := fun a =>
      if G (ext a) = y then 1 else 0
    let ψ : (↥({n} : Finset ℕ) → unitInterval) → ENNReal := fun b =>
      H y (b ⟨n, Finset.mem_singleton_self n⟩)
    have hφ : Measurable φ :=
      Measurable.ite ((hG.comp hext) (measurableSet_singleton y)) measurable_const measurable_const
    have hψ : Measurable ψ := (hH y).comp (measurable_pi_apply _)
    have hI := hAB.comp hφ hψ
    have hA : Measurable (fun (a : Coins) (i : ↥(Finset.range n)) => a i) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have hB : Measurable (fun (a : Coins) (i : ↥({n} : Finset ℕ)) => a i) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hφ.comp hA) (hψ.comp hB) hI
    have e1 : ∀ ω : Coins, (φ ∘ fun (a : Coins) (i : ↥(Finset.range n)) => a i) ω =
        if G ω = y then 1 else 0 := by
      intro ω
      have : G (ext (fun i : ↥(Finset.range n) => ω i)) = G ω := by
        apply hdep
        intro i hi
        simp only [ext, dif_pos (Finset.mem_range.2 hi)]
      simp only [Function.comp, φ, this]
    have e2 : ∀ ω : Coins, (ψ ∘ fun (a : Coins) (i : ↥({n} : Finset ℕ)) => a i) ω = H y (ω n) := by
      intro ω; rfl
    simp only [Pi.mul_apply, e1, e2] at hmul
    rw [hmul]
    congr 1
    · have : (fun ω : Coins => if G ω = y then (1 : ENNReal) else 0) =
          Set.indicator {ω | G ω = y} 1 := by
        funext ω; simp [Set.indicator_apply]
      rw [this]; exact lintegral_indicator_one (hG (measurableSet_singleton y))
    · exact (measurePreserving_eval_infinitePi _ n).lintegral_comp (hH y)
  · intro y _
    exact (Measurable.ite (hG (measurableSet_singleton y)) measurable_const measurable_const).mul
      ((hH y).comp (measurable_pi_apply n))


/-! ## Part 3: matchings, couplings, labelled configurations -/

section Match

variable {k : ℕ} {M : Type} [MetricSpace M]

theorem exists_label' (C : KConfig k M) :
    ∃ a : Fin k → M, Function.Injective a ∧ ∀ m, m ∈ C.1 ↔ ∃ i, a i = m := by
  classical
  let e := C.1.equivFin
  refine ⟨fun i => (e.symm (Fin.cast C.2.symm i)).1, ?_, ?_⟩
  · intro i j h
    have h' := Subtype.ext h
    have := e.symm.injective h'
    exact Fin.cast_injective _ this
  · intro m
    constructor
    · intro hm
      refine ⟨Fin.cast C.2 (e ⟨m, hm⟩), ?_⟩
      simp
    · rintro ⟨i, rfl⟩
      exact (e.symm (Fin.cast C.2.symm i)).2

theorem matchCost_nonneg' (C C' : KConfig k M) : 0 ≤ matchCost C C' := by
  unfold matchCost
  apply Real.sInf_nonneg
  rintro c ⟨a, b, -, -, -, -, rfl⟩
  exact Finset.sum_nonneg fun i _ => dist_nonneg

variable [Fintype M] [DecidableEq M]

theorem matchCost_attained (C C' : KConfig k M) :
    ∃ a b : Fin k → M, Function.Injective a ∧ Function.Injective b ∧
      (∀ m, m ∈ C.1 ↔ ∃ i, a i = m) ∧ (∀ m, m ∈ C'.1 ↔ ∃ i, b i = m) ∧
      matchCost C C' = ∑ i, dist (a i) (b i) := by
  classical
  let S : Set ℝ := {c | ∃ a b : Fin k → M, Function.Injective a ∧ Function.Injective b ∧
      (∀ m, m ∈ C.1 ↔ ∃ i, a i = m) ∧ (∀ m, m ∈ C'.1 ↔ ∃ i, b i = m) ∧
      c = ∑ i, dist (a i) (b i)}
  have hS : matchCost C C' = sInf S := by
    unfold matchCost
    congr 1
    ext c
    simp only [Set.mem_setOf_eq, S]
    constructor
    · rintro ⟨a, b, ha, hb, h1, h2, rfl⟩
      refine ⟨a, b, ha, hb, fun m => ?_, fun m => ?_, rfl⟩
      · rw [← h1]; simp
      · rw [← h2]; simp
    · rintro ⟨a, b, ha, hb, h1, h2, rfl⟩
      refine ⟨a, b, ha, hb, ?_, ?_, rfl⟩
      · ext m; simp [h1 m]
      · ext m; simp [h2 m]
  have hne : S.Nonempty := by
    obtain ⟨a, ha, hia⟩ := exists_label' C
    obtain ⟨b, hb, hib⟩ := exists_label' C'
    exact ⟨_, a, b, ha, hb, hia, hib, rfl⟩
  have hfin : S.Finite := (Set.finite_range (fun p : (Fin k → M) × (Fin k → M) =>
      ∑ i, dist (p.1 i) (p.2 i))).subset (by rintro c ⟨a, b, -, -, -, -, rfl⟩; exact ⟨(a, b), rfl⟩)
  obtain ⟨a, b, ha, hb, h1, h2, hc⟩ := hne.csInf_mem hfin
  exact ⟨a, b, ha, hb, h1, h2, hS.trans hc⟩

theorem isCoupling_prod' (S S' : KConfig k M → ℝ) (hS : IsKState S) (hS' : IsKState S') :
    IsCoupling S S' (fun z => S z.1 * S' z.2) := by
  refine ⟨fun z => mul_nonneg (hS.1 _) (hS'.1 _), fun C => ?_, fun C' => ?_⟩
  · simp only; rw [← Finset.mul_sum, hS'.2, mul_one]
  · simp only; rw [← Finset.sum_mul, hS.2, one_mul]

theorem transportCost_nonneg' (S S' : KConfig k M → ℝ) : 0 ≤ transportCost S S' := by
  unfold transportCost
  apply Real.sInf_nonneg
  rintro c ⟨q, hq, rfl⟩
  exact Finset.sum_nonneg fun z _ => mul_nonneg (hq.1 z) (matchCost_nonneg' _ _)

theorem coupling_near (S S' : KConfig k M → ℝ) (hS : IsKState S) (hS' : IsKState S') (ε : ℝ)
    (hε : 0 < ε) :
    ∃ q, IsCoupling S S' q ∧ ∑ z, q z * matchCost z.1 z.2 ≤ transportCost S S' + ε := by
  have hne : Set.Nonempty {c : ℝ | ∃ q, IsCoupling S S' q ∧ c = ∑ z, q z * matchCost z.1 z.2} :=
    ⟨_, _, isCoupling_prod' S S' hS hS', rfl⟩
  have hlt : sInf {c : ℝ | ∃ q, IsCoupling S S' q ∧ c = ∑ z, q z * matchCost z.1 z.2} <
      transportCost S S' + ε := by
    unfold transportCost; linarith
  obtain ⟨c, ⟨q, hq, rfl⟩, hc⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨q, hq, hc.le⟩

end Match

/-- Labelled configurations (injective labellings). -/
abbrev LConf (k : ℕ) (M : Type) := {L : Fin k → M // Function.Injective L}

section Build

variable {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]

local instance instMSL : MeasurableSpace (LConf k M) := ⊤
local instance instDML : DiscreteMeasurableSpace (LConf k M) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance instMSK : MeasurableSpace (KConfig k M) := ⊤
local instance instDMK : DiscreteMeasurableSpace (KConfig k M) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The unlabelled configuration of a labelled one. -/
def img (L : LConf k M) : KConfig k M :=
  ⟨Finset.univ.image L.1, by rw [Finset.card_image_of_injective _ L.2, Finset.card_univ,
    Fintype.card_fin]⟩

theorem mem_img (L : LConf k M) (m : M) : m ∈ (img L).1 ↔ ∃ i, L.1 i = m := by
  simp [img]

theorem relabel_exists (L : LConf k M) (C' : KConfig k M) :
    ∃ L' : LConf k M, img L' = C' ∧ KServer.moveCost L.1 L'.1 ≤ matchCost (img L) C' := by
  obtain ⟨a, b, ha, hb, hia, hib, hc⟩ := matchCost_attained (img L) C'
  have hL : ∀ i, ∃ j, a j = L.1 i := fun i => (hia (L.1 i)).1 ((mem_img L _).2 ⟨i, rfl⟩)
  choose π hπ using hL
  have hπi : Function.Injective π := by
    intro i i' h; apply L.2; rw [← hπ i, ← hπ i', h]
  have hπb : Function.Bijective π := Finite.injective_iff_bijective.mp hπi
  refine ⟨⟨b ∘ π, hb.comp hπi⟩, ?_, ?_⟩
  · apply Subtype.ext; ext m
    rw [show m ∈ (img (⟨b ∘ π, hb.comp hπi⟩ : LConf k M)).1 ↔ ∃ i, (b ∘ π) i = m from
      mem_img _ m, hib m]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨π i, rfl⟩
    · rintro ⟨j, rfl⟩; obtain ⟨i, rfl⟩ := hπb.2 j; exact ⟨i, rfl⟩
  · rw [hc]; unfold KServer.moveCost
    rw [← (Equiv.ofBijective π hπb).sum_comp (fun j => dist (a j) (b j))]
    apply le_of_eq; apply Finset.sum_congr rfl; intro i _
    simp [Equiv.ofBijective_apply, hπ i]

noncomputable def relabel (L : LConf k M) (C' : KConfig k M) : LConf k M :=
  (relabel_exists L C').choose

theorem relabel_img (L : LConf k M) (C' : KConfig k M) : img (relabel L C') = C' :=
  (relabel_exists L C').choose_spec.1

theorem relabel_cost (L : LConf k M) (C' : KConfig k M) :
    KServer.moveCost L.1 (relabel L C').1 ≤ matchCost (img L) C' :=
  (relabel_exists L C').choose_spec.2

/-- Conditional law of the next configuration given the current one. -/
noncomputable def condW (Q : List M → KConfig k M → ℝ)
    (q : List M → M → KConfig k M × KConfig k M → ℝ) (l : List M) (r : M)
    (C C' : KConfig k M) : ℝ :=
  if Q l C = 0 then Q (l ++ [r]) C' else q l r (C, C') / Q l C

section CondW

variable (Q : List M → KConfig k M → ℝ) (q : List M → M → KConfig k M × KConfig k M → ℝ)
  (hQ : ∀ l, IsKState (Q l)) (hq : ∀ l r, IsCoupling (Q l) (Q (l ++ [r])) (q l r))
include hQ hq

theorem q_le_row (l : List M) (r : M) (C C' : KConfig k M) : q l r (C, C') ≤ Q l C := by
  rw [← (hq l r).2.1 C]
  exact Finset.single_le_sum (f := fun C'' => q l r (C, C'')) (fun C'' _ => (hq l r).1 _)
    (Finset.mem_univ C')

theorem q_le_col (l : List M) (r : M) (C C' : KConfig k M) : q l r (C, C') ≤ Q (l ++ [r]) C' := by
  rw [← (hq l r).2.2 C']
  exact Finset.single_le_sum (f := fun C'' => q l r (C'', C')) (fun C'' _ => (hq l r).1 _)
    (Finset.mem_univ C)

theorem condW_nonneg (l : List M) (r : M) (C C' : KConfig k M) : 0 ≤ condW Q q l r C C' := by
  unfold condW; split_ifs with h
  · exact (hQ _).1 _
  · exact div_nonneg ((hq l r).1 _) ((hQ l).1 C)

theorem condW_sum (l : List M) (r : M) (C : KConfig k M) : ∑ C', condW Q q l r C C' = 1 := by
  unfold condW; split_ifs with h
  · exact (hQ _).2
  · rw [← Finset.sum_div, (hq l r).2.1 C, div_self h]

theorem condW_mul (l : List M) (r : M) (C C' : KConfig k M) :
    Q l C * condW Q q l r C C' = q l r (C, C') := by
  unfold condW; split_ifs with h
  · rw [h, zero_mul]
    have := q_le_row Q q hQ hq l r C C'
    rw [h] at this
    exact (le_antisymm this ((hq l r).1 _)).symm
  · field_simp

theorem condW_pos (l : List M) (r : M) (C C' : KConfig k M) (hpos : 0 < condW Q q l r C C') :
    0 < Q (l ++ [r]) C' := by
  unfold condW at hpos; split_ifs at hpos with h
  · exact hpos
  · have hQpos : 0 < Q l C := lt_of_le_of_ne ((hQ l).1 C) (Ne.symm h)
    have hq' : 0 < q l r (C, C') := (div_pos_iff_of_pos_right hQpos).mp hpos
    exact lt_of_lt_of_le hq' (q_le_col Q q hQ hq l r C C')

end CondW

set_option maxHeartbeats 1000000 in
theorem kuhn_core (L₀ : LConf k M) (Q : List M → KConfig k M → ℝ) (hQ : ∀ l, IsKState (Q l))
    (hQ0 : Q [] = pureState (img L₀))
    (hserve : ∀ (l : List M) (r : M) (C' : KConfig k M), 0 < Q (l ++ [r]) C' → r ∈ C'.1) :
    ∃ A : KServer.RandomizedAlgorithm k M, (∀ i, (A.alg i).conf [] = L₀.1) ∧ ∀ σ : List M,
      A.expCost σ ≤ ENNReal.ofReal (∑ j ∈ Finset.range σ.length,
        (transportCost (Q (σ.take j)) (Q (σ.take (j + 1))) + (1 / 2 : ℝ) ^ j)) := by
  choose q hq hqc using fun (l : List M) (r : M) =>
    coupling_near (Q l) (Q (l ++ [r])) (hQ l) (hQ _) ((1 / 2 : ℝ) ^ l.length) (by positivity)
  choose s hs_meas hs_pos hs_vol using fun (l : List M) (r : M) (C : KConfig k M) =>
    sample_exists (condW Q q l r C) (condW_nonneg Q q hQ hq l r C) (condW_sum Q q hQ hq l r C)
  let f : List M → M → LConf k M → unitInterval → LConf k M :=
    fun l r L u => relabel L (s l r (img L) u)
  have hf : ∀ l r L, Measurable (f l r L) := fun l r L =>
    (measurable_of_countable (relabel L)).comp (hs_meas l r (img L))
  have hZm : ∀ l, Measurable (Zc L₀ f l) := Zc_meas L₀ f hf
  have hGm : ∀ l, Measurable (fun ω => img (Zc L₀ f l ω)) := fun l =>
    (measurable_of_countable img).comp (hZm l)
  have hGdep : ∀ (l : List M) (ω ω' : Coins), (∀ i < l.length, ω i = ω' i) →
      img (Zc L₀ f l ω) = img (Zc L₀ f l ω') :=
    fun l ω ω' h => by rw [Zc_dep L₀ f l ω ω' h]
  have hsnoc : ∀ (l : List M) (r : M) (ω : Coins), Zc L₀ f (l ++ [r]) ω =
      relabel (Zc L₀ f l ω) (s l r (img (Zc L₀ f l ω)) (ω l.length)) :=
    fun l r ω => Zc_snoc L₀ f l r ω
  -- the law of the unlabelled configuration is `Q l`
  have hlaw : ∀ (l : List M) (C : KConfig k M),
      μC {ω | img (Zc L₀ f l ω) = C} = ENNReal.ofReal (Q l C) := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      intro C
      simp only [Zc_nil, hQ0, pureState]
      by_cases h : C = img L₀
      · subst h; simp
      · have h' : ¬ img L₀ = C := fun e => h e.symm
        simp [h, h']
    | append_singleton l r ih =>
      intro C'
      have key := indep_step l.length (fun ω => img (Zc L₀ f l ω)) (hGm l) (hGdep l)
        (fun C u => ((s l r C) ⁻¹' {C'}).indicator 1 u)
        (fun C => measurable_one.indicator (hs_meas l r C (measurableSet_singleton C')))
      have hL : ∫⁻ ω, ((s l r (img (Zc L₀ f l ω))) ⁻¹' {C'}).indicator 1 (ω l.length) ∂μC =
          μC {ω | img (Zc L₀ f (l ++ [r]) ω) = C'} := by
        have hpt : ∀ ω : Coins, ((s l r (img (Zc L₀ f l ω))) ⁻¹' {C'}).indicator
            (1 : unitInterval → ENNReal) (ω l.length) =
            ({ω | img (Zc L₀ f (l ++ [r]) ω) = C'}).indicator 1 ω := by
          intro ω
          classical
          rw [Set.indicator_apply, Set.indicator_apply]
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, hsnoc,
            relabel_img, Pi.one_apply]
        simp_rw [hpt]
        exact lintegral_indicator_one ((hGm (l ++ [r])) (measurableSet_singleton C'))
      rw [← hL, key]
      simp_rw [ih]
      have hv : ∀ C, ∫⁻ u, ((s l r C) ⁻¹' {C'}).indicator 1 u =
          ENNReal.ofReal (condW Q q l r C C') := by
        intro C
        rw [lintegral_indicator_one (hs_meas l r C (measurableSet_singleton C')), hs_vol]
      simp_rw [hv]
      rw [← (hq l r).2.2 C']
      simp_rw [← condW_mul Q q hQ hq l r]
      rw [ENNReal.ofReal_sum_of_nonneg (fun C _ =>
        mul_nonneg ((hQ l).1 C) (condW_nonneg Q q hQ hq l r C C'))]
      refine Finset.sum_congr rfl (fun C _ => ?_)
      rw [ENNReal.ofReal_mul ((hQ l).1 C)]
  -- the expected cost of one step
  have hstep : ∀ (l : List M) (r : M), ∫⁻ ω, ENNReal.ofReal (KServer.moveCost (Zc L₀ f l ω).1
      (Zc L₀ f (l ++ [r]) ω).1) ∂μC ≤ ENNReal.ofReal (∑ z, q l r z * matchCost z.1 z.2) := by
    intro l r
    calc ∫⁻ ω, ENNReal.ofReal (KServer.moveCost (Zc L₀ f l ω).1 (Zc L₀ f (l ++ [r]) ω).1) ∂μC
        ≤ ∫⁻ ω, (fun C u => ENNReal.ofReal (matchCost C (s l r C u))) (img (Zc L₀ f l ω))
            (ω l.length) ∂μC := by
          apply lintegral_mono; intro ω
          dsimp only
          rw [hsnoc]
          exact ENNReal.ofReal_le_ofReal (relabel_cost _ _)
      _ = ∑ C, μC {ω | img (Zc L₀ f l ω) = C} *
            ∫⁻ u, ENNReal.ofReal (matchCost C (s l r C u)) :=
          indep_step l.length _ (hGm l) (hGdep l)
            (fun C u => ENNReal.ofReal (matchCost C (s l r C u)))
            (fun C => (measurable_of_countable (fun C' => ENNReal.ofReal (matchCost C C'))).comp
              (hs_meas l r C))
      _ = ∑ C, ENNReal.ofReal (Q l C) * ∑ C', ENNReal.ofReal (condW Q q l r C C') *
            ENNReal.ofReal (matchCost C C') := by
          refine Finset.sum_congr rfl (fun C _ => ?_)
          rw [hlaw l C, lintegral_fin (s l r C) (hs_meas l r C)
            (fun C' => ENNReal.ofReal (matchCost C C'))]
          simp_rw [hs_vol]
      _ = ENNReal.ofReal (∑ z, q l r z * matchCost z.1 z.2) := by
          rw [Fintype.sum_prod_type]
          dsimp only
          rw [ENNReal.ofReal_sum_of_nonneg (fun C _ => Finset.sum_nonneg (fun C' _ =>
            mul_nonneg ((hq l r).1 _) (matchCost_nonneg' _ _)))]
          refine Finset.sum_congr rfl (fun C _ => ?_)
          rw [ENNReal.ofReal_sum_of_nonneg (fun C' _ =>
            mul_nonneg ((hq l r).1 _) (matchCost_nonneg' _ _)), Finset.mul_sum]
          refine Finset.sum_congr rfl (fun C' _ => ?_)
          rw [← condW_mul Q q hQ hq l r C C',
            ENNReal.ofReal_mul (mul_nonneg ((hQ l).1 C) (condW_nonneg Q q hQ hq l r C C')),
            ENNReal.ofReal_mul ((hQ l).1 C), mul_assoc]
  have hserveZ : ∀ (l : List M) (r : M) (ω : Coins), ∃ i, (Zc L₀ f (l ++ [r]) ω).1 i = r := by
    intro l r ω
    rw [hsnoc]
    have h1 : r ∈ (s l r (img (Zc L₀ f l ω)) (ω l.length)).1 :=
      hserve l r _ (condW_pos Q q hQ hq l r _ _ (hs_pos l r _ _))
    have h2 : r ∈ (img (relabel (Zc L₀ f l ω) (s l r (img (Zc L₀ f l ω)) (ω l.length)))).1 := by
      rw [relabel_img]; exact h1
    exact (mem_img _ r).1 h2
  have hmeasC : ∀ σ : List M, Measurable fun ω : Coins => ∑ j ∈ Finset.range σ.length,
      KServer.moveCost (Zc L₀ f (σ.take j) ω).1 (Zc L₀ f (σ.take (j + 1)) ω).1 := by
    intro σ
    apply Finset.measurable_sum
    intro j _
    exact (measurable_of_countable (fun p : LConf k M × LConf k M =>
      KServer.moveCost p.1.1 p.2.1)).comp ((hZm _).prodMk (hZm _))
  let A : KServer.RandomizedAlgorithm k M := KServer.RandomizedAlgorithm.mk (ι := Coins)
    (μ := μC) (prob := inferInstance)
    (alg := fun ω => ⟨fun l => (Zc L₀ f l ω).1, fun l r => hserveZ l r ω⟩)
    (meas := fun σ => hmeasC σ)
  refine ⟨A, fun ω => rfl, ?_⟩
  intro σ
  show ∫⁻ ω, ENNReal.ofReal (∑ j ∈ Finset.range σ.length,
      KServer.moveCost (Zc L₀ f (σ.take j) ω).1 (Zc L₀ f (σ.take (j + 1)) ω).1) ∂μC ≤ _
  have hnn : ∀ ω : Coins, ENNReal.ofReal (∑ j ∈ Finset.range σ.length,
      KServer.moveCost (Zc L₀ f (σ.take j) ω).1 (Zc L₀ f (σ.take (j + 1)) ω).1) =
      ∑ j ∈ Finset.range σ.length, ENNReal.ofReal
        (KServer.moveCost (Zc L₀ f (σ.take j) ω).1 (Zc L₀ f (σ.take (j + 1)) ω).1) := fun ω =>
    ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => dist_nonneg))
  simp_rw [hnn]
  rw [lintegral_finsetSum]
  swap
  · intro j _
    have hpair : ∀ (a b : List M) (g : LConf k M → LConf k M → ENNReal),
        Measurable (fun ω => g (Zc L₀ f a ω) (Zc L₀ f b ω)) := fun a b g =>
      (measurable_of_countable (fun p : LConf k M × LConf k M => g p.1 p.2)).comp
        ((hZm a).prodMk (hZm b))
    exact hpair (σ.take j) (σ.take (j + 1)) (fun L L' => ENNReal.ofReal (KServer.moveCost L.1 L'.1))
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (transportCost_nonneg' _ _)
    (by positivity))]
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j < σ.length := Finset.mem_range.1 hj
  have htk : σ.take (j + 1) = σ.take j ++ [σ[j]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hj']; rfl
  have hlen : (σ.take j).length = j := by simp [hj'.le]
  rw [htk]
  calc _ ≤ ENNReal.ofReal (∑ z, q (σ.take j) σ[j] z * matchCost z.1 z.2) := hstep _ _
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by have := hqc (σ.take j) σ[j]; rw [hlen] at this; exact this)

end Build


/-! ## Part 4: Theorem 7 from Theorem 24 -/

/-- The statement of Theorem 24 (online rounding), proved in the 80c9fd83 library. -/
def ORStmt : Prop :=
  ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M] [DecidableEq M] (e : M ≃ T.Leaf),
        T.IsLeafMetric M e →
      ∀ (k : ℕ) (C₀ : KConfig k M),
        ∃ P : List (M → ℝ) → (KConfig k M → ℝ),
          ∀ xs : ℕ → M → ℝ, (∀ t, IsFracState k (xs t)) →
            xs 0 = (fun m => if m ∈ C₀.1 then 1 else 0) →
            P [xs 0] = pureState C₀ ∧
            (∀ t, IsKState (P ((List.range (t + 1)).map xs)) ∧
              Consistent (P ((List.range (t + 1)).map xs)) (xs t)) ∧
            ∀ t, transportCost (P ((List.range (t + 1)).map xs))
                (P ((List.range (t + 2)).map xs)) ≤
              C * fracMoveCost T e (xs t) (xs (t + 1))

set_option maxHeartbeats 1000000 in
theorem t7_of (hOR : ORStmt) :
    ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf), T.IsLeafMetric M e →
      ∀ (k : ℕ) (C₀ : KServer.Config k M), Function.Injective C₀ →
      ∀ (F : FracKServerAlg k M) (c : ℝ), 0 ≤ c → F.IsCompetitiveFrom T e C₀ c →
        ∃ A : KServer.RandomizedAlgorithm k M, A.IsCompetitiveFrom C₀ (C * c) := by
  intro σ hσ
  obtain ⟨CR, hCR, hR⟩ := hOR σ hσ
  refine ⟨CR, hCR, ?_⟩
  intro V _ _ T hT M _ _ e hLM k C₀ hinj F c hc hF
  classical
  obtain ⟨hF0, hFs, hFr, a, ha⟩ := hF
  let L₀ : LConf k M := ⟨C₀, hinj⟩
  obtain ⟨P, hP⟩ := hR V T hT M e hLM k (img L₀)
  let Q : List M → KConfig k M → ℝ := fun l =>
    P ((List.range (l.length + 1)).map (fun t => F.state (l.take t)))
  have hx0 : ∀ l : List M, (fun t => F.state (l.take t)) 0 =
      (fun m => if m ∈ (img L₀).1 then 1 else 0) := by
    intro l
    simp only [List.take_zero, hF0]
    funext m
    by_cases h : ∃ i, C₀ i = m
    · have h1 : m ∈ (img L₀).1 := (mem_img L₀ m).2 h
      have h2 : m ∈ Set.range C₀ := h
      simp only [indicatorState, h1, h2, if_true]
    · have h1 : m ∉ (img L₀).1 := fun hm => h ((mem_img L₀ m).1 hm)
      have h2 : m ∉ Set.range C₀ := h
      simp only [indicatorState, h1, h2, if_false]
  have hfs : ∀ l : List M, ∀ t, IsFracState k ((fun t => F.state (l.take t)) t) :=
    fun l t => hFs _
  have hQk : ∀ l, IsKState (Q l) ∧ Consistent (Q l) (F.state l) := by
    intro l
    have h := (hP _ (hfs l) (hx0 l)).2.1 l.length
    have h2 := h.2
    simp only [List.take_length] at h2
    exact ⟨h.1, h2⟩
  have hQ0 : Q [] = pureState (img L₀) := (hP _ (hfs []) (hx0 [])).1
  have hserve : ∀ (l : List M) (r : M) (C' : KConfig k M), 0 < Q (l ++ [r]) C' → r ∈ C'.1 := by
    intro l r C' hpos
    by_contra hnot
    obtain ⟨hK, hC⟩ := hQk (l ++ [r])
    have h1 := hC r
    rw [hFr l r] at h1
    have h2 := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun C : KConfig k M => r ∈ C.1) (Q (l ++ [r]))
    rw [h1, hK.2] at h2
    have h3 : ∑ C ∈ Finset.univ.filter (fun C : KConfig k M => ¬ r ∈ C.1), Q (l ++ [r]) C = 0 := by
      linarith
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun C _ => hK.1 C)).1 h3 C' (by simp [hnot])
    linarith
  have htc : ∀ (l : List M) (r : M), transportCost (Q l) (Q (l ++ [r])) ≤
      CR * fracMoveCost T e (F.state l) (F.state (l ++ [r])) := by
    intro l r
    have h := (hP _ (hfs (l ++ [r])) (hx0 _)).2.2 l.length
    have e1 : (List.range (l.length + 1)).map (fun t => F.state ((l ++ [r]).take t)) =
        (List.range (l.length + 1)).map (fun t => F.state (l.take t)) := by
      apply List.map_congr_left
      intro t ht
      rw [List.mem_range] at ht
      rw [List.take_append_of_le_length (by omega)]
    have e2 : (List.range (l.length + 2)).map (fun t => F.state ((l ++ [r]).take t)) =
        (List.range ((l ++ [r]).length + 1)).map (fun t => F.state ((l ++ [r]).take t)) := by
      rw [List.length_append, List.length_singleton]
    have e3 : (l ++ [r]).take (l.length + 1) = l ++ [r] := by
      apply List.take_of_length_le; simp
    have e4 : (l ++ [r]).take l.length = l := by
      rw [List.take_append_of_le_length (le_refl _), List.take_length]
    rw [e1, e2] at h
    simp only [e3, e4] at h
    exact h
  obtain ⟨A, hA0, hAc⟩ := kuhn_core L₀ Q (fun l => (hQk l).1) hQ0 hserve
  refine ⟨A, hA0, CR * a + 2, fun ρ => ?_⟩
  refine (hAc ρ).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Finset.sum_add_distrib]
  have h1 : ∑ j ∈ Finset.range ρ.length, transportCost (Q (ρ.take j)) (Q (ρ.take (j + 1))) ≤
      CR * F.cost T e ρ := by
    unfold FracKServerAlg.cost
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have htk : ρ.take (j + 1) = ρ.take j ++ [ρ[j]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hj']; rfl
    rw [htk]
    exact htc _ _
  have h2 := sum_geometric_two_le ρ.length
  have h4 : CR * F.cost T e ρ ≤ CR * (c * KServer.offlineCost C₀ ρ + a) :=
    mul_le_mul_of_nonneg_left (ha ρ) hCR.le
  have h5 : CR * (c * KServer.offlineCost C₀ ρ + a) =
      CR * c * KServer.offlineCost C₀ ρ + CR * a := by ring
  linarith

end K1c810f69

open PolylogKServer.HST PolylogKServer.Fractional PolylogKServer.Rounding in
theorem solution :
    ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf), T.IsLeafMetric M e →
      ∀ (k : ℕ) (C₀ : KServer.Config k M), Function.Injective C₀ →
      ∀ (F : FracKServerAlg k M) (c : ℝ), 0 ≤ c → F.IsCompetitiveFrom T e C₀ c →
        ∃ A : KServer.RandomizedAlgorithm k M, A.IsCompetitiveFrom C₀ (C * c) := by
  exact K1c810f69.t7_of (R80c9fd83.online_rounding_of R80c9fd83.gr_all)
