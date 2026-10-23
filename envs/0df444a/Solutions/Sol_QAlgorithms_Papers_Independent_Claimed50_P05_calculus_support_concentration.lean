-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_support_concentration
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:47:43.916242+00:00
-- url     : https://prove2.me/submissions/c49da41e-faee-4d5e-9d3d-72d54b789ba9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

namespace X7Z10S

variable {k : Type*} [RCLike k]
variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]

theorem X7_value_bg (T : H →L[k] H) (x : H) : value (boundedGraph T) x = T x := by
  have h : ∃ y, (x, y) ∈ boundedGraph T := ⟨T x, rfl⟩
  unfold value
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem X7_zero_eq : (zeroGraph : Relation H) = boundedGraph (0 : H →L[k] H) := by
  ext p
  simp [zeroGraph, boundedGraph]

theorem X7_eq_of_sub (A : Relation H) (R : H →L[k] H) (hA : A ⊆ boundedGraph R)
    (hd : ∀ x, ∃ y, (x, y) ∈ A) : A = boundedGraph R := by
  apply Set.Subset.antisymm hA
  intro p hp
  obtain ⟨y, hy⟩ := hd p.1
  have h1 : y = R p.1 := hA hy
  have h2 : p.2 = R p.1 := hp
  have : p = (p.1, y) := by
    ext
    · rfl
    · simp [h1, h2]
  rw [this]
  exact hy

theorem X7_bounded_plus (f g : Symbol X k) (hf : BoundedSymbol f) (hg : BoundedSymbol g) :
    BoundedSymbol (plus f g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c + d, fun x => ?_⟩
  exact (norm_add_le _ _).trans (add_le_add (hc x) (hd x))

theorem X7_bounded_times (f g : Symbol X k) (hf : BoundedSymbol f) (hg : BoundedSymbol g) :
    BoundedSymbol (times f g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c * d, fun x => ?_⟩
  change ‖f.val x * g.val x‖ ≤ c * d
  rw [norm_mul]
  exact mul_le_mul (hc x) (hd x) (norm_nonneg _) ((norm_nonneg _).trans (hc x))

theorem X7_bounded_ind (A : Set X) (hA : MeasurableSet A) :
    BoundedSymbol (indicator (k := k) A hA) := by
  refine ⟨1, fun x => ?_⟩
  change ‖A.indicator (fun _ => (1 : k)) x‖ ≤ 1
  by_cases hx : x ∈ A
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

variable {F : Symbol X k → Relation H}

theorem X7_F_plus (hF : Calculus F) (f g : Symbol X k) (hf : BoundedSymbol f)
    (hg : BoundedSymbol g) : F (plus f g) = add (F f) (F g) := by
  obtain ⟨R, hR⟩ := (hF.2.2.1 (plus f g) (X7_bounded_plus f g hf hg)).1
  obtain ⟨T, hT⟩ := (hF.2.2.1 f hf).1
  obtain ⟨S, hS⟩ := (hF.2.2.1 g hg).1
  rw [hR]
  symm
  apply X7_eq_of_sub
  · rw [← hR]
    exact hF.2.1.2.1 f g
  · intro x
    refine ⟨T x + S x, T x, S x, ?_, ?_, rfl⟩
    · rw [hT]; rfl
    · rw [hS]; rfl

theorem X7_F_times (hF : Calculus F) (f g : Symbol X k) (hf : BoundedSymbol f)
    (hg : BoundedSymbol g) : F (times f g) = mul (F f) (F g) := by
  obtain ⟨R, hR⟩ := (hF.2.2.1 (times f g) (X7_bounded_times f g hf hg)).1
  obtain ⟨T, hT⟩ := (hF.2.2.1 f hf).1
  obtain ⟨S, hS⟩ := (hF.2.2.1 g hg).1
  rw [hR]
  symm
  apply X7_eq_of_sub
  · rw [← hR]
    exact hF.2.1.2.2.2.1 f g
  · intro x
    refine ⟨T (S x), S x, ?_, ?_⟩
    · rw [hS]; rfl
    · rw [hT]; rfl

theorem X7_null_empty (hF : Calculus F) : Null F (∅ : Set X) := by
  refine ⟨MeasurableSet.empty, ?_⟩
  have hb := X7_bounded_ind (k := k) (∅ : Set X) MeasurableSet.empty
  obtain ⟨R, hR⟩ := (hF.2.2.1 _ hb).1
  have hsym : plus (indicator (k := k) (∅ : Set X) MeasurableSet.empty)
      (indicator (∅ : Set X) MeasurableSet.empty) = indicator (∅ : Set X) MeasurableSet.empty := by
    apply Subtype.ext
    funext x
    simp [plus, indicator]
  have h := X7_F_plus hF _ _ hb hb
  rw [hsym, hR] at h
  have hR0 : R = 0 := by
    ext x
    have hx : (x, R x) ∈ boundedGraph R := rfl
    rw [h] at hx
    obtain ⟨a, b, ha, hb', he⟩ := hx
    have ha' : a = R x := ha
    have hb'' : b = R x := hb'
    simp only at he
    rw [ha', hb''] at he
    simp only [ContinuousLinearMap.zero_apply]
    have : R x + R x - R x = R x - R x := by rw [← he]
    simpa using this
  rw [hR, hR0, X7_zero_eq (k := k)]

theorem X7_null_union (hF : Calculus F) (A B : Set X) (hA : Null F A) (hB : Null F B) :
    Null F (A ∪ B) := by
  obtain ⟨hAm, hA0⟩ := hA
  obtain ⟨hBm, hB0⟩ := hB
  refine ⟨hAm.union hBm, ?_⟩
  have hsym : indicator (k := k) (A ∪ B) (hAm.union hBm) =
      plus (indicator A hAm) (times (indicator Aᶜ hAm.compl) (indicator B hBm)) := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ A <;> by_cases hy : x ∈ B <;> simp [plus, times, indicator, hx, hy]
  rw [hsym, X7_F_plus hF _ _ (X7_bounded_ind A hAm)
      (X7_bounded_times _ _ (X7_bounded_ind _ _) (X7_bounded_ind B hBm)),
    X7_F_times hF _ _ (X7_bounded_ind _ _) (X7_bounded_ind B hBm), hA0, hB0]
  obtain ⟨T, hT⟩ := (hF.2.2.1 _ (X7_bounded_ind (k := k) Aᶜ hAm.compl)).1
  rw [hT]
  ext p
  simp only [add, mul, zeroGraph, boundedGraph, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b, ha, ⟨z, hz, hb⟩, he⟩
    rw [he, ha, hb, hz]
    simp
  · intro hp
    exact ⟨0, 0, rfl, ⟨0, rfl, by simp⟩, by simp [hp]⟩

theorem X7_null_iUnion (hF : Calculus F) (A : ℕ → Set X) (hA : ∀ n, Null F (A n)) :
    Null F (⋃ n, A n) := by
  have hm : ∀ n, MeasurableSet (A n) := fun n => (hA n).1
  have hacc : ∀ n, Null F (Set.accumulate A n) := by
    intro n
    induction n with
    | zero =>
      have : Set.accumulate A 0 = A 0 := by simp [Set.accumulate_def]
      rw [this]; exact hA 0
    | succ n ih =>
      rw [Set.accumulate_succ]
      exact X7_null_union hF _ _ ih (hA (n + 1))
  have hUm : MeasurableSet (⋃ n, A n) := MeasurableSet.iUnion hm
  refine ⟨hUm, ?_⟩
  have hbp : BP (fun n => indicator (k := k) (Set.accumulate A n) (hacc n).1)
      (indicator (⋃ n, A n) hUm) := by
    refine ⟨?_, 1, ?_⟩
    · intro x
      by_cases hx : x ∈ ⋃ n, A n
      · obtain ⟨m, hmx⟩ := Set.mem_iUnion.mp hx
        apply tendsto_atTop_of_eventually_const (i₀ := m)
        intro n hn
        have hxn : x ∈ Set.accumulate A n :=
          Set.monotone_accumulate hn (Set.subset_accumulate hmx)
        simp [indicator, Set.indicator_of_mem hxn, Set.indicator_of_mem hx]
      · apply tendsto_atTop_of_eventually_const (i₀ := 0)
        intro n _
        have hxn : x ∉ Set.accumulate A n := fun h => hx (Set.accumulate_subset_iUnion n h)
        simp [indicator, Set.indicator_of_notMem hxn, Set.indicator_of_notMem hx]
    · intro n x
      by_cases hx : x ∈ Set.accumulate A n
      · simp [indicator, Set.indicator_of_mem hx]
      · simp [indicator, Set.indicator_of_notMem hx]
  have hw := (hF.2.2.2 _ _ hbp).2.2
  obtain ⟨R, hR⟩ := (hF.2.2.1 _ (X7_bounded_ind (k := k) _ hUm)).1
  have hzero : ∀ n, F (indicator (k := k) (Set.accumulate A n) (hacc n).1) = zeroGraph :=
    fun n => (hacc n).2
  have hR0 : R = 0 := by
    ext y
    have h := hw (R y) y
    have hv0 : value (zeroGraph : Relation H) y = 0 := by
      rw [X7_zero_eq (k := k), X7_value_bg]; rfl
    simp only [hzero, hv0, inner_zero_right, hR, X7_value_bg] at h
    have h2 : (0 : k) = inner k (R y) (R y) := tendsto_nhds_unique tendsto_const_nhds h
    simpa using h2.symm
  rw [hR, hR0, X7_zero_eq (k := k)]

end X7Z10S

end QAlgorithms.Papers.Independent.Claimed50.P05

end

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

open QAlgorithms.Papers.Independent.Claimed50.P05 QAlgorithms.Papers.Independent.Claimed50.P05.X7Z10S in
theorem solution {k : Type*} [RCLike k] {X : Type*} [MeasurableSpace X]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]
    [TopologicalSpace X] [BorelSpace X]
    [SecondCountableTopology X] (F : QAlgorithms.Papers.Independent.Claimed50.P05.Symbol X k → Relation H) (hF : Calculus F) :
    Concentrated F (calculusSupport F) := by
  set 𝒰 : Set (Set X) := {U : Set X | IsOpen U ∧ Null F U} with h𝒰
  have hopen : ∀ U ∈ 𝒰, IsOpen U := fun U hU => hU.1
  refine ⟨(isOpen_sUnion hopen).measurableSet.compl, ?_⟩
  unfold calculusSupport
  rw [compl_compl]
  obtain ⟨T, hTc, hT𝒰, hTeq⟩ := TopologicalSpace.isOpen_sUnion_countable 𝒰 hopen
  rw [← hTeq]
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT, sUnion_empty]
    exact X7_null_empty hF
  · obtain ⟨g, hg⟩ := hTc.exists_eq_range hT
    rw [hg, sUnion_range]
    apply X7_null_iUnion hF
    intro n
    have : g n ∈ T := by rw [hg]; exact ⟨n, rfl⟩
    exact (hT𝒰 this).2
