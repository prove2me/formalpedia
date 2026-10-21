-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P32.productRange_regularity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:24:10.214501+00:00
-- url     : https://prove2.me/submissions/0cf832ca-b87a-4793-8b26-6c44bf5ff532

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

open QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section G66B
variable {K : Type} [Field K] [TopologicalSpace K]

theorem g66b_ck_succ (n : ℕ) {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F] (U : Set E) (f : E → F) :
    fieldCk (K := K) (n + 1) U f ↔ ContinuousOn f U ∧
      ∃ g : (E × E × K) → F, fieldCk (K := K) n (jetDomain (K := K) U) g ∧
        ∀ z ∈ jetDomain (K := K) U, f (z.1 + z.2.2 • z.2.1) - f z.1 = z.2.2 • g z := by
  rw [fieldCk]

theorem g66b_ck_zero {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F] (U : Set E) (f : E → F) :
    fieldCk (K := K) 0 U f ↔ ContinuousOn f U := by
  rw [fieldCk]

theorem g66b_ck_cont (n : ℕ) {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F] (U : Set E) (f : E → F)
    (h : fieldCk (K := K) n U f) : ContinuousOn f U := by
  cases n with
  | zero => exact (g66b_ck_zero U f).mp h
  | succ n => exact ((g66b_ck_succ n U f).mp h).1

theorem g66b_ck_pi {I : Type u} {F : I → Type u}
    [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)] [∀ i, TopologicalSpace (F i)] (n : ℕ) :
    ∀ {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
      (U : Set E) (f : E → ∀ i, F i),
      fieldCk (K := K) n U f ↔ ∀ i, fieldCk (K := K) n U (fun x => f x i) := by
  induction n with
  | zero =>
    intro E _ _ _ U f
    simp only [g66b_ck_zero]
    exact continuousOn_pi
  | succ n ih =>
    intro E _ _ _ U f
    simp only [g66b_ck_succ]
    constructor
    · rintro ⟨hc, g, hg, hid⟩ i
      refine ⟨continuousOn_pi.mp hc i, fun z => g z i, (ih _ g).mp hg i, fun z hz => ?_⟩
      have := congrFun (hid z hz) i
      simpa using this
    · intro H
      choose hc g hg hid using H
      refine ⟨continuousOn_pi.mpr hc, fun z i => g i z, (ih _ _).mpr hg, fun z hz => ?_⟩
      funext i
      simpa using hid i z hz
end G66B

theorem solution
    {K : Type} [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [T2Space K] (hNonDiscrete : ¬ DiscreteTopology K)
    {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E]
    {I : Type u} {F : I → Type u}
    [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)]
    [∀ i, TopologicalSpace (F i)] [∀ i, IsTopologicalAddGroup (F i)]
    [∀ i, ContinuousSMul K (F i)] [∀ i, T2Space (F i)]
    (U : Set E) (hU : IsOpen U) (f : E → ∀ i, F i) (r : WithTop ℕ) :
    fieldCr (K := K) r U f ↔ ∀ i, fieldCr (K := K) r U (fun x => f x i) := by
  unfold fieldCr
  constructor
  · intro h i n hn
    exact (g66b_ck_pi n U f).mp (h n hn) i
  · intro h n hn
    exact (g66b_ck_pi n U f).mpr fun i => h i n hn
