-- Prove2me | solution 1 for ResolvingPricing.Tsharp_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T06:30:23.332788+00:00
-- url     : https://prove2.me/submissions/e4d0d43f-cb38-4ac8-8a05-0b6b8c1193fc

import Mathlib
import Definitions.Def_ResolvingPricing_Tsharp

open MeasureTheory

namespace Aux_RPTS

lemma aux {Ω : Type*} [MeasurableSpace Ω] (s : Finset ℕ) (P : ℕ → Ω → Prop)
    {inst : ∀ ω, DecidablePred (fun τ => P τ ω)} (N a : ℕ) (ha : 0 < a)
    (hP : ∀ τ ∈ s, a ≤ τ → MeasurableSet {ω | P τ ω}) :
    MeasurableSet {ω | a ≤ max ((s.filter (fun τ => P τ ω)).sup id) N} := by
  have hbot : (⊥ : ℕ) < a := ha
  have e : {ω | a ≤ max ((s.filter (fun τ => P τ ω)).sup id) N} =
      {ω | a ≤ N} ∪ ⋃ τ ∈ s, {ω | a ≤ τ ∧ P τ ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, le_max_iff, Set.mem_union, Set.mem_iUnion, exists_prop]
    rw [Finset.le_sup_iff hbot]
    simp only [Finset.mem_filter, id]
    constructor
    · rintro (⟨b, ⟨hb, hPb⟩, hab⟩ | h)
      · exact Or.inr ⟨b, hb, hab, hPb⟩
      · exact Or.inl h
    · rintro (h | ⟨b, hb, hab, hPb⟩)
      · exact Or.inr h
      · exact Or.inl ⟨b, ⟨hb, hPb⟩, hab⟩
  rw [e]
  refine (MeasurableSet.const _).union (Finset.measurableSet_biUnion _ (fun τ hτ => ?_))
  by_cases hτ' : a ≤ τ
  · simp only [hτ', true_and]; exact hP τ hτ hτ'
  · simp only [hτ', false_and, Set.setOf_false]; exact MeasurableSet.empty

end Aux_RPTS

open ResolvingPricing in
theorem solution (P : Model) (T : ℕ) (x : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ρ : Run P T x μ ℱ) :
    IsStoppingTime ℱ (fun ω => ((T + 1 - ρ.Tsharp ω : ℕ) : WithTop ℕ)) := by
  intro i
  have hset : {ω | ((T + 1 - ρ.Tsharp ω : ℕ) : WithTop ℕ) ≤ (i : WithTop ℕ)} =
      {ω | T + 1 - i ≤ ρ.Tsharp ω} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have hc : ((T + 1 - ρ.Tsharp ω : ℕ) : WithTop ℕ) ≤ (i : WithTop ℕ) ↔
        T + 1 - ρ.Tsharp ω ≤ i := by
      first
        | exact WithTop.coe_le_coe
        | exact Nat.cast_le
    rw [hc]
    omega
  show MeasurableSet[ℱ i] {ω | ((T + 1 - ρ.Tsharp ω : ℕ) : WithTop ℕ) ≤ (i : WithTop ℕ)}
  rw [hset]
  have hharm : ∀ τ, T + 1 - i ≤ τ → 2 ≤ τ →
      Measurable[ℱ i] (fun ω => harm T (fun τ => ρ.xiB τ ω) (τ - 1)) := by
    intro τ hτ h2
    unfold harm
    refine Finset.measurable_sum _ (fun j hj => ?_)
    rw [Finset.mem_Ioc] at hj
    apply Measurable.div_const
    unfold Run.xiB
    have hk : T - j < T := by omega
    exact (ρ.ξ_measurable (T - j) hk).mono (ℱ.mono (by omega)) le_rfl
  unfold Run.Tsharp Tsharp
  by_cases hT : T < ⌈2 * |P.r2 x| * P.Bξ / P.r1 x⌉₊
  · simp only [hT, ↓reduceIte]
    exact MeasurableSet.const _
  · simp only [hT, ↓reduceIte]
    by_cases hm : T + 1 - i = 0
    · rw [hm]
      simp only [Nat.zero_le, Set.setOf_true]
      exact MeasurableSet.univ
    · letI : MeasurableSpace Ω := ℱ i
      refine Aux_RPTS.aux (Finset.Icc 2 T) _ _ _ (Nat.pos_of_ne_zero hm) (fun τ hτ hmτ => ?_)
      exact measurableSet_lt measurable_const
        (hharm τ hmτ (Finset.mem_Icc.mp hτ).1).abs
