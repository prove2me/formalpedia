-- Prove2me | solution 1 for StochCompStatics.proof_theorem_3_h_increasing_differences
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:03:25.726274+00:00
-- url     : https://prove2.me/submissions/ec91d180-2be5-4118-8a48-1ad7fa3d17a1

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn
import Definitions.Def_StochCompStatics_Model

open MeasureTheory ProbabilityTheory Supermodularity.Monotonicity

open StochCompStatics in
theorem solution {S : Type*} [MeasurableSpace S] [PartialOrder S]
    (A : Set ℝ) (p : Kernel (S × ℝ) S) [IsMarkovKernel p] (r : S → ℝ → ℝ) (f : ℝ → S → ℝ)
    (hp : IsMonotoneKernel A p)
    (hf : ∀ β ∈ Set.Ioo (0 : ℝ) 1, Monotone (f β) ∧ Measurable (f β) ∧
      ∀ s, ∀ a ∈ A, Integrable (f β) (p (s, a)))
    (hID : IncreasingDifferencesOn (fun s β => f β s) (Set.univ ×ˢ Set.Ioo 0 1)) :
    (∀ s, IncreasingDifferencesOn (fun a β => h p r β (f β) s a) (A ×ˢ Set.Ioo 0 1)) ∧
    (∀ a ∈ A, IncreasingDifferencesOn (fun s β => h p r β (f β) s a)
      (Set.univ ×ˢ Set.Ioo 0 1)) := by
  have core : ∀ (x1 x2 : S × ℝ), x1 ∈ (Set.univ : Set S) ×ˢ A → x2 ∈ (Set.univ : Set S) ×ˢ A →
      x1 ≤ x2 → ∀ (b1 b2 : ℝ), b1 ∈ Set.Ioo (0 : ℝ) 1 → b2 ∈ Set.Ioo (0 : ℝ) 1 → b1 < b2 →
      b2 * ∫ s', f b2 s' ∂(p x1) - b1 * ∫ s', f b1 s' ∂(p x1) ≤
        b2 * ∫ s', f b2 s' ∂(p x2) - b1 * ∫ s', f b1 s' ∂(p x2) := by
    intro x1 x2 hx1 hx2 hle b1 b2 hb1 hb2 hlt
    have hD : Monotone (fun s => f b2 s - f b1 s) := by
      intro u w huw
      have hu : u ∈ {x : S | (x, b1) ∈ (Set.univ : Set S) ×ˢ Set.Ioo (0 : ℝ) 1} ∩
          {x : S | (x, b2) ∈ (Set.univ : Set S) ×ˢ Set.Ioo (0 : ℝ) 1} :=
        ⟨Set.mk_mem_prod (Set.mem_univ _) hb1, Set.mk_mem_prod (Set.mem_univ _) hb2⟩
      have hw : w ∈ {x : S | (x, b1) ∈ (Set.univ : Set S) ×ˢ Set.Ioo (0 : ℝ) 1} ∩
          {x : S | (x, b2) ∈ (Set.univ : Set S) ×ˢ Set.Ioo (0 : ℝ) 1} :=
        ⟨Set.mk_mem_prod (Set.mem_univ _) hb1, Set.mk_mem_prod (Set.mem_univ _) hb2⟩
      exact hID hlt hu hw huw
    have hf1 := hf b1 hb1
    have hf2 := hf b2 hb2
    have hDint : ∀ s, ∀ a ∈ A, Integrable (fun s => f b2 s - f b1 s) (p (s, a)) :=
      fun s a ha => (hf2.2.2 s a ha).sub (hf1.2.2 s a ha)
    have hmD := hp (fun s => f b2 s - f b1 s) hD (hf2.2.1.sub hf1.2.1) hDint
    have hm1 := hp (f b1) hf1.1 hf1.2.1 hf1.2.2
    have i1 : ∫ s', (f b2 s' - f b1 s') ∂(p x1) ≤ ∫ s', (f b2 s' - f b1 s') ∂(p x2) :=
      hmD hx1 hx2 hle
    have i2 : ∫ s', f b1 s' ∂(p x1) ≤ ∫ s', f b1 s' ∂(p x2) := hm1 hx1 hx2 hle
    have int2 : ∀ x ∈ (Set.univ : Set S) ×ˢ A, Integrable (f b2) (p x) :=
      fun x hx => hf2.2.2 x.1 x.2 hx.2
    have int1 : ∀ x ∈ (Set.univ : Set S) ×ˢ A, Integrable (f b1) (p x) :=
      fun x hx => hf1.2.2 x.1 x.2 hx.2
    have e1 : ∫ s', (f b2 s' - f b1 s') ∂(p x1) =
        ∫ s', f b2 s' ∂(p x1) - ∫ s', f b1 s' ∂(p x1) := integral_sub (int2 x1 hx1) (int1 x1 hx1)
    have e2 : ∫ s', (f b2 s' - f b1 s') ∂(p x2) =
        ∫ s', f b2 s' ∂(p x2) - ∫ s', f b1 s' ∂(p x2) := integral_sub (int2 x2 hx2) (int1 x2 hx2)
    rw [e1, e2] at i1
    have hb2pos : 0 ≤ b2 := le_of_lt hb2.1
    have hdiff : 0 ≤ b2 - b1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left i1 hb2pos, mul_le_mul_of_nonneg_left i2 hdiff]
  constructor
  · intro s b1 b2 hlt a ha c hc hac
    have hb1 : b1 ∈ Set.Ioo (0 : ℝ) 1 := ha.1.2
    have hb2 : b2 ∈ Set.Ioo (0 : ℝ) 1 := ha.2.2
    have haA : a ∈ A := ha.1.1
    have hcA : c ∈ A := hc.1.1
    have := core (s, a) (s, c) ⟨Set.mem_univ _, haA⟩ ⟨Set.mem_univ _, hcA⟩
      (Prod.mk_le_mk.mpr ⟨le_rfl, hac⟩) b1 b2 hb1 hb2 hlt
    simp only [StochCompStatics.h]
    linarith
  · intro a ha b1 b2 hlt s1 hs1 s2 hs2 hle
    have hb1 : b1 ∈ Set.Ioo (0 : ℝ) 1 := hs1.1.2
    have hb2 : b2 ∈ Set.Ioo (0 : ℝ) 1 := hs1.2.2
    have := core (s1, a) (s2, a) ⟨Set.mem_univ _, ha⟩ ⟨Set.mem_univ _, ha⟩
      (Prod.mk_le_mk.mpr ⟨hle, le_rfl⟩) b1 b2 hb1 hb2 hlt
    simp only [StochCompStatics.h]
    linarith
