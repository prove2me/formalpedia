-- Prove2me | solution 1 for P2M_exp_mul_sup__le_sum_07b6ab8eda1c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:52.549795+00:00
-- url     : https://prove2.me/submissions/2e1b5efe-e9bf-4ab0-9d58-69b71558b52c

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) (_ht : 0 ≤ t) :
    Real.exp (t * s.sup' hs f) ≤ ∑ i ∈ s, Real.exp (t * f i) := by
  -- sup' is achieved: ∃ i₀ ∈ s, f i₀ = sup' (since ℝ is LinearOrder, s finite nonempty)
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_mem_eq_sup' hs f
  -- exp(t * f i₀) ≤ ∑ exp(t * f i) since i₀ ∈ s and all terms are nonneg
  calc Real.exp (t * s.sup' hs f)
      = Real.exp (t * f i₀) := by rw [hmax]
    _ ≤ ∑ i ∈ s, Real.exp (t * f i) :=
        Finset.single_le_sum (f := fun i => Real.exp (t * f i))
          (fun i _ => (Real.exp_pos (t * f i)).le) hi₀
