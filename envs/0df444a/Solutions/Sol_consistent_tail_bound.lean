-- Prove2me | solution 1 for consistent_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:28.258405+00:00
-- url     : https://prove2.me/submissions/172a4c41-9262-48ea-8f3a-2ce4c7fd4d87

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (herr : D { x | h x ≠ c x } ≥ ENNReal.ofReal ε)
    (hmeas : MeasurableSet { x | h x ≠ c x }) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { xs : Fin m → X | ∀ i, h (xs i) = c (xs i) }
      ≤ ENNReal.ofReal ((1 - ε) ^ m) := by
  have hset : { xs : Fin m → X | ∀ i, h (xs i) = c (xs i) } =
      Set.pi Set.univ (fun _ : Fin m => { x : X | h x = c x }) := by
    ext xs
    simp [Set.mem_pi]
  rw [hset, MeasureTheory.Measure.pi_pi]
  have hcompl : { x : X | h x = c x } = { x : X | h x ≠ c x }ᶜ := by
    ext x; simp
  have hD_agree : D { x | h x = c x } ≤ ENNReal.ofReal (1 - ε) := by
    rw [hcompl, MeasureTheory.measure_compl hmeas (MeasureTheory.measure_ne_top D _),
        MeasureTheory.IsProbabilityMeasure.measure_univ,
        ENNReal.ofReal_sub 1 hε.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left herr 1
  calc ∏ i : Fin m, D { x | h x = c x }
      ≤ ∏ _i : Fin m, ENNReal.ofReal (1 - ε) :=
        Finset.prod_le_prod (fun _ _ => bot_le) (fun i _ => hD_agree)
    _ = ENNReal.ofReal (1 - ε) ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = ENNReal.ofReal ((1 - ε) ^ m) := by
        rw [ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 1 - ε)]
