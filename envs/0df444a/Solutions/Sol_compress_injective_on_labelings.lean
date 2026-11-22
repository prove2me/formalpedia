-- Prove2me | solution 1 for compress_injective_on_labelings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:34:32.432798+00:00
-- url     : https://prove2.me/submissions/328da935-8a7c-41cb-85dd-87e6c12ed3e5

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
theorem _root_.solution {X : Type u} {n : ℕ}
    {C : ConceptClass X Bool}
    (cs : CompressionScheme X Bool C)
    (pts : Fin n → X) (_hpts : Function.Injective pts)
    (f g : Fin n → Bool)
    (hf_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i)
    (hg_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = g i)
    (hfg : cs.compress (fun i => (pts i, f i)) = cs.compress (fun i => (pts i, g i))) :
    f = g := by
  have h_recon : cs.reconstruct (cs.compress (fun i => (pts i, f i))) =
                 cs.reconstruct (cs.compress (fun i => (pts i, g i))) :=
    congr_arg cs.reconstruct hfg
  funext i
  -- Realizability hypotheses match the correct field's guard
  have hf_real' : ∃ c ∈ C, ∀ i : Fin n,
      c ((fun i => (pts i, f i)) i).1 = ((fun i => (pts i, f i)) i).2 := by
    simp_all
  have hg_real' : ∃ c ∈ C, ∀ i : Fin n,
      c ((fun i => (pts i, g i)) i).1 = ((fun i => (pts i, g i)) i).2 := by
    simp_all
  have hf := cs.correct (fun i => (pts i, f i)) hf_real' i
  have hg := cs.correct (fun i => (pts i, g i)) hg_real' i
  simp_all
