-- Prove2me | solution 1 for block_extract_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:47.257257+00:00
-- url     : https://prove2.me/submissions/74f4ee56-23a3-41aa-886e-82488761abd9

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (k m : ℕ) (j₁ j₂ : Fin k) (hne : j₁ ≠ j₂) :
    Disjoint
      (Finset.image (fun i : Fin m => finProdFinEquiv (j₁, i)) Finset.univ)
      (Finset.image (fun i : Fin m => finProdFinEquiv (j₂, i)) Finset.univ) := by
  rw [Finset.disjoint_iff_ne]
  simp_all
