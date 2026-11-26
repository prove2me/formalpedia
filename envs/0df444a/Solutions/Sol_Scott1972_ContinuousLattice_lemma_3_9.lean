-- Prove2me | solution 1 for Scott1972.ContinuousLattice.lemma_3_9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:37.364612+00:00
-- url     : https://prove2.me/submissions/d09e0773-6055-44a1-8bfd-a3056e77dc59

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Theorems.Thm_Scott1972_ContinuousLattice_ScottMap_continuous
import Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_continuous
import Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_eq_of_continuous
import Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_maximal
import Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_maximal_le


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {X Y D D' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompleteLattice D] [CompleteLattice D']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D')
    (P : IsContinuousLatticeProjection D D') (e : X → Y) (he : IsEmbedding e)
    {f : X → D} {g : X → D'} (hf : @Continuous X D _ scottTopologicalSpace f)
    (hg : @Continuous X D' _ scottTopologicalSpace g)
    (hfg : ∀ x, f x = (P.retr : D' → D) (g x)) (y : Y) :
    scottExtend e f y = (P.retr : D' → D) (scottExtend e g y) := by
  have hfbar : @Continuous Y D _ scottTopologicalSpace (scottExtend e f) :=
    scottExtend_continuous hD e f
  have hgbar : @Continuous Y D' _ scottTopologicalSpace (scottExtend e g) :=
    scottExtend_continuous hD' e g
  -- `j ∘ ḡ` and `i ∘ f̄` are continuous (Scott topology is not an instance; register it locally so
  -- `Continuous.comp` can fire, scoped to avoid the lattice `≤` clashing with specialization order).
  have hjg : @Continuous Y D _ scottTopologicalSpace (fun z => (P.retr : D' → D) (scottExtend e g z)) := by
    letI : TopologicalSpace D := scottTopologicalSpace
    letI : TopologicalSpace D' := scottTopologicalSpace
    exact P.retr.continuous.comp hgbar
  have hif : @Continuous Y D' _ scottTopologicalSpace (fun z => (P.incl : D → D') (scottExtend e f z)) := by
    letI : TopologicalSpace D := scottTopologicalSpace
    letI : TopologicalSpace D' := scottTopologicalSpace
    exact P.incl.continuous.comp hfbar
  -- Step A: `j ∘ ḡ ⊑ f̄`.
  have hA : ∀ z, (P.retr : D' → D) (scottExtend e g z) ≤ scottExtend e f z := by
    intro z
    refine scottExtend_maximal hD e hjg ?_ z
    intro x
    show (P.retr : D' → D) (scottExtend e g (e x)) = f x
    rw [scottExtend_eq_of_continuous hD' e he g hg x, ← hfg x]
  -- Step B: `i ∘ f̄ ⊑ ḡ`.
  have hB : ∀ z, (P.incl : D → D') (scottExtend e f z) ≤ scottExtend e g z := by
    intro z
    refine scottExtend_maximal_le hD' e hif ?_ z
    intro x
    show (P.incl : D → D') (scottExtend e f (e x)) ≤ g x
    rw [scottExtend_eq_of_continuous hD e he f hf x, hfg x]
    exact P.incl_retr_le (g x)
  refine le_antisymm ?_ (hA y)
  calc scottExtend e f y
      = (P.retr : D' → D) ((P.incl : D → D') (scottExtend e f y)) :=
        (P.retr_incl (scottExtend e f y)).symm
    _ ≤ (P.retr : D' → D) (scottExtend e g y) := P.retr.monotone (hB y)
end Scott1972.ContinuousLattice
