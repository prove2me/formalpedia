-- Prove2me | solution 1 for ThreeSum.BoxStages.partialZeta_eq_boxSum
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:42:05.287049+00:00
-- url     : https://prove2.me/submissions/e7e96e31-0370-4ca3-9eda-62674f7dfdd3

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Canonical sparse boxes as stored prefix-zeta stages

A global coordinate prefix intersects each flagged set in an initial
segment. Storing those initialCoords stages uses only a polynomial factor more
than the compact downset. The resulting entries are exactly the signed
box sums used by the sparse-query partition.
-/

namespace ThreeSum.BoxStages

open Finset





































































theorem partialZeta_eq_boxSum_sourceProof {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (flags processed : Finset (Fin L)) :
    Subset.partialZeta processed weight flags =
      SparseBoxes.boxSum flags (flags ∩ processed) weight := by
  have hrequired : flags \ (flags ∩ processed) = flags \ processed := by
    ext a
    simp only [mem_sdiff,mem_inter]
    tauto
  unfold Subset.partialZeta SparseBoxes.boxSum
  rw [hrequired,← Finset.sum_filter]
  apply Finset.sum_bij (fun x _ => (flags \ processed) ∪ x)
  · intro x hx
    have hsub := Finset.mem_powerset.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_,Finset.subset_union_left⟩
    exact Finset.union_subset Finset.sdiff_subset (hsub.trans Finset.inter_subset_left)
  · intro x hx y hy he
    have hxp := (Finset.mem_powerset.mp hx).trans Finset.inter_subset_right
    have hyp := (Finset.mem_powerset.mp hy).trans Finset.inter_subset_right
    ext a
    constructor
    · intro ha
      have he' : a ∈ (flags \ processed) ∪ y := he ▸ Finset.mem_union_right _ ha
      rcases Finset.mem_union.mp he' with hh | hh
      · exact False.elim ((Finset.mem_sdiff.mp hh).2 (hxp ha))
      · exact hh
    · intro ha
      have he' : a ∈ (flags \ processed) ∪ x := he.symm ▸ Finset.mem_union_right _ ha
      rcases Finset.mem_union.mp he' with hh | hh
      · exact False.elim ((Finset.mem_sdiff.mp hh).2 (hyp ha))
      · exact hh
  · intro leaf hl
    obtain ⟨hleaf,hrequired⟩ := Finset.mem_filter.mp hl
    have hlf := Finset.mem_powerset.mp hleaf
    refine ⟨leaf ∩ processed,Finset.mem_powerset.mpr ?_,?_⟩
    · intro a ha
      exact Finset.mem_inter.mpr ⟨hlf (Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp ha).2⟩
    · ext a
      simp only [mem_union,mem_sdiff,mem_inter]
      constructor
      · rintro (⟨haf,hap⟩ | ⟨hal,hap⟩)
        · exact hrequired (Finset.mem_sdiff.mpr ⟨haf,hap⟩)
        · exact hal
      · intro hal
        by_cases hap : a ∈ processed
        · exact Or.inr ⟨hal,hap⟩
        · exact Or.inl ⟨hlf hal,hap⟩
  · intro x hx
    rfl



















end ThreeSum.BoxStages

end


theorem solution : ∀ {L : Nat} (weight : Finset.{0} (Fin L) → Int) (flags processed : Finset.{0} (Fin L)),
  @Eq.{1} Int (@ThreeSum.Subset.partialZeta.{0} (Fin L) (instDecidableEqFin L) processed weight flags)
    (@ThreeSum.SparseBoxes.boxSum.{0} (Fin L) (@Fin.instLinearOrder L) flags
      (@Inter.inter.{0} (Finset.{0} (Fin L)) (@Finset.instInter.{0} (Fin L) (instDecidableEqFin L)) flags processed)
      weight) := by
  exact @ThreeSum.BoxStages.partialZeta_eq_boxSum_sourceProof

#print axioms solution
