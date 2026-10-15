-- Prove2me | solution 1 for ThreeSum.MaskDifference.subsetMask_union_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:47:57.246968+00:00
-- url     : https://prove2.me/submissions/db945e7d-f65b-476e-80ff-95f5529903f7

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference

open Finset ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [subsetMask,maskOf,natPositions]












theorem subsetMask_union_sdiff_sourceProof {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    subsetMask U+subsetMask (Q \ U) = subsetMask Q := by
  have hd : Disjoint U (Q \ U) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  have he : U ∪ (Q \ U) = Q := by
    ext a
    simp only [mem_union,mem_sdiff]
    constructor
    · rintro (ha | ⟨ha,_⟩)
      · exact hU ha
      · exact ha
    · intro ha
      by_cases hb : a ∈ U
      · exact Or.inl hb
      · exact Or.inr ⟨ha,hb⟩
  calc
    _ = (∑ i ∈ U, 2^i.val)+(∑ i ∈ Q \ U, 2^i.val) := by simp only [subsetMask_sum]
    _ = ∑ i ∈ U ∪ (Q \ U), 2^i.val := (Finset.sum_union hd).symm
    _ = subsetMask Q := by rw [he,subsetMask_sum]













end ThreeSum.MaskDifference

end


theorem solution : ∀ {L : Nat} (Q U : Finset.{0} (Fin L)),
  @LE.le.{0} (Finset.{0} (Fin L))
      (@Preorder.toLE.{0} (Finset.{0} (Fin L))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin L)) (@Finset.instPartialOrder.{0} (Fin L))))
      U Q →
    @Eq.{1} Nat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@ThreeSum.SubsetAddress.subsetMask L U)
        (@ThreeSum.SubsetAddress.subsetMask L
          (@SDiff.sdiff.{0} (Finset.{0} (Fin L)) (@Finset.instSDiff.{0} (Fin L) (instDecidableEqFin L)) Q U)))
      (@ThreeSum.SubsetAddress.subsetMask L Q) := by
  exact @ThreeSum.MaskDifference.subsetMask_union_sdiff_sourceProof

#print axioms solution
