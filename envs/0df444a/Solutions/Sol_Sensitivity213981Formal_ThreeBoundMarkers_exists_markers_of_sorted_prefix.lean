-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMarkers.exists_markers_of_sorted_prefix
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:35:43.619277+00:00
-- url     : https://prove2.me/submissions/1235ffb2-2f9c-4467-901e-25c719ab3f09

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/- The sorted residual prefixes in the case records are sums over actual
distinct marker subsets, not merely optimistic numerical minima. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundMarkers
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [DecidableEq V]

theorem exists_markers_of_sorted_prefix (vs : List V) (hvs : vs.Nodup)
    (res : V → ℕ) (k : ℕ) (hk : k ≤  vs.length) :
    ∃ M : Finset V, M ⊆ vs.toFinset ∧ M.card = k ∧
      (∑ v ∈ M, res v) = (((vs.map res).mergeSort (· ≤  ·)).take k).sum := by
  let sorted := vs.mergeSort (fun a b => decide (res a ≤  res b))
  have hp : sorted.Perm vs := List.mergeSort_perm _ _
  have hnd : sorted.Nodup := hp.nodup_iff.mpr hvs
  have htake : (sorted.take k).Nodup := hnd.take
  have hm : sorted.map res = (vs.map res).mergeSort (· ≤  ·) :=
    List.map_mergeSort (fun _ _ _ _ => rfl)
  refine ⟨(sorted.take k).toFinset, ?_, ?_, ?_⟩
  · intro v hv
    exact List.mem_toFinset.mpr (hp.mem_iff.mp
      (List.mem_of_mem_take (List.mem_toFinset.mp hv)))
  · rw [List.toFinset_card_of_nodup htake,List.length_take,hp.length_eq]
    exact min_eq_left hk
  · rw [List.sum_toFinset res htake,List.map_take,hm]





end
end ThreeBoundMarkers




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [inst : DecidableEq.{1} V] (vs : List.{0} V) (hvs : @List.Nodup.{0} V vs) (res : V → Nat) (k : Nat)
  (hk : @LE.le.{0} Nat instLENat k (@List.length.{0} V vs)),
  @Exists.{1} (Finset.{0} V) fun (M : Finset.{0} V) =>
    And
      (@LE.le.{0} (Finset.{0} V)
        (@Preorder.toLE.{0} (Finset.{0} V)
          (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
        M (@List.toFinset.{0} V inst vs))
      (And (@Eq.{1} Nat (@Finset.card.{0} V M) k)
        (@Eq.{1} Nat (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid M fun (v : V) => res v)
          (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
            (@List.take.{0} Nat k
              (@List.mergeSort.{0} Nat (@List.map.{0, 0} V Nat res vs) fun (x1 x2 : Nat) =>
                @Decidable.decide (@LE.le.{0} Nat instLENat x1 x2) (Nat.decLe x1 x2)))))) := @Sensitivity213981Formal.ThreeBoundMarkers.exists_markers_of_sorted_prefix
