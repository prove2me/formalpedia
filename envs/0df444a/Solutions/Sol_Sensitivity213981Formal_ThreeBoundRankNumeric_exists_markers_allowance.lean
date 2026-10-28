-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.exists_markers_allowance
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:41:34.651858+00:00
-- url     : https://prove2.me/submissions/0a87c810-07e2-4f91-81cd-533702981fab

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_RankSmallAverage
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMarkers_exists_markers_of_sorted_prefix
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_sorted_prefix_bound


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



theorem exists_markers_finset (H : Finset V) (res : V → ℕ)
    (k : ℕ) (hk : k ≤  H.card) :
    ∃ M : Finset V, M ⊆ H ∧ M.card = k ∧
      (∑ v ∈ M, res v) = (((H.toList.map res).mergeSort (· ≤  ·)).take k).sum := by
  have hh := exists_markers_of_sorted_prefix H.toList H.nodup_toList res k
    (by simpa using hk)
  simpa using hh



end
end ThreeBoundMarkers




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact integer averaging for sorted residual weights and actual marker subsets. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankNumeric
open scoped BigOperators









/-- Marker averaging selects actual distinct members of the original set. -/
theorem exists_markers_allowance {V : Type} [DecidableEq V]
    (G : Finset V) (weight : V → ℕ) (m : ℕ) (hm : m ≤  G.card) :
    ∃ M : Finset V, M ⊆ G ∧ M.card=m ∧
      (∑ v ∈ M, weight v) ≤  allowance m (∑ v ∈ G, weight v) G.card := by
  obtain ⟨M,hM,hcard,hsum⟩ := ThreeBoundMarkers.exists_markers_finset G weight m hm
  refine ⟨M,hM,hcard,?_⟩
  rw [hsum]
  let xs := (G.toList.map weight).mergeSort (· ≤  ·)
  have hp : xs.Perm (G.toList.map weight) := List.mergeSort_perm _ _
  have hlen : xs.length=G.card := by simpa only [List.length_map,Finset.length_toList] using hp.length_eq
  have hsum' : xs.sum=∑ v ∈ G, weight v := by
    rw [hp.sum_eq]
    simpa using (List.sum_toFinset weight G.nodup_toList).symm
  have hh := sorted_prefix_bound xs (List.pairwise_mergeSort' (· ≤  ·) _) m (by simpa only [hlen] using hm)
  simpa only [hsum',hlen] using hh





end ThreeBoundRankNumeric





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [DecidableEq.{1} V] (G : Finset.{0} V) (weight : V → Nat) (m : Nat)
  (hm : @LE.le.{0} Nat instLENat m (@Finset.card.{0} V G)),
  @Exists.{1} (Finset.{0} V) fun (M : Finset.{0} V) =>
    And
      (@LE.le.{0} (Finset.{0} V)
        (@Preorder.toLE.{0} (Finset.{0} V)
          (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
        M G)
      (And (@Eq.{1} Nat (@Finset.card.{0} V M) m)
        (@LE.le.{0} Nat instLENat (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid M fun (v : V) => weight v)
          (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance m
            (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid G fun (v : V) => weight v) (@Finset.card.{0} V G)))) := @Sensitivity213981Formal.ThreeBoundRankNumeric.exists_markers_allowance
