-- Prove2me | solution 1 for Reduce.structural_canonical_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:08:12.017108+00:00
-- url     : https://prove2.me/submissions/d7a5a85a-dfec-456d-a53c-441a6f08794d

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
import Theorems.Thm_Reduce_structural_canonical_key
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_RawBdd_cook_inj
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution {n s : Nat}
    {v : Vector (RawNode n) s} {hh : ∀ k : Fin s, v[k].Bounded k}
    (hsc : ∀ k1 k2 : Fin s, v[k1] = v[k2] → k1 = k2)
    {root : Pointer s}
    (hord : Bdd.Ordered ⟨cook_heap v hh, root⟩)
    (hnored : Bdd.NoRedundancy ⟨cook_heap v hh, root⟩) :
    OBdd.Reduced ⟨⟨cook_heap v hh, root⟩, hord⟩ := by
  let O : OBdd n s := ⟨⟨cook_heap v hh, root⟩, hord⟩
  -- Helper: cook_heap nodes relate back to raw nodes
  have cook_heap_eq : ∀ k : Fin s, (cook_heap v hh)[k] = v[k].cook (RawNode.bounded_of_le (hh k) (by omega)) := by
    intro k
    simp [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn]
  -- Helper: if cooked nodes at kp and kq are equal, then kp = kq
  have node_inj : ∀ (kp kq : Fin s),
      (cook_heap v hh)[kp].var  = (cook_heap v hh)[kq].var →
      (cook_heap v hh)[kp].low  = (cook_heap v hh)[kq].low →
      (cook_heap v hh)[kp].high = (cook_heap v hh)[kq].high →
      kp = kq := by
    intro kp kq hvar hlow hhigh
    apply hsc
    rw [cook_heap_eq kp, cook_heap_eq kq] at hvar hlow hhigh
    simp only [RawNode.cook] at hvar hlow hhigh
    have hlo : v[kp].lo = v[kq].lo := cook_inj hlow
    have hhi : v[kp].hi = v[kq].hi := cook_inj hhigh
    rcases hkp : v[kp] with ⟨vap, lop, hip⟩
    rcases hkq : v[kq] with ⟨vaq, loq, hiq⟩
    simp only [hkp] at hvar hlo hhi
    simp only [hkq] at hvar hlo hhi
    subst hvar; subst hlo; subst hhi
    rfl
  let M := cook_heap v hh
  have key : ∀ (P Q : OBdd n s), P.1.heap = M → Q.1.heap = M →
      OBdd.toTree P = OBdd.toTree Q → P.1.root = Q.1.root :=
    structural_canonical_key node_inj
  -- Now prove Reduced
  constructor
  · exact hnored
  · intro ⟨p, hp_reach⟩ ⟨q, hq_reach⟩ hsim
    -- hsim : SimilarRP O ⟨p, hp_reach⟩ ⟨q, hq_reach⟩
    -- = toTree of sub-BDD at p = toTree of sub-BDD at q
    show p = q
    have hop : Bdd.Ordered ⟨M, p⟩ :=
      Bdd.ordered_of_reachable (O := O) hp_reach
    have hoq : Bdd.Ordered ⟨M, q⟩ :=
      Bdd.ordered_of_reachable (O := O) hq_reach
    exact key ⟨⟨M, p⟩, hop⟩ ⟨⟨M, q⟩, hoq⟩ rfl rfl hsim
end Reduce
