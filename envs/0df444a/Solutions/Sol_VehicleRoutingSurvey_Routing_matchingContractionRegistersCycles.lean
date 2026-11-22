-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.matchingContractionRegistersCycles
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:16:51.551153+00:00
-- url     : https://prove2.me/submissions/b32dd8da-db3d-4386-a813-560e2ba39672

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionArm

/-! matching/MatchingWarmPrimal.lean -/
section RppSource_MatchingWarmPrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory













theorem CompactTopMatching.crossing_endpoints {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) {u v : Fin k} (edge : s(u, v) ∈ state.edges)
    (separate : part.blocks.block u ≠ part.blocks.block v) :
    part.representative u = u ∧ part.representative v = v := by
  have atBase {a b : Fin k} (present : s(a, b) ∈ state.edges)
      (separated : part.blocks.block a ≠ part.blocks.block b) : part.representative a = a := by
    by_contra notBase
    obtain ⟨inner, member, incident, allInside⟩ := top.interior a a
      (part.blocks.self_mem a (Finset.mem_univ a)) (Ne.symm notBase)
    have covered := (state.perfect.1 _ present).2 a (Sym2.mem_mk_left _ _)
    have equal := (state.perfect.2 a covered).unique ⟨present, Sym2.mem_mk_left _ _⟩ ⟨member, incident⟩
    have bIn := allInside b (equal ▸ Sym2.mem_mk_right a b)
    exact separated (part.blocks.same_of_mem (Finset.mem_univ a) bIn).symm
  exact ⟨atBase edge separate, atBase (Sym2.eq_swap ▸ edge) separate.symm⟩








end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmPrimal

/-! matching/MatchingMemberTree.lean -/
section RppSource_MatchingMemberTree
namespace VehicleRoutingSurvey.Routing



namespace MatchingMemberTree

















@[simp] theorem rootKeys_length (tree : MatchingMemberTree) : tree.rootKeys.length = tree.arity := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simp [rootKeys, arity, ih, Nat.add_comm]
  | blossom r node children siblings _ ih => simp [rootKeys, arity, ih, Nat.add_comm]





theorem encoded_congr {tree : MatchingMemberTree} {before after : ℕ → ℕ} {startBase countBase : ℕ}
    {untouched : ℕ → Prop} (input : tree.encoded before startBase countBase)
    (frame : tree.readable before startBase countBase untouched)
    (keeps : ∀ a, untouched a → after a = before a) : tree.encoded after startBase countBase := by
  induction tree with
  | nil => trivial
  | leaf v siblings ih => exact ih input frame
  | blossom r node children siblings ihChildren ihSiblings =>
    obtain ⟨count, records, childInput, siblingInput⟩ := input
    obtain ⟨header, total, region, childFrame, siblingFrame⟩ := frame
    refine ⟨(keeps _ total).trans count, ?_, ihChildren childInput childFrame, ihSiblings siblingInput siblingFrame⟩
    intro i hi
    have index : i < children.arity := by simpa using hi
    have zero : untouched (before (startBase + node) + 4 * i) := by simpa using region i index 0 (by decide)
    have one := region i index 1 (by decide)
    have restored := records i hi
    simpa only [keeps _ header, rootKey, matchingCycleChildAt, keeps _ zero, keeps _ one] using restored



end MatchingMemberTree

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberTree

/-! matching/MatchingMemberStack.lean -/
section RppSource_MatchingMemberStack
namespace VehicleRoutingSurvey.Routing



namespace MatchingMemberJob





def proper (job : MatchingMemberJob) : Prop :=
  match job.children with
  | none => job.node = 0
  | some children => 0 < job.node ∧ 2 ≤ children.arity ∧ children.proper













end MatchingMemberJob

namespace MatchingMemberTree



theorem jobs_length (tree : MatchingMemberTree) (owner : Option ℕ) : (tree.jobs owner).length = tree.arity := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simp [jobs, arity, ih, Nat.add_comm]
  | blossom r node children siblings _ ih => simp [jobs, arity, ih, Nat.add_comm]

theorem jobs_rootKeys (tree : MatchingMemberTree) (owner : Option ℕ) :
    (tree.jobs owner).map (fun job => rootKey job.representative job.node) = tree.rootKeys := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simp [jobs, rootKeys, ih]
  | blossom r node children siblings _ ih => simp [jobs, rootKeys, ih]









theorem jobs_frontier_vertices (tree : MatchingMemberTree) (owner : Option ℕ) :
    (MatchingMemberJob.frontier (tree.jobs owner)).map Prod.fst = tree.leaves := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments] using congrArg (v :: ·) ih
  | blossom r node children siblings _ ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments, List.map_map, Function.comp_def] using
      congrArg (children.leaves ++ ·) ih



end MatchingMemberTree

namespace MatchingMemberJob























end MatchingMemberJob

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberStack

/-! matching/MatchingMemberWalkRAM.lean -/
section RppSource_MatchingMemberWalkRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096



def matchingMemberJobValid (s : ArithmeticState) (job : MatchingMemberJob) : Prop :=
  job.proper ∧ job.tree.encoded s.nm (s.nr 77) (s.nr 78) ∧
    job.tree.readable s.nm (s.nr 77) (s.nr 78) (outsideMatchingMemberScratch s) ∧
    job.tree.recordsAbove s.nm (s.nr 77) (s.nr 80 + 3 * s.nr 55)

















end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberWalkRAM

/-! matching/MatchingRebaseTaskMemory.lean -/
section RppSource_MatchingRebaseTaskMemory
namespace VehicleRoutingSurvey.Routing

theorem MatchingMemberTree.readable_after_move {tree : MatchingMemberTree}
    {before after : ℕ → ℕ} {startBase countBase : ℕ} {preserved readable : ℕ → Prop}
    (region : tree.readable before startBase countBase (fun address => preserved address ∧ readable address))
    (same : ∀ address, preserved address → after address = before address) :
    tree.readable after startBase countBase readable := by
  induction tree with
  | nil => trivial
  | leaf v siblings ih => exact ih region
  | blossom r node children siblings ihChildren ihSiblings =>
    obtain ⟨header, count, records, below, later⟩ := region
    refine ⟨header.2, count.2, ?_, ihChildren below, ihSiblings later⟩
    intro i inside word within
    rw [same (startBase + node) header.1]
    exact (records i inside word within).2

theorem MatchingMemberTree.recordsAbove_after_move {tree : MatchingMemberTree}
    {before after : ℕ → ℕ} {startBase countBase lower : ℕ} {preserved : ℕ → Prop}
    (region : tree.readable before startBase countBase preserved)
    (above : tree.recordsAbove before startBase lower)
    (same : ∀ address, preserved address → after address = before address) :
    tree.recordsAbove after startBase lower := by
  induction tree with
  | nil => trivial
  | leaf v siblings ih => exact ih region above
  | blossom r node children siblings ihChildren ihSiblings =>
    obtain ⟨header, _, _, below, later⟩ := region
    obtain ⟨address, childAbove, siblingAbove⟩ := above
    exact ⟨by rwa [same (startBase + node) header], ihChildren below childAbove, ihSiblings later siblingAbove⟩



end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseTaskMemory

/-! matching/MatchingLiveCycleHighFrame.lean -/
section RppSource_MatchingLiveCycleHighFrame
namespace VehicleRoutingSurvey.Routing



theorem MatchingMemberTree.readableAnd {tree : MatchingMemberTree} {mem : ℕ → ℕ} {starts sizes : ℕ}
    {p q : ℕ → Prop} (left : tree.readable mem starts sizes p) (right : tree.readable mem starts sizes q) :
    tree.readable mem starts sizes (fun a => p a ∧ q a) := by
  induction tree with
  | nil => trivial
  | leaf v rest ih => exact ih left right
  | blossom r n c rest ci ri =>
    obtain ⟨a,b,d,e,f⟩ := left
    obtain ⟨x,y,z,w,h⟩ := right
    exact ⟨⟨a,x⟩, ⟨b,y⟩, fun i hi j hj => ⟨d i hi j hj,z i hi j hj⟩, ci e w, ri f h⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleHighFrame

/-! matching/MatchingExpansionRegistryIds.lean -/
section RppSource_MatchingExpansionRegistryIds
namespace VehicleRoutingSurvey.Routing

/-- Singleton children have no top registry record after promotion. -/
def MatchingMemberJob.promotedTree (job : MatchingMemberJob) : MatchingMemberTree :=
  match job.children with
  | none => .nil
  | some children => .blossom job.representative job.node children .nil

theorem MatchingMemberTree.promoted_ids (tree : MatchingMemberTree) (owner : Option ℕ) :
    (tree.jobs owner).flatMap (fun job => job.promotedTree.registryIds) = tree.registryIds := by
  induction tree with
  | nil => rfl
  | leaf v tail ih => simpa [MatchingMemberTree.jobs, MatchingMemberJob.promotedTree, MatchingMemberTree.registryIds] using ih
  | blossom v n sub tail _ ih =>
    simpa [MatchingMemberTree.jobs, MatchingMemberJob.promotedTree, MatchingMemberTree.registryIds] using ih

private theorem finRange_perm_cycle {k : ℕ} (cycle : List (Fin k)) (unique : cycle.Nodup) :
    (List.finRange k).Perm (cycle ++ (List.finRange k).filter (fun v => decide (v ∉ cycle))) := by
  let rest := (List.finRange k).filter (fun v => decide (v ∉ cycle))
  have separated : (cycle ++ rest).Nodup := by
    refine List.nodup_append.mpr ⟨unique,(List.nodup_finRange k).filter _,?_⟩
    intro a ha b hb eq
    have outside := of_decide_eq_true (List.mem_filter.mp hb).2
    exact outside (eq ▸ ha)
  apply (List.perm_ext_iff_of_nodup (List.nodup_finRange k) separated).mpr
  intro v
  by_cases member : v ∈ cycle <;> simp [rest,member]

/-- Splitting one root distributes its child subtrees among their own top
slots. As a multiset of allocated IDs the only removal is the root itself. -/
theorem MatchingTopMemberTrees.expansionIds {k : ℕ} {s t : ArithmeticState}
    (old : MatchingTopMemberTrees k s) (next : MatchingTopMemberTrees k t)
    {node : ℕ} {base : Fin k} (children : List (Fin k)) (cycle : List (Fin k)) (offset : ℕ)
    (tree : MatchingMemberTree) (unique : cycle.Nodup) (rotate : cycle.rotate offset = base :: children)
    (root : old.tree base = .blossom base.val node tree .nil)
    (dormant : ∀ p ∈ children, old.tree p = .nil)
    (keeps : ∀ p ∉ cycle, next.tree p = old.tree p)
    (restored : cycle.flatMap (fun p => (next.tree p).registryIds) = tree.registryIds) :
    old.registryIds.Perm (node :: next.registryIds) := by
  let outside := (List.finRange k).filter (fun v => decide (v ∉ cycle))
  let a := fun p => (old.tree p).registryIds
  let b := fun p => (next.tree p).registryIds
  have outsideEq : outside.flatMap b = outside.flatMap a := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro p hp
    exact congrArg MatchingMemberTree.registryIds (keeps _ (of_decide_eq_true (List.mem_filter.mp hp).2))
  have empty : children.flatMap a = [] := List.flatMap_eq_nil_iff.mpr fun p hp => by
    simp [a,dormant p hp,MatchingMemberTree.registryIds]
  have rotateOrder : cycle.Perm (base :: children) := rotate ▸ (List.rotate_perm cycle offset).symm
  have oldSeg := rotateOrder.flatMap_right a
  have baseRows : a base = node :: tree.registryIds := by simp [a,root,MatchingMemberTree.registryIds]
  rw [List.flatMap_cons,empty,List.append_nil,baseRows] at oldSeg
  have enumeration := finRange_perm_cycle cycle unique
  have prior : old.registryIds.Perm ((node :: tree.registryIds) ++ outside.flatMap a) := by
    have ordered := enumeration.flatMap_right a
    rw [List.flatMap_append] at ordered
    exact ordered.trans (oldSeg.append_right _)
  have later : next.registryIds.Perm (tree.registryIds ++ outside.flatMap a) := by
    have ordered := enumeration.flatMap_right b
    rw [List.flatMap_append] at ordered
    change next.registryIds.Perm (cycle.flatMap b ++ outside.flatMap b) at ordered
    rwa [show cycle.flatMap b = tree.registryIds from restored,outsideEq] at ordered
  exact prior.trans (List.Perm.cons node later.symm)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRegistryIds

/-! matching/MatchingLiveCycleRegion.lean -/
section RppSource_MatchingLiveCycleRegion
namespace VehicleRoutingSurvey.Routing

/-- An archive can be transported across writes at any addresses disjoint
from its headers and records. The same frame covers the recursive member
tree encoding and the two original endpoint words used for expansion. -/
def MatchingLiveCycleMemory.onRegion {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle state node B} {s t : ArithmeticState} (memory : MatchingLiveCycleMemory e s)
    {region : ℕ → Prop}
    (coverage : (MatchingMemberTree.blossom 0 (node B) e.tree .nil).readable s.nm (s.nr 77) (s.nr 78) region)
    (ports : ∀ r ∈ ([55,77,78,79,80] : List ℕ), t.nr r = s.nr r)
    (natural : ∀ a, region a → t.nm a = s.nm a) : MatchingLiveCycleMemory e t := by
  have fixed (r : ℕ) (used : r ∈ ([55,77,78,79,80] : List ℕ) := by decide) := ports r used
  let root := MatchingMemberTree.blossom 0 (node B) e.tree .nil
  have words : root.readable s.nm (s.nr 77) (s.nr 78) region := coverage
  let a := matchingRebaseNodeState s (node B)
  let b := matchingRebaseNodeState t (node B)
  have old : MatchingMemberRoot a e.tree := memory.members
  have reg (r : ℕ) (allowed : r ∈ ([55,77,78,79,80] : List ℕ) := by decide) : b.nr r = a.nr r := by
    have away : r ≠ 22 := by simp at allowed; omega
    simpa [a,b,matchingRebaseNodeState,Function.update_of_ne away] using fixed r allowed
  have common : outsideMatchingMemberScratch b = outsideMatchingMemberScratch a := by
    funext x; simp only [outsideMatchingMemberScratch, reg 79, reg 80, reg 55]
  have before : root.readable s.nm (s.nr 77) (s.nr 78) (outsideMatchingMemberScratch a) := by
    simpa only [root,a,matchingRebaseNodeState,Function.update_self,
      Function.update_of_ne (by decide : 77 ≠ 22),Function.update_of_ne (by decide : 78 ≠ 22)] using old.readable
  have encoding : root.encoded s.nm (s.nr 77) (s.nr 78) := by
    simpa [root,a,matchingRebaseNodeState] using old.encoded
  have lower : root.recordsAbove s.nm (s.nr 77) (s.nr 80+3*s.nr 55) := by
    simpa [root,a,matchingRebaseNodeState] using old.above
  have members : MatchingMemberRoot b e.tree := by
    have id : b.nr 22 = a.nr 22 := by simp [a,b,matchingRebaseNodeState]
    refine ⟨by rw [id]; exact old.proper, ?_, ?_, ?_, old.unique, by rw [reg 55]; exact old.valid,
      by rw [reg 79,reg 55,reg 80]; exact old.separated⟩
    · simpa [root,b,matchingRebaseNodeState,fixed 77,fixed 78] using
        (MatchingMemberTree.encoded_congr encoding words natural)
    · rw [common]
      simpa only [root,b,matchingRebaseNodeState,Function.update_self,
        Function.update_of_ne (by decide : 77 ≠ 22),Function.update_of_ne (by decide : 78 ≠ 22),fixed 77,fixed 78] using
        (MatchingMemberTree.readable_after_move (tree := root) (MatchingMemberTree.readableAnd (tree := root) words before) natural)
    · simpa [root,b,matchingRebaseNodeState,fixed 77,fixed 80,fixed 55] using
        (MatchingMemberTree.recordsAbove_after_move words lower natural)
  have start : matchingCycleRecordStart t (node B) = matchingCycleRecordStart s (node B) := by
    rw [matchingCycleRecordStart,fixed 77]
    exact natural _ words.1
  refine ⟨members, ⟨?_, ?_⟩⟩
  · rw [fixed 78,natural _ words.2.1]
    exact memory.rows.length
  · intro i
    let addr := matchingCycleRecordStart s (node B)+4*i.val
    have within : i.val < e.tree.arity := e.arity.symm ▸ i.isLt
    have byte (w : ℕ) (bound : w < 4) : t.nm (addr+w) = s.nm (addr+w) :=
      natural _ (words.2.2.1 i.val within w bound)
    have first : t.nm addr = s.nm addr := byte 0 (by decide)
    have cell : matchingCycleChildAt t.nm addr = matchingCycleChildAt s.nm addr := by
      simp only [matchingCycleChildAt,first,byte 1 (by decide),byte 2 (by decide),byte 3 (by decide)]
    simpa only [start, show matchingCycleChildAt t.nm (matchingCycleRecordStart s (node B) + 4*i.val) = _ from cell]
      using memory.rows.records i

end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleRegion

/-! matching/MatchingLiveCycleTransport.lean -/
section RppSource_MatchingLiveCycleTransport
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Retain a cycle's owners, current bases, and ordered original witnesses
as the outside cut family or the dual point changes. -/
noncomputable def MatchingLiveCycle.reindex {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state next : CompactMatchingPrimalDual k cost} {node nextNode : Finset (Fin k) → ℕ}
    {B : Finset (Fin k)} (e : MatchingLiveCycle state node B)
    (childLive : ∀ p ∈ e.ports.ports, (e.ports.block p).card ≠ 1 → e.ports.block p ∈ next.cuts.erase B)
    (childIds : ∀ p ∈ e.ports.ports, (e.ports.block p).card ≠ 1 → nextNode (e.ports.block p) = node (e.ports.block p))
    (descend : ∀ C ∈ next.cuts.erase B, C ⊆ B → ∃ p ∈ e.ports.ports, C ⊆ e.ports.block p)
    (unchanged : next.edges = state.edges)
    (tight : ∀ i, oddCutDualEdgeValue next.cuts next.potential next.cutDual
      s((e.geometry.edges i).1,(e.geometry.edges i).2) = edgeCost cost s((e.geometry.edges i).1,(e.geometry.edges i).2)) :
    MatchingLiveCycle next nextNode B := by
  let ports : MatchingExpansionChildPorts next B :=
    ⟨e.ports.ports,e.ports.block,e.ports.owner,e.ports.containsPort,e.ports.subset,e.ports.covered,e.ports.unique,childLive⟩
  let g := e.geometry
  let geometry : MatchingExpansionGeometry ports e.tree e.base := {
    members := ⟨g.members.assignment,g.members.absent⟩
    cycle := g.cycle
    edges := g.edges
    baseSlot := g.baseSlot
    children := g.children
    distinct := g.distinct
    odd := g.odd
    rotate := g.rotate
    atBase := g.atBase
    ports := g.ports
    source := g.source
    target := g.target
    tight := tight
    matched := by
      intro a b on
      obtain ⟨ab,ba⟩ := g.matched a b on
      exact ⟨next.partialMate_some_iff.mpr (unchanged.symm ▸ state.partialMate_some_iff.mp ab),
        next.partialMate_some_iff.mpr (unchanged.symm ▸ state.partialMate_some_iff.mp ba)⟩ }
  refine ⟨e.base,e.tree,ports,geometry,e.arity,e.keys,e.owner,?_,descend,?_,?_⟩
  · intro job listed p rep
    have inPorts := (e.owner job listed p rep).1
    by_cases single : (e.ports.block p).card = 1
    · simpa only [ports,if_pos single] using e.childNode job listed p rep
    · simpa only [ports,if_neg single,childIds p inPorts single] using e.childNode job listed p rep
  · simpa only [matchingCycleInterior,unchanged] using e.internal
  · intro i p q matched
    exact e.matchedRow i (state.partialMate_some_iff.mpr (unchanged ▸ next.partialMate_some_iff.mp matched))





end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleTransport

/-! matching/MatchingContractionCycleOrder.lean -/
section RppSource_MatchingContractionCycleOrder
namespace VehicleRoutingSurvey.Routing

def contractionLegPoint {α : Type*} (leg : List α) (base : α) (i : ℕ) (inside : i ≤ leg.length) : α :=
  (leg ++ [base])[i]'(by simp <;> omega)

theorem contractionLegPoint_last {α : Type*} (leg : List α) (base : α) :
    contractionLegPoint leg base leg.length le_rfl = base := by
  simp [contractionLegPoint,List.getElem_append_right (le_refl leg.length)]

theorem contractionLegPoint_before {α : Type*} (leg : List α) (base : α) {i : ℕ} (before : i < leg.length) :
    contractionLegPoint leg base i before.le = leg[i] := by
  simp only [contractionLegPoint,List.getElem_append_left before]





@[simp] theorem contractionCycleOrder_length {α : Type*} (left right : List α) (base : α) :
    (contractionCycleOrder left right base).length = left.length + right.length + 1 := by
  simp [contractionCycleOrder,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem contractionCycleOrder_left {α : Type*} (left right : List α) (base : α)
    {i : ℕ} (within : i ≤ left.length) :
    (contractionCycleOrder left right base)[i]'(by simp <;> omega) = contractionLegPoint left base i within := by
  rcases lt_or_eq_of_le within with h | rfl
  · rw [contractionLegPoint_before _ _ h]
    exact List.getElem_append_left h
  · rw [contractionLegPoint_last]
    simp [contractionCycleOrder,List.getElem_append_right (le_refl left.length)]



/-- Exact location and rotation of the newly allocated base. -/
theorem contractionCycleOrder_base {α : Type*} (left right : List α) (base : α) :
    (contractionCycleOrder left right base).rotate left.length = base :: (right.reverse ++ left) ∧
      (contractionCycleOrder left right base)[left.length]'(by simp <;> omega) = base := by
  constructor
  · simpa only [contractionCycleOrder,List.cons_append] using List.rotate_append_length_eq left (base :: right.reverse)
  · exact (contractionCycleOrder_left left right base le_rfl).trans (contractionLegPoint_last _ _)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCycleOrder

/-! matching/MatchingContractionPartition.lean -/
section RppSource_MatchingContractionPartition
namespace VehicleRoutingSurvey.Routing











theorem CompactMatchingPartition.contract_representative {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (cycle : Finset (Fin k)) (base : Fin k) (baseIn : base ∈ cycle)
    (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card)
    (covered : ∀ c ∈ cycle, c ≠ base → c ∈ state.covered) (v : Fin k) :
    (part.contract cycle base baseIn fixed odd covered).representative v =
      blossomRepresentative cycle base (part.representative v) := rfl

theorem CompactMatchingPartition.contract_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (cycle : Finset (Fin k)) (base : Fin k) (baseIn : base ∈ cycle)
    (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card)
    (covered : ∀ c ∈ cycle, c ≠ base → c ∈ state.covered) (v : Fin k) :
    (part.contract cycle base baseIn fixed odd covered).blocks.block v =
      if part.representative v ∈ cycle then part.contractCut cycle else part.blocks.block v := by
  change (if part.blocks.block v ∈ cycle.image part.blocks.block then part.contractCut cycle else part.blocks.block v) = _
  simp only [part.mem_contractionChildren cycle fixed]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPartition

/-! matching/MatchingContractionChildPorts.lean -/
section RppSource_MatchingContractionChildPorts
namespace VehicleRoutingSurvey.Routing

/-- The physical child labels at allocation are the old top-level ports. Each
original is owned by its old representative, including originals of previously
contracted children. -/
noncomputable def CompactMatchingPartition.contractionChildPorts {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (cycle : Finset (Fin k))
    (fixed : ∀ p ∈ cycle, part.representative p = p) (odd : Odd cycle.card) (many : 1 < cycle.card) :
    MatchingExpansionChildPorts (state.registerCut (part.contractCut cycle) (part.contractCut_odd cycle fixed odd))
      (part.contractCut cycle) where
  ports := cycle
  block := part.blocks.block
  owner := part.representative
  containsPort p _ := part.blocks.self_mem p (Finset.mem_univ _)
  subset p hp v hv := Finset.mem_biUnion.mpr ⟨part.blocks.block p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,hv⟩
  covered v hv := ⟨(part.mem_contractCut cycle fixed v).mp hv,
    (part.same_block.mp (part.representative_idem v)).symm ▸ part.blocks.self_mem v (Finset.mem_univ v)⟩
  unique p hp v hv := (part.same_block.mpr (part.blocks.same_of_mem (Finset.mem_univ p) hv)).trans (fixed p hp)
  live p hp large := by
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_insert_of_mem (part.blocks.cut_mem (Finset.mem_univ _) large)⟩
    intro eq
    have only (q : Fin k) (hq : q ∈ cycle) : q = p := by
      have inside := (part.mem_contractCut cycle fixed q).mpr ((fixed q hq).symm ▸ hq)
      have same := part.same_block.mpr (part.blocks.same_of_mem (Finset.mem_univ p) (eq.symm ▸ inside))
      exact (fixed q hq).symm.trans (same.trans (fixed p hp))
    obtain ⟨a,ha,b,hb,apart⟩ := Finset.one_lt_card.mp many
    exact apart ((only a ha).trans (only b hb).symm)

/-- Every earlier cut below the new node lies in one of its direct children. -/
theorem CompactMatchingPartition.contractionChildPorts_descendants {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (cycle : Finset (Fin k))
    (fixed : ∀ p ∈ cycle, part.representative p = p) (odd : Odd cycle.card) (many : 1 < cycle.card)
    (nested : ∀ C ∈ state.cuts, ∀ u ∈ C, ∀ v ∈ C, part.blocks.block u = part.blocks.block v) :
    let next := state.registerCut (part.contractCut cycle) (part.contractCut_odd cycle fixed odd)
    let ports := part.contractionChildPorts cycle fixed odd many
    ∀ C ∈ next.cuts.erase (part.contractCut cycle), C ⊆ part.contractCut cycle →
      ∃ p ∈ ports.ports, C ⊆ ports.block p := by
  intro next ports C present below
  obtain ⟨different,member⟩ := Finset.mem_erase.mp present
  have old := (Finset.mem_insert.mp member).resolve_left different
  have cardOdd := Nat.odd_iff.mp (state.cutValid C old).1
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < C.card by omega)
  have inside := (part.mem_contractCut cycle fixed u).mp (below hu)
  refine ⟨part.representative u,inside,?_⟩
  intro v hv
  change v ∈ part.blocks.block (part.representative u)
  rw [part.same_block.mp (part.representative_idem u), ← nested C old v hv u hu]
  exact part.blocks.self_mem v (Finset.mem_univ _)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionChildPorts

/-! matching/MatchingContractionPrimal.lean -/
section RppSource_MatchingContractionPrimal
namespace VehicleRoutingSurvey.Routing



/-- The old top bases and matched cycle edges furnish the new block's internal
near-perfect matching. Its distinguished base keeps an exterior mate when matched. -/
theorem CompactTopMatching.contract {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) {cycle : Finset (Fin k)} {base : Fin k} (baseIn : base ∈ cycle)
    (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card)
    (pairs : ∀ x ∈ cycle, x ≠ base → ∃ y ∈ cycle, y ≠ base ∧ state.partialMate x = some y) :
    CompactTopMatching (part.contract cycle base baseIn fixed odd (contractionMates_covered pairs)) := by
  let next := part.contract cycle base baseIn fixed odd (contractionMates_covered pairs)
  have rep (v : Fin k) : next.representative v = if part.representative v ∈ cycle then base else part.representative v := rfl
  have block := part.contract_block cycle base baseIn fixed odd (contractionMates_covered pairs)
  have maps (v : Fin k) : part.blocks.block v ⊆ next.blocks.block v := by
    rw [block]
    by_cases merged : part.representative v ∈ cycle
    · rw [if_pos merged]
      intro w hw
      exact (part.mem_contractCut cycle fixed w).mpr
        ((part.same_block.mpr (part.blocks.same_of_mem (Finset.mem_univ v) hw)).symm ▸ merged)
    · rw [if_neg merged]
  change CompactTopMatching next
  constructor
  · intro u v atU away
    have equal := next.blocks.same_of_mem (Finset.mem_univ u) atU
    by_cases atPort : part.representative v = v
    · have newBase : next.representative v ≠ v := fun h => away ((next.constant v u equal).symm.trans h).symm
      have inside : v ∈ cycle := by
        by_contra outside
        exact newBase (by rw [rep,atPort,if_neg outside])
      have apart : v ≠ base := by
        intro same
        exact newBase (by rw [rep,atPort,if_pos inside,same])
      obtain ⟨w,hw,_,matched⟩ := pairs v inside apart
      have member := state.partialMate_some_iff.mp matched
      have wAt : w ∈ next.blocks.block v := by
        rw [block,atPort,if_pos inside]
        exact (part.mem_contractCut cycle fixed w).mpr ((fixed w hw).symm ▸ hw)
      refine ⟨s(v,w),member,Sym2.mem_mk_left _ _,?_⟩
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact atU
      · exact equal ▸ wAt
    · obtain ⟨e,he,hv,others⟩ := top.interior v v (part.blocks.self_mem v (Finset.mem_univ v)) (Ne.symm atPort)
      exact ⟨e,he,hv,fun z hz => equal ▸ maps v (others z hz)⟩
  · intro u v newFixed paired
    change state.partialMate u = some v at paired
    have oldFixed : part.representative u = u := by
      by_cases merged : part.representative u ∈ cycle
      · have baseEq : base = u := by simpa only [rep,if_pos merged] using newFixed
        exact baseEq ▸ fixed base baseIn
      · simpa only [rep,if_neg merged] using newFixed
    have separate := top.matchedBase oldFixed paired
    have edge := state.partialMate_some_iff.mp paired
    have vFixed := (top.crossing_endpoints edge separate).2
    intro equal
    have same := next.same_block.mpr equal
    rw [rep,rep,oldFixed,vFixed] at same
    by_cases a : u ∈ cycle <;> by_cases b : v ∈ cycle
    · have baseEq : base = u := by simpa only [rep,oldFixed,if_pos a] using newFixed
      have diff : v ≠ base := fun h => separate (congrArg part.blocks.block (baseEq.symm.trans h.symm))
      obtain ⟨w,_,other,reverse⟩ := pairs v b diff
      have backwards := state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ edge : s(v,u) ∈ state.edges)
      exact other ((Option.some.inj (reverse.symm.trans backwards)).trans baseEq.symm)
    · simp only [if_pos a,if_neg b] at same
      exact b (same ▸ baseIn)
    · simp only [if_neg a,if_pos b] at same
      exact a (same.symm ▸ baseIn)
    · simp only [if_neg a,if_neg b] at same
      exact separate (congrArg part.blocks.block same)



end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPrimal

/-! matching/BlossomLaminarity.lean -/
section RppSource_BlossomLaminarity
namespace VehicleRoutingSurvey.Routing

variable {k : ℕ} {vertices : Finset (Fin k)} {cuts : Finset (Finset (Fin k))}

private theorem cut_disjoint_or_subset_merged {blocks : TopLevelMatchingBlocks vertices cuts}
    {children : Finset (Finset (Fin k))} (top : children ⊆ vertices.image blocks.block)
    (contained : ∀ S ∈ cuts, S ⊆ vertices)
    (nested : ∀ S ∈ cuts, ∀ u ∈ S, ∀ v ∈ S, blocks.block u = blocks.block v)
    {S : Finset (Fin k)} (inCuts : S ∈ cuts) :
    Disjoint S (children.biUnion id) ∨ S ⊆ children.biUnion id := by
  by_cases overlap : ∃ u ∈ S, u ∈ children.biUnion id
  · obtain ⟨v, inS, inUnion⟩ := overlap
    obtain ⟨child, selected, vInChild⟩ := Finset.mem_biUnion.mp inUnion
    obtain ⟨representative, inside, isChild⟩ := Finset.mem_image.mp (top selected)
    have blockV := (blocks.same_of_mem inside (isChild.symm ▸ vInChild)).trans isChild
    right
    intro w wIn
    have blockW := (nested S inCuts w wIn v inS).trans blockV
    exact Finset.mem_biUnion.mpr ⟨child, selected, blockW ▸ blocks.self_mem w (contained S inCuts wIn)⟩
  · left
    apply Finset.disjoint_left.mpr
    intro v inS inUnion
    exact overlap ⟨v, inS, inUnion⟩

/-- A contraction registers a union of current top-level blocks. Every
existing cut belongs to one old block, so no existing cut crosses that union. -/
theorem contractedBlossom_preserves_laminar (blocks : TopLevelMatchingBlocks vertices cuts)
    {children : Finset (Finset (Fin k))} (top : children ⊆ vertices.image blocks.block)
    (contained : ∀ S ∈ cuts, S ⊆ vertices)
    (nested : ∀ S ∈ cuts, ∀ u ∈ S, ∀ v ∈ S, blocks.block u = blocks.block v)
    (laminar : ∀ S ∈ cuts, ∀ T ∈ cuts, Disjoint S T ∨ S ⊆ T ∨ T ⊆ S) :
    ∀ S ∈ insert (children.biUnion id) cuts, ∀ T ∈ insert (children.biUnion id) cuts,
      Disjoint S T ∨ S ⊆ T ∨ T ⊆ S := by
  intro S inS T inT
  rcases Finset.mem_insert.mp inS with rfl | oldS
  · rcases Finset.mem_insert.mp inT with rfl | oldT
    · exact Or.inr (Or.inl (fun _ h => h))
    · rcases cut_disjoint_or_subset_merged top contained nested oldT with apart | inside
      · exact Or.inl apart.symm
      · exact Or.inr (Or.inr inside)
  · rcases Finset.mem_insert.mp inT with rfl | oldT
    · rcases cut_disjoint_or_subset_merged top contained nested oldS with apart | inside
      · exact Or.inl apart
      · exact Or.inr (Or.inl inside)
    · exact laminar S oldS T oldT



theorem TopLevelMatchingBlocks.contract_cuts_nested (blocks : TopLevelMatchingBlocks vertices cuts)
    {children : Finset (Finset (Fin k))} (top : children ⊆ vertices.image blocks.block)
    (nested : ∀ S ∈ cuts, ∀ u ∈ S, ∀ v ∈ S, blocks.block u = blocks.block v) :
    ∀ S ∈ insert (children.biUnion id) cuts, ∀ u ∈ S, ∀ v ∈ S,
      (blocks.contract children top).block u = (blocks.contract children top).block v := by
  have selected (w : Fin k) (inside : w ∈ children.biUnion id) : blocks.block w ∈ children := by
    obtain ⟨child, childMem, inChild⟩ := Finset.mem_biUnion.mp inside
    obtain ⟨x, xIn, childEq⟩ := Finset.mem_image.mp (top childMem)
    have same : blocks.block w = child := (blocks.same_of_mem xIn (childEq.symm ▸ inChild)).trans childEq
    rwa [same]
  intro S inS u inU v inV
  rcases Finset.mem_insert.mp inS with rfl | old
  · simp [TopLevelMatchingBlocks.contract, selected u inU, selected v inV]
  · simp only [TopLevelMatchingBlocks.contract, nested S old u inU v inV]





end VehicleRoutingSurvey.Routing
end RppSource_BlossomLaminarity

/-! matching/MatchingContractionRegisteredDual.lean -/
section RppSource_MatchingContractionRegisteredDual
namespace VehicleRoutingSurvey.Routing

/-- A union of at least two distinct current top blocks is a fresh cut. -/
theorem CompactMatchingPartition.contractCut_fresh {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (cycle : Finset (Fin k))
    (fixed : ∀ v ∈ cycle, part.representative v = v) (many : 1 < cycle.card)
    (nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v) :
    part.contractCut cycle ∉ state.cuts := by
  intro old
  obtain ⟨a,ha,b,hb,absurd⟩ := Finset.one_lt_card.mp many
  have contained (p : Fin k) (hp : p ∈ cycle) := (part.mem_contractCut cycle fixed p).mpr ((fixed p hp).symm ▸ hp)
  exact absurd ((fixed a ha).symm.trans ((part.same_block.mpr (nested _ old a (contained a ha) b (contained b hb))).trans (fixed b hb)))





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionRegisteredDual

/-! matching/MatchingContractionOlderCycles.lean -/
section RppSource_MatchingContractionOlderCycles
namespace VehicleRoutingSurvey.Routing

/-- All old cuts lie inside a single old top block. The newly merged cut
therefore cannot become a descendant of an earlier archive entry. -/
theorem CompactMatchingPartition.contractCut_not_below {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (cycle : Finset (Fin k))
    (fixed : ∀ v ∈ cycle, part.representative v = v) (many : 1 < cycle.card)
    (nested : ∀ C ∈ state.cuts, ∀ u ∈ C, ∀ v ∈ C, part.blocks.block u = part.blocks.block v)
    {C : Finset (Fin k)} (older : C ∈ state.cuts) : ¬part.contractCut cycle ⊆ C := by
  intro below
  obtain ⟨a,ha,b,hb,different⟩ := Finset.one_lt_card.mp many
  have contained (p : Fin k) (hp : p ∈ cycle) := below ((part.mem_contractCut cycle fixed p).mpr ((fixed p hp).symm ▸ hp))
  exact different ((fixed a ha).symm.trans ((part.same_block.mpr (nested _ older a (contained a ha) b (contained b hb))).trans (fixed b hb)))

/-- Reindex a surviving archive entry at the registered dual point. Its
internal cycle, ownership and child IDs remain valid whether it is a direct
child of the union, a deeper descendant, or an exterior blossom. -/
noncomputable def MatchingLiveCycle.afterContraction {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (cycle : Finset (Fin k))
    (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card) (many : 1 < cycle.card)
    (nested : ∀ C ∈ state.cuts, ∀ u ∈ C, ∀ v ∈ C, part.blocks.block u = part.blocks.block v)
    {node newId : Finset (Fin k) → ℕ} (unchanged : ∀ C ∈ state.cuts, newId C = node C)
    {C : Finset (Fin k)} (present : C ∈ state.cuts) (e : MatchingLiveCycle state node C) :
    MatchingLiveCycle (state.registerCut (part.contractCut cycle) (part.contractCut_odd cycle fixed odd)) newId C := by
  let B := part.contractCut cycle
  apply e.reindex
  · intro p hp large
    obtain ⟨away,old⟩ := Finset.mem_erase.mp (e.ports.live p hp large)
    exact Finset.mem_erase.mpr ⟨away,Finset.mem_insert_of_mem old⟩
  · intro p hp large
    exact unchanged _ (Finset.mem_of_mem_erase (e.ports.live p hp large))
  · intro D h inside
    obtain ⟨away,member⟩ := Finset.mem_erase.mp h
    rcases Finset.mem_insert.mp member with rfl | old
    · exact (part.contractCut_not_below cycle fixed many nested present inside).elim
    · exact e.descendants _ (Finset.mem_erase.mpr ⟨away,old⟩) inside
  · rfl
  · intro i
    change oddCutDualEdgeValue (insert B state.cuts) state.potential (extendBlossomCutDual state.cuts state.cutDual) _ = _
    rw [oddCutDualEdgeValue_register_cut]
    exact e.geometry.tight i

theorem MatchingLiveCycleMemory.afterContraction {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (cycle : Finset (Fin k))
    (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card) (many : 1 < cycle.card)
    (nested : ∀ C ∈ state.cuts, ∀ u ∈ C, ∀ v ∈ C, part.blocks.block u = part.blocks.block v)
    {node newId : Finset (Fin k) → ℕ} (unchanged : ∀ C ∈ state.cuts, newId C = node C)
    {C : Finset (Fin k)} (present : C ∈ state.cuts) {e : MatchingLiveCycle state node C}
    {t : ArithmeticState} (memory : MatchingLiveCycleMemory e t) :
    MatchingLiveCycleMemory (e.afterContraction part cycle fixed odd many nested unchanged present) t := by
  change MatchingLiveCycleMemory (MatchingLiveCycle.afterContraction part cycle fixed odd many nested unchanged present e) t
  constructor
  · change MatchingMemberRoot (matchingRebaseNodeState t (newId C)) e.tree
    rw [unchanged _ present]
    exact memory.members
  · change MatchingNodeCycleRows t (newId C) e.geometry.cycle e.geometry.edges
    rw [unchanged _ present]
    exact memory.rows

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionOlderCycles

/-! matching/MatchingContractionMemberTree.lean -/
section RppSource_MatchingContractionMemberTree
namespace VehicleRoutingSurvey.Routing

theorem MatchingLiveCycle.leaf_iff {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle state node B) (u : Fin k) : u.val ∈ e.tree.leaves ↔ u ∈ B := by
  constructor
  · intro present
    by_contra outside
    exact e.geometry.members.absent u outside present
  · intro inside
    rw [← e.tree.jobs_frontier_vertices none]
    exact List.mem_map.mpr ⟨_,e.geometry.members.assignment u inside,rfl⟩

/-- For a singleton the child record stores zero. For a blossom the record
points to the whole earlier live subtree at the old port. -/
noncomputable def MatchingLiveCycles.contractionJob {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {dual : MatchingSearchDualMemory part forest s}
    {reg : MatchingRegistryView dual} (live : MatchingLiveCycles reg) (p : Fin k) : MatchingMemberJob :=
  if h : (part.blocks.block p).card = 1 then ⟨p.val,0,p.val,none⟩ else
    ⟨p.val,dual.node (part.blocks.block p),p.val,some (live.entry _ (part.blocks.cut_mem (Finset.mem_univ p) h)).tree⟩

theorem MatchingLiveCycles.contractionJob_spec {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {dual : MatchingSearchDualMemory part forest s}
    {reg : MatchingRegistryView dual} (live : MatchingLiveCycles reg) (p : Fin k) :
    let job := live.contractionJob p
    job.representative = p.val ∧ job.owner = p.val ∧
      job.node = (if (part.blocks.block p).card = 1 then 0 else dual.node (part.blocks.block p)) ∧
      job.proper ∧ ∀ u : Fin k, u.val ∈ job.tree.leaves ↔ u ∈ part.blocks.block p := by
  intro job
  by_cases one : (part.blocks.block p).card = 1
  · have self := part.blocks.self_mem p (Finset.mem_univ p)
    obtain ⟨x,h⟩ := Finset.card_eq_one.mp one
    have eq : p = x := by simpa only [h,Finset.mem_singleton] using self
    simp [job,contractionJob,one,MatchingMemberJob.proper,MatchingMemberJob.tree,MatchingMemberTree.leaves,h,←eq,Fin.ext_iff]
  · let present := part.blocks.cut_mem (Finset.mem_univ p) one
    let e := live.entry _ present
    have good := (live.memory _ present).members.proper
    change (MatchingMemberTree.blossom 0 (dual.node (part.blocks.block p)) e.tree .nil).proper at good
    refine ⟨by simp [job,contractionJob,one],by simp [job,contractionJob,one],by simp [job,contractionJob,one],?_,?_⟩
    · simpa [job,contractionJob,one,MatchingMemberTree.proper,MatchingMemberJob.proper,e] using good
    · intro u
      simpa [job,contractionJob,one,MatchingMemberJob.tree,MatchingMemberTree.leaves,e] using e.leaf_iff u

/-- Build the child forest in precisely the order written in the append area. -/
def contractionChildTree (jobs : List MatchingMemberJob) : MatchingMemberTree :=
  match jobs with
  | [] => .nil
  | j :: rest => match j.children with
    | none => .leaf j.representative (contractionChildTree rest)
    | some child => .blossom j.representative j.node child (contractionChildTree rest)

theorem contractionChildTree_jobs (jobs : List MatchingMemberJob)
    (good : ∀ j ∈ jobs, j.proper ∧ j.owner = j.representative) : (contractionChildTree jobs).jobs none = jobs := by
  induction jobs with
  | nil => rfl
  | cons j rest ih =>
    have tail := ih (fun x h => good x (List.mem_cons_of_mem _ h))
    obtain ⟨ok,owner⟩ := good j (by simp)
    cases j with
    | mk p n o child =>
      change o = p at owner
      subst o
      cases child with
      | none =>
        change n = 0 at ok
        subst n
        simp [contractionChildTree,MatchingMemberTree.jobs,tail]
      | some child => simp [contractionChildTree,MatchingMemberTree.jobs,tail]

theorem contractionChildTree_proper (jobs : List MatchingMemberJob) (good : ∀ j ∈ jobs, j.proper) :
    (contractionChildTree jobs).proper := by
  induction jobs with
  | nil => trivial
  | cons j rest ih =>
    have tail := ih (fun x h => good x (List.mem_cons_of_mem _ h))
    have head := good j (by simp)
    cases h : j.children with
    | none => simpa [contractionChildTree,h,MatchingMemberTree.proper] using tail
    | some child =>
      obtain ⟨node, branching, descendants⟩ := (show 0 < j.node ∧ 2 ≤ child.arity ∧ child.proper by
        simpa [MatchingMemberJob.proper,h] using head)
      simp [contractionChildTree,h,MatchingMemberTree.proper,node,branching,descendants,tail]

private theorem contractionJobAssignment (job : MatchingMemberJob) (u : ℕ) :
    (u,job.owner) ∈ job.assignments ↔ u ∈ job.tree.leaves := by
  cases h : job.children <;> simp [MatchingMemberJob.assignments,MatchingMemberJob.tree,MatchingMemberTree.leaves,h]

theorem MatchingLiveCycles.contractionTree {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {dual : MatchingSearchDualMemory part forest s}
    {reg : MatchingRegistryView dual} (live : MatchingLiveCycles reg) (cycle : List (Fin k))
    (fixed : ∀ p ∈ cycle.toFinset, part.representative p = p) (odd : Odd cycle.toFinset.card) (many : 1 < cycle.toFinset.card) :
    let ports := part.contractionChildPorts cycle.toFinset fixed odd many
    let tree := contractionChildTree (cycle.map live.contractionJob)
    MatchingChildMemberTree ports tree ∧ tree.proper ∧ tree.arity = cycle.length ∧
      tree.rootKeys.map Prod.fst = cycle.map Fin.val ∧ tree.jobs none = cycle.map live.contractionJob := by
  classical
  intro ports tree
  have good (j : MatchingMemberJob) (hj : j ∈ cycle.map live.contractionJob) : j.proper ∧ j.owner = j.representative := by
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hj
    have info := live.contractionJob_spec p
    exact ⟨info.2.2.2.1,info.2.1.trans info.1.symm⟩
  have jobs : tree.jobs none = cycle.map live.contractionJob := contractionChildTree_jobs _ good
  have assignments : matchingMemberAssignments tree = (cycle.map live.contractionJob).flatMap MatchingMemberJob.assignments := by
    simp only [matchingMemberAssignments,MatchingMemberJob.frontier,jobs]
  refine ⟨⟨?_,?_⟩,contractionChildTree_proper _ (fun j h => (good j h).1),?_,?_,jobs⟩
  · intro u inB
    let p := part.representative u
    have located := ports.covered u inB
    have ep := live.contractionJob_spec p
    rw [assignments]
    apply List.mem_flatMap.mpr
    refine ⟨live.contractionJob p,List.mem_map.mpr ⟨p,List.mem_toFinset.mp located.1,rfl⟩,?_⟩
    change (u.val,p.val) ∈ _
    rw [←ep.2.1,contractionJobAssignment]
    exact (ep.2.2.2.2 u).mpr located.2
  · intro u outB appears
    rw [←tree.jobs_frontier_vertices none] at appears
    obtain ⟨⟨v,owner⟩,h,eq⟩ := List.mem_map.mp appears
    change v = u.val at eq
    subst v
    change (u.val,owner) ∈ matchingMemberAssignments tree at h
    rw [assignments] at h
    obtain ⟨j,hj,found⟩ := List.mem_flatMap.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
    have ep := live.contractionJob_spec p
    have inLeaf : u.val ∈ (live.contractionJob p).tree.leaves := by
      cases hc : (live.contractionJob p).children <;>
        simp [MatchingMemberJob.assignments,MatchingMemberJob.tree,MatchingMemberTree.leaves,hc] at found ⊢ <;> aesop
    exact outB (ports.subset p (List.mem_toFinset.mpr hp) ((ep.2.2.2.2 u).mp inLeaf))
  · rw [← tree.jobs_length none,jobs,List.length_map]
  · rw [←tree.jobs_rootKeys none,jobs,List.map_map,List.map_map]
    exact List.map_congr_left (fun p _ => (live.contractionJob_spec p).1)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionMemberTree

/-! matching/MatchingContractionRegistryView.lean -/
section RppSource_MatchingContractionRegistryView
namespace VehicleRoutingSurvey.Routing

theorem MatchingLiveCycles.contractionJob_promoted {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {dual : MatchingSearchDualMemory part forest s}
    {registry : MatchingRegistryView dual} (live : MatchingLiveCycles registry) (p : Fin k)
    (fixed : part.representative p = p) : (live.contractionJob p).promotedTree = registry.trees.tree p := by
  by_cases one : (part.blocks.block p).card = 1
  · have root := registry.trees.roots p
    have zero : blossomNodeAt s p.val = 0 := by simp [dual.top p,one]
    change (registry.trees.tree p).rootKeys = if blossomNodeAt s p.val = 0 then [] else _ at root
    rw [if_pos zero] at root
    have absent : registry.trees.tree p = .nil := by
      cases h : registry.trees.tree p <;> simp [h,MatchingMemberTree.rootKeys] at root ⊢
    simp [contractionJob,one,MatchingMemberJob.promotedTree,absent]
  · let h := part.blocks.cut_mem (Finset.mem_univ p) one
    have stored := (live.top p h fixed).2
    simpa only [contractionJob,dif_neg one,MatchingMemberJob.promotedTree] using stored.symm

def MatchingRegistryView.afterContraction {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState} {old : MatchingSearchDualMemory part forest s}
    (registry : MatchingRegistryView old) (cycle : Finset (Fin k)) (base : Fin k) (baseIn : base ∈ cycle)
    (fixed : ∀ p ∈ cycle, part.representative p = p) (odd : Odd cycle.card) (many : 1 < cycle.card)
    (covered : ∀ v ∈ cycle, v ≠ base → v ∈ state.covered)
    (after : MatchingSearchDualMemory (part.contract cycle base baseIn fixed odd covered) (forest.contract cycle base) t)
    (trees : MatchingTopMemberTrees k t)
    (bytes : ∀ v, (trees.tree v).readable t.nm (t.nr 77) (t.nr 78) (fun a => t.nr 65+2*(k*k) ≤ a))
    (allIds : trees.registryIds.Perm (s.nr 76 :: registry.trees.registryIds))
    (ids : ∀ C ∈ state.cuts, after.node C = old.node C)
    (id : after.node (part.contractCut cycle) = s.nr 76) (allocated : t.nr 76 = s.nr 76+1) : MatchingRegistryView after := by
  let B := part.contractCut cycle
  have fresh : s.nr 76 ∉ registry.trees.registryIds := by
    intro member
    obtain ⟨C,h,eq⟩ := (registry.keys _).mp member
    exact (registry.allocated C h).ne eq
  refine ⟨trees,bytes,allIds.symm.nodup (List.nodup_cons.mpr ⟨fresh,registry.unique⟩),?_,?_,?_,?_,?_⟩
  · intro n
    rw [allIds.mem_iff,List.mem_cons,registry.keys]
    constructor
    · rintro (rfl | ⟨C,h,eq⟩)
      · exact ⟨B,Finset.mem_insert_self _ _,id⟩
      · exact ⟨C,Finset.mem_insert_of_mem h,(ids C h).trans eq⟩
    · rintro ⟨C,h,eq⟩
      rcases Finset.mem_insert.mp h with rfl | oldCut
      · exact Or.inl (eq.symm.trans id)
      · exact Or.inr ⟨C,oldCut,(ids C oldCut).symm.trans eq⟩
  · intro C h
    rcases Finset.mem_insert.mp h with rfl | oldCut
    · rw [id,allocated]; omega
    · rw [ids C oldCut,allocated]; exact Nat.lt_succ_of_lt (registry.allocated C oldCut)
  · intro C h
    rcases Finset.mem_insert.mp h with rfl | oldCut
    · obtain ⟨a,ha,b,hb,diff⟩ := Finset.one_lt_card.mp many
      have contains (v : Fin k) (hv : v ∈ cycle) := (part.mem_contractCut cycle fixed v).mpr ((fixed v hv).symm ▸ hv)
      exact Finset.one_lt_card.mpr ⟨a,contains a ha,b,contains b hb,diff⟩
    · exact registry.nontrivial C oldCut
  · exact contractedBlossom_preserves_laminar part.blocks (Finset.image_mono _ (Finset.subset_univ cycle))
      (fun _ _ => Finset.subset_univ _) registry.nested registry.laminar
  · exact part.blocks.contract_cuts_nested (Finset.image_mono _ (Finset.subset_univ cycle)) registry.nested

/-- The direct children consumed by the physical writer carry exactly the IDs
which they contributed as separate top roots before the contraction. -/
theorem MatchingLiveCycles.contractionIds {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)}
    {s t : ArithmeticState} {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (live : MatchingLiveCycles registry) (trees : MatchingTopMemberTrees k t) (cycle : List (Fin k)) (base : Fin k)
    (children : List (Fin k)) (slot : ℕ) (unique : cycle.Nodup) (rotate : cycle.rotate slot = base :: children)
    (fixed : ∀ p ∈ cycle, part.representative p = p)
    (root : trees.tree base = .blossom base.val (s.nr 76) (contractionChildTree (cycle.map live.contractionJob)) .nil)
    (hidden : ∀ p ∈ children, trees.tree p = .nil) (retained : ∀ p ∉ cycle, trees.tree p = registry.trees.tree p) :
    trees.registryIds.Perm (s.nr 76 :: registry.trees.registryIds) := by
  let tree := contractionChildTree (cycle.map live.contractionJob)
  have jobs : tree.jobs none = cycle.map live.contractionJob := contractionChildTree_jobs _ (by
    intro j h
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp h
    have spec := live.contractionJob_spec p
    exact ⟨spec.2.2.2.1,spec.2.1.trans spec.1.symm⟩)
  apply trees.expansionIds registry.trees children cycle slot tree unique rotate root hidden (fun p hp => (retained p hp).symm)
  rw [←tree.promoted_ids none,jobs,List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro p hp
  exact congrArg MatchingMemberTree.registryIds (live.contractionJob_promoted p (fixed p hp)).symm

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionRegistryView

/-! matching/MatchingContractionArchiveFrame.lean -/
section RppSource_MatchingContractionArchiveFrame
namespace VehicleRoutingSurvey.Routing



theorem MatchingMemberTree.readable_before_contraction {s : ArithmeticState} (tree : MatchingMemberTree)
    (order : MatchingCycleRecordOrder s) (encoded : tree.encoded s.nm (s.nr 77) (s.nr 78))
    (ids : ∀ n ∈ tree.registryIds, 0 < n ∧ n < s.nr 76) :
    tree.readable s.nm (s.nr 77) (s.nr 78) (matchingContractionOldArchive s) := by
  induction tree with
  | nil => trivial
  | leaf v rest ih => exact ih encoded ids
  | blossom v n child rest ih tail =>
    have bound := ids n (by simp [MatchingMemberTree.registryIds])
    obtain ⟨lo,hi⟩ := order.bounded n bound.1 bound.2
    refine ⟨.inl ⟨n,bound.2,.inl rfl⟩,.inl ⟨n,bound.2,.inr rfl⟩,?_,
      ih encoded.2.2.1 (fun i h => ids i (by simp [MatchingMemberTree.registryIds,h])),
      tail encoded.2.2.2 (fun i h => ids i (by simp [MatchingMemberTree.registryIds,h]))⟩
    intro i inside w width
    have count := encoded.1
    change s.nm (s.nr 78+n) = child.arity at count
    simp only [matchingCycleRecordStart,matchingCycleRecordEnd,count] at lo hi
    exact .inr ⟨by omega,by omega⟩



def MatchingLiveCycles.oldMemoryAtContraction {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState} {dual : MatchingSearchDualMemory part forest s}
    {registry : MatchingRegistryView dual} (live : MatchingLiveCycles registry) (order : MatchingCycleRecordOrder s)
    (ports : ∀ r ∈ ([55,77,78,79,80] : List ℕ), t.nr r = s.nr r)
    (held : ∀ a, matchingContractionOldArchive s a → t.nm a = s.nm a) (C : Finset (Fin k)) (old : C ∈ state.cuts) :
    MatchingLiveCycleMemory (live.entry C old) t := by
  let e := live.entry C old
  let root := MatchingMemberTree.blossom 0 (dual.node C) e.tree .nil
  have encoded : root.encoded s.nm (s.nr 77) (s.nr 78) := by
    simpa [root,e,matchingRebaseNodeState] using (live.memory C old).members.encoded
  apply (live.memory C old).onRegion (root.readable_before_contraction order encoded _) ports held
  intro n h
  change n ∈ root.registryIds at h
  rcases (show n = dual.node C ∨ n ∈ e.tree.registryIds by simpa [root,MatchingMemberTree.registryIds] using h) with rfl | sub
  · exact ⟨Nat.pos_of_ne_zero (dual.nodeNonzero C old),registry.allocated C old⟩
  · obtain ⟨D,hD,rfl⟩ := (registry.keys n).mp (live.ids C old n sub)
    exact ⟨Nat.pos_of_ne_zero (dual.nodeNonzero D hD),registry.allocated D hD⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionArchiveFrame

/-! matching/MatchingContractionChildMemory.lean -/
section RppSource_MatchingContractionChildMemory
namespace VehicleRoutingSurvey.Routing

theorem MatchingLiveCycles.contractionJob_memory {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)}
    {s t : ArithmeticState} {dual : MatchingSearchDualMemory part forest s} {reg : MatchingRegistryView dual}
    (live : MatchingLiveCycles reg) (memory : ∀ C h, MatchingLiveCycleMemory (live.entry C h) t) (p : Fin k) :
    let job := live.contractionJob p
    matchingMemberJobValid t job ∧ job.tree.leaves.Nodup ∧ ∀ x ∈ job.tree.leaves, x < t.nr 55 ∨ x = p.val := by
  intro job
  by_cases single : (part.blocks.block p).card = 1
  · simp [job,contractionJob,single,matchingMemberJobValid,MatchingMemberJob.proper,MatchingMemberJob.tree,
      MatchingMemberTree.leaves,MatchingMemberTree.encoded,MatchingMemberTree.readable,MatchingMemberTree.recordsAbove]
  · let C := part.blocks.block p
    have cut := part.blocks.cut_mem (Finset.mem_univ p) single
    let e := live.entry C cut
    have root := (memory C cut).members
    let u := matchingRebaseNodeState t (dual.node C)
    have same : outsideMatchingMemberScratch u = outsideMatchingMemberScratch t := by
      funext a
      simp [u,matchingRebaseNodeState,outsideMatchingMemberScratch]
    have readable := root.readable
    change (MatchingMemberTree.blossom 0 (dual.node C) e.tree .nil).readable t.nm (t.nr 77) (t.nr 78)
      (outsideMatchingMemberScratch u) at readable
    rw [same] at readable
    have info := live.contractionJob_spec p
    let j : MatchingMemberJob := ⟨p.val,dual.node C,p.val,some e.tree⟩
    have eq : job = j := by simp [job,j,contractionJob,single,C,e]
    have proper : j.proper := eq ▸ info.2.2.2.1
    rw [eq]
    exact ⟨⟨proper,root.encoded,readable,root.above⟩,by simpa [j,MatchingMemberJob.tree,MatchingMemberTree.leaves] using root.unique,
      fun x hx => .inl (root.valid x (by simpa [j,MatchingMemberJob.tree,MatchingMemberTree.leaves] using hx))⟩

theorem contractionChildTree_tables {t : ArithmeticState} (jobs : List MatchingMemberJob)
    (valid : ∀ j ∈ jobs, matchingMemberJobValid t j) :
    let tree := contractionChildTree jobs
    tree.encoded t.nm (t.nr 77) (t.nr 78) ∧
      tree.readable t.nm (t.nr 77) (t.nr 78) (outsideMatchingMemberScratch t) ∧
      tree.recordsAbove t.nm (t.nr 77) (t.nr 80+3*t.nr 55) := by
  induction jobs with
  | nil => exact ⟨trivial,trivial,trivial⟩
  | cons j rest ih =>
    obtain ⟨_,encoded,ready,above⟩ := valid j (by simp)
    obtain ⟨tailE,tailR,tailA⟩ := ih (fun x h => valid x (List.mem_cons_of_mem _ h))
    cases h : j.children with
    | none => simpa [contractionChildTree,h,MatchingMemberTree.encoded,MatchingMemberTree.readable,MatchingMemberTree.recordsAbove]
        using And.intro tailE (And.intro tailR tailA)
    | some child =>
      simp only [contractionChildTree,h,MatchingMemberTree.encoded,MatchingMemberTree.readable,MatchingMemberTree.recordsAbove]
      simp only [MatchingMemberJob.tree,h,MatchingMemberTree.encoded,MatchingMemberTree.readable,MatchingMemberTree.recordsAbove] at encoded ready above
      exact ⟨⟨encoded.1,encoded.2.1,encoded.2.2.1,tailE⟩,⟨ready.1,ready.2.1,ready.2.2.1,ready.2.2.2.1,tailR⟩,
        ⟨above.1,above.2.1,tailA⟩⟩

theorem contractionChildTree_leaves (jobs : List MatchingMemberJob) :
    (contractionChildTree jobs).leaves = jobs.flatMap (fun j => j.tree.leaves) := by
  induction jobs with
  | nil => rfl
  | cons j rest ih =>
    cases h : j.children <;> simp [contractionChildTree,h,MatchingMemberJob.tree,MatchingMemberTree.leaves,ih]

theorem MatchingLiveCycles.contractionLeaves {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)}
    {s t : ArithmeticState} {dual : MatchingSearchDualMemory part forest s} {reg : MatchingRegistryView dual}
    (live : MatchingLiveCycles reg) (memory : ∀ C h, MatchingLiveCycleMemory (live.entry C h) t)
    (dim : t.nr 55 = k) (cycle : List (Fin k)) (distinct : cycle.Nodup) (fixed : ∀ p ∈ cycle, part.representative p = p) :
    let tree := contractionChildTree (cycle.map live.contractionJob)
    tree.leaves.Nodup ∧ ∀ x ∈ tree.leaves, x < t.nr 55 := by
  let bytes := fun p => (live.contractionJob p).tree.leaves
  have bound (p : Fin k) (x : ℕ) (hx : x ∈ bytes p) : x < t.nr 55 := by
    rcases (live.contractionJob_memory memory p).2.2 x hx with bySize | rfl
    · exact bySize
    · exact dim.symm ▸ p.isLt
  dsimp only
  rw [contractionChildTree_leaves,List.flatMap_map]
  change (cycle.flatMap bytes).Nodup ∧ ∀ x ∈ cycle.flatMap bytes, x < t.nr 55
  constructor
  · induction cycle with
    | nil => simp
    | cons p rest ih =>
      obtain ⟨absent,nd⟩ := List.nodup_cons.mp distinct
      rw [List.flatMap_cons,List.nodup_append]
      refine ⟨(live.contractionJob_memory memory p).2.1,ih nd (fun q h => fixed q (by simp [h])),?_⟩
      intro x hx y hy same
      subst y
      obtain ⟨q,hq,hy⟩ := List.mem_flatMap.mp hy
      let v : Fin k := ⟨x,dim ▸ bound p x hx⟩
      have owner (a : Fin k) (ha : a ∈ p :: rest) (leaf : x ∈ bytes a) : part.representative v = a :=
        (part.same_block.mpr (part.blocks.same_of_mem (Finset.mem_univ a) (((live.contractionJob_spec a).2.2.2.2 v).mp leaf))).trans (fixed a ha)
      have equal := (owner p (by simp) hx).symm.trans (owner q (by simp [hq]) hy)
      exact absent (equal.symm ▸ hq)
  · intro x present
    obtain ⟨p,_,hx⟩ := List.mem_flatMap.mp present
    exact bound p x hx

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionChildMemory

/-! matching/MatchingContractionNewMemory.lean -/
section RppSource_MatchingContractionNewMemory
namespace VehicleRoutingSurvey.Routing

/-- Encode the newly appended member tree using the exact direct-child IDs
and representatives written at each physical row. Every older subtree is
already readable at the end of the structural prefix. -/
theorem MatchingLiveCycles.newContractionRoot {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)}
    {s t : ArithmeticState} {dual : MatchingSearchDualMemory part forest s} {reg : MatchingRegistryView dual}
    (live : MatchingLiveCycles reg) (memory : ∀ C h, MatchingLiveCycleMemory (live.entry C h) t)
    (dim : t.nr 55 = k) (cycle : List (Fin k)) (unique : cycle.Nodup) (fixed : ∀ p ∈ cycle, part.representative p = p)
    (many : 1 < cycle.length) (node : ℕ) (positive : 0 < node)
    (count : t.nm (t.nr 78+node) = cycle.length)
    (records : ∀ i : Fin cycle.length, let row := matchingCycleChildAt t.nm (matchingCycleRecordStart t node+4*i.val)
      row.representative = (cycle.get i).val ∧ row.node = blossomNodeAt s (cycle.get i).val)
    (starts : t.nr 77+node < t.nr 79) (counts : t.nr 78+node < t.nr 79)
    (past : matchingRebaseScratchEnd t ≤ matchingCycleRecordStart t node)
    (separate : t.nr 79+t.nr 55 ≤ t.nr 80) :
    MatchingMemberRoot (matchingRebaseNodeState t node) (contractionChildTree (cycle.map live.contractionJob)) := by
  let tree := contractionChildTree (cycle.map live.contractionJob)
  have jobs : tree.jobs none = cycle.map live.contractionJob := contractionChildTree_jobs _ (by
    intro j hj
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hj
    have spec := live.contractionJob_spec p
    exact ⟨spec.2.2.2.1,spec.2.1.trans spec.1.symm⟩)
  have arity : tree.arity = cycle.length := by rw [← tree.jobs_length none,jobs,List.length_map]
  have proper := contractionChildTree_proper (cycle.map live.contractionJob) (by
    intro j hj
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hj
    exact (live.contractionJob_spec p).2.2.2.1)
  have keys : tree.rootKeys = cycle.map (fun p => MatchingMemberTree.rootKey p.val (blossomNodeAt s p.val)) := by
    rw [← tree.jobs_rootKeys none,jobs,List.map_map]
    apply List.map_congr_left
    intro p hp
    have spec := live.contractionJob_spec p
    simp only [Function.comp_apply,spec.1,spec.2.2.1,dual.top p,fixed p hp,true_and]
    by_cases one : (part.blocks.block p).card = 1 <;> simp [one]
  obtain ⟨enc,reads,above⟩ := contractionChildTree_tables (cycle.map live.contractionJob) (t := t) (by
    intro j hj
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hj
    exact (live.contractionJob_memory memory p).1)
  obtain ⟨nd,bound⟩ := live.contractionLeaves memory dim cycle unique fixed
  let u := matchingRebaseNodeState t node
  have keep (i : ℕ) (away : i ≠ 22 := by decide) : u.nr i = t.nr i := by simp [u,matchingRebaseNodeState,Function.update_of_ne away]
  have same : outsideMatchingMemberScratch u = outsideMatchingMemberScratch t := by
    funext i
    simp only [outsideMatchingMemberScratch,keep 79,keep 55,keep 80]
  have root : u.nr 22 = node := by simp [u,matchingRebaseNodeState]
  change MatchingMemberRoot u tree
  refine ⟨?_,?_,?_,?_,nd,?_,?_⟩
  · exact ⟨root.symm ▸ positive,by omega,proper,trivial⟩
  · rw [root,keep 77,keep 78]
    refine ⟨count.trans arity.symm,?_,enc,trivial⟩
    intro i hi
    have h : i < cycle.length := by simpa only [MatchingMemberTree.rootKeys_length,arity] using hi
    obtain ⟨p,n⟩ := records ⟨i,h⟩
    change MatchingMemberTree.rootKey (matchingCycleChildAt t.nm (matchingCycleRecordStart t node+4*i)).representative
      (matchingCycleChildAt t.nm (matchingCycleRecordStart t node+4*i)).node = tree.rootKeys[i]
    simp only [p,n,keys,List.getElem_map,List.get_eq_getElem]
  · rw [root,keep 77,keep 78,same]
    have before (a : ℕ) (lo : a < t.nr 79) : outsideMatchingMemberScratch t a := ⟨.inl lo,.inl (by omega)⟩
    refine ⟨before _ starts,before _ counts,?_,reads,trivial⟩
    intro i _ w _
    have lo := past
    change t.nr 80+5*t.nr 55 ≤ t.nm (t.nr 77+node) at lo
    change outsideMatchingMemberScratch t (t.nm (t.nr 77+node)+4*i+w)
    exact ⟨.inr (by omega),.inr (by omega)⟩
  · rw [root,keep 77,keep 80,keep 55]
    have lo := past
    change t.nr 80+5*t.nr 55 ≤ t.nm (t.nr 77+node) at lo
    exact ⟨by change t.nr 80+3*t.nr 55 ≤ t.nm (t.nr 77+node); omega,above,trivial⟩
  · rw [keep 55]
    exact bound
  · rwa [keep 79,keep 80,keep 55]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionNewMemory

/-! matching/MatchingContractionTopTrees.lean -/
section RppSource_MatchingContractionTopTrees
namespace VehicleRoutingSurvey.Routing

theorem MatchingMemberTree.readable_of_above {memory : ℕ → ℕ} {first count bottom high : ℕ}
    (tree : MatchingMemberTree) (lower : tree.recordsAbove memory first bottom)
    (starts : high ≤ first) (lengths : high ≤ count) (past : high ≤ bottom) :
    tree.readable memory first count (fun a => high ≤ a) := by
  induction tree with
  | nil => trivial
  | leaf v rest ih => exact ih lower
  | blossom v n child rest ci ri =>
    obtain ⟨a,c,r⟩ := lower
    refine ⟨by omega,by omega,?_,ci c,ri r⟩
    intro i _ w _
    omega

/-- Install the fresh root in the base slot, retire the absorbed top
pointers, and reuse all surviving registry trees across the physical writes. -/
def MatchingRegistryView.contractionTopTrees {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)}
    {s t : ArithmeticState} {dual : MatchingSearchDualMemory part forest s} (registry : MatchingRegistryView dual)
    (cycle : Finset (Fin k)) (base : Fin k) (child : MatchingMemberTree)
    (order : MatchingCycleRecordOrder s) (root : MatchingMemberRoot (matchingRebaseNodeState t (s.nr 76)) child)
    (ports : t.nr 77 = s.nr 77 ∧ t.nr 78 = s.nr 78 ∧ t.nr 65 = s.nr 65)
    (held : ∀ a, matchingContractionOldArchive s a → t.nm a = s.nm a)
    (top : ∀ p : Fin k, blossomNodeAt t p.val = if p = base then s.nr 76 else if p ∈ cycle then 0 else blossomNodeAt s p.val) :
    MatchingTopMemberTrees k t := by
  let tree (p : Fin k) := if p = base then MatchingMemberTree.blossom base.val (s.nr 76) child .nil else
    if p ∈ cycle then .nil else registry.trees.tree p
  refine ⟨tree,?_,?_,?_⟩
  · intro p
    change (tree p).rootKeys = if blossomNodeAt t p.val = 0 then [] else [MatchingMemberTree.rootKey p.val (blossomNodeAt t p.val)]
    rw [top p]
    by_cases h : p = base
    · subst p
      simp [tree,MatchingMemberTree.rootKeys,show s.nr 76 ≠ 0 by have lo := order.cursor; omega]
    · by_cases hc : p ∈ cycle
      · simp [tree,h,hc,MatchingMemberTree.rootKeys]
      · simpa only [tree,if_neg h,if_neg hc,blossomNodeAt] using registry.trees.roots p
  · intro p
    by_cases h : p = base
    · simpa only [tree,if_pos h] using! root.proper
    · by_cases hc : p ∈ cycle
      · simp [tree,h,hc,MatchingMemberTree.proper]
      · simpa only [tree,if_neg h,if_neg hc] using registry.trees.proper p
  · intro p
    by_cases h : p = base
    · simpa only [tree,if_pos h] using! root.encoded
    · by_cases hc : p ∈ cycle
      · simp [tree,h,hc,MatchingMemberTree.encoded]
      · rw [show tree p = registry.trees.tree p by simp [tree,h,hc],ports.1,ports.2.1]
        apply MatchingMemberTree.encoded_congr (registry.trees.encoded p) _ held
        apply MatchingMemberTree.readable_before_contraction _ order (registry.trees.encoded p)
        intro id h
        obtain ⟨C,hC,rfl⟩ := (registry.keys id).mp (List.mem_flatMap.mpr ⟨p,List.mem_finRange p,h⟩)
        exact ⟨Nat.pos_of_ne_zero (dual.nodeNonzero C hC),registry.allocated C hC⟩

theorem MatchingRegistryView.contractionTopReadable {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)}
    {s t : ArithmeticState} {dual : MatchingSearchDualMemory part forest s} (registry : MatchingRegistryView dual)
    (cycle : Finset (Fin k)) (base : Fin k) (child : MatchingMemberTree)
    (order : MatchingCycleRecordOrder s) (root : MatchingMemberRoot (matchingRebaseNodeState t (s.nr 76)) child)
    (ports : t.nr 77 = s.nr 77 ∧ t.nr 78 = s.nr 78 ∧ t.nr 65 = s.nr 65)
    (held : ∀ a, matchingContractionOldArchive s a → t.nm a = s.nm a)
    (top : ∀ p : Fin k, blossomNodeAt t p.val = if p = base then s.nr 76 else if p ∈ cycle then 0 else blossomNodeAt s p.val)
    (starts : t.nr 65+2*(k*k) ≤ t.nr 77) (counts : t.nr 65+2*(k*k) ≤ t.nr 78)
    (stack : t.nr 65+2*(k*k) ≤ t.nr 80+3*t.nr 55) (p : Fin k) :
    let trees := registry.contractionTopTrees cycle base child order root ports held top
    (trees.tree p).readable t.nm (t.nr 77) (t.nr 78) (fun a => t.nr 65+2*(k*k) ≤ a) := by
  intro trees
  change (if p = base then MatchingMemberTree.blossom base.val (s.nr 76) child .nil else
    if p ∈ cycle then .nil else registry.trees.tree p).readable _ _ _ _
  by_cases h : p = base
  · rw [if_pos h]
    exact MatchingMemberTree.readable_of_above _ root.above starts counts stack
  · rw [if_neg h]
    by_cases on : p ∈ cycle
    · rw [if_pos on]; trivial
    · rw [if_neg on,ports.1,ports.2.1,ports.2.2]
      have area := (registry.trees.tree p).readable_before_contraction order (registry.trees.encoded p) (by
        intro id hi
        obtain ⟨C,hC,rfl⟩ := (registry.keys id).mp (List.mem_flatMap.mpr ⟨p,List.mem_finRange p,hi⟩)
        exact ⟨Nat.pos_of_ne_zero (dual.nodeNonzero C hC),registry.allocated C hC⟩)
      exact MatchingMemberTree.readable_after_move (tree := registry.trees.tree p)
        (MatchingMemberTree.readableAnd (tree := registry.trees.tree p) area (registry.readable p)) held

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionTopTrees

/-! matching/MatchingContractionLiveCycles.lean -/
section RppSource_MatchingContractionLiveCycles
namespace VehicleRoutingSurvey.Routing

/-- Extend the entire live-cycle collection at a contraction. The newly
registered node owns precisely the previous top subtrees of the cycle and
all older direct-child links retain their original node IDs and ports. -/
noncomputable def MatchingLiveCycles.afterContraction {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)}
    {s t : ArithmeticState} {dual : MatchingSearchDualMemory part forest s} {reg : MatchingRegistryView dual}
    (live : MatchingLiveCycles reg) (cycle : List (Fin k)) (base : Fin k) (baseIn : base ∈ cycle.toFinset)
    (fixed : ∀ p ∈ cycle.toFinset, part.representative p = p) (odd : Odd cycle.toFinset.card) (many : 1 < cycle.toFinset.card)
    (covered : ∀ p ∈ cycle.toFinset, p ≠ base → p ∈ state.covered)
    {after : MatchingSearchDualMemory (part.contract cycle.toFinset base baseIn fixed odd covered)
      (forest.contract cycle.toFinset base) t} (nextRegistry : MatchingRegistryView after)
    (keepIds : ∀ C ∈ state.cuts, after.node C = dual.node C)
    (kept : ∀ C h, MatchingLiveCycleMemory (live.entry C h) t)
    (added : MatchingLiveCycle (state.registerCut (part.contractCut cycle.toFinset) (part.contractCut_odd cycle.toFinset fixed odd))
      after.node (part.contractCut cycle.toFinset))
    (physical : MatchingLiveCycleMemory added t) (atBase : added.base = base)
    (jobs : added.tree.jobs none = cycle.map live.contractionJob) (blocks : added.ports.block = part.blocks.block)
    (root : nextRegistry.trees.tree base = .blossom base.val (after.node (part.contractCut cycle.toFinset)) added.tree .nil)
    (outside : ∀ p ∉ cycle, nextRegistry.trees.tree p = reg.trees.tree p) :
    MatchingLiveCycles nextRegistry := by
  classical
  let B := part.contractCut cycle.toFinset
  let next := state.registerCut B (part.contractCut_odd cycle.toFinset fixed odd)
  let joined := part.contract cycle.toFinset base baseIn fixed odd covered
  have newCut : B ∉ state.cuts := part.contractCut_fresh cycle.toFinset fixed many reg.nested
  let older := fun (C : Finset (Fin k)) (h : C ∈ state.cuts) =>
    (live.entry C h).afterContraction part cycle.toFinset fixed odd many reg.nested keepIds h
  let entry (C : Finset (Fin k)) (h : C ∈ next.cuts) : MatchingLiveCycle next after.node C :=
    if old : C ∈ state.cuts then older C old else
      (show C = B from (Finset.mem_insert.mp h).resolve_right old).symm ▸ added
  have oldEntry (C : Finset (Fin k)) (h : C ∈ state.cuts) (hc : C ∈ next.cuts) : entry C hc = older C h := by simp [entry,h]
  have newEntry (h : B ∈ next.cuts) : entry B h = added := by simp [entry,newCut]
  have keepTreeIds {id : ℕ} (h : id ∈ reg.trees.registryIds) : id ∈ nextRegistry.trees.registryIds := by
    obtain ⟨C,hC,eq⟩ := (reg.keys _).mp h
    exact (nextRegistry.keys _).mpr ⟨C,Finset.mem_insert_of_mem hC,(keepIds C hC).trans eq⟩
  refine ⟨entry,?_,?_,?_,?_⟩
  · intro C h
    rcases Finset.mem_insert.mp h with rfl | old
    · rw [newEntry h]; exact physical
    · rw [oldEntry C old h]
      exact (kept C old).afterContraction part cycle.toFinset fixed odd many reg.nested keepIds old
  · intro p registered isBase
    change joined.representative p = p at isBase
    by_cases inside : part.representative p ∈ cycle.toFinset
    · have eq : base = p := by simpa only [joined,part.contract_representative,blossomRepresentative,if_pos inside] using isBase
      subst p
      have block : joined.blocks.block base = B := by rw [part.contract_block,if_pos inside]
      have fields (C : Finset (Fin k)) (h : C ∈ next.cuts) (eq : C = B) :
          (entry C h).base = base ∧ nextRegistry.trees.tree base =
            .blossom base.val (after.node C) (entry C h).tree .nil := by
        subst C
        rw [newEntry h]
        exact ⟨atBase,root⟩
      exact fields _ registered block
    · have fixedP : part.representative p = p := by
        simpa only [joined,part.contract_representative,blossomRepresentative,if_neg inside] using isBase
      have out : p ∉ cycle := fun h => inside (fixedP.symm ▸ List.mem_toFinset.mpr h)
      have block : joined.blocks.block p = part.blocks.block p := by rw [part.contract_block,if_neg inside]
      have diff : part.blocks.block p ≠ B := by
        intro same
        have present : p ∈ B := same ▸ part.blocks.self_mem p (Finset.mem_univ p)
        exact inside ((part.mem_contractCut cycle.toFinset fixed p).mp present)
      have present : part.blocks.block p ∈ next.cuts := block ▸ registered
      have old := (Finset.mem_insert.mp present).resolve_left diff
      obtain ⟨port,tree⟩ := live.top p old fixedP
      have fields (C : Finset (Fin k)) (h : C ∈ next.cuts) (eq : C = part.blocks.block p) :
          (entry C h).base = p ∧ nextRegistry.trees.tree p =
            .blossom p.val (after.node C) (entry C h).tree .nil := by
        subst C
        rw [oldEntry _ old h, keepIds _ old, outside p out]
        exact ⟨port,tree⟩
      exact fields _ registered block
  · intro C h job hj sub child
    rcases Finset.mem_insert.mp h with rfl | old
    · rw [newEntry h] at hj ⊢
      rw [jobs] at hj
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
      by_cases one : (part.blocks.block p).card = 1
      · simp [contractionJob,one] at child
      · let D := part.blocks.block p
        have hd := part.blocks.cut_mem (Finset.mem_univ p) one
        have pBase := (live.top p hd (fixed p (List.mem_toFinset.mpr hp))).1
        have subEq : (live.entry D hd).tree = sub := by simpa [D,contractionJob,one] using child
        have oldMem : D ∈ next.cuts := Finset.mem_insert_of_mem hd
        refine ⟨D,oldMem,?_,?_,?_,?_⟩
        · simp [D,contractionJob,one,keepIds _ hd]
        · rw [oldEntry _ hd oldMem]; exact subEq
        · rw [oldEntry _ hd oldMem]
          exact (congrArg Fin.val pBase).trans (live.contractionJob_spec p).1.symm
        · rw [oldEntry _ hd oldMem,blocks]
          exact (congrArg part.blocks.block pBase).symm
    · rw [oldEntry _ old h] at hj ⊢
      obtain ⟨D,hd,id,tree,port,block⟩ := live.child C old job hj sub child
      have present : D ∈ next.cuts := Finset.mem_insert_of_mem hd
      refine ⟨D,present,(keepIds _ hd).trans id,?_,?_,?_⟩
      · rw [oldEntry _ hd present]; exact tree
      · rw [oldEntry _ hd present]; exact port
      · rw [oldEntry _ hd present]; exact block
  · intro C h n present
    rcases Finset.mem_insert.mp h with rfl | old
    · rw [newEntry h] at present
      apply List.mem_flatMap.mpr
      exact ⟨base,List.mem_finRange base,by simp [root,MatchingMemberTree.registryIds,present]⟩
    · rw [oldEntry _ old h] at present
      exact keepTreeIds (live.ids C old n present)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionLiveCycles

/-! matching/MatchingContractionLiveGeometry.lean -/
section RppSource_MatchingContractionLiveGeometry
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The cycle written when the node is allocated supplies its expansion and
rebase geometry. The original endpoints, including matched child ports, are
those in the four-word records, in their physical order. -/
theorem contractionCreatesLiveGeometry {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (left right : List (Fin k)) (base : Fin k) (s : ArithmeticState)
    (distinct : (contractionCycleOrder left right base).Nodup)
    (odd : Odd (contractionCycleOrder left right base).length)
    (length : 1 < (contractionCycleOrder left right base).length)
    (fixed : ∀ p ∈ (contractionCycleOrder left right base).toFinset, part.representative p = p)
    (pairs : ∀ u v, s(u,v) ∈ alternatingEdges (right.reverse ++ left) →
      state.partialMate u = some v ∧ state.partialMate v = some u)
    (words : let cycle := contractionCycleOrder left right base
      ∀ i : Fin cycle.length, let row := matchingContractionWrittenChild s i.val
        let src := cycle.get i
        let dst := cycle.get ⟨(i.val+1) % cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
        row.representative = src.val ∧ row.node = (matchingCycleRecordReference s).nm (s.nr 74+src.val) ∧
          ContractionCycleEdgeWords part src dst (row.endpointA,row.endpointB))
    (tree : MatchingMemberTree) :
    let cycle := contractionCycleOrder left right base
    let ports := part.contractionChildPorts cycle.toFinset fixed
      (by change Odd (contractionCycleOrder left right base).toFinset.card
          rw [List.toFinset_card_of_nodup distinct]; exact odd)
      (by change 1 < (contractionCycleOrder left right base).toFinset.card
          rw [List.toFinset_card_of_nodup distinct]; exact length)
    MatchingChildMemberTree ports tree →
      ∃ g : MatchingExpansionGeometry ports tree base,
        g.cycle = cycle ∧ g.children = right.reverse ++ left ∧
          (∀ i : Fin g.cycle.length, let row := matchingContractionWrittenChild s i.val
            row.representative = (g.cycle.get i).val ∧
            row.node = (matchingCycleRecordReference s).nm (s.nr 74+(g.cycle.get i).val) ∧
            (row.endpointA,row.endpointB) = ((g.edges i).1.val,(g.edges i).2.val)) ∧
          ∀ i : Fin g.cycle.length, let src := g.cycle.get i
            let dst := g.cycle.get ⟨(i.val+1) % g.cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
            state.partialMate src = some dst → g.edges i = (src,dst) := by
  classical
  intro cycle ports members
  let src (i : Fin cycle.length) := cycle.get i
  let dst (i : Fin cycle.length) := cycle.get ⟨(i.val+1) % cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
  have sourceData (i : Fin cycle.length) := (words i).2.2
  choose a b bytes source target value matched using sourceData
  let emit := fun i : Fin cycle.length => (a i,b i)
  have owner (v p : Fin k) (onCycle : p ∈ cycle.toFinset) (rep : part.representative v = p) : v ∈ part.blocks.block p := by
    have eq := part.same_block.mp (rep.trans (fixed p onCycle).symm)
    exact eq ▸ part.blocks.self_mem v (Finset.mem_univ v)
  let slot : Fin cycle.length := ⟨left.length,by simp only [cycle,contractionCycleOrder_length]; omega⟩
  let geom : MatchingExpansionGeometry ports tree base := {
    members := members
    cycle := cycle
    edges := emit
    baseSlot := slot
    children := right.reverse ++ left
    distinct := distinct
    odd := odd
    rotate := (contractionCycleOrder_base left right base).1
    atBase := (contractionCycleOrder_base left right base).2
    ports := rfl
    source := fun i => owner (a i) (src i) (List.mem_toFinset.mpr (List.get_mem _ _)) (source i)
    target := fun i => owner (b i) (dst i) (List.mem_toFinset.mpr (List.get_mem _ _)) (target i)
    tight := by
      intro i
      change oddCutDualEdgeValue (insert (part.contractCut cycle.toFinset) state.cuts) state.potential
        (extendBlossomCutDual state.cuts state.cutDual) s(a i,b i) = _
      rw [oddCutDualEdgeValue_register_cut]
      exact value i
    matched := pairs }
  refine ⟨geom,rfl,rfl,fun i => ⟨(words i).1,(words i).2.1,bytes i⟩,?_⟩
  intro i p q h
  obtain ⟨first,second⟩ := matched i h
  exact Prod.ext first second

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionLiveGeometry

/-! matching/MatchingContractionNodeInterior.lean -/
section RppSource_MatchingContractionNodeInterior
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Restricting the global matching to a top block removes exactly its current
exposed port. This yields the concrete edge set used by the live cycle archive. -/
theorem CompactTopMatching.blockInterior {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) {p : Fin k} (fixed : part.representative p = p) :
    IsPerfectMatchingOn ((part.blocks.block p).erase p) (matchingCycleInterior state (part.blocks.block p) p) := by
  classical
  constructor
  · intro edge member
    obtain ⟨present,inside⟩ := Finset.mem_filter.mp member
    exact ⟨(state.perfect.1 edge present).1,inside⟩
  · intro v included
    obtain ⟨apart,inside⟩ := Finset.mem_erase.mp included
    obtain ⟨e,he,hv,all⟩ := top.interior p v inside (fixed.symm ▸ apart)
    have noPort : p ∉ e := by
      intro hp
      have covered := (state.perfect.1 e he).2 p hp
      let q := mateOfMatching state.perfect p
      have matched : state.partialMate p = some q := by simp [CompactMatchingPrimalDual.partialMate,covered,q]
      have pair := state.partialMate_some_iff.mp matched
      have exactEdge := (state.perfect.2 p covered).unique ⟨pair,Sym2.mem_mk_left _ _⟩ ⟨he,hp⟩
      have belongs := all q (exactEdge ▸ Sym2.mem_mk_right p q)
      exact top.matchedBase fixed matched (part.blocks.same_of_mem (Finset.mem_univ p) belongs).symm
    refine ⟨e,⟨Finset.mem_filter.mpr ⟨he,fun u hu => Finset.mem_erase.mpr ⟨fun same => noPort (same ▸ hu),all u hu⟩⟩,hv⟩,?_⟩
    intro f hf
    exact (state.perfect.2 v ((state.perfect.1 e he).2 v hv)).unique ⟨(Finset.mem_filter.mp hf.1).1,hf.2⟩ ⟨he,hv⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionNodeInterior

/-! matching/MatchingContractionLiveNode.lean -/
section RppSource_MatchingContractionLiveNode
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Assemble the new archive entry from the old archive, the immutable
directional rows of this allocation, and the matching retained by contraction. -/
theorem contractionCreatesLiveNode {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {registryState : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest registryState} {registry : MatchingRegistryView dual}
    (live : MatchingLiveCycles registry) (top : CompactTopMatching part)
    (left right : List (Fin k)) (base : Fin k) (writer : ArithmeticState) (node : Finset (Fin k) → ℕ)
    (distinct : (contractionCycleOrder left right base).Nodup) (odd : Odd (contractionCycleOrder left right base).length)
    (length : 1 < (contractionCycleOrder left right base).length)
    (fixed : ∀ p ∈ (contractionCycleOrder left right base).toFinset, part.representative p = p)
    (oldIds : ∀ C ∈ state.cuts, C ≠ part.contractCut (contractionCycleOrder left right base).toFinset → node C = dual.node C)
    (mate : ∀ x ∈ (contractionCycleOrder left right base).toFinset, x ≠ base →
      ∃ y ∈ (contractionCycleOrder left right base).toFinset, y ≠ base ∧ state.partialMate x = some y)
    (pairs : ∀ u v, s(u,v) ∈ alternatingEdges (right.reverse ++ left) →
      state.partialMate u = some v ∧ state.partialMate v = some u)
    (rows : let cycle := contractionCycleOrder left right base
      ∀ i : Fin cycle.length, let row := matchingContractionWrittenChild writer i.val
        let src := cycle.get i
        let dst := cycle.get ⟨(i.val+1) % cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
        row.representative = src.val ∧ row.node = (matchingCycleRecordReference writer).nm (writer.nr 74+src.val) ∧
          ContractionCycleEdgeWords part src dst (row.endpointA,row.endpointB)) :
    let cycle := contractionCycleOrder left right base
    let oddCard : Odd cycle.toFinset.card := by
      change Odd (contractionCycleOrder left right base).toFinset.card
      rw [List.toFinset_card_of_nodup distinct]
      exact odd
    let next := state.registerCut (part.contractCut cycle.toFinset) (part.contractCut_odd cycle.toFinset fixed oddCard)
    ∃ e : MatchingLiveCycle next node (part.contractCut cycle.toFinset),
      e.base = base ∧ e.geometry.cycle = cycle ∧ e.geometry.children = right.reverse ++ left ∧ e.tree = contractionChildTree (cycle.map live.contractionJob) ∧
      e.ports.block = part.blocks.block ∧ e.tree.jobs none = cycle.map live.contractionJob ∧
      ∀ i : Fin e.geometry.cycle.length, let row := matchingContractionWrittenChild writer i.val
        row.representative = (e.geometry.cycle.get i).val ∧
          (row.endpointA,row.endpointB) = ((e.geometry.edges i).1.val,(e.geometry.edges i).2.val) := by
  classical
  intro cycle oddCard next
  have many : 1 < cycle.toFinset.card := by
    change 1 < (contractionCycleOrder left right base).toFinset.card
    rw [List.toFinset_card_of_nodup distinct]
    exact length
  let ports := part.contractionChildPorts cycle.toFinset fixed oddCard many
  let tree := contractionChildTree (cycle.map live.contractionJob)
  obtain ⟨members,_,arity,keys,jobs⟩ := live.contractionTree cycle fixed oddCard many
  obtain ⟨g,gCycle,gTail,written,matching⟩ := contractionCreatesLiveGeometry part left right base writer distinct odd length fixed pairs rows tree members
  have baseIn : base ∈ cycle.toFinset := by simp [cycle,contractionCycleOrder]
  let joined := part.contract cycle.toFinset base baseIn fixed oddCard (contractionMates_covered mate)
  have merged := top.contract baseIn fixed oddCard mate
  have joinedBlock : joined.blocks.block base = part.contractCut cycle.toFinset := by
    rw [part.contract_block,fixed base baseIn,if_pos baseIn]
  have joinedFixed : joined.representative base = base := by
    rw [part.contract_representative,fixed base baseIn,blossomRepresentative,if_pos baseIn]
  have info {j : MatchingMemberJob} (hj : j ∈ tree.jobs none) {p : Fin k} (port : j.representative = p.val) :
      p ∈ cycle ∧ j = live.contractionJob p := by
    rw [jobs] at hj
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hj
    have eq : q = p := Fin.ext ((live.contractionJob_spec q).1.symm.trans port)
    exact ⟨eq ▸ hq,congrArg live.contractionJob eq⟩
  let e : MatchingLiveCycle next node (part.contractCut cycle.toFinset) := {
    base := base
    tree := tree
    ports := ports
    geometry := g
    arity := arity.trans (congrArg List.length gCycle).symm
    keys := keys.trans (congrArg (List.map Fin.val) gCycle).symm
    owner := by
      intro j hj p hp
      obtain ⟨on,rfl⟩ := info hj hp
      exact ⟨List.mem_toFinset.mpr on,(live.contractionJob_spec p).2.2.2.2⟩
    childNode := by
      intro j hj p hp
      obtain ⟨on,rfl⟩ := info hj hp
      have recorded := (live.contractionJob_spec p).2.2.1
      by_cases single : (part.blocks.block p).card = 1
      · simpa only [ports,CompactMatchingPartition.contractionChildPorts,if_pos single] using recorded
      · have cut := part.blocks.cut_mem (Finset.mem_univ p) single
        have away := (Finset.mem_erase.mp (ports.live p (List.mem_toFinset.mpr on) single)).1
        simpa only [ports,CompactMatchingPartition.contractionChildPorts,if_neg single,oldIds _ cut away] using recorded
    descendants := part.contractionChildPorts_descendants cycle.toFinset fixed oddCard many registry.nested
    internal := joinedBlock ▸ merged.blockInterior joinedFixed
    matchedRow := matching }
  exact ⟨e,rfl,gCycle,gTail,rfl,rfl,jobs,fun i => ⟨(written i).1,(written i).2.2⟩⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionLiveNode

/-! matching/MatchingContractionRegistration.lean -/
section RppSource_MatchingContractionRegistration
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Register the whole collection immediately after allocation, including
its new recursive member tree, old descendants and all forward cycle edge
words. The data for the new index are the concrete emitted records. -/
theorem matchingContractionRegistersCycles {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (live : MatchingLiveCycles registry) (top : CompactTopMatching part) (left right : List (Fin k)) (base : Fin k)
    (unique : (contractionCycleOrder left right base).Nodup) (odd : Odd (contractionCycleOrder left right base).length)
    (many : 1 < (contractionCycleOrder left right base).length)
    (fixed : ∀ p ∈ (contractionCycleOrder left right base).toFinset, part.representative p = p)
    (mate : ∀ x ∈ (contractionCycleOrder left right base).toFinset, x ≠ base →
      ∃ y ∈ (contractionCycleOrder left right base).toFinset, y ≠ base ∧ state.partialMate x = some y)
    (pairs : ∀ x y, s(x,y) ∈ alternatingEdges (right.reverse ++ left) → state.partialMate x = some y ∧ state.partialMate y = some x)
    (rows : let cycle := contractionCycleOrder left right base
      ∀ i : Fin cycle.length, let row := matchingContractionWrittenChild s i.val
        let p := cycle.get i
        let q := cycle.get ⟨(i.val+1)%cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
        row.representative = p.val ∧ row.node = (matchingCycleRecordReference s).nm (s.nr 74+p.val) ∧
          ContractionCycleEdgeWords part p q (row.endpointA,row.endpointB))
    (oldPtrs : ∀ p : Fin k, (matchingCycleRecordReference s).nm (s.nr 74+p.val) = blossomNodeAt s p.val)
    (order : MatchingCycleRecordOrder s) (ports : ∀ r ∈ ([55,65,77,78,79,80] : List ℕ), t.nr r = s.nr r)
    (held : ∀ a, matchingContractionOldArchive s a → t.nm a = s.nm a)
    (topNodes : ∀ p : Fin k, blossomNodeAt t p.val =
      if p = base then s.nr 76 else if p ∈ (contractionCycleOrder left right base).toFinset then 0 else blossomNodeAt s p.val)
    (count : t.nm (t.nr 78+s.nr 76) = (contractionCycleOrder left right base).length)
    (table : ∀ i < (contractionCycleOrder left right base).length, matchingCycleChildAt t.nm (matchingCycleRecordStart t (s.nr 76)+4*i) =
      matchingContractionWrittenChild s i)
    (newCursor : t.nr 76 = s.nr 76+1) (startSafe : t.nr 77+s.nr 76 < t.nr 79) (countSafe : t.nr 78+s.nr 76 < t.nr 79)
    (past : matchingRebaseScratchEnd t ≤ matchingCycleRecordStart t (s.nr 76)) (separated : t.nr 79+t.nr 55 ≤ t.nr 80)
    (starts : t.nr 65+2*(k*k) ≤ t.nr 77) (counts : t.nr 65+2*(k*k) ≤ t.nr 78) (stack : t.nr 65+2*(k*k) ≤ t.nr 80+3*t.nr 55) :
    let cycle := contractionCycleOrder left right base
    let B := part.contractCut cycle.toFinset
    let baseIn : base ∈ cycle.toFinset := by simp [cycle,contractionCycleOrder]
    let oddCard : Odd cycle.toFinset.card := by
      change Odd (contractionCycleOrder left right base).toFinset.card
      rw [List.toFinset_card_of_nodup unique]
      exact odd
    let joined := part.contract cycle.toFinset base baseIn fixed oddCard (contractionMates_covered mate)
    ∀ (after : MatchingSearchDualMemory joined (forest.contract cycle.toFinset base) t),
      (∀ C ∈ state.cuts, after.node C = dual.node C) → after.node B = s.nr 76 →
      ∃ newRegistry : MatchingRegistryView after, Nonempty (MatchingLiveCycles newRegistry) := by
  classical
  intro cycle B baseIn oddCard joined after ids id
  have large : 1 < cycle.toFinset.card := by
    change 1 < (contractionCycleOrder left right base).toFinset.card
    rw [List.toFinset_card_of_nodup unique]
    exact many
  have port (r : ℕ) (inScope : r ∈ ([55,65,77,78,79,80] : List ℕ) := by decide) := ports r inScope
  have kept := live.oldMemoryAtContraction order (t := t) (fun r h => port r (by simp at h ⊢; aesop)) held
  obtain ⟨e,baseEq,cycleEq,tailEq,treeEq,blocks,jobs,words⟩ := contractionCreatesLiveNode live top left right base s after.node unique odd many fixed
    (fun C h _ => ids C h) mate pairs rows
  let child := contractionChildTree (cycle.map live.contractionJob)
  have labels (i : Fin cycle.length) :
      let row := matchingCycleChildAt t.nm (matchingCycleRecordStart t (s.nr 76)+4*i.val)
      row.representative = (cycle.get i).val ∧ row.node = blossomNodeAt s (cycle.get i).val := by
    dsimp only
    rw [table i.val i.isLt]
    exact ⟨(rows i).1,(rows i).2.1.trans (oldPtrs _)⟩
  have root := live.newContractionRoot kept after.dimension cycle unique (fun p hp => fixed p (List.mem_toFinset.mpr hp)) many
    (s.nr 76) order.cursor count labels startSafe countSafe past separated
  have memory : MatchingLiveCycleMemory e t := by
    refine ⟨?_,?_,?_⟩
    · rw [id,treeEq]; exact root
    · rw [id,cycleEq]; exact count
    · intro i
      dsimp only
      rw [id,table _ (by simpa only [←cycleEq] using i.isLt)]
      exact words i
  let header := And.intro (port 77) (And.intro (port 78) (port 65))
  let trees := registry.contractionTopTrees cycle.toFinset base child order root header held topNodes
  have installed : trees.tree base = .blossom base.val (s.nr 76) child .nil := by
    change (if base = base then _ else _) = _; rw [if_pos rfl]
  have retained (p : Fin k) (out : p ∉ cycle) : trees.tree p = registry.trees.tree p := by
    have apart : p ≠ base := fun eq => out (eq.symm ▸ List.mem_toFinset.mp baseIn)
    change (if p = base then _ else if p ∈ cycle.toFinset then _ else _) = _
    simp only [if_neg apart,if_neg (fun h => out (List.mem_toFinset.mp h))]
  have rotate : cycle.rotate left.length = base :: (right.reverse ++ left) := (contractionCycleOrder_base left right base).1
  have perm := (List.rotate_perm cycle left.length).symm
  rw [rotate] at perm
  have uniqueRot := perm.nodup unique
  have hidden (p : Fin k) (hp : p ∈ right.reverse ++ left) : trees.tree p = .nil := by
    have ne : p ≠ base := fun eq => (List.nodup_cons.mp uniqueRot).1 (eq ▸ hp)
    have inside : p ∈ cycle.toFinset := List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ hp))
    change (if p = base then _ else if p ∈ cycle.toFinset then _ else _) = _
    rw [if_neg ne,if_pos inside]
  have all := live.contractionIds trees cycle base (right.reverse ++ left) left.length unique rotate
    (fun p hp => fixed p (List.mem_toFinset.mpr hp)) installed hidden retained
  let next := registry.afterContraction cycle.toFinset base baseIn fixed oddCard large (contractionMates_covered mate)
    after trees (registry.contractionTopReadable cycle.toFinset base child order root header held topNodes starts counts stack) all ids id newCursor
  have rootNext : next.trees.tree base = .blossom base.val (after.node B) e.tree .nil := by
    change trees.tree base = _
    rw [id,treeEq]; exact installed
  exact ⟨next,⟨live.afterContraction cycle base baseIn fixed oddCard large (contractionMates_covered mate) next
    ids kept e memory baseEq jobs blocks rootNext retained⟩⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionRegistration

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.matchingContractionRegistersCycles) :=
  @VehicleRoutingSurvey.Routing.matchingContractionRegistersCycles
