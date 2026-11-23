-- Prove2me | solution 1 for StableMSR.Recovery.SingleSearch.numeric_tight_table_row
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T20:35:20.125783+00:00
-- url     : https://prove2.me/submissions/070c7715-19c0-4633-a0ef-68f2590cdb0a

import Definitions.Def_StableMSR_TightComponentTrace
import Definitions.Def_StableMSR_SingleVertexSearch
import Theorems.Thm_StableMSR_Recovery_SingleSearch_deletion_piece_geometry
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
open scoped Classical
set_option autoImplicit false
theorem product_unit_left {A:Type} (L:Lang A) : product emptyWord L=L := by
  funext s;apply propext
  constructor
  · rintro ⟨a,b,rfl,h,rfl⟩;simpa using h
  · intro h;exact ⟨[],s,rfl,h,rfl⟩

theorem product_unit_right {A:Type} (L:Lang A) : product L emptyWord=L := by
  funext s;apply propext
  constructor
  · rintro ⟨a,b,h,rfl,rfl⟩;simpa using h
  · intro h;exact ⟨s,[],h,rfl,(List.append_nil s).symm⟩

theorem product_assoc {A:Type} (P Q R:Lang A) : product (product P Q) R=product P (product Q R) := by
  funext s;apply propext
  constructor
  · rintro ⟨_,c,⟨a,b,h,k,rfl⟩,l,rfl⟩
    exact ⟨a,b++c,h,⟨b,c,k,l,rfl⟩,List.append_assoc ..⟩
  · rintro ⟨a,_,h,⟨b,c,k,l,rfl⟩,rfl⟩
    exact ⟨a++b,c,⟨a,b,h,k,rfl⟩,l,(List.append_assoc ..).symm⟩

theorem fold_product {A:Type} (ls:List (Lang A)) (P Q:Lang A) :
    ls.foldl product (product P Q)=product P (ls.foldl product Q) := by
  induction ls generalizing Q with
  | nil=>rfl
  | cons x xs ih=>simp only [List.foldl_cons,product_assoc,ih]

theorem fold_concatenate {A:Type} (ls:List (Lang A)) (P:Lang A) :
    ls.foldl product P=product P (concatenate ls) := by
  simpa only [product_unit_right,concatenate] using fold_product ls P emptyWord

theorem union_flat {A B:Type} [DecidableEq A] [DecidableEq B] (ls:List A) (f:A→List B) :
    (ls.flatMap f).toFinset=ls.toFinset.biUnion (fun j=>(f j).toFinset) := by
  classical
  ext b;simp


end StableMSR.Recovery.TightLanguage
namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch
open SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def grow (S A : Finset V) := A ∪ Finset.univ.filter (fun y=>y∉S ∧ ∃x∈A,G.Adj x y)
def flood (S : Finset V) (a : V) : ℕ→Finset V
  | 0=>{a} | i+1=>grow G S (flood S a i)
theorem mem_grow {S A : Finset V} {y : V} :
    y∈grow G S A ↔ y∈A ∨ y∉S ∧ ∃x∈A,G.Adj x y := by simp [grow]
theorem flood_step (S : Finset V) (a : V) (i : ℕ) : flood G S a i⊆flood G S a (i+1) :=
  fun _ h=>(mem_grow G).2 (Or.inl h)
theorem flood_fixed (S : Finset V) (a : V) :
    grow G S (flood G S a (Fintype.card V))=flood G S a (Fintype.card V) := by
  have aux (m : ℕ) : flood G S a (m+1)=flood G S a m ∨ m+1≤(flood G S a m).card := by
    induction m with
    | zero=>right;simp [flood]
    | succ i ih=>
      rcases ih with h|h
      · left;exact congrArg (grow G S) h
      · by_cases eq:flood G S a (i+1)=flood G S a i
        · left;exact congrArg (grow G S) eq
        · right
          have lt:=Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨flood_step G S a i,Ne.symm eq⟩)
          omega
  rcases aux (Fintype.card V) with h|h
  · exact h
  · have:=Finset.card_le_univ (flood G S a (Fintype.card V));omega
theorem flood_seed (S : Finset V) (a : V) (i : ℕ) : a∈flood G S a i := by
  induction i with
  | zero=>simp [flood]
  | succ i ih=>exact flood_step G S a i ih
theorem flood_flap (S : Finset V) (a : V) (ha:a∉S) : IsFlap G S (flood G S a (Fintype.card V)) := by
  let A:=flood G S a
  have reach (i : ℕ) (v : V) (hv:v∈A i) : ∃p:G.Walk a v, ∀z∈p.support,z∈A i := by
    induction i generalizing v with
    | zero=>
      have e:v=a:=by simpa [A,flood] using hv
      subst v
      refine ⟨.nil,?_⟩
      intro z hz
      have e:z=a:=by simpa using hz
      simpa [e] using hv
    | succ i ih=>
      rcases (mem_grow G).1 hv with h|⟨_,x,hx,adj⟩
      · obtain ⟨p,hp⟩:=ih v h
        exact ⟨p,fun z hz=>flood_step G S a i (hp z hz)⟩
      · obtain ⟨p,hp⟩:=ih x hx
        refine ⟨p.concat adj,?_⟩
        intro z hz
        rw [SimpleGraph.Walk.support_concat,List.mem_append] at hz
        rcases hz with hz|hz
        · exact flood_step G S a i (hp z hz)
        · have e:z=v:=by simpa using hz
          simpa [e] using hv
  have avoid (i : ℕ) (v : V) (hv:v∈A i) : v∉S := by
    induction i with
    | zero=>have e:v=a:=by simpa [A,flood] using hv
            simpa [e] using ha
    | succ i ih=>rcases (mem_grow G).1 hv with h|h
                 · exact ih h
                 · exact h.1
  refine ⟨⟨⟨a,flood_seed G S a _⟩,?_⟩,Finset.disjoint_left.mpr (fun _ hv hw=>avoid _ _ hw hv),?_⟩
  · intro x hx y hy
    obtain ⟨p,hp⟩:=reach _ x hx
    obtain ⟨q,hq⟩:=reach _ y hy
    refine ⟨p.reverse.append q,?_⟩
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_append_iff p.reverse q).mp hz with hz|hz
    · exact hp _ (by simpa [SimpleGraph.Walk.support_reverse] using hz)
    · exact hq _ hz
  · intro x hx y hxy hy
    rw [←flood_fixed G S a]
    exact (mem_grow G).2 (Or.inr ⟨hy,x,hx,hxy⟩)

theorem flood_stable (S:Finset V) (v:V) (m:ℕ) (hm:Fintype.card V ≤ m) :
    flood G S v m=flood G S v (Fintype.card V) := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero=>rfl
  | succ k ih=>change grow G S (flood G S v (Fintype.card V+k))=_;rw [ih,flood_fixed]

end StableMSR.Recovery.TightLanguage.Graph

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

structure Presentation {V:Type} (d:Instance) (G:SimpleGraph V) where
  ix : V→Fin d.n
  injective : Function.Injective ix
  active : ∀i:Fin d.n,d.active i.val=true ↔ ∃v,ix v=i
  edges : ∀v z,d.edge (ix v).val (ix z).val=true ↔ G.Adj v z

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)
def idx (v:V) := (P.ix v).val
theorem idx_injective : Function.Injective P.idx := fun _ _ h=>P.injective (Fin.ext h)
noncomputable def code (C:Finset V) : List ℕ := (C.image P.idx).sort (·≤·)
theorem code_sorted (C:Finset V) : (P.code C).Pairwise (·<·) := (C.image P.idx).sortedLT_sort.pairwise
theorem code_nodup (C:Finset V) : (P.code C).Nodup := (code_sorted P C).imp Nat.ne_of_lt
theorem mem_code {C:Finset V} {i:ℕ} : i∈P.code C ↔ ∃v∈C,P.idx v=i := by simp [code]
theorem idx_mem {C:Finset V} {v:V} : P.idx v∈P.code C ↔ v∈C := by
  rw [mem_code];exact ⟨fun ⟨y,h,e⟩=>P.idx_injective e ▸ h,fun h=>⟨v,h,rfl⟩⟩
theorem code_injective : Function.Injective P.code := by
  intro C E h;ext v;rw [←P.idx_mem, h,P.idx_mem]
theorem code_length (C:Finset V) : (P.code C).length=C.card := by
  simp [code,Finset.card_image_of_injective _ P.idx_injective]
theorem code_single (v:V) : P.code {v}=[P.idx v] := by simp [code]
theorem code_empty : P.code ∅=[] := by simp [code]

theorem code_eq {C:Finset V} {s:List ℕ} (hs:s.Pairwise (·<·))
    (covers:∀i∈s,∃v,P.idx v=i) (mem:∀v,P.idx v∈s ↔ v∈C) : s=P.code C := by
  apply hs.eq_of_mem_iff (P.code_sorted C)
  intro i;constructor
  · intro hi;obtain ⟨v,rfl⟩:=covers i hi;exact P.idx_mem.mpr ((mem v).1 hi)
  · intro hi;obtain ⟨v,hv,rfl⟩:=P.mem_code.mp hi;exact (mem v).2 hv

theorem all_code : vertices d=P.code Finset.univ := by
  apply P.code_eq (List.pairwise_lt_range.filter _)
  · intro i h
    obtain ⟨hi,ok⟩:=List.mem_filter.mp h
    obtain ⟨v,hv⟩:=(P.active ⟨i,List.mem_range.mp hi⟩).1 ok
    exact ⟨v,congrArg Fin.val hv⟩
  · intro v;simp [vertices,idx,(P.ix v).isLt,(P.active (P.ix v)).2 ⟨v,rfl⟩]

theorem code_filter (C:Finset V) (p:ℕ→Bool) :
    (P.code C).filter p=P.code (C.filter (fun v=>p (P.idx v))) := by
  apply P.code_eq ((P.code_sorted C).filter p)
  · intro i hi;obtain ⟨v,_,e⟩:=P.mem_code.mp (List.mem_filter.mp hi).1;exact ⟨v,e⟩
  · intro v;simp [P.idx_mem]

theorem code_erase (C:Finset V) (v:V) : (P.code C).erase (P.idx v)=P.code (C.erase v) := by
  apply P.code_eq ((P.code_sorted C).erase _)
  · intro i hi;obtain ⟨v,_,e⟩:=P.mem_code.mp (List.mem_of_mem_erase hi);exact ⟨v,e⟩
  · intro u
    rw [(P.code_nodup C).mem_erase_iff,Finset.mem_erase,P.idx_mem]
    simp only [P.idx_injective.ne_iff]

theorem code_comp (S:Finset V) :
    (vertices d).filter (fun i=> !(P.code S).contains i)=P.code Sᶜ := by
  rw [P.all_code,P.code_filter];congr 1;ext v;simp [P.idx_mem]

theorem rim_code (C:Finset V) : rimOf d (P.code C)=P.code (boundary G C) := by
  unfold rimOf;rw [P.all_code,P.code_filter];congr 1;ext v
  have outside : (P.code C).contains (P.idx v)=false ↔ v∉C:=by simp [P.idx_mem]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Bool.and_eq_true,Bool.not_eq_true',outside,
    P.idx_mem,List.any_eq_true,mem_boundary]
  constructor
  · rintro ⟨outside,i,hi,he⟩
    obtain ⟨u,hu,rfl⟩:=P.mem_code.mp hi
    exact ⟨outside,u,hu,(P.edges u v).1 he⟩
  · rintro ⟨outside,u,hu,he⟩
    exact ⟨outside,P.idx u,P.idx_mem.mpr hu,(P.edges u v).2 he⟩
end Presentation
end StableMSR.Recovery.TightLanguage.Graph


namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V}
variable (P:Presentation d G)

theorem one_round [DecidableRel G.Adj] (U A:Finset V) (inc:A⊆U) :
    (P.code U).filter (fun i=>(P.code A).contains i || (P.code A).any (fun j=>d.edge j i)) =
      P.code (grow G Uᶜ A) := by
  rw [P.code_filter];congr 1;ext v
  have near : (∃j∈P.code A,d.edge j (P.idx v)=true) ↔ ∃u∈A,G.Adj u v := by
    constructor
    · rintro ⟨j,hj,e⟩;obtain ⟨u,hu,rfl⟩:=P.mem_code.mp hj
      exact ⟨u,hu,(P.edges u v).1 e⟩
    · rintro ⟨u,hu,e⟩;exact ⟨P.idx u,P.idx_mem.mpr hu,(P.edges u v).2 e⟩
  simp only [Finset.mem_filter,Bool.or_eq_true,List.contains_iff_mem,P.idx_mem,List.any_eq_true,near,
    mem_grow,Finset.mem_compl,not_not]
  constructor
  · rintro ⟨hu,(ha|nb)⟩
    · exact Or.inl ha
    · exact Or.inr ⟨hu,nb⟩
  · rintro (ha|⟨hu,nb⟩)
    · exact ⟨inc ha,Or.inl ha⟩
    · exact ⟨hu,Or.inr nb⟩

theorem rounds_eq [DecidableRel G.Adj] (U:Finset V) (v:V) (hv:v∈U) (m:ℕ) :
    (List.range m).foldl (fun seen _=>(P.code U).filter
      (fun i=>seen.contains i || seen.any (fun j=>d.edge j i))) [P.idx v] =
      P.code (flood G Uᶜ v m) := by
  have inside (k:ℕ) : flood G Uᶜ v k⊆U := by
    induction k with
    | zero=>simpa [flood] using hv
    | succ k ih=>
      intro x hx
      rcases (mem_grow G).mp hx with h|⟨h,_⟩
      · exact ih h
      · simpa using h
  induction m with
  | zero=>exact (P.code_single v).symm
  | succ m ih=>
    rw [List.range_succ,List.foldl_append,ih]
    exact P.one_round U _ (inside m)

theorem piece_geometry [DecidableRel G.Adj] (U:Finset V) (v:V) (hv:v∈U) :
    let C:=flood G Uᶜ v (Fintype.card V)
    pieceAt d (P.code U) (P.idx v)=P.code C ∧ IsFlap G Uᶜ C ∧ v∈C := by
  have size:Fintype.card V≤d.n:=by simpa using Fintype.card_le_of_injective P.ix P.injective
  refine ⟨?_,flood_flap G _ _ (by simpa using hv),flood_seed G _ _ _⟩
  unfold pieceAt
  rw [P.rounds_eq U v hv d.n,flood_stable G _ _ _ size]

theorem flap_unique {S C E:Finset V} (c:IsFlap G S C) (e:IsFlap G S E) {v:V}
    (hc:v∈C) (he:v∈E) : C=E := by
  have incl {C E:Finset V} (c:IsFlap G S C) (e:IsFlap G S E) (uc:v∈C) (ue:v∈E) : C⊆E := by
    intro z hz
    obtain ⟨p,hp⟩:=c.connected.2 v uc z hz
    have path {u t:V} (p:G.Walk u t) (start:u∈E) (safe:∀z∈p.support,z∉S) : t∈E := by
      induction p with
      | nil=>exact start
      | @cons a b d ab p ih=>
        apply ih (e.closed a start b ab (safe b (by simp [p.start_mem_support])))
        intro z h;exact safe z (by simp [h])
    exact path p ue (fun z h bad=>Finset.disjoint_left.mp c.avoids bad (hp _ h))
  exact Finset.Subset.antisymm (incl c e hc he) (incl e c he hc)

theorem piece_of_flap [DecidableRel G.Adj] {U C:Finset V} (hc:IsFlap G Uᶜ C) (v:V) (hv:v∈C) :
    pieceAt d (P.code U) (P.idx v)=P.code C := by
  have hu:v∈U:=by by_contra h;exact Finset.disjoint_left.mp hc.avoids (Finset.mem_compl.mpr h) hv
  obtain ⟨eq,flap,hit⟩:=P.piece_geometry U v hu
  exact eq.trans (congrArg P.code (flap_unique flap hc hit hv))

theorem parts_spec (vs s:List ℕ) : s∈parts d vs ↔
    ∃i∈vs,pieceAt d vs i=s ∧ s.head?=some i := by
  simp only [parts,List.mem_filterMap]
  constructor
  · rintro ⟨i,hi,h⟩
    split at h
    · rename_i eq;obtain rfl:=Option.some.inj h;exact ⟨i,hi,rfl,beq_iff_eq.mp eq⟩
    · contradiction
  · rintro ⟨i,hi,rfl,head⟩
    exact ⟨i,hi,by simp [head]⟩

theorem parts_distinct (vs:List ℕ) (hn:vs.Nodup) : (parts d vs).Nodup := by
  unfold parts
  apply List.Nodup.filterMap _ hn
  intro i j s hi hj
  have head (a:ℕ) (h:s∈(if (pieceAt d vs a).head? == some a then some (pieceAt d vs a) else none)) :
      s.head?=some a := by
    split at h
    · rename_i eq;have es:pieceAt d vs a=s:=Option.some.inj h;rw [←es];exact beq_iff_eq.mp eq
    · contradiction
  exact Option.some.inj ((head i hi).symm.trans (head j hj))

theorem parts_geometry (U:Finset V) (s:List ℕ) :
    s∈parts d (P.code U) ↔ ∃C:Finset V,IsFlap G Uᶜ C ∧ P.code C=s := by
  classical
  rw [parts_spec];constructor
  · rintro ⟨i,hi,rfl,_⟩
    obtain ⟨v,hv,rfl⟩:=P.mem_code.mp hi
    obtain ⟨eq,hc,_⟩:=P.piece_geometry U v hv
    exact ⟨_,hc,eq.symm⟩
  · rintro ⟨C,hc,rfl⟩
    obtain ⟨v,hv⟩:=hc.connected.1
    let vs:=P.code C
    have hn:vs≠[]:=List.ne_nil_of_mem (P.idx_mem.mpr hv)
    let i:=vs.head hn
    have head:vs.head?=some i:=List.head?_eq_some_head hn
    obtain ⟨z,hz,ez⟩:=P.mem_code.mp (List.mem_of_head? head)
    have hu:z∈U:=by by_contra h;exact Finset.disjoint_left.mp hc.avoids (Finset.mem_compl.mpr h) hz
    exact ⟨P.idx z,P.idx_mem.mpr hu,P.piece_of_flap hc z hz,ez ▸ head⟩
end Presentation
end StableMSR.Recovery.TightLanguage.Graph


namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V}
variable (P:Presentation d G)

def fromCode (s:List ℕ) : Finset V := Finset.univ.filter (fun v=>s.contains (P.idx v))
theorem from_code (C:Finset V) : P.fromCode (P.code C)=C := by
  ext v;simp [fromCode,P.idx_mem]

noncomputable def pieces (U:Finset V) := (parts d (P.code U)).map P.fromCode

theorem restore_piece {U:Finset V} {s:List ℕ} (hs:s∈parts d (P.code U)) : P.code (P.fromCode s)=s := by
  obtain ⟨C,_,rfl⟩:=(P.parts_geometry U s).1 hs
  rw [P.from_code]

theorem pieces_code (U:Finset V) : (P.pieces U).map P.code=parts d (P.code U) := by
  unfold pieces;rw [List.map_map]
  exact List.map_congr_left (g:=id) (fun s hs=>P.restore_piece hs) |>.trans (List.map_id ..)

theorem mem_piece {U C:Finset V} : C∈P.pieces U ↔ IsFlap G Uᶜ C := by
  unfold pieces;constructor
  · intro h;obtain ⟨s,hs,rfl⟩:=List.mem_map.mp h
    obtain ⟨C,hc,rfl⟩:=(P.parts_geometry U _).1 hs
    simpa only [P.from_code] using hc
  · intro hc
    exact List.mem_map.mpr ⟨P.code C,(P.parts_geometry U _).2 ⟨C,hc,rfl⟩,P.from_code C⟩

theorem pieces_nodup (U:Finset V) : (P.pieces U).Nodup := by
  apply List.Nodup.of_map (f:=P.code)
  rw [P.pieces_code];exact parts_distinct _ (P.code_nodup U)

theorem root_pieces : (P.pieces Finset.univ).toFinset=PartialDecompositions.components G ∅ := by
  ext C;simp [P.mem_piece,PartialDecompositions.mem_components]

theorem piece_rim_empty {C:Finset V} (hc:C∈P.pieces Finset.univ) : boundary G C=∅ := by
  have flap:IsFlap G ∅ C:=by simpa using P.mem_piece.mp hc
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨out,v,hv,edge⟩:=mem_boundary.mp hz
  exact out (flap.closed v hv z edge (Finset.notMem_empty _))

theorem different_pieces {U C E:Finset V} (hc:C∈P.pieces U) (he:E∈P.pieces U) (ne:C≠E) : Disjoint C E :=
  Finset.disjoint_left.mpr (fun _ h k=>ne (flap_unique (P.mem_piece.mp hc) (P.mem_piece.mp he) h k))

theorem children_geometry {S C:Finset V} (flap:IsFlap G S C) (v:V) (hv:v∈C) (E:Finset V) :
    E∈P.pieces (C.erase v) ↔ E∈children G (insert v S) C := by
  rw [P.mem_piece,mem_children]
  constructor
  · intro e
    have inc:E⊆C.erase v:=by
      intro z hz;by_contra bad;exact Finset.disjoint_left.mp e.avoids (Finset.mem_compl.mpr bad) hz
    refine ⟨⟨e.connected,Finset.disjoint_left.mpr ?_,?_⟩,fun _ h=>Finset.mem_of_mem_erase (inc h)⟩
    · intro z hz he
      rcases Finset.mem_insert.mp hz with rfl|hs
      · exact (Finset.mem_erase.mp (inc he)).1 rfl
      · exact Finset.disjoint_left.mp flap.avoids hs (Finset.mem_of_mem_erase (inc he))
    · intro z hz u zu hu
      have uS:u∉S:=fun hs=>hu (Finset.mem_insert_of_mem hs)
      have uC:=flap.closed z (Finset.mem_of_mem_erase (inc hz)) u zu uS
      exact e.closed z hz u zu (by simpa using Finset.mem_erase.mpr ⟨fun eq=>hu (Finset.mem_insert.mpr (Or.inl eq)),uC⟩)
  · rintro ⟨e,inc⟩
    refine ⟨e.connected,Finset.disjoint_left.mpr ?_,?_⟩
    · intro z hz he
      exact Finset.mem_compl.mp hz (Finset.mem_erase.mpr ⟨fun eq=>Finset.disjoint_left.mp e.avoids (Finset.mem_insert.mpr (Or.inl eq)) he,inc he⟩)
    · intro z hz u zu hu
      have hU:u∈C.erase v:=by simpa using hu
      apply e.closed z hz u zu
      intro t;rcases Finset.mem_insert.mp t with rfl|t
      · exact (Finset.mem_erase.mp hU).1 rfl
      · exact Finset.disjoint_left.mp flap.avoids t (Finset.mem_of_mem_erase hU)

theorem parts_children {S C:Finset V} (flap:IsFlap G S C) (v:V) (hv:v∈C) :
    (P.pieces (C.erase v)).map P.code=parts d ((P.code C).erase (P.idx v)) ∧
      (P.pieces (C.erase v)).toFinset=children G (insert v S) C := by
  refine ⟨by rw [P.code_erase,P.pieces_code],?_⟩;ext E;simp [P.children_geometry flap v hv]
end Presentation
end StableMSR.Recovery.TightLanguage.Graph


namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

def available {A:Type} (o:Option (Lang A)) : Lang A := o.getD (fun _=>False)
def joined {A I:Type} (f:I→Option (Lang A)) (xs:List I) : Lang A :=
  match xs.mapM (m:=Option) f with
  | some ls=>concatenate ls
  | none=>fun _=>False

theorem concatenate_cons {A:Type} (L:Lang A) (ls:List (Lang A)) :
    concatenate (L::ls)=product L (concatenate ls) := by
  unfold concatenate;rw [List.foldl_cons,product_unit_left,fold_concatenate];rfl

theorem joined_cons {I A:Type} (f:I→Option (Lang A)) (i:I) (xs:List I) (s:List A) :
    joined f (i::xs) s ↔ product (available (f i)) (joined f xs) s := by
  cases ei:f i <;> cases es:xs.mapM (m:=Option) f <;>
    simp [joined,available,List.mapM_cons,ei,es,concatenate_cons,product]

theorem joined_iff {I A:Type} [DecidableEq I] (f:I→Option (Lang A)) (xs:List I) (hn:xs.Nodup) (s:List A) :
    joined f xs s ↔ ∃out:I→List A,(∀i∈xs,available (f i) (out i)) ∧ s=xs.flatMap out := by
  induction xs generalizing s with
  | nil=>
    change s=[] ↔ _
    exact ⟨fun h=>⟨fun _=>[],by simp,h⟩,fun ⟨_,_,h⟩=>h⟩
  | cons i xs ih=>
    have fresh:=(List.nodup_cons.mp hn).1
    have nodup:=(List.nodup_cons.mp hn).2
    rw [joined_cons];constructor
    · rintro ⟨x,t,hx,ht,rfl⟩
      obtain ⟨g,ok,rfl⟩:=(ih nodup t).1 ht
      let out:=Function.update g i x
      have rest (k:I) (hk:k∈xs) : out k=g k:=Function.update_of_ne (by rintro rfl;exact fresh hk) .. 
      refine ⟨out,?_,?_⟩
      · intro k hk;rcases List.mem_cons.mp hk with rfl|hk
        · simpa [out] using hx
        · rw [rest k hk];exact ok k hk
      · rw [List.flatMap_cons,show out i=x from Function.update_self ..]
        congr 1;exact List.flatMap_congr (fun k hk=>(rest k hk).symm)
    · rintro ⟨out,ok,rfl⟩
      exact ⟨out i,xs.flatMap out,ok i (by simp),(ih nodup _).2 ⟨out,fun k hk=>ok k (by simp [hk]),rfl⟩,rfl⟩

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)
noncomputable def rootEntry (w:ℕ) (C:Finset V) := lookup (build wordAlgebra d w).2 (P.code C) []

theorem root_split (w:ℕ) (s:List Letter) : traces d w s ↔ ∃f:Finset V→List Letter,
    (∀C∈P.pieces Finset.univ,available (P.rootEntry w C) (f C)) ∧ s=(P.pieces Finset.univ).flatMap f := by
  rw [←joined_iff (P.rootEntry w) (P.pieces Finset.univ) (P.pieces_nodup _)]
  unfold traces scan joined rootEntry
  dsimp only
  rw [P.all_code,←P.pieces_code,List.mapM_map];simp only [Function.comp_def]
  cases h:(P.pieces Finset.univ).mapM (m:=Option) (fun C=>lookup (build wordAlgebra d w).2 (P.code C) []) <;> rfl
end Presentation
end StableMSR.Recovery.TightLanguage.Graph


namespace StableMSR.Recovery.TightLanguage.Graph
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery
def RowLaw : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (d : SingleCircuit.Instance) (ix : V → Fin d.n)
    (_inj : Function.Injective ix) (G : SimpleGraph V)
    (_active : ∀ i : Fin d.n, d.active i.val = true ↔ ∃ v, ix v = i)
    (_edges : ∀ v z, d.edge (ix v).val (ix z).val = true ↔ G.Adj v z)
    (w m : ℕ) (C : Finset V) (a : ℕ → ℕ)
    (_flap : Havens.IsFlap G (DecompositionSearch.boundary G C) C)
    (_space : (DecompositionSearch.boundary G C).card ≤ w) (_depth : C.card ≤ m)
    (_valid : ∀ v ∈ DecompositionSearch.boundary G C, a (ix v).val ∈ d.menu (ix v).val),
    let code := fun K : Finset V => (K.image (fun v => (ix v).val)).sort (· ≤ ·)
    let S := DecompositionSearch.boundary G C
    let key := (code S).map (fun j => (j,a j))
    let table := (TightLanguage.build TightLanguage.wordAlgebra d w).2
    let accepts := (TightLanguage.lookup table (code C) key).getD (fun _ => False)
    let dom := fun v => (d.menu (ix v).val).toFinset
    let test := fun v z c k => d.test (ix v).val (ix z).val c k = true
    let tag := fun t : V × ℕ => ((ix t.1).val,t.2)
    let runs := SingleSearch.run G dom test w m S C (fun v => a (ix v).val)
    (∀ t, accepts t → ∃ l : List (V × ℕ), l.map tag = t ∧ (l.map Prod.fst).Nodup ∧
      (l.map Prod.fst).toFinset = C ∧ runs l.toFinset) ∧
    ∀ O, runs O → ∃ l : List (V × ℕ), accepts (l.map tag) ∧ l.toFinset = O
end StableMSR.Recovery.TightLanguage.Graph

namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

theorem cuts_exact (vs:List ℕ) (w:ℕ) (s:List ℕ) :
    s∈cuts vs w ↔ s.Sublist vs ∧ s.length≤w := by
  induction vs generalizing w s with
  | nil=>cases s <;> simp [cuts]
  | cons v vs ih=>
    cases w with
    | zero=>cases s <;> simp [cuts]
    | succ w=>
      simp only [cuts,List.mem_append,List.mem_map,ih]
      constructor
      · rintro (⟨h,size⟩|⟨r,⟨h,size⟩,rfl⟩)
        · exact ⟨h.cons v,size⟩
        · exact ⟨h.cons_cons v,by simpa using size⟩
      · rintro ⟨h,size⟩
        cases h with
        | cons _ h=>exact Or.inl ⟨h,size⟩
        | cons_cons _ h=>exact Or.inr ⟨_,⟨h,by simpa using size⟩,rfl⟩

def bindCodes (s:List ℕ) (a:ℕ→ℕ) : Assignment := s.map (fun i=>(i,a i))

theorem bindings_mem (d:Instance) (s:List ℕ) (a:ℕ→ℕ) :
    bindCodes s a∈assignments d s ↔ ∀i∈s,a i∈d.menu i := by
  induction s with
  | nil=>simp [bindCodes,assignments]
  | cons i is ih=>
    simp only [bindCodes,List.map_cons,assignments,List.mem_flatMap,List.mem_map,List.cons.injEq,Prod.mk.injEq,true_and]
    constructor
    · rintro ⟨x,hx,b,hb,eq,rfl⟩;subst x
      exact List.forall_mem_cons.mpr ⟨hx,ih.mp hb⟩
    · intro h;obtain ⟨hx,ht⟩:=List.forall_mem_cons.mp h
      exact ⟨a i,hx,bindCodes is a,ih.mpr ht,rfl,rfl⟩

theorem binding_value (s:List ℕ) (a:ℕ→ℕ) (i:ℕ) (hi:i∈s) : value (bindCodes s a) i=a i := by
  induction s with
  | nil=>contradiction
  | cons j js ih=>
    by_cases eq:j=i
    · subst i;simp [value,bindCodes]
    · have rest:i∈js:=by simpa [Ne.symm eq] using hi
      simpa [value,bindCodes,List.find?_cons,eq] using ih rest

theorem restrict_binding {s t:List ℕ} (sub:∀j∈t,j∈s) (a:ℕ→ℕ) :
    restricted t (bindCodes s a)=bindCodes t a := by
  apply List.map_congr_left
  intro j hj;rw [binding_value s a j (sub j hj)]

theorem bindings_exhaust (d:Instance) (s:List ℕ) (distinct:s.Nodup) (b:Assignment) (hb:b∈assignments d s) :
    ∃a:ℕ→ℕ,b=bindCodes s a ∧ ∀i∈s,a i∈d.menu i := by
  induction s generalizing b with
  | nil=>
    have eq:b=[]:=by simpa [assignments] using hb
    subst b;exact ⟨fun _=>0,rfl,by simp⟩
  | cons i is ih=>
    obtain ⟨x,hx,hit⟩:=List.mem_flatMap.mp hb
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hit
    obtain ⟨f,rfl,valid⟩:=ih (List.nodup_cons.mp distinct).2 c hc
    let a:=Function.update f i x
    have same (j:ℕ) (h:j∈is) : a j=f j:=Function.update_of_ne (by rintro rfl;exact (List.nodup_cons.mp distinct).1 h) ..
    refine ⟨a,?_,?_⟩
    · unfold bindCodes;rw [List.map_cons,show a i=x from Function.update_self ..]
      congr 1;apply List.map_congr_left;intro j hj;rw [same j hj]
    · rw [List.forall_mem_cons];exact ⟨by simpa [a] using hx,fun j h=>same j h ▸ valid j h⟩

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

theorem good_cut (S:Finset V) (w:ℕ) (hw:S.card≤w) : P.code S∈cuts (vertices d) (min w d.n) := by
  rw [cuts_exact,P.code_length,P.all_code,Nat.le_min]
  have length:Fintype.card V≤d.n:=by simpa using Fintype.card_le_of_injective P.ix P.injective
  refine ⟨?_,hw,(Finset.card_le_univ S).trans length⟩
  apply List.sublist_of_subperm_of_pairwise _ (P.code_sorted S) (P.code_sorted Finset.univ)
  apply List.subperm_of_subset (P.code_nodup S)
  intro i hi
  obtain ⟨v,_,rfl⟩:=P.mem_code.mp hi
  exact P.idx_mem.mpr (Finset.mem_univ v)

theorem layer_contains (w:ℕ) (C:Finset V) (a:ℕ→ℕ) (hC:IsFlap G (boundary G C) C)
    (small:(boundary G C).card≤w) (valid:∀v∈boundary G C,a (P.idx v)∈d.menu (P.idx v)) :
    let S:=boundary G C
    P.code S∈cuts (vertices d) (min w d.n) ∧ P.code C∈keysFor d (vertices d) (P.code S) ∧
      rimOf d (P.code C)=P.code S ∧ bindCodes (P.code S) a∈assignments d (P.code S) := by
  refine ⟨P.good_cut _ w small,?_,P.rim_code C,(bindings_mem ..).2 ?_⟩
  · unfold keysFor;rw [P.code_comp,P.parts_geometry]
    exact ⟨C,by simpa using hC,rfl⟩
  · intro i hi;obtain ⟨v,hv,rfl⟩:=P.mem_code.mp hi;exact valid v hv
end Presentation
end StableMSR.Recovery.TightLanguage.Graph


namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

/-- The chronological list of keys installed by one component-size pass. -/
def layerKeys (d:Instance) (w k:ℕ) : List Key :=
  let vs:=vertices d
  (cuts vs (min w d.n)).flatMap fun s=>(keysFor d vs s).flatMap fun c=>
    if c.length==k+1 && rimOf d c==s then (assignments d s).map fun a=>(c,a) else []

theorem layer_mem (d:Instance) (w k:ℕ) (c:List ℕ) (a:Assignment) :
    (c,a)∈layerKeys d w k ↔ c.length=k+1 ∧ rimOf d c∈cuts (vertices d) (min w d.n) ∧
      c∈keysFor d (vertices d) (rimOf d c) ∧ a∈assignments d (rimOf d c) := by
  unfold layerKeys;simp only [List.mem_flatMap]
  constructor
  · rintro ⟨s,hs,t,ht,occ⟩
    split at occ
    · rename_i test
      simp only [Bool.and_eq_true,beq_iff_eq] at test
      obtain ⟨size,rfl⟩:=test
      obtain ⟨b,hb,eq⟩:=List.mem_map.mp occ
      cases eq;exact ⟨size,hs,ht,hb⟩
    · contradiction
  · rintro ⟨size,hs,hc,ha⟩
    exact ⟨rimOf d c,hs,c,hc,by simp [size,ha]⟩

abbrev WordTable := Table (Lang Letter)
def writeRow (d:Instance) (tab:WordTable) (k:Key) : WordTable :=
  (k,(collect wordAlgebra d tab k.1 k.2 ()).2)::tab
def sheet (d:Instance) (w m:ℕ) : WordTable :=
  (List.range m).foldl (fun tab k=>(layerKeys d w k).foldl (writeRow d) tab) []

theorem sheet_succ (d:Instance) (w m:ℕ) : sheet d w (m+1)=(layerKeys d w m).foldl (writeRow d) (sheet d w m) := by
  simp [sheet,List.range_succ,List.foldl_append]

theorem build_sheet (d:Instance) (w:ℕ) : (build wordAlgebra d w).2=sheet d w d.n := by
  let emit:=fun (p:Unit×WordTable) (k:Key)=>install wordAlgebra d k.1 k.2 p
  let layer:=fun (p:Unit×WordTable) (k:ℕ)=>(layerKeys d w k).foldl emit p
  have eq:build wordAlgebra d w=(List.range d.n).foldl layer ((),[]) := by
    unfold build;dsimp only;congr 1
    funext p k;unfold layer layerKeys
    simp only [List.foldl_flatMap]
    congr 1;funext z s;congr 1;funext t c
    unfold visit;split
    · simp only [List.foldl_map];rfl
    · rfl
  rw [eq];unfold sheet;symm
  apply List.foldl_hom (g₁:=layer) (init:=((),[])) Prod.snd
  intro z k
  apply List.foldl_hom (g₁:=emit) (init:=z) Prod.snd
  intro s key;rfl

theorem lookup_row_iff (t:WordTable) (k:Key) : (lookup t k.1 k.2).isSome ↔ k∈t.map Prod.fst := by
  induction t with
  | nil=>simp [lookup]
  | cons row rs ih=>
    by_cases e:row.1=k
    · simp [lookup,List.find?_cons,e]
    · have ne:k≠row.1:=Ne.symm e
      simpa [lookup,List.find?_cons,e,ne] using ih

theorem written_keys (d:Instance) (keys:List Key) (t:WordTable) :
    ((keys.foldl (writeRow d) t).map Prod.fst)=keys.reverse ++ t.map Prod.fst := by
  induction keys generalizing t with
  | nil=>rfl
  | cons k ks ih=>simp [List.foldl_cons,ih,writeRow,List.append_assoc]

theorem sheet_has (d:Instance) (w m:ℕ) (key:Key) :
    (lookup (sheet d w m) key.1 key.2).isSome ↔ ∃k < m,key∈layerKeys d w k := by
  rw [lookup_row_iff]
  induction m with
  | zero=>simp [sheet]
  | succ m ih=>
    rw [sheet_succ,written_keys,List.mem_append,List.mem_reverse,ih]
    constructor
    · rintro (h|⟨k,hk,h⟩)
      · exact ⟨m,Nat.lt_succ_self _,h⟩
      · exact ⟨k,Nat.lt.step hk,h⟩
    · rintro ⟨k,hk,h⟩;rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with a|rfl
      · exact Or.inr ⟨k,a,h⟩
      · exact Or.inl h

theorem has_iff (d:Instance) (w m:ℕ) (c:List ℕ) (a:Assignment) :
    (lookup (sheet d w m) c a).isSome ↔ 0<c.length ∧ c.length ≤ m ∧
      rimOf d c∈cuts (vertices d) (min w d.n) ∧ c∈keysFor d (vertices d) (rimOf d c) ∧
      a∈assignments d (rimOf d c) := by
  rw [show (lookup (sheet d w m) c a).isSome ↔ _ from sheet_has d w m (c,a)]
  constructor
  · rintro ⟨k,hk,h⟩
    obtain ⟨sz,row⟩:=(layer_mem d w k c a).1 h;exact ⟨by omega,by omega,row⟩
  · rintro ⟨h,small,row⟩
    exact ⟨c.length-1,by omega,(layer_mem ..).2 ⟨by omega,row⟩⟩

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

theorem row_present (w m:ℕ) (C:Finset V) (a:ℕ→ℕ) (flap:IsFlap G (boundary G C) C)
    (width:(boundary G C).card≤w) (depth:C.card ≤ m)
    (valid:∀v∈boundary G C,a (P.idx v)∈d.menu (P.idx v)) :
    (lookup (sheet d w m) (P.code C) (bindCodes (P.code (boundary G C)) a)).isSome := by
  obtain ⟨cut,comp,eq,good⟩:=P.layer_contains w C a flap width valid
  rw [has_iff,P.code_length,eq];exact ⟨Finset.card_pos.mpr flap.connected.1,depth,cut,comp,good⟩
end Presentation
end StableMSR.Recovery.TightLanguage.Graph


namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

theorem fold_congr_mem {A I:Type} {f g:A→I→A} (xs:List I) (a:A) (h:∀z i,i∈xs → f z i=g z i) :
    xs.foldl f a=xs.foldl g a := by
  induction xs generalizing a with
  | nil=>rfl
  | cons i is ih=>
    simp only [List.foldl_cons];rw [h a i (by simp)];exact ih _ (fun z j hj=>h z j (by simp [hj]))

theorem queries_congr {A I:Type} {f g:I→Option A} (xs:List I) (h:∀i∈xs,f i=g i) :
    xs.mapM f=xs.mapM g := by
  induction xs with
  | nil=>rfl
  | cons i is ih=>simp only [List.mapM_cons,h i (by simp),ih (fun j hj=>h j (by simp [hj]))]

theorem child_shorter (d:Instance) (nonempty:0<d.n) {c:List ℕ} {v:ℕ} (pivot:v∈c)
    {t:List ℕ} (ht:t∈parts d (c.erase v)) : t.length<c.length := by
  obtain ⟨j,_,rfl,_⟩:=Presentation.parts_spec (d:=d) (c.erase v) t |>.1 ht
  obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt nonempty)
  unfold pieceAt;rw [hk,List.range_succ,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil]
  have bound:=List.length_erase_of_mem pivot
  have cpos:=List.length_pos_of_mem pivot
  exact Nat.lt_of_le_of_lt (List.length_filter_le ..) (by omega)

def AgreeBelow (m:ℕ) (t u:WordTable) := ∀c a,c.length ≤ m → lookup t c a=lookup u c a

theorem collect_congr (d:Instance) (alive:0<d.n) (c:List ℕ) (a:Assignment) (t u:WordTable)
    (same:∀s b,s.length<c.length → lookup t s b=lookup u s b) :
    collect wordAlgebra d t c a ()=collect wordAlgebra d u c a () := by
  unfold collect;apply fold_congr_mem
  intro z v hv;apply fold_congr_mem
  intro y x _;unfold offer
  have eq:refs d t c v ((v,x)::a)=refs d u c v ((v,x)::a):=by
    apply queries_congr;intro s hs;apply same;exact child_shorter d alive hv hs
  dsimp only;rw [eq]

theorem lookup_cons (t:WordTable) (k:Key) (v:Lang Letter) (c:List ℕ) (a:Assignment) :
    lookup ((k,v)::t) c a=if k=(c,a) then some v else lookup t c a := by
  by_cases eq:k=(c,a) <;> simp [lookup,List.find?_cons,eq]

def frozen (d:Instance) (t:WordTable) (k:Key) : Key×Lang Letter :=
  (k,(collect wordAlgebra d t k.1 k.2 ()).2)

theorem frozen_layer (d:Instance) (alive:0<d.n) (k:ℕ) (old cur:WordTable) (ks:List Key)
    (sizes:∀p∈ks,p.1.length=k+1) (same:AgreeBelow k cur old) :
    ks.foldl (writeRow d) cur=(ks.map (frozen d old)).reverse ++ cur := by
  induction ks generalizing cur with
  | nil=>rfl
  | cons key ks ih=>
    have size:=sizes key (by simp)
    have v:=collect_congr d alive key.1 key.2 cur old (fun c a h=>same c a (by omega))
    have next:AgreeBelow k (writeRow d cur key) old := by
      intro c a h
      have ne:key≠(c,a):=by intro e;have l:=congrArg (fun z:Key=>z.1.length) e;dsimp only at l;omega
      unfold writeRow;rw [lookup_cons,if_neg ne];exact same c a h
    rw [List.foldl_cons,ih (writeRow d cur key) (fun p hp=>sizes p (by simp [hp])) next]
    simp [frozen,writeRow,v,List.append_assoc]

theorem lookup_frozen (d:Instance) (old cur:WordTable) (ks:List Key) (c:List ℕ) (a:Assignment) :
    lookup (ks.map (frozen d old) ++ cur) c a =
      if (c,a)∈ks then some (collect wordAlgebra d old c a ()).2 else lookup cur c a := by
  induction ks with
  | nil=>simp
  | cons key ks ih=>
    by_cases eq:key=(c,a)
    · subst key;simp [frozen,lookup_cons]
    · simp [frozen,lookup_cons,eq,Ne.symm eq,ih]

theorem layer_lookup (d:Instance) (alive:0<d.n) (w k:ℕ) (c:List ℕ) (a:Assignment) :
    lookup (sheet d w (k+1)) c a =
      if (c,a)∈layerKeys d w k then some (collect wordAlgebra d (sheet d w k) c a ()).2 else lookup (sheet d w k) c a := by
  have sizes (p:Key) (hp:p∈layerKeys d w k) : p.1.length=k+1 := (layer_mem d w k p.1 p.2).1 hp |>.1
  rw [sheet_succ,frozen_layer d alive k _ _ _ sizes (fun _ _ _=>rfl),←List.map_reverse,lookup_frozen];simp only [List.mem_reverse]

theorem sheet_stable (d:Instance) (alive:0<d.n) (w k m:ℕ) (km:k ≤ m) :
    AgreeBelow k (sheet d w m) (sheet d w k) := by
  obtain ⟨r,rfl⟩:=Nat.exists_eq_add_of_le km;clear km
  induction r with
  | zero=>exact fun _ _ _=>rfl
  | succ r ih=>
    intro c a h
    have skip:(c,a)∉layerKeys d w (k+r):=by intro hx;have:=((layer_mem ..).1 hx).1;omega
    rw [←Nat.add_assoc,layer_lookup d alive w (k+r),if_neg skip];exact ih c a h

/-- Each present entry of the final table is precisely the union of its legal
pivot productions using final child entries. Child lookups always decrease size. -/
theorem row_equation (d:Instance) (w:ℕ) (c:List ℕ) (a:Assignment)
    (registered:(lookup (build wordAlgebra d w).2 c a).isSome) :
    lookup (build wordAlgebra d w).2 c a=some (collect wordAlgebra d (build wordAlgebra d w).2 c a ()).2 := by
  rw [build_sheet] at *
  obtain ⟨pos,bound,_⟩:=(has_iff d w d.n c a).1 registered
  have alive:0<d.n:=by omega
  obtain ⟨k,hk,hit⟩:=(sheet_has d w d.n (c,a)).1 registered
  have sz:=((layer_mem ..).1 hit).1
  rw [sheet_stable d alive w (k+1) d.n hk c a (by omega),layer_lookup d alive w k,if_pos hit]
  have eq:=collect_congr d alive c a (sheet d w d.n) (sheet d w k)
    (fun s b h=>sheet_stable d alive w k d.n (Nat.le_of_lt hk) s b (by omega))
  rw [eq]
end StableMSR.Recovery.TightLanguage.Graph


namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

def production (d:Instance) (tab:WordTable) (c:List ℕ) (a:Assignment) (v x:ℕ) (s:List Letter) :=
  let b:=(v,x)::a
  localOK d b=true ∧ ∃tail,joined (fun t=>lookup tab t (restricted (rimOf d t) b))
    (parts d (c.erase v)) tail ∧ s=(v,x)::tail

theorem offer_words (d:Instance) (tab:WordTable) (c:List ℕ) (a:Assignment) (v x:ℕ) (z:Unit×Lang Letter) (s:List Letter) :
    (offer wordAlgebra d tab c a v x z).2 s ↔ z.2 s ∨ production d tab c a v x s := by
  let b:=(v,x)::a
  by_cases good:localOK d b=true
  · unfold offer production;dsimp only
    have ok:localOK d ((v,x)::a)=true:=good
    simp only [ok,if_true,true_and]
    unfold joined refs
    cases hit:(parts d (c.erase v)).mapM (m:=Option) (fun t=>lookup tab t (restricted (rimOf d t) ((v,x)::a))) <;> simp [wordAlgebra]
  · have no:localOK d ((v,x)::a)≠true:=good
    simp [offer,production,no]

theorem fold_accept {I S:Type} (f:S→I→S) (P:S→Prop) (Q:I→Prop)
    (step:∀z i,P (f z i) ↔ P z ∨ Q i) (xs:List I) (z:S) :
    P (xs.foldl f z) ↔ P z ∨ ∃i∈xs,Q i := by
  induction xs generalizing z with
  | nil=>simp
  | cons i is ih=>simp only [List.foldl_cons,ih,step,List.mem_cons];grind

theorem collect_words (d:Instance) (tab:WordTable) (c:List ℕ) (a:Assignment) (s:List Letter) :
    (collect wordAlgebra d tab c a ()).2 s ↔ ∃v∈c,∃x∈d.menu v,production d tab c a v x s := by
  let P:=fun z:Unit×Lang Letter=>z.2 s
  let Q:=production d tab c a
  let f:=fun (v:ℕ) (z:Unit×Lang Letter) (x:ℕ)=>offer wordAlgebra d tab c a v x z
  let g:=fun (z:Unit×Lang Letter) (v:ℕ)=>(d.menu v).foldl (f v) z
  have inner (z:Unit×Lang Letter) (v:ℕ) : P (g z v) ↔ P z ∨ ∃x∈d.menu v,Q v x s :=
    fold_accept (f v) P (fun x=>Q v x s) (fun z x=>offer_words ..) .. 
  have result:=fold_accept g P (fun v=>∃x∈d.menu v,Q v x s) inner c ((),wordAlgebra.fail)
  exact result.trans (Iff.of_eq (false_or _))

namespace Presentation
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

noncomputable def accepts (w:ℕ) (C:Finset V) (a:ℕ→ℕ) : Lang Letter :=
  available (lookup (build wordAlgebra d w).2 (P.code C) (bindCodes (P.code (boundary G C)) a))
def tag (z:V×ℕ) : Letter := (P.idx z.1,z.2)
def menu (v:V) := (d.menu (P.idx v)).toFinset
def test (u v:V) (a b:ℕ) := d.test (P.idx u) (P.idx v) a b=true
def decoded (a:ℕ→ℕ) (v:V) := a (P.idx v)

theorem width_of_word {w:ℕ} {C:Finset V} {a:ℕ→ℕ} {s:List Letter} (h:P.accepts w C a s) :
    (boundary G C).card≤w := by
  unfold accepts at h;rw [build_sheet] at h
  have present {o:Option (Lang Letter)} (hh:available o s) : o.isSome:=by cases o with
    | none=>exact False.elim hh
    | some _=>rfl
  have hc:=((has_iff ..).1 (present h)).2.2.1
  have len:=(cuts_exact ..).1 hc |>.2
  rw [P.rim_code,P.code_length] at len;exact len.trans (Nat.min_le_left ..)

theorem row_choices (w:ℕ) (C:Finset V) (a:ℕ→ℕ) (flap:IsFlap G (boundary G C) C)
    (width:(boundary G C).card≤w) (valid:∀v∈boundary G C,a (P.idx v)∈d.menu (P.idx v)) (s:List Letter) :
    P.accepts w C a s ↔ ∃v∈C,∃x∈d.menu (P.idx v),
      production d (build wordAlgebra d w).2 (P.code C) (bindCodes (P.code (boundary G C)) a) (P.idx v) x s := by
  have bound:C.card≤d.n:=(Finset.card_le_univ C).trans (by simpa using Fintype.card_le_of_injective P.ix P.injective)
  have ok:=P.row_present w d.n C a flap width bound valid
  rw [←build_sheet] at ok
  unfold accepts;rw [row_equation d w _ _ ok]
  change (collect wordAlgebra d _ _ _ ()).2 s ↔ _
  rw [collect_words]
  constructor
  · rintro ⟨i,hi,x,hx,h⟩;obtain ⟨v,hv,rfl⟩:=P.mem_code.mp hi;exact ⟨v,hv,x,hx,h⟩
  · rintro ⟨v,hv,x,hx,h⟩;exact ⟨P.idx v,P.idx_mem.mpr hv,x,hx,h⟩
end Presentation
end StableMSR.Recovery.TightLanguage.Graph


namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

namespace Presentation
open WindowCuts
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

def newLabel (a:ℕ→ℕ) (v:V) (x:ℕ) := Function.update a (P.idx v) x

theorem decoded_new (a:ℕ→ℕ) (v:V) (x:ℕ) :
    P.decoded (P.newLabel a v x)=Function.update (P.decoded a) v x := by
  funext u;by_cases eq:u=v
  · subst u;simp [decoded,newLabel]
  · simp [decoded,newLabel,eq,P.idx_injective.ne eq,Function.update_of_ne]

theorem labelled_bag (S:Finset V) (v:V) (fresh:v∉S) (x:ℕ) (a:ℕ→ℕ) (z:Letter) :
    z∈(P.idx v,x)::bindCodes (P.code S) a ↔
    ∃u∈insert v S,(P.idx u,P.decoded (P.newLabel a v x) u)=z := by
  rw [List.mem_cons];constructor
  · rintro (rfl|hit)
    · exact ⟨v,Finset.mem_insert_self ..,by simp [decoded,newLabel]⟩
    · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hit
      obtain ⟨u,hu,rfl⟩:=P.mem_code.mp hi
      have ne:u≠v:=fun eq=>fresh (eq ▸ hu)
      exact ⟨u,Finset.mem_insert_of_mem hu,by simp [decoded,newLabel,Function.update_of_ne (P.idx_injective.ne ne)]⟩
  · rintro ⟨u,hu,rfl⟩
    rcases Finset.mem_insert.mp hu with rfl|hu
    · left;simp [decoded,newLabel]
    · right
      have ne:u≠v:=fun eq=>fresh (eq ▸ hu)
      apply List.mem_map.mpr
      exact ⟨P.idx u,P.idx_mem.mpr hu,by simp [decoded,newLabel,Function.update_of_ne (P.idx_injective.ne ne)]⟩

theorem bag_ok (S:Finset V) (v:V) (fresh:v∉S) (x:ℕ) (hx:x∈d.menu (P.idx v))
    (a:ℕ→ℕ) (valid:∀u∈S,a (P.idx u)∈d.menu (P.idx u)) :
    localOK d ((P.idx v,x)::bindCodes (P.code S) a)=true ↔
      okay G P.menu P.test (insert v S) (P.decoded (P.newLabel a v x)) := by
  have imp (e k:Bool) : (!e || k)=true ↔ (e=true → k=true):=by cases e <;> cases k <;> decide
  simp only [localOK,List.all_eq_true,imp]
  constructor
  · intro h;constructor
    · intro u hu;rcases Finset.mem_insert.mp hu with rfl|hu
      · simpa [menu,decoded,newLabel] using hx
      · have ne:u≠v:=fun e=>fresh (e ▸ hu)
        simpa [menu,decoded,newLabel,Function.update_of_ne (P.idx_injective.ne ne)] using valid u hu
    · intro u hu y hy edge
      exact h _ ((P.labelled_bag S v fresh x a _).2 ⟨u,hu,rfl⟩) _ ((P.labelled_bag S v fresh x a _).2 ⟨y,hy,rfl⟩) ((P.edges u y).2 edge)
  · intro h z hz t ht edge
    obtain ⟨u,hu,rfl⟩:=(P.labelled_bag S v fresh x a _).1 hz
    obtain ⟨y,hy,rfl⟩:=(P.labelled_bag S v fresh x a _).1 ht
    exact h.2 u hu y hy ((P.edges u y).1 edge)

theorem restrict_new {S T:Finset V} {v:V} (inside:T⊆insert v S) (x:ℕ) (a:ℕ→ℕ) :
    restricted (P.code T) ((P.idx v,x)::bindCodes (P.code S) a)=bindCodes (P.code T) (P.newLabel a v x) := by
  apply List.map_congr_left
  intro i hi;obtain ⟨u,hu,rfl⟩:=P.mem_code.mp hi
  by_cases eq:u=v
  · subst u;simp [value,newLabel]
  · have hS:=Finset.mem_of_mem_insert_of_ne (inside hu) eq
    have ne:P.idx v≠P.idx u:=Ne.symm (P.idx_injective.ne eq)
    have bit : (P.idx v == P.idx u)=false:=by simp [ne]
    have read:=binding_value (P.code S) a (P.idx u) (P.idx_mem.mpr hS)
    simpa only [value,List.find?_cons,bit,Prod.mk.injEq,true_and,
      newLabel,Function.update_of_ne (Ne.symm ne)] using congrArg (Prod.mk (P.idx u)) read

theorem child_facts {S C:Finset V} (hc:IsFlap G S C) (v:V) (hv:v∈C) :
    let es:=P.pieces (C.erase v)
    let B:=insert v S
    es.toFinset.biUnion id=C.erase v ∧ ∀E∈es,IsFlap G (boundary G E) E ∧
      boundary G E⊆B ∧ E⊆C.erase v ∧ E.card<C.card := by
  have geo:=SingleSearch.deletion_piece_geometry G S C (insert v S) hc (Finset.subset_insert ..)
    (Finset.insert_subset (Finset.mem_union_right _ hv) Finset.subset_union_left)
  have table:=P.parts_children hc v hv
  refine ⟨?_,?_⟩
  · rw [table.2,geo.1];ext u
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_erase,not_or]
    constructor
    · rintro ⟨h,n,_⟩;exact ⟨n,h⟩
    · rintro ⟨n,h⟩;exact ⟨h,n,fun hs=>Finset.disjoint_left.mp hc.avoids hs h⟩
  · intro E he
    have entry:=(P.children_geometry hc v hv E).1 he
    have h:=geo.2.2.1 E entry
    have subset:E⊆C.erase v:=by
      intro u hu;refine Finset.mem_erase.mpr ⟨?_,(mem_children.mp entry).2 hu⟩
      rintro rfl;exact Finset.disjoint_left.mp h.2.1 hu (Finset.mem_insert_self ..)
    exact ⟨h.1,h.2.2.1,subset,(Finset.card_le_card subset).trans_lt (Finset.card_erase_lt_of_mem hv)⟩
end Presentation
end StableMSR.Recovery.TightLanguage.Graph


namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

namespace Presentation
open WindowCuts
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

theorem tail_split (w:ℕ) (C:Finset V) (a:ℕ→ℕ) (flap:IsFlap G (boundary G C) C)
    (v:V) (hv:v∈C) (x:ℕ) (tail:List Letter) :
    let tab:=(build wordAlgebra d w).2
    let b:=(P.idx v,x)::bindCodes (P.code (boundary G C)) a
    joined (fun t=>lookup tab t (restricted (rimOf d t) b)) (parts d ((P.code C).erase (P.idx v))) tail ↔
      ∃f:Finset V→List Letter,(∀E∈P.pieces (C.erase v),P.accepts w E (P.newLabel a v x) (f E)) ∧
        tail=(P.pieces (C.erase v)).flatMap f := by
  let es:=P.pieces (C.erase v)
  let tab:=(build wordAlgebra d w).2
  let b:=(P.idx v,x)::bindCodes (P.code (boundary G C)) a
  let ask:=fun t=>lookup tab t (restricted (rimOf d t) b)
  let row:=fun E=>lookup tab (P.code E) (bindCodes (P.code (boundary G E)) (P.newLabel a v x))
  have eq:(parts d ((P.code C).erase (P.idx v))).mapM (m:=Option) ask=es.mapM row := by
    rw [←(P.parts_children flap v hv).1,List.mapM_map]
    apply queries_congr;intro E he
    change lookup tab (P.code E) (restricted (rimOf d (P.code E)) b)=_
    rw [P.rim_code,P.restrict_new ((P.child_facts flap v hv).2 E he).2.1]
  change joined ask _ tail ↔ _
  have same:joined ask (parts d ((P.code C).erase (P.idx v)))=joined row es:=by unfold joined;rw [eq]
  rw [same];exact joined_iff row es (P.pieces_nodup _) tail

theorem step_words (w:ℕ) (C:Finset V) (a:ℕ→ℕ) (flap:IsFlap G (boundary G C) C)
    (width:(boundary G C).card≤w) (valid:∀u∈boundary G C,a (P.idx u)∈d.menu (P.idx u)) (s:List Letter) :
    P.accepts w C a s ↔ ∃v∈C,∃x∈d.menu (P.idx v),
      okay G P.menu P.test (insert v (boundary G C)) (P.decoded (P.newLabel a v x)) ∧
      ∃f:Finset V→List Letter,(∀E∈P.pieces (C.erase v),P.accepts w E (P.newLabel a v x) (f E)) ∧
      s=(P.idx v,x)::(P.pieces (C.erase v)).flatMap f := by
  rw [P.row_choices w C a flap width valid]
  have each (v:V) (hv:v∈C) (x:ℕ) (hx:x∈d.menu (P.idx v)) :
      production d (build wordAlgebra d w).2 (P.code C) (bindCodes (P.code (boundary G C)) a) (P.idx v) x s ↔
      okay G P.menu P.test (insert v (boundary G C)) (P.decoded (P.newLabel a v x)) ∧
      ∃f:Finset V→List Letter,(∀E∈P.pieces (C.erase v),P.accepts w E (P.newLabel a v x) (f E)) ∧
      s=(P.idx v,x)::(P.pieces (C.erase v)).flatMap f := by
    have fresh:v∉boundary G C:=fun hs=>Finset.disjoint_left.mp flap.avoids hs hv
    unfold production;dsimp only
    rw [P.bag_ok _ v fresh x hx a valid]
    apply and_congr_right;intro _
    constructor
    · rintro ⟨tail,h,rfl⟩;obtain ⟨f,hf,rfl⟩:=(P.tail_split w C a flap v hv x tail).1 h
      exact ⟨f,hf,rfl⟩
    · rintro ⟨f,hf,rfl⟩;exact ⟨_,(P.tail_split w C a flap v hv x _).2 ⟨f,hf,rfl⟩,rfl⟩
  constructor
  · rintro ⟨v,hv,x,hx,h⟩;exact ⟨v,hv,x,hx,(each v hv x hx).1 h⟩
  · rintro ⟨v,hv,x,hx,h⟩;exact ⟨v,hv,x,hx,(each v hv x hx).2 h⟩

theorem assemble_support {S C:Finset V} (flap:IsFlap G S C) (v:V) (hv:v∈C) (x:ℕ)
    (l:Finset V→List (V×ℕ)) (each:∀E∈P.pieces (C.erase v),
      ((l E).map Prod.fst).Nodup ∧ ((l E).map Prod.fst).toFinset=E) :
    let all:=((v,x)::(P.pieces (C.erase v)).flatMap l).map Prod.fst
    all.Nodup ∧ all.toFinset=C := by
  classical
  let es:=P.pieces (C.erase v)
  let g:=fun E=>(l E).map Prod.fst
  have flat:((v,x)::es.flatMap l).map Prod.fst=v::es.flatMap g:=by simp [List.map_flatMap,g]
  rw [flat]
  have geom:=P.child_facts flap v hv
  have inside (E:Finset V) (he:E∈es) (u:V) (hu:u∈g E) : u∈E:=by rw [←(each E he).2];exact List.mem_toFinset.mpr hu
  constructor
  · rw [List.nodup_cons];constructor
    · intro h;obtain ⟨E,he,hv'⟩:=List.mem_flatMap.mp h
      exact (Finset.mem_erase.mp ((geom.2 E he).2.2.1 (inside E he v hv'))).1 rfl
    · apply List.nodup_flatMap.mpr
      refine ⟨fun E he=>(each E he).1,(P.pieces_nodup _).pairwise_of_forall_ne ?_⟩
      intro E he F hf diff u hE hF
      exact Finset.disjoint_left.mp (P.different_pieces he hf diff) (inside E he u hE) (inside F hf u hF)
  · rw [List.toFinset_cons,union_flat]
    have eq:es.toFinset.biUnion (fun E=>(g E).toFinset)=es.toFinset.biUnion id:=
      Finset.biUnion_congr rfl (fun E he=>(each E (List.mem_toFinset.mp he)).2)
    rw [eq,geom.1,Finset.insert_erase hv]
end Presentation
end StableMSR.Recovery.TightLanguage.Graph


namespace StableMSR.Recovery.TightLanguage.Graph
open Havens DecompositionSearch SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

namespace Presentation
open WindowCuts SingleSearch
variable {V:Type} [Fintype V] [DecidableEq V] {d:Instance} {G:SimpleGraph V} (P:Presentation d G)

def RowMeaning (w m:ℕ) (C:Finset V) (a:ℕ→ℕ) :=
  let runs:=run G P.menu P.test w m (boundary G C) C (P.decoded a)
  (∀t,P.accepts w C a t → ∃l:List (V×ℕ),l.map P.tag=t ∧ (l.map Prod.fst).Nodup ∧
    (l.map Prod.fst).toFinset=C ∧ runs l.toFinset) ∧
  ∀O,runs O → ∃l:List (V×ℕ),P.accepts w C a (l.map P.tag) ∧ l.toFinset=O

theorem exact_row (w m:ℕ) (C:Finset V) (a:ℕ→ℕ) (flap:IsFlap G (boundary G C) C)
    (width:(boundary G C).card≤w) (depth:C.card ≤ m) (valid:∀v∈boundary G C,a (P.idx v)∈d.menu (P.idx v)) :
    P.RowMeaning w m C a := by
  classical
  induction m generalizing C a with
  | zero=>have positive:=Finset.card_pos.mpr flap.connected.1;omega
  | succ m ih=>
    let S:=boundary G C
    have step:=P.step_words w C a flap width valid
    constructor
    · intro t ht
      obtain ⟨v,hv,x,hx,ok,f,hf,rfl⟩:=(step t).1 ht
      let es:=P.pieces (C.erase v)
      let b:=P.newLabel a v x
      have facts:=P.child_facts flap v hv
      have components:=P.parts_children flap v hv |>.2
      have cm (E:Finset V) : E∈es ↔ E∈children G (insert v S) C := by
        rw [←components];exact List.mem_toFinset.symm
      have child (E:Finset V) (he:E∈es) : P.RowMeaning w m E b := by
        obtain ⟨tight,rim,_,lt⟩:=facts.2 E he
        apply ih E b tight (P.width_of_word (hf E he)) (by omega)
        intro z hz;exact List.mem_toFinset.mp (ok.1 z (rim hz))
      have choices (E:Finset V) (he:E∈es) := (child E he).1 (f E) (hf E he)
      let l (E:Finset V) := if he:E∈es then (choices E he).choose else []
      have hl (E:Finset V) (he:E∈es) :
          (l E).map P.tag=f E ∧ ((l E).map Prod.fst).Nodup ∧ ((l E).map Prod.fst).toFinset=E ∧
          run G P.menu P.test w m (boundary G E) E (P.decoded b) (l E).toFinset := by
        simpa only [l,dif_pos he] using (choices E he).choose_spec
      have support:=P.assemble_support flap v hv x l (fun E he=>⟨(hl E he).2.1,(hl E he).2.2.1⟩)
      refine ⟨(v,x)::es.flatMap l,?_,support.1,support.2,?_⟩
      · simp only [List.map_cons,List.map_flatMap]
        exact congrArg (List.cons (P.idx v,x)) (List.flatMap_congr (fun E he=>(hl E he).1))
      · refine ⟨width,v,hv,x,?_,fun E=>(l E).toFinset,?_,?_⟩
        · rw [←P.decoded_new];exact ok
        · intro E hE;have he:=(cm E).2 hE
          rw [←P.decoded_new];exact ⟨P.width_of_word (hf E he),(hl E he).2.2.2⟩
        · rw [List.toFinset_cons,union_flat,show es.toFinset=_ from components]
    · rintro O ⟨_,v,hv,x,good,out,childrenOK,rfl⟩
      let es:=P.pieces (C.erase v)
      let b:=P.newLabel a v x
      have facts:=P.child_facts flap v hv
      have components:=P.parts_children flap v hv |>.2
      have cm (E:Finset V) : E∈es ↔ E∈children G (insert v S) C := by
        rw [←components];exact List.mem_toFinset.symm
      have ok:okay G P.menu P.test (insert v S) (P.decoded b):=by rw [P.decoded_new];exact good
      have hx:x∈d.menu (P.idx v):=by
        have validx:=ok.1 v (Finset.mem_insert_self ..)
        simpa [b,menu,decoded,newLabel] using validx
      have choices (E:Finset V) (he:E∈es) :
          ∃l:List (V×ℕ),P.accepts w E b (l.map P.tag) ∧ l.toFinset=out E := by
        obtain ⟨tight,rim,_,lt⟩:=facts.2 E he
        obtain ⟨small,runs⟩:=childrenOK E ((cm E).1 he)
        have dom:∀z∈boundary G E,b (P.idx z)∈d.menu (P.idx z):=
          fun z hz=>List.mem_toFinset.mp (ok.1 z (rim hz))
        apply (ih E b tight small (by omega) dom).2 (out E)
        rw [P.decoded_new];exact runs
      let l (E:Finset V) := if he:E∈es then (choices E he).choose else []
      have hl (E:Finset V) (he:E∈es) : P.accepts w E b ((l E).map P.tag) ∧ (l E).toFinset=out E := by
        simpa only [l,dif_pos he] using (choices E he).choose_spec
      refine ⟨(v,x)::es.flatMap l,(step _).2 ⟨v,hv,x,hx,ok,fun E=>(l E).map P.tag,
        fun E he=>(hl E he).1,?_⟩,?_⟩
      · simp only [List.map_cons,List.map_flatMap];rfl
      · rw [List.toFinset_cons,union_flat,show es.toFinset=_ from components]
        congr 1;exact Finset.biUnion_congr rfl (fun E h=>(hl E ((cm E).2 h)).2)
end Presentation

theorem table_rows_correct : RowLaw := by
  intro V _ _ d ix inj G active edges w m C a flap width depth valid
  let P:Presentation d G:=⟨ix,inj,active,edges⟩
  exact P.exact_row w m C a flap width depth valid


end StableMSR.Recovery.TightLanguage.Graph

open scoped Classical
open StableMSR.Recovery
theorem solution
    {V : Type} [Fintype V] [DecidableEq V] (d : SingleCircuit.Instance) (ix : V → Fin d.n)
    (inj : Function.Injective ix) (G : SimpleGraph V)
    (active : ∀ i : Fin d.n, d.active i.val = true ↔ ∃ v, ix v = i)
    (edges : ∀ v z, d.edge (ix v).val (ix z).val = true ↔ G.Adj v z)
    (w m : ℕ) (C : Finset V) (a : ℕ → ℕ)
    (flap : Havens.IsFlap G (DecompositionSearch.boundary G C) C)
    (space : (DecompositionSearch.boundary G C).card ≤ w) (depth : C.card ≤ m)
    (valid : ∀ v ∈ DecompositionSearch.boundary G C, a (ix v).val ∈ d.menu (ix v).val) :
    let code := fun K : Finset V => (K.image (fun v => (ix v).val)).sort (· ≤ ·)
    let S := DecompositionSearch.boundary G C
    let key := (code S).map (fun j => (j,a j))
    let table := (TightLanguage.build TightLanguage.wordAlgebra d w).2
    let accepts := (TightLanguage.lookup table (code C) key).getD (fun _ => False)
    let dom := fun v => (d.menu (ix v).val).toFinset
    let test := fun v z c k => d.test (ix v).val (ix z).val c k = true
    let tag := fun t : V × ℕ => ((ix t.1).val,t.2)
    let runs := SingleSearch.run G dom test w m S C (fun v => a (ix v).val)
    (∀ t, accepts t → ∃ l : List (V × ℕ), l.map tag = t ∧ (l.map Prod.fst).Nodup ∧
      (l.map Prod.fst).toFinset = C ∧ runs l.toFinset) ∧
    ∀ O, runs O → ∃ l : List (V × ℕ), accepts (l.map tag) ∧ l.toFinset = O := @TightLanguage.Graph.table_rows_correct V _ _ d ix inj G active edges w m C a flap space depth valid
