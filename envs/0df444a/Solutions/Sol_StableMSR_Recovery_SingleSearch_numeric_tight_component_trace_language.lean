-- Prove2me | solution 1 for StableMSR.Recovery.SingleSearch.numeric_tight_component_trace_language
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T20:29:29.89822+00:00
-- url     : https://prove2.me/submissions/facfd2fa-d2c3-47b4-a0fc-f56b4ead2d63

import Definitions.Def_StableMSR_TightComponentTrace
import Definitions.Def_StableMSR_SingleVertexSearch
import Theorems.Thm_StableMSR_Recovery_SingleSearch_numeric_tight_table_row
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

def NumericGraphLaw : Prop := ∀ {V:Type} [Fintype V] [DecidableEq V]
    (d:Instance) (ix:V→Fin d.n) (_:Function.Injective ix) (G:SimpleGraph V)
    (_:∀i:Fin d.n,d.active i.val=true ↔ ∃v,ix v=i)
    (_:∀v z,d.edge (ix v).val (ix z).val=true ↔ G.Adj v z) (w:ℕ),
    let dom:=fun v=>(d.menu (ix v).val).toFinset
    let test:=fun v z a b=>d.test (ix v).val (ix z).val a b=true
    let tag:=fun t:V×ℕ=>((ix t.1).val,t.2)
    let accepts:=SingleSearch.root G dom test w (fun _=>0)
    (∀t,traces d w t → ∃l:List (V×ℕ),l.map tag=t ∧ (l.map Prod.fst).Nodup ∧ accepts l.toFinset) ∧
    ∀O,accepts O → ∃l:List (V×ℕ),traces d w (l.map tag) ∧ l.toFinset=O


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

theorem graph_from_rows (rows:RowLaw) : NumericGraphLaw := by
  intro V _ _ d ix inj G active edges w
  classical
  let P:Presentation d G:=⟨ix,inj,active,edges⟩
  let ks:=P.pieces Finset.univ
  let tag:=fun j:V×ℕ=>((ix j.1).val,j.2)
  let D:=fun v=>(d.menu (ix v).val).toFinset
  let test:=fun v z c k=>d.test (ix v).val (ix z).val c k=true
  let ok:=fun C=>SingleSearch.run G D test w (Fintype.card V) ∅ C (fun _=>0)
  let accept:=fun C=>available (P.rootEntry w C)
  have cm (C:Finset V) : C∈ks ↔ C∈PartialDecompositions.components G ∅ := by
    rw [←P.root_pieces];exact List.mem_toFinset.symm
  have entry (C:Finset V) (hc:C∈ks) :
      (∀t,accept C t → ∃l:List (V×ℕ),l.map tag=t ∧ (l.map Prod.fst).Nodup ∧
        (l.map Prod.fst).toFinset=C ∧ ok C l.toFinset) ∧
      ∀O,ok C O → ∃l:List (V×ℕ),accept C (l.map tag) ∧ l.toFinset=O := by
    have empty:=P.piece_rim_empty hc
    have flap:IsFlap G (boundary G C) C:=empty ▸ PartialDecompositions.mem_components.mp ((cm C).1 hc)
    have fit:(boundary G C).card≤w:=by simp [empty]
    have valid:∀v∈boundary G C,(0:ℕ)∈d.menu (ix v).val:=by simp [empty]
    have h:=rows d ix inj G active edges w (Fintype.card V) C (fun _=>0) flap fit (Finset.card_le_univ C) valid
    dsimp only at h
    simp only [empty,Finset.image_empty,Finset.sort_empty,List.map_nil] at h
    exact h
  constructor
  · intro t ht
    obtain ⟨f,hf,rfl⟩:=(P.root_split w t).1 ht
    have choices (C:Finset V) (hc:C∈ks) := (entry C hc).1 _ (hf C hc)
    let l (C:Finset V) := if hc:C∈ks then (choices C hc).choose else []
    have hl (C:Finset V) (hc:C∈ks) : (l C).map tag=f C ∧ ((l C).map Prod.fst).Nodup ∧
        ((l C).map Prod.fst).toFinset=C ∧ ok C (l C).toFinset := by
      simpa only [l,dif_pos hc] using (choices C hc).choose_spec
    refine ⟨ks.flatMap l,?_,?_,?_⟩
    · rw [List.map_flatMap];exact List.flatMap_congr (fun C h=>(hl C h).1)
    · rw [List.map_flatMap];apply List.nodup_flatMap.mpr
      refine ⟨fun C hc=>(hl C hc).2.1,?_⟩
      apply (P.pieces_nodup Finset.univ).pairwise_of_forall_ne
      intro C hc E he diff v hC hE
      have inside (C:Finset V) (hc:C∈ks) (h:v∈(l C).map Prod.fst) : v∈C := by
        rw [←(hl C hc).2.2.1];exact List.mem_toFinset.mpr h
      exact Finset.disjoint_left.mp (P.different_pieces hc he diff) (inside C hc hC) (inside E he hE)
    · refine ⟨fun C=>(l C).toFinset,fun C hc=>(hl C ((cm C).2 hc)).2.2.2,?_⟩
      rw [union_flat,show ks.toFinset=_ from P.root_pieces]
  · rintro O ⟨out,good,rfl⟩
    have choices (C:Finset V) (hc:C∈ks) := (entry C hc).2 (out C) (good C ((cm C).1 hc))
    let l (C:Finset V) := if hc:C∈ks then (choices C hc).choose else []
    have hl (C:Finset V) (hc:C∈ks) : accept C ((l C).map tag) ∧ (l C).toFinset=out C := by
      simpa only [l,dif_pos hc] using (choices C hc).choose_spec
    refine ⟨ks.flatMap l,(P.root_split w _).2 ⟨fun C=>(l C).map tag,fun C hc=>(hl C hc).1,?_⟩,?_⟩
    · rw [List.map_flatMap]
    · rw [union_flat,show ks.toFinset=_ from P.root_pieces]
      exact Finset.biUnion_congr rfl (fun C hc=>(hl C ((cm C).2 hc)).2)
end StableMSR.Recovery.TightLanguage.Graph


open scoped Classical
open StableMSR.Recovery
theorem solution
    {V : Type} [Fintype V] [DecidableEq V] (d : SingleCircuit.Instance) (ix : V → Fin d.n)
    (inj : Function.Injective ix) (G : SimpleGraph V)
    (active : ∀ i : Fin d.n, d.active i.val = true ↔ ∃ v, ix v = i)
    (edges : ∀ v z, d.edge (ix v).val (ix z).val = true ↔ G.Adj v z) (w : ℕ) :
    let dom := fun v => (d.menu (ix v).val).toFinset
    let test := fun v z a b => d.test (ix v).val (ix z).val a b = true
    let tag := fun t : V × ℕ => ((ix t.1).val, t.2)
    let accepts := SingleSearch.root G dom test w (fun _ => 0)
    (∀ t, TightLanguage.traces d w t → ∃ l : List (V × ℕ),
      l.map tag = t ∧ (l.map Prod.fst).Nodup ∧ accepts l.toFinset) ∧
    ∀ O, accepts O → ∃ l : List (V × ℕ), TightLanguage.traces d w (l.map tag) ∧ l.toFinset = O := @TightLanguage.Graph.graph_from_rows (@SingleSearch.numeric_tight_table_row) V _ _ d ix inj G active edges w
