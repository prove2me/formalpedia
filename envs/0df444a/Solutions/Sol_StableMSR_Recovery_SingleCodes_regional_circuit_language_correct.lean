-- Prove2me | solution 1 for StableMSR.Recovery.SingleCodes.regional_circuit_language_correct
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T20:22:55.805054+00:00
-- url     : https://prove2.me/submissions/6ee1409a-73e7-4fb8-8179-ca030e5ce1d6

import Definitions.Def_StableMSR_DenseGlobalAssembly
import Definitions.Def_StableMSR_TightComponentTrace
import Theorems.Thm_StableMSR_Recovery_SingleCircuit_regional_compiler_trace_language
import Theorems.Thm_StableMSR_Recovery_SingleSearch_numeric_tight_component_trace_language
import Theorems.Thm_StableMSR_Recovery_SingleSearch_singleton_labelled_component_language
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
open scoped Classical
set_option autoImplicit false
def letterBlocks {A:Type} (d:Instance) (emit:List ℕ→List A) (letter:Letter) :=
  (d.owned letter.1 letter.2).flatMap emit

noncomputable def regionalMaskWord (n:ℕ) (m:List ℕ) := WindowMasks.emit (Finset.univ.filter (fun i:Point n=>m.contains i.val))

theorem compiledMaskLanguage (n:ℕ) (d:Instance) (w:ℕ) :
    let out:=compileRegion d w
    out.2<out.1.size ∧ ∀s,Language n out.1 out.2 s ↔
      ∃t,traces d w t ∧ s=t.flatMap (letterBlocks d (regionalMaskWord n)) := SingleCircuit.regional_compiler_trace_language n d w
end StableMSR.Recovery.TightLanguage
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

open SingleSearch WindowCuts Havens PartialDecompositions
open scoped Classical

section
variable {V X Y:Type} [Fintype V] [DecidableEq V] [DecidableEq X] [DecidableEq Y]

def relabel (f:V→X→Y) (z:V×X) : V×Y := (z.1,f z.1 z.2)

theorem relabel_labels (f:V→X→Y) (C:Finset V) (a:V→X) :
    (labels C a).image (relabel f)=labels C (fun v=>f v (a v)) := by
  classical
  simp [labels,Finset.image_image,relabel,Function.comp_def]

theorem run_empty_iff (G:SimpleGraph V) (D:V→Finset X) (T:V→V→X→X→Prop) (w m:ℕ)
    {C:Finset V} (hc:IsFlap G ∅ C) (a:V→X) (O:Finset (V×X)) :
    run G D T w m ∅ C a O ↔ one G w m ∅ C ∧ ∃f,okay G D T C f ∧ O=labels C f := by
  rw [singleton_labelled_component_language G D T w m ∅ C hc a O]
  simp

/-- Quotienting the local labels by a vertex-dependent decoder preserves and
reflects the root search, including simultaneous outputs of all components. -/
theorem root_image_iff (G:SimpleGraph V) (D:V→Finset X) (E:V→Finset Y)
    (f:V→X→Y) (onto:∀v y,y∈E v ↔ ∃c∈D v,f v c=y)
    (T:V→V→Y→Y→Prop) (w:ℕ) (a:V→X) (b:V→Y) (Q:Finset (V×Y)) :
    let U:=fun v z c k=>T v z (f v c) (f z k)
    root G E T w b Q ↔ ∃O,root G D U w a O ∧ O.image (relabel f)=Q := by
  classical
  let U:=fun v z c k=>T v z (f v c) (f z k)
  let K:=PartialDecompositions.components G ∅
  let m:=Fintype.card V
  have component (C:Finset V) (hc:C∈K) (o:Finset (V×Y)) :
      run G E T w m ∅ C b o ↔
        ∃s,run G D U w m ∅ C a s ∧ s.image (relabel f)=o := by
    have flap:=mem_components.mp hc
    rw [run_empty_iff G E T w m flap]
    constructor
    · rintro ⟨shape,p,valid,rfl⟩
      have pick (v:V) : ∃c:X,v∈C → c∈D v ∧ f v c=p v := by
        by_cases h:v∈C
        · obtain ⟨c,hc,eq⟩:=(onto v (p v)).1 (valid.1 v h)
          exact ⟨c,fun _=>⟨hc,eq⟩⟩
        · exact ⟨a v,fun hv=>False.elim (h hv)⟩
      choose code ok using pick
      have good:okay G D U C code:=by
        refine ⟨fun v hv=>(ok v hv).1,?_⟩
        intro v hv z hz edge
        change T v z (f v (code v)) (f z (code z))
        rw [(ok v hv).2,(ok z hz).2];exact valid.2 v hv z hz edge
      refine ⟨labels C code,(run_empty_iff G D U w m flap ..).2 ⟨shape,code,good,rfl⟩,?_⟩
      rw [relabel_labels];apply Finset.image_congr
      intro v hv;exact congrArg (Prod.mk v) (ok v hv).2
    · rintro ⟨s,hs,rfl⟩
      obtain ⟨shape,p,valid,rfl⟩:=(run_empty_iff G D U w m flap ..).1 hs
      refine ⟨shape,fun v=>f v (p v),⟨fun v hv=>(onto v _).2 ⟨p v,valid.1 v hv,rfl⟩,valid.2⟩,relabel_labels ..⟩
  constructor
  · rintro ⟨out,good,rfl⟩
    have chooseOut (C:Finset V) : ∃s:Finset (V×X),C∈K →
        run G D U w m ∅ C a s ∧ s.image (relabel f)=out C := by
      by_cases hc:C∈K
      · obtain ⟨s,hs⟩:=(component C hc _).1 (good C hc)
        exact ⟨s,fun _=>hs⟩
      · exact ⟨∅,fun h=>False.elim (hc h)⟩
    choose codes chosen using chooseOut
    refine ⟨K.biUnion codes,⟨codes,fun C hc=>(chosen C hc).1,rfl⟩,?_⟩
    rw [Finset.biUnion_image];exact Finset.biUnion_congr rfl (fun C hc=>(chosen C hc).2)
  · rintro ⟨O,⟨out,good,rfl⟩,rfl⟩
    refine ⟨fun C=>(out C).image (relabel f),fun C hc=>(component C hc _).2 ⟨out C,good C hc,rfl⟩,?_⟩
    exact Finset.biUnion_image
end
end StableMSR.Recovery.TightLanguage


namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

open OracleQueries WindowCSP RegionalSeeds CartesianBallRows FewBallRows SingleCodes SingleWindows
open scoped Classical

theorem mem_decode_menu (x:World) (W:Cluster x.n) (h:ℕ) (Q:Partition x.n) :
    Q∈traceMenu x h W ↔ ∃c∈SingleCodes.menu x W h,SingleCodes.decode x W h c=Q := by
  classical
  have unpair (g u:ℕ) (hg:g<h+1) :
      encode h g u%(h+1)=g ∧ encode h g u/(h+1)=u := by
    unfold encode
    constructor
    · simp [Nat.add_mod,Nat.mod_eq_of_lt hg]
    · rw [Nat.mul_comm u _,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hg,Nat.add_zero]
  constructor
  · intro hQ
    obtain ⟨hit,ok⟩:=Finset.mem_filter.mp hQ
    obtain ⟨⟨g,u⟩,gu,eq⟩:=Finset.mem_image.mp hit
    obtain ⟨hg,hu⟩:=Finset.mem_product.mp gu
    obtain ⟨hm,hd⟩:=unpair g u (Finset.mem_range.mp hg)
    have dec:decode x W h (encode h g u)=Q:=by simpa only [decode,hm,hd] using eq
    refine ⟨encode h g u,List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨g,List.mem_range.mpr (Finset.mem_range.mp hg),
      List.mem_map.mpr ⟨u,List.mem_range.mpr (Finset.mem_range.mp hu),rfl⟩⟩,?_⟩,dec⟩
    simp only [dec,decide_eq_true_eq];exact ok
  · rintro ⟨c,hc,rfl⟩
    obtain ⟨hw,yes⟩:=List.mem_filter.mp hc
    obtain ⟨g,hg,vc⟩:=List.mem_flatMap.mp hw
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp vc
    have z:=unpair g u (List.mem_range.mp hg)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(g,u),Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (List.mem_range.mp hg),Finset.mem_range.mpr (List.mem_range.mp hu)⟩,?_⟩,
      of_decide_eq_true yes⟩
    simp only [decode,z.1,z.2]

theorem mask_of_block {n:ℕ} (C:Cluster n) :
    Finset.univ.filter (fun i:Point n=>(C.toList.map Fin.val).contains i.val)=C := by
  classical
  ext i;simp only [Finset.mem_filter,Finset.mem_univ,true_and,List.contains_iff_mem,List.mem_map,Finset.mem_toList]
  exact ⟨fun ⟨a,h,e⟩=>(Fin.ext e) ▸ h,fun h=>⟨i,h,rfl⟩⟩

theorem block_output {n:ℕ} (A:Point n→Point n) (v:Point n) (P:Partition n) :
    (blockList (owned A v P)).flatMap (regionalMaskWord n)=(owned A v P).toList := by
  classical
  let U:=owned A v P
  change (U.toList.map _).flatMap (regionalMaskWord n)=U.toList
  rw [List.flatMap_map]
  have eq (C:Cluster n) (hc:C∈U.toList) : regionalMaskWord n (C.toList.map Fin.val)=[C] := by
    have hold:=(Finset.mem_filter.mp (Finset.mem_toList.mp hc)).2
    obtain ⟨j,hj,_⟩:=hold
    unfold regionalMaskWord;rw [mask_of_block];simp [WindowMasks.emit,show C.Nonempty from ⟨j,hj⟩]
  rw [List.flatMap_congr (g:=fun C=>[C]) (fun C hc=>eq C hc)]
  simp

theorem same_owner {n:ℕ} {A:Point n→Point n} {v z:Point n} {P Q:Partition n} {C:Cluster n}
    (h:C∈owned A v P) (j:C∈owned A z Q) : v=z := by
  obtain ⟨i,hi,hv,le⟩:=(Finset.mem_filter.mp h).2
  obtain ⟨b,hb,hz,le'⟩:=(Finset.mem_filter.mp j).2
  have eq:=le_antisymm (le b hb) (le' i hi)
  exact hv.symm.trans ((congrArg A eq).trans hz)

theorem union_flat {A B:Type} [DecidableEq A] [DecidableEq B] (ls:List A) (f:A→List B) :
    (ls.flatMap f).toFinset=ls.toFinset.biUnion (fun j=>(f j).toFinset) := by
  classical
  ext b;simp

theorem lookup_fin {n:ℕ} {A:Type} (f:Point n→A) (i:Point n) (a:A) :
    SingleCodes.lookup f i.val a=f i := by simp [SingleCodes.lookup,i.isLt]
end StableMSR.Recovery.TightLanguage


namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

open OracleQueries WindowCSP RegionalSeeds SingleCodes SingleWindows SingleSearch
open scoped Classical

/-- Soundness and completeness of the numeric *graph* search, with addresses
erased. All gate semantics and partition decoding are proved below this interface. -/
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

theorem regional_language_from_graph (graph:NumericGraphLaw) (x:World) (W:Cluster x.n) (R:ℝ) (h w:ℕ) :
    let c:=regionalCircuit x W R h w
    let gen:=generates x W R h w
    c.2<c.1.size ∧ (∀L,Language x.n c.1 c.2 L → L.Nodup ∧ gen L.toFinset) ∧
      ∀Q,gen Q → ∃L,Language x.n c.1 c.2 L ∧ L.toFinset=Q := by
  classical
  let d:=instanceOf x W R h
  let V:=Vertex x W R
  let G:=Supplement.interactionGraph x.dist R W
  let ix:V→Fin d.n:=fun v=>v.val
  let D:=fun v:V=>(d.menu (ix v).val).toFinset
  let dec:=fun (v:V) c=>decode x (window x.dist W R v) h c
  let T:=constraint x W R
  let tc:=fun (v z:V) (c k:ℕ)=>d.test (ix v).val (ix z).val c k=true
  let tag:=fun z:V×ℕ=>((ix z.1).val,z.2)
  let raw:=SingleSearch.root G D tc w (fun _=>0)
  let read:=relabel dec
  let projected:=project x W R
  have inj:Function.Injective ix:=fun _ _ e=>Subtype.ext e
  have active (i:Fin d.n) : d.active i.val=true ↔ ∃v,ix v=i := by
    have hi : i.val < x.n := i.isLt
    simp only [d,instanceOf,SingleCodes.lookup,hi,dif_pos,decide_eq_true_eq]
    constructor
    · intro member;exact ⟨⟨i,member⟩,rfl⟩
    · rintro ⟨v,rfl⟩;exact v.property
  have edge (v z:V) : d.edge (ix v).val (ix z).val=true ↔ G.Adj v z := by
    simp only [d,ix,instanceOf,lookup_fin,decide_eq_true_eq]
    change _ ↔ v.val≠z.val ∧ v.val∈_ ∧ z.val∈_ ∧ _
    simp only [v.property,z.property,true_and];rfl
  have onto (v:V) (P:Partition x.n) : P∈domains x W R h v ↔ ∃c∈D v,dec v c=P := by
    simpa only [D,d,ix,instanceOf,lookup_fin,List.mem_toFinset,dec,domains] using mem_decode_menu x (window x.dist W R v) h P
  have tests:tc=(fun v z c k=>T v z (dec v c) (dec z k)) := by
    funext v z c k;apply propext
    simp only [tc,d,ix,instanceOf,lookup_fin,decide_eq_true_eq,T,constraint,dec]
  have root_eq (Q:Finset (V×Partition x.n)) :
      SingleSearch.root G (domains x W R h) T w (fun _=>∅) Q ↔ ∃O,raw O ∧ O.image read=Q := by
    change _ ↔ ∃O,SingleSearch.root G D tc w (fun _=>0) O ∧ _
    rw [tests];exact root_image_iff G D _ dec onto T w (fun _=>0) (fun _=>∅) Q
  let F:=letterBlocks d (regionalMaskWord x.n)
  let blocks:=fun z:V×ℕ=>owned (anchor x.dist W R) z.1.val (dec z.1 z.2)
  let out:=fun z:V×ℕ=>F (tag z)
  have each (z:V×ℕ) : out z=(blocks z).toList := by
    simpa only [out,F,letterBlocks,tag,ix,d,instanceOf,lookup_fin,blocks,dec] using block_output (anchor x.dist W R) z.1.val (dec z.1 z.2) 
  have projection (l:List (V×ℕ)) : (l.flatMap out).toFinset=projected (l.toFinset.image read) := by
    rw [union_flat]
    change _=(l.toFinset.image read).biUnion _
    rw [Finset.image_biUnion]
    apply Finset.biUnion_congr rfl
    intro z hz;rw [each];simp [blocks,read,relabel]
  have unique (l:List (V×ℕ)) (hn:(l.map Prod.fst).Nodup) : (l.flatMap out).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun z _=>by rw [each];exact Finset.nodup_toList _,?_⟩
    rw [List.nodup_iff_pairwise_ne] at hn
    apply (List.pairwise_map.mp hn).imp
    intro i j distinct C hi hj
    rw [each] at hi hj
    exact distinct (Subtype.ext (same_owner (Finset.mem_toList.mp hi) (Finset.mem_toList.mp hj)))
  have physical:=compiledMaskLanguage x.n d w
  obtain ⟨sound,complete⟩:=graph d ix inj G active edge w
  refine ⟨physical.1,?_,?_⟩
  · intro L hL
    obtain ⟨t,ht,rfl⟩:=(physical.2 L).1 hL
    obtain ⟨l,rfl,hn,ok⟩:=sound t ht
    change ((l.map tag).flatMap F).Nodup ∧ generates x W R h w ((l.map tag).flatMap F).toFinset
    rw [List.flatMap_map]
    exact ⟨unique l hn,l.toFinset.image read,(root_eq _).2 ⟨l.toFinset,ok,rfl⟩,(projection l).symm⟩
  · rintro Q ⟨P,hP,rfl⟩
    obtain ⟨O,hO,rfl⟩:=(root_eq P).1 hP
    obtain ⟨l,hl,rfl⟩:=complete O hO
    refine ⟨l.flatMap out,(physical.2 _).2 ⟨l.map tag,hl,?_⟩,projection l⟩
    simp only [List.flatMap_map];rfl
end StableMSR.Recovery.TightLanguage


open StableMSR.Recovery StableMSR.Recovery.OracleQueries StableMSR.Recovery.TightLanguage
open StableMSR.Recovery.WindowProfiles (piece)
open StableMSR.Recovery.SingleRAM
theorem solution (x : World) (h w u i : ℕ) : LiveCircuitCorrect x h w u i :=
  regional_language_from_graph (@SingleSearch.numeric_tight_component_trace_language)
    x (piece x u i) (WindowCSP.scale x u) h w
