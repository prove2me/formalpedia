-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits.exact_tape_from_ordered_seeds
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T00:31:46.724812+00:00
-- url     : https://prove2.me/submissions/0abc2c77-2159-4b6b-aef1-a7ee3693dd55

import Definitions.Def_StableMSR_IntegerWindowCandidates
set_option linter.all false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
open Compiler OracleQueries WindowCSP SingleCircuit CartesianBallRows FewBallRows RegionalSeeds Supplement
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem piece_eq (x:World) (u i:ℕ) : piece x.n x.mem u i=WindowProfiles.piece x u i:=by rfl
theorem pair_eq (x:World) (m:ℤ→ℤ) (a b:ℤ) : MinSumFPT.oracleAnswer (matrix x m).dist a b=(atPair x.n m a b:ℝ):=by
  simp only [MinSumFPT.oracleAnswer,atPair,matrix]
  cases MinSumFPT.toPoint x.n a <;> cases MinSumFPT.toPoint x.n b <;> simp
theorem within (x:World) (m:ℤ→ℤ) (t:ℕ) (a b:Fin x.n) :
    (matrix x m).dist a b≤(t:ℝ)*(unit x.n:ℝ) ↔ m (address a b)≤(t:ℤ)*(unit x.n:ℤ):=by
  change (m (address a b):ℝ)≤_ ↔ _;exact_mod_cast Iff.rfl
theorem near2 (x:World) (m:ℤ→ℤ) (a b:Fin x.n) : (matrix x m).dist a b≤2*(unit x.n:ℝ) ↔ m (address a b)≤2*(unit x.n:ℤ):=by
  change (m (address a b):ℝ)≤_ ↔ _;exact_mod_cast Iff.rfl
theorem near4 (x:World) (m:ℤ→ℤ) (a b:Fin x.n) : (matrix x m).dist a b≤4*(unit x.n:ℝ) ↔ m (address a b)≤4*(unit x.n:ℤ):=by
  change (m (address a b):ℝ)≤_ ↔ _;exact_mod_cast Iff.rfl
theorem near8 (x:World) (m:ℤ→ℤ) (a b:Fin x.n) : (matrix x m).dist a b≤8*(unit x.n:ℝ) ↔ m (address a b)≤8*(unit x.n:ℤ):=by
  change (m (address a b):ℝ)≤_ ↔ _;exact_mod_cast Iff.rfl
theorem net_eq (x:World) (m:ℤ→ℤ) (W:Cluster x.n) : net m W=greedyNet (matrix x m).dist (unit x.n:ℝ) W:=by
  let d:=fun a b:Fin x.n=>(m (address a b):ℝ)
  change net m W=greedyNet d (unit x.n:ℝ) W
  have far (a b:Fin x.n) : 2*(unit x.n:ℝ)<d a b ↔ 2*(unit x.n:ℤ) < m (address a b):=by
    dsimp only [d];exact_mod_cast Iff.rfl
  simp only [net,greedyNet,far]
theorem owner_eq (x:World) (m:ℤ→ℤ) (W:Cluster x.n) : owner m (net m W)=anchor (matrix x m).dist W (unit x.n:ℝ):=by
  let d:=fun a b:Fin x.n=>(m (address a b):ℝ)
  change owner m (net m W)=anchor d W (unit x.n:ℝ)
  have ne:net m W=greedyNet d (unit x.n:ℝ) W:=net_eq x m W
  have thr (a b:Fin x.n) : d a b≤2*(unit x.n:ℝ) ↔ m (address a b)≤2*(unit x.n:ℤ):=near2 x m a b
  funext p;simp only [owner,anchor,representative,ne,thr]
theorem win_eq (x:World) (m:ℤ→ℤ) (W:Cluster x.n) (a:Fin x.n) :
    win m W a=window (matrix x m).dist W (unit x.n:ℝ) a:=by
  let d:=fun a b:Fin x.n=>(m (address a b):ℝ)
  change win m W a=window d W (unit x.n:ℝ) a
  have thr (a b:Fin x.n) : d a b≤4*(unit x.n:ℝ) ↔ m (address a b)≤4*(unit x.n:ℤ):=near4 x m a b
  ext p;simp [win,window,ball,Finset.mem_inter,thr]
theorem joins_eq (x:World) (m:ℤ→ℤ) (h c:ℕ) (i j:Fin x.n) :
    joins x.n m h c i j=true ↔ digitRel (seedWorld (matrix x m) h) (c%(h+1)) (c/(h+1)) i.val j.val:=by
  simp only [joins,digitRel,joined,distAt,seedWorld,pair_eq x m]
  simp [List.any_eq_true,Bool.and_eq_true,Bool.or_eq_true,Int.cast_le]
  aesop

theorem block_eq (x:World) (m:ℤ→ℤ) (U:Cluster x.n) (h c:ℕ) (p:Fin x.n) :
    block m U h c p=U.filter (fun q=>digitRel (seedWorld (matrix x m) h) (c%(h+1)) (c/(h+1)) p.val q.val):=by
  ext q;simp only [block,Finset.mem_filter,joins_eq x m]
theorem blocks_eq (x:World) (m:ℤ→ℤ) (U:Cluster x.n) (h c:ℕ) :
    (blocks m U h c).toFinset=SingleCodes.decode (matrix x m) U h c:=by
  change (blocks m U h c).toFinset=U.image (fun p:Fin x.n=>U.filter (fun q:Fin x.n=>digitRel (seedWorld (matrix x m) h) (c%(h+1)) (c/(h+1)) p.val q.val))
  ext C;simp [blocks,block_eq x m,Finset.mem_image]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
open Compiler OracleQueries WindowCSP SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000

theorem feasible_eq {n:ℕ} (U:Cluster n) (P:List (Cluster n)) :
    feasible U P=true ↔ Feasible U P.toFinset.card P.toFinset := by
  simp only [feasible,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,Bool.or_eq_true,
    Feasible,true_and,Finset.mem_coe,List.mem_toFinset,Set.Pairwise]
  constructor
  · rintro ⟨⟨nonempty,pair⟩,cover⟩
    refine ⟨nonempty,?_,cover⟩
    intro C hc D hd ne;exact (pair C hc D hd).resolve_left ne
  · rintro ⟨nonempty,pair,cover⟩
    refine ⟨⟨nonempty,?_⟩,cover⟩
    intro C hc D hd;by_cases eq:C=D
    · exact Or.inl eq
    · exact Or.inr (pair hc hd eq)

theorem touches_eq {n:ℕ} (own:Fin n→Fin n) (a:Fin n) (C:Cluster n) :
    touchesB own a C=true ↔ touches own a C:=by simp [touchesB,touches]
theorem holds_eq {n:ℕ} (own:Fin n→Fin n) (a:Fin n) (C:Cluster n) :
    holdsB own a C=true ↔ holds own a C:=by
  by_cases h:C.Nonempty
  · simp only [holdsB,dif_pos h,beq_iff_eq,holds]
    constructor
    · intro eq;exact ⟨_,C.min'_mem h,eq,fun j hj=>C.min'_le _ hj⟩
    · rintro ⟨p,hp,eq,least⟩;rw [show C.min' h=p from le_antisymm (C.min'_le _ hp) (least _ (C.min'_mem h)),eq]
  · simp only [holdsB,dif_neg h,Bool.false_eq_true,false_iff,holds]
    rintro ⟨p,hp,_⟩;exact h ⟨p,hp⟩

theorem disjoint_iff_empty {n:ℕ} (C D:Cluster n) : Disjoint C D ↔ ¬(C∩D).Nonempty:=by
  simp [Finset.disjoint_left,Finset.Nonempty] <;> aesop

theorem compat_eq {n:ℕ} (own:Fin n→Fin n) (a b:Fin n) (P Q:List (Cluster n)) :
    compat own a b P Q=true ↔ compatible own a b P.toFinset Q.toFinset := by
  simp only [compat,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true',Bool.eq_false_iff,
    touches_eq,decide_eq_true_eq,disjoint_iff_empty,compatible,accepted,Finset.mem_filter,List.mem_toFinset]
  constructor
  · intro chk C hc D hd inter
    rcases chk C hc.1 D hd.1 with ((no|no)|no)|eq
    · exact False.elim (no ((touches_eq _ _ _).mpr hc.2))
    · exact False.elim (no ((touches_eq _ _ _).mpr hd.2))
    · exact False.elim (no inter)
    · exact eq
  · intro chk C hc D hd
    by_cases ta:touches own a C
    · by_cases tb:touches own b D
      · by_cases meet:(C∩D).Nonempty
        · exact Or.inr (chk C ⟨hc,ta⟩ D ⟨hd,tb⟩ meet)
        · exact Or.inl (Or.inr meet)
      · exact Or.inl (Or.inl (Or.inr ((touches_eq _ _ _).not.mpr tb)))
    · exact Or.inl (Or.inl (Or.inl ((touches_eq _ _ _).not.mpr ta)))

theorem masked {n:ℕ} (C:Cluster n) : (listed C).toFinset=C.image Fin.val:=by ext p;simp [listed]
theorem unorderedMask {n:ℕ} (C:Cluster n) : (C.toList.map Fin.val).toFinset=C.image Fin.val:=by ext p;simp

theorem owned_perm {n:ℕ} (own:Fin n→Fin n) (a:Fin n) (P:List (Cluster n)) (nd:P.Nodup) :
    MasksAgree ((P.filter (holdsB own a)).map listed) (SingleCodes.blockList (owned own a P.toFinset)):=by
  have eq:(P.filter (holdsB own a)).toFinset=owned own a P.toFinset:=by ext C;simp [owned,holds_eq]
  have perm: (P.filter (holdsB own a)).Perm (owned own a P.toFinset).toList:=by
    rw [←eq];exact (List.toFinset_toList (nd.filter _)).symm
  simpa only [MasksAgree,SingleCodes.blockList,List.map_map,Function.comp_def,masked,unorderedMask] using perm.map (fun C=>C.image Fin.val)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
open Compiler OracleQueries WindowCSP SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem menus_eq (x:World) (m:ℤ→ℤ) (U:Cluster x.n) (h:ℕ) :
    menus m U h=SingleCodes.menu (matrix x m) U h:=by
  unfold menus SingleCodes.menu
  congr 1;funext c
  apply Bool.eq_iff_iff.mpr
  rw [feasible_eq,decide_eq_true_eq,blocks_eq x m U h c]

theorem compat_windows (x:World) (m:ℤ→ℤ) (W:Cluster x.n) (h:ℕ) (a b:Fin x.n) (c k:ℕ) :
    compat (owner m (net m W)) a b (blocks m (win m W a) h c) (blocks m (win m W b) h k)=
    decide (compatible (anchor (matrix x m).dist W (unit x.n:ℝ)) a b
      (SingleCodes.decode (matrix x m) (window (matrix x m).dist W (unit x.n:ℝ) a) h c)
      (SingleCodes.decode (matrix x m) (window (matrix x m).dist W (unit x.n:ℝ) b) h k)):=by
  apply Bool.eq_iff_iff.mpr
  rw [compat_eq,decide_eq_true_eq,blocks_eq x m (win m W a) h c,blocks_eq x m (win m W b) h k,owner_eq x m W,win_eq x m W a,win_eq x m W b]

theorem firsts_nodup {α:Type} [DecidableEq α] (xs:List α) : xs.eraseDups.Nodup:=by
  have go (ls acc:List α) (nd:acc.Nodup) : (List.eraseDupsBy.loop (· == ·) ls acc).Nodup:=by
    induction ls generalizing acc with
    | nil=>simpa [List.eraseDupsBy.loop] using nd
    | cons a ls ih=>
      simp only [List.eraseDupsBy.loop]
      split
      · exact ih _ nd
      · rename_i eq
        have h:a∉acc:=by
          intro ha;have neq:∀x∈acc,¬a=x:=by simpa [List.any_eq_false] using eq
          exact neq _ ha rfl
        exact ih _ (List.nodup_cons.mpr ⟨h,nd⟩)
  exact go xs [] (by simp)
theorem owned_windows (x:World) (m:ℤ→ℤ) (W:Cluster x.n) (h:ℕ) (a:Fin x.n) (c:ℕ) :
    MasksAgree (((blocks m (win m W a) h c).filter (holdsB (owner m (net m W)) a)).map listed)
      (SingleCodes.blockList (owned (anchor (matrix x m).dist W (unit x.n:ℝ)) a
        (SingleCodes.decode (matrix x m) (window (matrix x m).dist W (unit x.n:ℝ) a) h c))) := by
  let P:=blocks m (win m W a) h c
  have nd:P.Nodup:=firsts_nodup _
  have perm:=owned_perm (owner m (net m W)) a P nd
  change MasksAgree _ (SingleCodes.blockList (owned (owner m (net m W)) a (blocks m (win m W a) h c).toFinset)) at perm
  rw [blocks_eq x m (win m W a) h c] at perm
  rw [←owner_eq x m W,←win_eq x m W a];exact perm

theorem lookup_congr {n:ℕ} {α:Type} (f g:Fin n→α) (j:ℕ) (alt:α) (fg:∀p,f p=g p) :
    lookup f j alt=SingleCodes.lookup g j alt:=by
  by_cases hj:j<n <;> simp [lookup,SingleCodes.lookup,hj,fg]
theorem normalized_ok (x:World) (m:ℤ→ℤ) (W:Cluster x.n) (h:ℕ) :
    let d:=SingleCodes.instanceOf (matrix x m) W (unit x.n:ℝ) h
    let t:=normalized m W h
    t.n=d.n ∧ t.active=d.active ∧ t.edge=d.edge ∧ t.menu=d.menu ∧ t.test=d.test ∧
      ∀a c,MasksAgree (t.owned a c) (d.owned a c):=by
  dsimp only [normalized,SingleCodes.instanceOf]
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · funext a;apply lookup_congr;intro v;rw [net_eq x m W]
  · funext a b;apply lookup_congr;intro v;apply lookup_congr;intro u
    simp only [near8 x m v u,near8 x m u v]
  · funext a;apply lookup_congr;intro v;rw [menus_eq x m (win m W v) h,win_eq x m W v]
  · funext a b c k;apply lookup_congr;intro v;apply lookup_congr;intro u;exact compat_windows x m W h v u c k
  · intro a c;by_cases ha:a<x.n
    · have h':a<(matrix x m).n:=ha
      simpa only [normalized,SingleCodes.instanceOf,lookup,SingleCodes.lookup,dif_pos ha,dif_pos h'] using owned_windows x m W h ⟨a,ha⟩ c
    · have h':¬a<(matrix x m).n:=ha
      simp only [normalized,SingleCodes.instanceOf,lookup,SingleCodes.lookup,dif_neg ha,dif_neg h',MasksAgree,List.map_nil,List.Perm.refl]


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
open SingleCircuit WindowCSP OracleQueries Compiler
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem indices_for {n:ℕ} (U:Cluster n) (f:Fin n→Cluster n) (q:List (Cluster n)) (nd:q.Nodup)
    (realizes:∀C∈q,∃i∈U,f i=C) :
    ∃is:List (Fin n),is.Nodup ∧ (∀i∈is,i∈U) ∧ is.map f=q:=by
  induction q with
  | nil=>exact ⟨[],by simp,by simp,by simp⟩
  | cons C cs ih=>
    obtain ⟨hc,tail⟩:=List.nodup_cons.mp nd
    obtain ⟨p,hp,eq⟩:=realizes C (by simp)
    obtain ⟨ps,unique,inside,rest⟩:=ih tail (fun D hd=>realizes D (List.mem_cons_of_mem _ hd))
    have absent:p∉ps:=by intro h;apply hc;rw [←rest,←eq];exact List.mem_map_of_mem h
    exact ⟨p::ps,List.nodup_cons.mpr ⟨absent,unique⟩,by simpa [hp] using inside,by simp [eq,rest]⟩

def indexed {n:ℕ} (m:ℤ→ℤ) (W:Cluster n) (h:ℕ) (ord:ℕ→ℕ→List (Fin n)) : Instance :=
  {normalized m W h with owned:=fun a c=>lookup (fun v:Fin n=>(ord a c).map (fun p=>listed (block m (win m W v) h c p))) a []}

theorem ordered_seed (x:World) (m:ℤ→ℤ) (W:Cluster x.n) (h:ℕ) (v:Fin x.n) (c:ℕ) :
   ∃is:List (Fin x.n),is.Nodup ∧ (∀p∈is,p∈win m W v) ∧
    (is.map (fun p=>(listed (block m (win m W v) h c p)).toFinset))=
      (((SingleCodes.instanceOf (matrix x m) W (unit x.n:ℝ) h).owned v.val c).map List.toFinset) := by
  let U:=win m W v
  let own:=owner m (net m W)
  let rows:=blocks m U h c
  let family:=owned own v rows.toFinset
  have real (C:Cluster x.n) (hc:C∈family.toList) : ∃p∈U,block m U h c p=C:=by
    have hm:C∈rows.toFinset:=(Finset.mem_filter.mp (Finset.mem_toList.mp hc)).1
    simpa [rows,blocks] using hm
  obtain ⟨is,nd,inside,order⟩:=indices_for U (block m U h c) family.toList family.nodup_toList real
  have masks: is.map (fun p=>(listed (block m U h c p)).toFinset)=(SingleCodes.blockList family).map List.toFinset:=by
    simpa only [List.map_map,Function.comp_def,SingleCodes.blockList,masked,unorderedMask] using
      congrArg (List.map (fun C:Cluster x.n=>C.image Fin.val)) order
  refine ⟨is,nd,inside,?_⟩
  have ix:v.val<(matrix x m).n:=v.isLt
  have fm:family=owned (anchor (matrix x m).dist W (unit x.n:ℝ)) v
      (SingleCodes.decode (matrix x m) (window (matrix x m).dist W (unit x.n:ℝ) v) h c):=by
    change owned own v (blocks m U h c).toFinset=_
    rw [blocks_eq x m U h c]
    change owned (owner m (net m W)) v (SingleCodes.decode (matrix x m) (win m W v) h c)=_
    rw [owner_eq x m W,win_eq x m W v]
  rw [fm] at masks
  simp only [SingleCodes.instanceOf,SingleCodes.lookup,dif_pos ix]
  with_unfolding_all exact masks


theorem choose_order (x:World) (m:ℤ→ℤ) (W:Cluster x.n) (h:ℕ) :
    ∃ord:ℕ→ℕ→List (Fin x.n),(∀a c,(ord a c).Nodup ∧ (ord a c).length≤x.n) ∧
    ∀a c,((indexed m W h ord).owned a c).map List.toFinset=
      ((SingleCodes.instanceOf (matrix x m) W (unit x.n:ℝ) h).owned a c).map List.toFinset := by
  choose seq nd inside same using ordered_seed x m W h
  let ord:=fun a c:ℕ=>lookup (fun p:Fin x.n=>seq p c) a []
  refine ⟨ord,?_,?_⟩
  · intro a c;by_cases ha:a<x.n
    · have nn:(ord a c).Nodup:=by simpa [ord,lookup,ha] using nd ⟨a,ha⟩ c
      exact ⟨nn,by simpa only [←List.toFinset_card_of_nodup nn,Fintype.card_fin] using (Finset.card_le_univ (ord a c).toFinset)⟩
    · simp [ord,lookup,ha]
  · intro a c;by_cases ha:a<x.n
    · have h':a<(matrix x m).n:=ha
      simpa only [indexed,ord,lookup,SingleCodes.instanceOf,SingleCodes.lookup,dif_pos ha,dif_pos h',List.map_map,
        Function.comp_def] using same ⟨a,ha⟩ c
    · have h':¬a<(matrix x m).n:=ha
      simp only [indexed,lookup,SingleCodes.instanceOf,SingleCodes.lookup,dif_neg ha,dif_neg h']

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
open SingleCircuit TightLanguage OracleQueries Compiler
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def renameMasks (f:List ℕ→List ℕ) (d:Instance) : Instance :=
  {d with owned:=fun a c=>(d.owned a c).map f}
def renameInstr (f:List ℕ→List ℕ) : Instr→Instr
  | .lit m=>.lit (f m)
  | .need k=>.need k | .close b=>.close b | .seal k=>.seal k | .finish=>.finish

theorem trial_map (f:List ℕ→List ℕ) (enc:Key→ℕ) (d:Instance) (c:List ℕ) (a:Assignment) (v x:ℕ) :
    (trial enc d c a v x).map (renameInstr f)=trial enc (renameMasks f d) c a v x:=by
  simp only [trial,List.map_append,List.map_map,List.map_singleton,Function.comp_def,renameInstr,renameMasks]
  rfl
theorem entry_map (f:List ℕ→List ℕ) (enc:Key→ℕ) (d:Instance) (c:List ℕ) (a:Assignment) :
    (entry enc d c a).map (renameInstr f)=entry enc (renameMasks f d) c a:=by
  simp only [entry,List.map_append,List.map_flatMap,List.map_singleton,renameInstr,trial_map]
  rfl
theorem visit_map (f:List ℕ→List ℕ) (enc:Key→ℕ) (d:Instance) (k:ℕ) (s c:List ℕ) :
    (visitTape enc d k s c).map (renameInstr f)=visitTape enc (renameMasks f d) k s c:=by
  have rim:rimOf (renameMasks f d) c=rimOf d c:=rfl
  have asn:assignments (renameMasks f d) s=assignments d s:=by
    induction s with
    | nil=>rfl
    | cons v vs ih=>simp only [assignments,ih];rfl
  unfold visitTape;rw [rim,asn]
  split <;> simp only [List.map_flatMap,entry_map,List.map_nil]
theorem tape_map (f:List ℕ→List ℕ) (enc:Key→ℕ) (d:Instance) (w:ℕ) :
    (tape enc d w).map (renameInstr f)=tape enc (renameMasks f d) w:=by
  simp only [tape,rowTape,List.map_append,List.map_flatMap,List.map_map,Function.comp_def,visit_map,
    List.map_singleton,renameInstr]
  rfl

def canon (l:List ℕ) := l.toFinset.sort (·≤·)
theorem canon_contains (l:List ℕ) (i:ℕ) : (canon l).contains i=l.contains i:=by
  apply Bool.eq_iff_iff.mpr;simp [canon,List.contains_iff_mem]

def slot (n:ℕ) (m:ℤ→ℤ) (j:ℕ) (e:Instr) :=
  m (inputCell 1 j)=e.tag ∧ m (inputCell 2 j)=e.arg ∧
    ∀mask,e=.lit mask → ∀i<n,m (inputCell 3 (j*n+i))=(if mask.contains i then 1 else 0)
theorem slot_canon (n:ℕ) (m:ℤ→ℤ) (j:ℕ) (e:Instr) :
    slot n m j (renameInstr canon e) ↔ slot n m j e:=by
  cases e <;> simp [slot,renameInstr,Instr.tag,Instr.arg,canon_contains,canon]
theorem input_map (n:ℕ) (m:ℤ→ℤ) (xs:List Instr) :
    Input n m (xs.map (renameInstr canon)) ↔ Input n m xs:=by
  change (_ ∧ ∀j (hj:j<(xs.map (renameInstr canon)).length),slot n m j ((xs.map (renameInstr canon))[j])) ↔
    (_ ∧ ∀j (hj:j<xs.length),slot n m j xs[j])
  simp only [List.length_map,List.getElem_map,slot_canon]

theorem tape_input_congr (n:ℕ) (m:ℤ→ℤ) (enc:Key→ℕ) (d t:Instance) (w:ℕ)
    (size:d.n=t.n) (active:d.active=t.active) (edge:d.edge=t.edge) (menu:d.menu=t.menu) (test:d.test=t.test)
    (masks:∀a c,(d.owned a c).map List.toFinset=(t.owned a c).map List.toFinset) :
    Input n m (tape enc d w) ↔ Input n m (tape enc t w):=by
  have eq:renameMasks canon d=renameMasks canon t:=by
    have mask:(fun a c=>(d.owned a c).map canon)=(fun a c=>(t.owned a c).map canon):=by
      have mapCanon (ls:List (List ℕ)) : ls.map canon=(ls.map List.toFinset).map (fun C:Finset ℕ=>C.sort (·≤·)):=by
        induction ls with
        | nil=>rfl
        | cons x xs ih=>simp only [List.map_cons,ih];rfl
      funext a c;rw [mapCanon,mapCanon,masks a c]
    cases d;cases t;simp only [renameMasks] at *;congr 1 <;> assumption
  rw [←input_map n m (tape enc d w),←input_map n m (tape enc t w),tape_map,tape_map,eq]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
open SingleCircuit WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem fields_at (x:World) (m:ℤ→ℤ) (r h:ℕ) :
    let t:=normalized m (piece x.n x.mem (r/x.n) (r%x.n)) h
    let d:=data x m r h
    t.n=d.n ∧ t.active=d.active ∧ t.edge=d.edge ∧ t.menu=d.menu ∧ t.test=d.test ∧
      ∀a c,MasksAgree (t.owned a c) (d.owned a c):=by
  change _;rw [piece_eq x];exact normalized_ok x m _ h

theorem ordered_tape (x:World) (m:ℤ→ℤ) (r h:ℕ) :
    let W:=piece x.n x.mem (r/x.n) (r%x.n)
    ∃ord:ℕ→ℕ→List (Fin x.n),(∀a c,(ord a c).Nodup ∧ (ord a c).length≤x.n) ∧
      ∀(enc:Key→ℕ) (w:ℕ) (mem:ℤ→ℤ),Input x.n mem (tape enc (indexed m W h ord) w) ↔
        Input x.n mem (tape enc (data x m r h) w):=by
  dsimp only
  rw [piece_eq x]
  let W:=WindowProfiles.piece x (r/x.n) (r%x.n)
  obtain ⟨ord,small,masks⟩:=choose_order x m W h
  obtain ⟨size,active,edge,menu,test,_⟩:=normalized_ok x m W h
  exact ⟨ord,small,fun enc w mem=>tape_input_congr x.n mem enc (indexed m W h ord) (data x m r h) w size active edge menu test masks⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
theorem solution
    (x:World) (m:ℤ→ℤ) (r h:ℕ) :
    let W:=Bits.piece x.n x.mem (r/x.n) (r%x.n)
    ∃ord:ℕ→ℕ→List (Fin x.n),(∀a c,(ord a c).Nodup ∧ (ord a c).length≤x.n) ∧
      let ownedRows:=fun (a c:ℕ)=>Bits.lookup (fun v:Fin x.n=>(ord a c).map (fun p=>Bits.listed (Bits.block m (Bits.win m W v) h c p))) a []
      let t:Instance:={Bits.normalized m W h with owned:=ownedRows}
      ∀(enc:Key→ℕ) (w:ℕ) (mem:ℤ→ℤ),Input x.n mem (tape enc t w) ↔ Input x.n mem (tape enc (data x m r h) w) := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits.ordered_tape x m r h
