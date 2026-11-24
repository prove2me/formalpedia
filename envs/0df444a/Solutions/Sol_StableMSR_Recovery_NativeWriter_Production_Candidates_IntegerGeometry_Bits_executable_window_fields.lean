-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits.executable_window_fields
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T00:32:07.54156+00:00
-- url     : https://prove2.me/submissions/f8c55362-60b1-4555-864f-c01df394a321

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
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem fields_at (x:World) (m:ℤ→ℤ) (r h:ℕ) :
    let t:=normalized m (piece x.n x.mem (r/x.n) (r%x.n)) h
    let d:=data x m r h
    t.n=d.n ∧ t.active=d.active ∧ t.edge=d.edge ∧ t.menu=d.menu ∧ t.test=d.test ∧
      ∀a c,MasksAgree (t.owned a c) (d.owned a c):=by
  change _;rw [piece_eq x];exact normalized_ok x m _ h

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
theorem solution
    (x:World) (m:ℤ→ℤ) (r h:ℕ) :
    let t:=Bits.normalized m (Bits.piece x.n x.mem (r/x.n) (r%x.n)) h
    let d:=data x m r h
    t.n=d.n ∧ t.active=d.active ∧ t.edge=d.edge ∧ t.menu=d.menu ∧ t.test=d.test ∧
      ∀a c,Bits.MasksAgree (t.owned a c) (d.owned a c) := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits.fields_at x m r h
