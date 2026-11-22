-- Prove2me | solution 1 for StableMSR.Recovery.WindowMasks.physical_block_literals
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:26:25.235488+00:00
-- url     : https://prove2.me/submissions/908575ca-9689-43db-8276-b6fc0a9556c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_StableMSR_WindowBlockMasks
import Theorems.Thm_StableMSR_Recovery_WindowMasks_canonical_block_endpoints
import Theorems.Thm_StableMSR_Recovery_WindowMasks_block_trace_word_correspondence
import Theorems.Thm_StableMSR_Recovery_WindowCSP_pairwise_windows_glue
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowMasks
private structure SameTopology (A B : Board) : Prop where
  vol : A.size=B.size
  fields : ∀q< A.size,A.tag q=B.tag q ∧ A.dest q=B.dest q ∧ A.child q=B.child q
private def SameTopology.flip {A B : Board} (s : SameTopology A B) : SameTopology B A where
  vol:=s.vol.symm
  fields:=by intro q h;obtain ⟨a,b,c⟩:=s.fields q (s.vol.symm ▸ h);exact ⟨a.symm,b.symm,c.symm⟩
private lemma tracesAcross {n : ℕ} (F : ℕ→Cluster n) {A B : Board} (s : SameTopology A B) :
    ∀p L,Trace A F p L → Trace B F p L:=by
  have lit {q p : ℕ} (h : initial A q p) : initial B q p:=by
    obtain ⟨t,d,c⟩:=s.fields _ h.1;unfold initial at *;simpa only [←s.vol,←t,←d] using h
  have ported {z : ℤ} {q p : ℕ} (h : port A z q p) : port B z q p:=by
    obtain ⟨t,d,c⟩:=s.fields _ h.1;unfold port at *;simpa only [←s.vol,←t,←d,←c] using h
  intro p L h;induction h with
  | literal h=>exact .literal (lit h)
  | @fork l r p L R hl hr _ _ il ir =>
    exact .fork (ported hl) (ported hr) ((s.fields _ hl.1).2.2 ▸ il) ((s.fields _ hr.1).2.2 ▸ ir)
private lemma inhabitedBlocks {n : ℕ} {B : Board} {F : ℕ→Cluster n} {p L} (h : Trace B F p L) :
    ∀C∈L,C.Nonempty:=by
  induction h with
  | @literal q p init =>
    intro C hc;by_cases ne : (F q).Nonempty
    · simpa [emit,ne] using (show C=F q from by simpa [emit,ne] using hc) ▸ ne
    · simp [emit,ne] at hc
  | fork _ _ _ _ il ir =>
    intro C hc;rcases List.mem_append.mp hc with left|right
    · exact il C left
    · exact ir C right
private lemma distinct {n : ℕ} (L : List (Cluster n)) (ne : ∀C∈L,C.Nonempty) (h : L.Pairwise Disjoint) : L.Nodup:=by
  induction L with
  | nil=>simp
  | cons C L ih=>
    obtain ⟨cross,tail⟩:=List.pairwise_cons.mp h
    refine List.nodup_cons.mpr ⟨?_,ih (fun D d=>ne D (List.mem_cons_of_mem _ d)) tail⟩
    intro mem;obtain ⟨p,hp⟩:=ne C (List.mem_cons_self ..)
    exact Finset.disjoint_left.mp (cross C mem) hp hp
private lemma paySet {n : ℕ} (d : Point n→Point n→ℝ) (L : List (Cluster n)) (nodup : L.Nodup) : payment d L=cost d L.toFinset:=by
  induction L with
  | nil=>simp [payment,cost]
  | cons a L ih=>
    obtain ⟨na,nd⟩:=List.nodup_cons.mp nodup
    have ne : a∉L.toFinset:=by simpa using na
    simpa [payment,cost,Finset.sum_insert ne] using congrArg (fun v=>radius d a+v) (ih nd)
private lemma subAt (x : World) (p q : ℕ) (h : q< x.rows) : subR x (p+q) p=q:=by
  unfold subR;rw [Finset.sum_eq_single q]
  · simp
  · intro j _ ne;exact if_neg (by omega)
  · intro no;exact (no (Finset.mem_range.mpr h)).elim
theorem solution (x : World) (e : ℚ) (H : ℕ) (m f : WindowProfiles.Mem) (hk : 1≤ x.k) (kn : x.k< x.n)
    (dm : IsMetricArray x.dist) (cert : Describes x e {x with rows:=H,mem:=m})
    (head0 : f 0=m 0) (head1 : f 1=m 1)
    (fill : Writes {x with rows:=H,mem:=m} {x with rows:=H,mem:=f} normalized) :
    Presents x e {x with rows:=H,mem:=f} := by
  let y : World:={x with rows:=H,mem:=m}
  let z : World:={x with rows:=H,mem:=f}
  let A:=board y;let B:=board z;let M:=rawSize y
  have sz : rawSize z=M:=congrArg Int.toNat head0
  have roomY : 1+5*(1+M*x.n*x.n)< H:=cert.space
  have major : M≤ M*x.n*x.n:=by
    have pos : 0< x.n:=by omega
    exact (Nat.le_mul_of_pos_right M pos).trans (Nat.le_mul_of_pos_right _ pos)
  have scene : z.mem 1=(x.rows:ℤ):=head1.trans cert.scenes
  have bandEQ (b q j : ℕ) (hb : b≤3) (hq : q< M) (hj : j< x.k) (s : Bool) :
      readBand z b q j s=normalized y (1+b*M+q) j s:=by
    unfold readBand;rw [sz]
    apply fill (1+b*M+q) (by change 1+b*M+q< H;interval_cases b <;> omega) j hj s
  have fields (q : ℕ) (hq : q< M) :
      B.tag q=A.tag q ∧ B.dest q=A.dest q ∧ B.child q=A.child q ∧ B.arity q=chargeCount y q:=by
    have e:=bandEQ 0 q 0 (by decide) hq hk false;have g:=bandEQ 0 q 0 (by decide) hq hk true
    have s:=bandEQ 1 q 0 (by decide) hq hk false;have t:=bandEQ 1 q 0 (by decide) hq hk true
    have addr:=subAt y (1+M) q (by change q< H;omega)
    have nz : 1+q≠0:=by omega
    have bz : 1+M+q≠0:=by omega
    have na : ¬(1+M≤1+q ∧ 1+q<1+2*M):=by omega
    have nb : ¬(1+2*M≤1+q ∧ 1+q<1+3*M):=by omega
    have ab : 1+M≤1+M+q ∧ 1+M+q<1+2*M:=by omega
    simp only [normalized,←show M=rawSize y from rfl,Nat.zero_mul,Nat.add_zero,Nat.one_mul,if_neg nz,if_neg bz,if_neg na,if_neg nb,if_pos ab,addr] at e g s t
    have raw0 (w : Bool) : field y (1+q) 0 w=readBand y 0 q 0 w:=by simp [readBand]
    have raw1 : field y (1+M+q) 0 false=readBand y 1 q 0 false:=by simp [readBand,M]
    simp only [Bool.false_eq_true,if_false,if_true] at s t
    exact ⟨e.trans (raw0 false),congrArg Int.toNat (g.trans (raw0 true)),congrArg Int.toNat (s.trans raw1),(congrArg Int.toNat t).trans (Int.toNat_natCast _)⟩
  have val (q : ℕ) (hq : q< B.size) (j : ℕ) (hj : j< x.k) (s : Bool) : B.value q j s=oneWord y q j s:=by
    have sm : B.size=M:=sz
    have h : q< M:=sm ▸ hq
    have eq:=bandEQ 2 q j (by decide) h hj s
    have t:=subAt y (1+2*M) q (by change q< H;omega)
    have lo : ¬(1+M≤1+2*M+q ∧ 1+2*M+q<1+2*M):=by omega
    have mid : 1+2*M≤1+2*M+q ∧ 1+2*M+q<1+3*M:=by omega
    simp only [normalized,←show M=rawSize y from rfl,if_neg (show 1+2*M+q≠0 by omega),if_neg lo,if_pos mid,t] at eq
    change legalize x.n (readBand z 2 q j s)=_;rw [eq];exact if_pos ((canonical_block_endpoints y q hk (by change 0< x.n;omega)).2.2.2 j s)
  have root (q : ℕ) (h : q< M) : B.root q=A.root q:=by
    have eq:=bandEQ 3 q 0 (by decide) h hk false
    have lo : ¬(1+M≤1+3*M+q ∧ 1+3*M+q<1+2*M):=by omega
    have hi : ¬(1+2*M≤1+3*M+q ∧ 1+3*M+q<1+3*M):=by omega
    simp only [normalized,←show M=rawSize y from rfl,if_neg (show 1+3*M+q≠0 by omega),if_neg lo,if_neg hi] at eq
    exact congrArg Int.toNat eq
  have topo : SameTopology B A:=
    ⟨sz,fun q h=>by have t:=fields q (sz ▸ h);exact ⟨t.1,t.2.1,t.2.2.1⟩⟩
  have counts (q : ℕ) (hq : q< B.size) : B.arity q=chargeCount y q:=(fields q (sz ▸ hq)).2.2.2
  obtain ⟨forward,back⟩:=block_trace_word_correspondence y B hk (by change 0< x.n;omega) counts val
  refine ⟨?_,scene,?_⟩
  · change 1+5*(1+rawSize z*x.n*x.n)< H;rwa [sz]
  · intro u hu i hi
    obtain ⟨lt,pin,sound,zero,rep⟩:=cert.targets u hu i hi
    let a:=u*x.n+i;let v:=A.root a
    have eq : B.root a=v:=root a lt
    change a< B.size ∧ B.root a< B.size ∧ _
    refine ⟨topo.vol.symm ▸ lt,by rw [eq,topo.vol];exact pin,?_⟩
    intro c hc;change (∀w,Reach x.k B (B.root a) c w → _) ∧ _;rw [eq]
    refine ⟨?_,?_,?_⟩
    · intro w dw;obtain ⟨L,tr,ll,cost,own⟩:=forward _ _ _ dw
      obtain ⟨dis,un⟩:=sound L (tracesAcross _ topo _ _ tr)
      exact un ▸ own dis
    · intro absent cz;subst c
      obtain ⟨w,d,_⟩:=back v [] (tracesAcross _ topo.flip _ _ (zero absent)) (by simp);exact ⟨w,d⟩
    · intro present pos tw P admiss cnt
      obtain ⟨L,tr,equals⟩:=rep present pos tw P admiss (cnt ▸ hc)
      obtain ⟨feas,price,_⟩:=pairwise_windows_glue x (piece x u i) (scale x u) _ P dm pos.le admiss
      have nd:=distinct L (inhabitedBlocks tr) (sound L tr).1
      have len : L.length=c:=(List.toFinset_card_of_nodup nd).symm.trans ((congrArg Finset.card equals).trans (feas.1.trans cnt))
      obtain ⟨w,d,pay⟩:=back v L (tracesAcross _ topo.flip _ _ tr) (len ▸ hc)
      refine ⟨w,len ▸ d,?_⟩
      change weight y c w≤_;rw [←len,pay,paySet _ _ nd,equals];exact price.le
