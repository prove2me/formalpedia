-- Prove2me | solution 1 for StableMSR.Recovery.WindowCSP.finite_pairwise_cost_plan
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T16:10:54.113472+00:00
-- url     : https://prove2.me/submissions/859416b7-3b67-44e0-bc74-3a9a5903e539

import Theorems.Thm_StableMSR_Recovery_TreeDP_bounded_treewidth_dp
import Definitions.Def_StableMSR_WindowPlans
import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
open StableMSR.Recovery.TreeDP
private noncomputable def choices {V X : Type} [DecidableEq V] (b : Finset V) (D : V→Finset X) (base : X) :
    Finset (V→X) :=
  (Fintype.piFinset (fun v : ↥b=>D v.val)).image (fun f v=>if hv : v∈b then f ⟨v,hv⟩ else base)
private lemma match_choices {V X : Type} [DecidableEq V] (b : Finset V) (D : V→Finset X) (base : X) (f : V→X) :
    (∃g∈choices b D base,AgreeOn b f g) ↔ ∀v∈b,f v∈D v := by
  classical
  constructor
  · rintro ⟨g,mem,eq⟩ v hv
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp mem
    rw [eq v hv];simpa only [dif_pos hv] using (Fintype.mem_piFinset.mp hu ⟨v,hv⟩)
  · intro dom
    let u (v : ↥b):=f v.val
    let g (v : V):=if h : v∈b then u ⟨v,h⟩ else base
    refine ⟨g,Finset.mem_image.mpr ⟨u,Fintype.mem_piFinset.mpr (fun v=>dom v v.property),rfl⟩,?_⟩
    intro v hv;simp [g,u,hv]
private lemma bound_choices {V X : Type} [DecidableEq V] (b : Finset V) (D : V→Finset X) (base : X)
    (B : ℕ) (bd : ∀v,(D v).card≤ B) : (choices b D base).card≤ B^b.card := by
  unfold choices;apply Finset.card_image_le.trans
  rw [Fintype.card_piFinset]
  calc
    _ ≤ ∏_ : ↥b,B := Finset.prod_le_prod' (fun v _=>bd v.val)
    _ = _ := by simp
theorem solution {V X : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ)
    (tw : RobertsonSeymour1986.GM5.TreewidthLE G w) (D : V→Finset X) (fallback : X)
    (test : V→V→X→X→Prop) (cnt : V→X→ℕ) (cost' : V→X→ℝ) (B : ℕ)
    (bpos : 1≤ B) (bd : ∀v,(D v).card≤ B) :
    ∃p : TreeDP.Plan V X,p.Coherent ∧ p.Local ∧ p.nodes≤2*Fintype.card V+1 ∧
    p.AllData (fun d=>d.bag.card≤ w+1 ∧ d.choices.card≤ B^(w+1)) ∧
    (∀cap,p.tableVolume cap≤(2*Fintype.card V+1)*(B^(w+1)*(cap+1)) ∧
      p.rawCandidateVolume cap≤(2*Fintype.card V+1)*((B^(w+1))^3*(cap+1)^2)) ∧
    ∀cap j,j≤ cap → ∀f : V→X,admissible G D test f → (∑v,cnt v (f v))=j →
      ∃u∈TreeDP.solve cap p,∃g : V→X,u.2.1=j ∧ admissible G D test g ∧
        (∑v,cnt v (g v))=j ∧ (∑v,cost' v (g v))=u.2.2 ∧
        ∀g' : V→X,admissible G D test g' → (∑v,cnt v (g' v))=j → u.2.2≤∑v,cost' v (g' v) := by
  classical
  obtain ⟨T,ft,dt,tree,bags,td,sizes,_,build⟩:=bounded_treewidth_dp (X:=X) G w tw
  letI : Fintype T:=ft
  letI : DecidableEq T:=dt
  choose home member using td.2.1
  let fibers (t : T):=(Finset.univ : Finset V).filter (fun v=>home v=t)
  let check (t : T) (f : V→X):=∀v∈bags t,∀u∈bags t,G.Adj v u → test v u (f v) (f u)
  let data (t : T) : BagData V X:={
    bag:=bags t, choices:=choices (bags t) D fallback,valid:=check t,
    count:=fun f=>∑v ∈ fibers t,cnt v (f v),weight:=fun f=>∑v ∈ fibers t,cost' v (f v)}
  have loc (t : T) : (data t).Local := by
    intro a b eq
    have inbag {v : V} (hv : v∈fibers t) : v∈bags t :=
      (Finset.mem_filter.mp hv).2 ▸ member v
    have take {a b : V→X} (e : AgreeOn (bags t) a b) (h : check t a) : check t b := by
      intro v hv u hu edge
      rw [←e v hv,←e u hu];exact h v hv u hu edge
    refine ⟨⟨take eq,take (fun v hv=>(eq v hv).symm)⟩,?_,?_⟩
    · exact Finset.sum_congr rfl (fun v hv=>congrArg (cnt v) (eq v (inbag hv)))
    · exact Finset.sum_congr rfl (fun v hv=>congrArg (cost' v) (eq v (inbag hv)))
  have sz (t : T) : (data t).choices.card≤ B^(w+1) :=
    (bound_choices _ _ _ _ bd).trans (Nat.pow_le_pow_right bpos (sizes t))
  obtain ⟨p,co,lo,nn,all,_,bounds,_,opt⟩:=build data (B^(w+1)) (fun _=>rfl) loc sz
  have yes (f : V→X) : admissible G D test f ↔
      (∀t,(data t).valid f) ∧ (∀t,∃u∈(data t).choices,AgreeOn (data t).bag f u) := by
    constructor
    · rintro ⟨hs,edges⟩
      exact ⟨fun _ v _ u _=>edges v u,fun t=>(match_choices _ _ _ _).mpr (fun v _=>hs v)⟩
    · rintro ⟨tests,dom⟩
      refine ⟨fun v=>(match_choices _ _ _ _).mp (dom (home v)) v (member v),?_⟩
      intro v u edge;obtain ⟨t,hv,hu⟩:=td.2.2.1 v u edge
      exact tests t v hv u hu edge
  have count_eq (f : V→X) : (∑t,(data t).count f)=∑v,cnt v (f v) :=
    Finset.sum_fiberwise Finset.univ home _
  have cost_eq (f : V→X) : (∑t,(data t).weight f)=∑v,cost' v (f v) :=
    Finset.sum_fiberwise Finset.univ home _
  refine ⟨p,co,lo,nn,all,bounds,?_⟩
  intro cap j hj f af cf
  obtain ⟨hv,hd⟩:=(yes f).mp af
  obtain ⟨u,hu,g,uj,vg,dg,cg,pg,min⟩:=opt cap j hj ⟨f,hv,hd,(count_eq f).trans cf⟩
  refine ⟨u,hu,g,uj,(yes g).mpr ⟨vg,dg⟩,(count_eq g).symm.trans cg,(cost_eq g).symm.trans pg,?_⟩
  intro o ao co
  obtain ⟨vo,do'⟩:=(yes o).mp ao
  exact (min o vo do' ((count_eq o).trans co)).trans_eq (cost_eq o)

