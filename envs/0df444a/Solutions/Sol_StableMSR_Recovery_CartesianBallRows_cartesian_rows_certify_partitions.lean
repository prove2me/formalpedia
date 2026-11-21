-- Prove2me | solution 1 for StableMSR.Recovery.CartesianBallRows.cartesian_rows_certify_partitions
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:31:27.094516+00:00
-- url     : https://prove2.me/submissions/5a28b954-67f9-4bce-9e9f-d500ad341eb8

import Definitions.Def_StableMSR_CartesianBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private lemma oracleFin {n : ℕ} (d : Point n→Point n→ℝ) (i j : Fin n) :
    MinSumFPT.oracleAnswer d (i.val:ℤ) (j.val:ℤ)=d i j := by
  simp [MinSumFPT.oracleAnswer,MinSumFPT.toPoint,i.isLt,j.isLt]

theorem solution (x : World) (hn : 0 < x.n) (h : pairs x) :
    endpoints x ∧ ∀O,Feasible Finset.univ x.k O →
      ∃r < x.rows,good x r ∧ score x r=cost x.dist O := by
  classical
  refine ⟨?_,?_⟩
  · intro r hr j hj
    obtain ⟨hc,hw⟩ := h.2 r hr j hj
    exact ⟨⟨_,Nat.mod_lt _ hn⟩,⟨_,Nat.mod_lt _ hn⟩,hc,hw⟩
  intro O feasible
  let E : Fin x.k ≃ O := (Finset.equivFinOfCardEq feasible.1).symm
  let B (j : Fin x.k) : Cluster x.n := (E j).val
  have member (j : Fin x.k) : B j ∈ O := (E j).property
  have choosePair (j : Fin x.k) : ∃ c w : Fin x.n,c∈B j ∧ x.dist c w=radius x.dist (B j) ∧
      ∀i∈B j,x.dist c i ≤ x.dist c w := by
    have ne := feasible.2.1 _ (member j)
    obtain ⟨c,hc,eqc⟩ := Finset.exists_mem_eq_inf' ne (eccentricity x.dist (B j))
    obtain ⟨w,hw,eqw⟩ := Finset.exists_mem_eq_sup' ne (x.dist c)
    refine ⟨c,w,hc,?_,?_⟩
    · rw [radius,dif_pos ne,eqc,eccentricity,dif_pos ne,eqw]
    · intro i hi;rw [← eqw];exact Finset.le_sup' _ hi
  choose c w hc price cover using choosePair
  let val (i : Fin (2*x.k)) : Fin x.n :=
    if even : i.val%2=0 then c ⟨i.val/2,by have:=i.isLt;omega⟩ else w ⟨i.val/2,by have:=i.isLt;omega⟩
  let code : Fin (rows x.n x.k) := finFunctionFinEquiv val
  have hr : code.val < x.rows := by rw [h.1];exact code.isLt
  have digits (i : Fin (2*x.k)) : digit x.n code.val i.val=(val i).val :=
    congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply val) i)
  have C (j : Fin x.k) : center x code.val j.val=((c j).val:ℤ) := by
    rw [(h.2 _ hr _ j.isLt).1]
    have dd := digits ⟨2*j.val,by have:=j.isLt;omega⟩
    simpa [val] using congrArg (fun a : ℕ=>(a:ℤ)) dd
  have W (j : Fin x.k) : witness x code.val j.val=((w j).val:ℤ) := by
    rw [(h.2 _ hr _ j.isLt).2]
    have dd := digits ⟨2*j.val+1,by have:=j.isLt;omega⟩
    simpa [val,Nat.add_div] using congrArg (fun a : ℕ=>(a:ℤ)) dd
  have rad (j : Fin x.k) : charge x code.val j.val=radius x.dist (B j) := by
    rw [charge,C,W,oracleFin,price]
  refine ⟨code.val,hr,⟨?_,?_⟩,?_⟩
  · intro j hj l hl eq
    let a : Fin x.k := ⟨j,hj⟩
    let b : Fin x.k := ⟨l,hl⟩
    have v : c a=c b := Fin.ext (Int.ofNat.inj ((C a).symm.trans (eq.trans (C b))))
    by_contra ne
    have ab : B a ≠ B b := fun e=>ne (congrArg Fin.val (E.injective (Subtype.ext e)))
    have dis := feasible.2.2.1 (member a) (member b) ab
    exact (Finset.disjoint_left.mp dis) (hc a) (v ▸ hc b)
  · intro i hi
    let u : Fin x.n := ⟨i,hi⟩
    have hu : u ∈ O.biUnion id := by rw [feasible.2.2.2];exact Finset.mem_univ _
    obtain ⟨K,hK,mem⟩ := Finset.mem_biUnion.mp hu
    let j := E.symm ⟨K,hK⟩
    have bj : B j=K := congrArg Subtype.val (E.apply_symm_apply ⟨K,hK⟩)
    refine ⟨j.val,j.isLt,?_⟩
    change MinSumFPT.oracleAnswer x.dist (center x code.val j.val) (u.val:ℤ) ≤ charge x code.val j.val
    rw [C,oracleFin,charge,C,W,oracleFin]
    exact cover j u (bj ▸ mem)
  · calc
      score x code.val = ∑j : Fin x.k,charge x code.val j.val := (Fin.sum_univ_eq_sum_range _ _).symm
      _ = ∑j : Fin x.k,radius x.dist (B j) := Finset.sum_congr rfl (fun j _=>rad j)
      _ = ∑K : O,radius x.dist K.val := E.sum_comp (fun K=>radius x.dist K.val)
      _ = cost x.dist O := Finset.sum_attach _ _
