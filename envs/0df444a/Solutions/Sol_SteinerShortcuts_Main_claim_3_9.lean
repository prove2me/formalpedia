-- Prove2me | solution 1 for SteinerShortcuts.Main.claim_3_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:40:15.671111+00:00
-- url     : https://prove2.me/submissions/a3f2f3e4-cbf4-4db4-a2da-954a3e619e3c

import Theorems.Thm_SteinerShortcuts_Main_claim_2_6
import Theorems.Thm_SteinerShortcuts_Main_claim_3_8
import Definitions.Def_SteinerShortcuts_Main_Graphs
open SteinerShortcuts.Main
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

private def atV {V : Type} (P : Route V) (i : ℕ) : V := P.vertices[i]?.getD P.start

private theorem atV_some {V : Type} (P : Route V) (i : ℕ) (hi : i ≤ P.length) :
    P.vertices[i]? = some (atV P i) := by
  have hh : i < P.vertices.length := by simp [Route.vertices,Route.length] at *;omega
  simp [atV,List.getElem?_eq_getElem hh]

private theorem atV_start {V : Type} (P : Route V) : atV P 0 = P.start := by
  simp [atV,Route.vertices]

private theorem atV_finish {V : Type} (P : Route V) : atV P P.length = P.finish := by
  have hi : P.length = P.vertices.length-1 := by simp [Route.vertices,Route.length]
  unfold atV
  rw [hi,← List.getLast?_eq_getElem?]
  change P.vertices.getLastD P.start = P.finish
  simp only [Route.vertices,Route.finish,List.getLastD_cons]

private theorem mem_atV {V : Type} (P : Route V) (v : V) (hv : v ∈ P.vertices) :
    ∃ i ≤ P.length, v = atV P i := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hv
  refine ⟨i,by simp [Route.vertices,Route.length] at hi ⊢;omega,?_⟩
  simpa [atV,List.getElem?_eq_getElem hi] using he.symm

private theorem atV_mem {V : Type} (P : Route V) (i : ℕ) (hi : i ≤ P.length) :
    atV P i ∈ P.vertices := by
  exact List.mem_iff_getElem?.mpr ⟨i,atV_some P i hi⟩

private theorem adj_atV {V : Type} (G : Digraph V) (P : Route V) (hp : IsPath G P)
    (i : ℕ) (hi : i < P.length) : G.Adj (atV P i) (atV P (i+1)) := by
  have h0 : i < P.vertices.length := by simp [Route.vertices,Route.length] at *;omega
  have h1 : i+1 < P.vertices.length := by simp [Route.vertices,Route.length] at *;omega
  have hh := List.isChain_iff_getElem.mp hp i h1
  simpa [atV,List.getElem?_eq_getElem h0,List.getElem?_eq_getElem h1] using hh

private theorem reach_indices {V : Type} (G : Digraph V) (P : Route V) (hp : IsPath G P)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ P.length) : Reaches G (atV P i) (atV P j) := by
  revert hj
  induction j, hij using Nat.le_induction with
  | base => intro hj;exact .refl
  | succ j hij ih =>
    intro hj
    exact (ih (by omega)).tail (adj_atV G P hp j (by omega))

private theorem path_layer {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P : Route V) (hp : IsPath G P) (i : ℕ) (hi : i ≤ P.length) :
    layer (atV P i) = layer P.start+i := by
  induction i with
  | zero => simp [atV_start]
  | succ i ih =>
    have hh := hl _ _ (adj_atV G P hp i (by omega))
    rw [ih (by omega)] at hh
    exact hh

private theorem reach_on_path {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P : Route V) (hp : IsPath G P) (u v : V) (hu : u ∈ P.vertices) (hv : v ∈ P.vertices)
    (huv : layer u ≤ layer v) : Reaches G u v := by
  obtain ⟨i,hi,rfl⟩ := mem_atV P u hu
  obtain ⟨j,hj,rfl⟩ := mem_atV P v hv
  have hli := path_layer G layer hl P hp i hi
  have hlj := path_layer G layer hl P hp j hj
  exact reach_indices G P hp i j (by omega) hj

private theorem path_reaches {V : Type} (G : Digraph V) (P : Route V) (hp : IsPath G P) :
    Reaches G P.start P.finish := by
  have hh := reach_indices G P hp 0 P.length (by omega) (by omega)
  simpa only [atV_start,atV_finish] using hh

private theorem reaches_route {V : Type} (G : Digraph V) (u v : V) (h : Reaches G u v) :
    ∃ P : Route V, IsPath G P ∧ P.start=u ∧ P.finish=v := by
  obtain ⟨l,hl,hend⟩ := List.exists_isChain_cons_of_relationReflTransGen h
  refine ⟨⟨u,l⟩,hl,rfl,?_⟩
  change l.getLastD u = v
  simpa only [List.getLast_eq_getLastD] using hend

private def cat {V : Type} (P Q : Route V) : Route V := ⟨P.start,P.tail++Q.tail⟩

private theorem cat_vertices {V : Type} (P Q : Route V) :
    (cat P Q).vertices = P.vertices++Q.tail := by simp [cat,Route.vertices]

private theorem cat_path {V : Type} (G : Digraph V) (P Q : Route V)
    (hp : IsPath G P) (hq : IsPath G Q) (he : P.finish=Q.start) : IsPath G (cat P Q) := by
  rcases P with ⟨a,l⟩
  induction l generalizing a with
  | nil =>
    change a=Q.start at he
    simpa [cat,Route.vertices,he] using hq
  | cons b l ih =>
    have hp' := List.isChain_cons_cons.mp hp
    have he' : (⟨b,l⟩ : Route V).finish=Q.start := by simpa only [Route.finish,List.getLastD_cons] using he
    have hh := ih b hp'.2 he'
    exact List.isChain_cons_cons.mpr ⟨hp'.1,hh⟩

private theorem lastD_append {V : Type} (l m : List V) (a : V) :
    (l++m).getLastD a = m.getLastD (l.getLastD a) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simpa only [List.cons_append,List.getLastD_cons] using ih b

private theorem cat_finish {V : Type} (P Q : Route V) (he : P.finish=Q.start) :
    (cat P Q).finish=Q.finish := by
  change (P.tail++Q.tail).getLastD P.start = Q.tail.getLastD Q.start
  rw [lastD_append]
  change Q.tail.getLastD P.finish = Q.tail.getLastD Q.start
  rw [he]

private theorem start_mem {V : Type} (P : Route V) : P.start ∈ P.vertices := by simp [Route.vertices]
private theorem finish_mem {V : Type} (P : Route V) : P.finish ∈ P.vertices := List.getLastD_mem_cons

private theorem cat_mem_left {V : Type} (P Q : Route V) (v : V) (hv : v ∈ P.vertices) :
    v ∈ (cat P Q).vertices := by rw [cat_vertices];exact List.mem_append_left _ hv

private theorem unique_through {V : Type} (G : Digraph V) (P : Route V)
    (hu : ∀ Q, IsPath G Q → Q.start=P.start → Q.finish=P.finish → Q=P)
    (v : V) (h1 : Reaches G P.start v) (h2 : Reaches G v P.finish) : v ∈ P.vertices := by
  obtain ⟨A,hA,hAs,hAt⟩ := reaches_route G _ _ h1
  obtain ⟨B,hB,hBs,hBt⟩ := reaches_route G _ _ h2
  have he : A.finish=B.start := hAt.trans hBs.symm
  have hcat := cat_path G A B hA hB he
  have heq := hu (cat A B) hcat hAs ((cat_finish A B he).trans hBt)
  have hv : v ∈ (cat A B).vertices := cat_mem_left A B v (by rw [← hAt];exact finish_mem A)
  rwa [heq] at hv

private theorem reach_prefix {V : Type} (G : Digraph V) (P : Route V) (hp : IsPath G P)
    (v : V) (hv : v ∈ P.vertices) : Reaches G P.start v := by
  obtain ⟨i,hi,rfl⟩ := mem_atV P v hv
  simpa only [atV_start] using reach_indices G P hp 0 i (by omega) hi

private theorem reach_suffix {V : Type} (G : Digraph V) (P : Route V) (hp : IsPath G P)
    (v : V) (hv : v ∈ P.vertices) : Reaches G v P.finish := by
  obtain ⟨i,hi,rfl⟩ := mem_atV P v hv
  simpa only [atV_finish] using reach_indices G P hp i P.length hi (by omega)

private theorem triangle_ordered {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (A B C : Route V) (hA : IsPath G A) (hB : IsPath G B) (hC : IsPath G C)
    (uA : ∀ Q, IsPath G Q → Q.start=A.start → Q.finish=A.finish → Q=A)
    (uB : ∀ Q, IsPath G Q → Q.start=B.start → Q.finish=B.finish → Q=B)
    (uC : ∀ Q, IsPath G Q → Q.start=C.start → Q.finish=C.finish → Q=C)
    (x y z : V) (hxA : x ∈ A.vertices) (hxB : x ∈ B.vertices)
    (hyA : y ∈ A.vertices) (hyC : y ∈ C.vertices) (hzB : z ∈ B.vertices) (hzC : z ∈ C.vertices)
    (hxy : layer x ≤ layer y) : ∃ v, v ∈ A.vertices ∧ v ∈ B.vertices ∧ v ∈ C.vertices := by
  by_cases hzx : layer z ≤ layer x
  · refine ⟨x,hxA,hxB,?_⟩
    apply unique_through G C uC x
    · exact (reach_prefix G C hC z hzC).trans (reach_on_path G layer hl B hB z x hzB hxB hzx)
    · exact (reach_on_path G layer hl A hA x y hxA hyA hxy).trans (reach_suffix G C hC y hyC)
  · by_cases hzy : layer z ≤ layer y
    · refine ⟨z,?_,hzB,hzC⟩
      apply unique_through G A uA z
      · exact (reach_prefix G A hA x hxA).trans (reach_on_path G layer hl B hB x z hxB hzB (by omega))
      · exact (reach_on_path G layer hl C hC z y hzC hyC hzy).trans (reach_suffix G A hA y hyA)
    · refine ⟨y,hyA,?_,hyC⟩
      apply unique_through G B uB y
      · exact (reach_prefix G B hB x hxB).trans (reach_on_path G layer hl A hA x y hxA hyA hxy)
      · exact (reach_on_path G layer hl C hC y z hyC hzC (by omega)).trans (reach_suffix G B hB z hzB)

private theorem triangle_common {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (A B C : Route V) (hA : IsPath G A) (hB : IsPath G B) (hC : IsPath G C)
    (uA : ∀ Q, IsPath G Q → Q.start=A.start → Q.finish=A.finish → Q=A)
    (uB : ∀ Q, IsPath G Q → Q.start=B.start → Q.finish=B.finish → Q=B)
    (uC : ∀ Q, IsPath G Q → Q.start=C.start → Q.finish=C.finish → Q=C)
    (x y z : V) (hxA : x ∈ A.vertices) (hxB : x ∈ B.vertices)
    (hyA : y ∈ A.vertices) (hyC : y ∈ C.vertices) (hzB : z ∈ B.vertices) (hzC : z ∈ C.vertices) :
    ∃ v, v ∈ A.vertices ∧ v ∈ B.vertices ∧ v ∈ C.vertices := by
  by_cases hxy : layer x ≤ layer y
  · exact triangle_ordered G layer hl A B C hA hB hC uA uB uC x y z hxA hxB hyA hyC hzB hzC hxy
  · obtain ⟨v,hvA,hvC,hvB⟩ := triangle_ordered G layer hl A C B hA hC hB uA uC uB y x z
      hyA hyC hxA hxB hzC hzB (by omega)
    exact ⟨v,hvA,hvB,hvC⟩

private theorem route_ext {V : Type} (P Q : Route V) (he : P.vertices=Q.vertices) : P=Q := by
  cases P with | mk a l =>
    cases Q with | mk b m =>
      simp only [Route.vertices,List.cons.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      rfl

private theorem layer_injective {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P : Route V) (hp : IsPath G P) (u v : V) (hu : u ∈ P.vertices) (hv : v ∈ P.vertices)
    (he : layer u=layer v) : u=v := by
  obtain ⟨i,hi,rfl⟩ := mem_atV P u hu
  obtain ⟨j,hj,rfl⟩ := mem_atV P v hv
  have hli := path_layer G layer hl P hp i hi
  have hlj := path_layer G layer hl P hp j hj
  have hij : i=j := by omega
  rw [hij]

private theorem vertex_at_layer {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P : Route V) (hp : IsPath G P) (ell : ℕ) (hlo : layer P.start ≤ ell) (hhi : ell ≤ layer P.finish) :
    ∃ v ∈ P.vertices, layer v=ell := by
  have hlast := path_layer G layer hl P hp P.length (by omega)
  rw [atV_finish] at hlast
  have hi : ell-layer P.start ≤ P.length := by omega
  refine ⟨atV P (ell-layer P.start),atV_mem P _ hi,?_⟩
  have hh := path_layer G layer hl P hp (ell-layer P.start) hi
  omega

private theorem subpath_subset {V : Type} (P S : Route V) (hsub : IsSubpath S P) :
    ∀ v ∈ S.vertices, v ∈ P.vertices := by
  obtain ⟨pre,post,he⟩ := hsub
  intro v hv
  rw [he]
  exact List.mem_append_left post (List.mem_append_right pre hv)

private theorem subpath_path {V : Type} (G : Digraph V) (P S : Route V)
    (hp : IsPath G P) (hsub : IsSubpath S P) : IsPath G S := by
  obtain ⟨pre,post,he⟩ := hsub
  unfold IsPath at hp ⊢
  rw [he] at hp
  exact hp.left_of_append.right_of_append

private theorem same_length {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P Q : Route V) (hp : IsPath G P) (hq : IsPath G Q) (hs : P.start=Q.start) (ht : P.finish=Q.finish) :
    P.length=Q.length := by
  have hP := path_layer G layer hl P hp P.length (by omega)
  have hQ := path_layer G layer hl Q hq Q.length (by omega)
  rw [atV_finish,hs,ht] at hP
  rw [atV_finish] at hQ
  omega

private theorem route_eq_indices {V : Type} (P Q : Route V) (hlen : P.length=Q.length)
    (he : ∀ i ≤ P.length, atV P i=atV Q i) : P=Q := by
  apply route_ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i ≤ P.length
  · rw [atV_some P i hi,atV_some Q i (by omega),he i hi]
  · have hP : P.vertices[i]?=none := List.getElem?_eq_none_iff.mpr (by simp [Route.vertices,Route.length] at *;omega)
    have hQ : Q.vertices[i]?=none := List.getElem?_eq_none_iff.mpr (by simp [Route.vertices,Route.length] at *;omega)
    rw [hP,hQ]

private theorem subpath_unique {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P S : Route V) (hp : IsPath G P)
    (hu : ∀ Q, IsPath G Q → Q.start=P.start → Q.finish=P.finish → Q=P)
    (hsub : IsSubpath S P) : IsPath G S ∧
      ∀ Q, IsPath G Q → Q.start=S.start → Q.finish=S.finish → Q=S := by
  have hS := subpath_path G P S hp hsub
  have hss := subpath_subset P S hsub S.start (start_mem S)
  have hst := subpath_subset P S hsub S.finish (finish_mem S)
  refine ⟨hS,?_⟩
  intro Q hQ hs ht
  have hQsub : ∀ v ∈ Q.vertices, v ∈ P.vertices := by
    intro v hv
    apply unique_through G P hu v
    · have hh := reach_prefix G Q hQ v hv
      rw [hs] at hh
      exact (reach_prefix G P hp S.start hss).trans hh
    · have hh := reach_suffix G Q hQ v hv
      rw [ht] at hh
      exact hh.trans (reach_suffix G P hp S.finish hst)
  have hlen := same_length G layer hl Q S hQ hS hs ht
  apply route_eq_indices Q S hlen
  intro i hi
  apply layer_injective G layer hl P hp _ _ (hQsub _ (atV_mem Q i hi))
    (subpath_subset P S hsub _ (atV_mem S i (by omega)))
  rw [path_layer G layer hl Q hQ i hi,path_layer G layer hl S hS i (by omega),hs]

private theorem member_in_subpath {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P S : Route V) (hp : IsPath G P) (hS : IsPath G S)
    (hsub : ∀ v ∈ S.vertices, v ∈ P.vertices) (v : V) (hv : v ∈ P.vertices)
    (hlo : layer S.start ≤ layer v) (hhi : layer v ≤ layer S.finish) : v ∈ S.vertices := by
  obtain ⟨w,hw,he⟩ := vertex_at_layer G layer hl S hS (layer v) hlo hhi
  have hveq := layer_injective G layer hl P hp v w hv (hsub w hw) he.symm
  rwa [hveq]

private theorem reach_layer_le {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (u v : V) (hr : Reaches G u v) : layer u ≤ layer v := by
  induction hr with
  | refl => rfl
  | tail hxy hyz ih => have hh:=hl _ _ hyz;omega

private theorem cat_mem_right {V : Type} (P Q : Route V) (he : P.finish=Q.start)
    (v : V) (hv : v ∈ Q.vertices) : v ∈ (cat P Q).vertices := by
  rcases List.mem_cons.mp hv with hv | hv
  · subst v
    rw [← he]
    exact cat_mem_left P Q P.finish (finish_mem P)
  · rw [cat_vertices]
    exact List.mem_append_right _ hv

private theorem extended_cross {V : Type} (G : Digraph V) (P Q S T : Route V)
    (hP : IsPath G P) (hQ : IsPath G Q) (hsubS : ∀ v ∈ S.vertices, v ∈ P.vertices)
    (hsubT : ∀ v ∈ T.vertices, v ∈ Q.vertices) (hST : Reaches G S.start T.finish) :
    ∃ R, IsCrossPath G P Q R ∧ S.start ∈ R.vertices ∧ T.finish ∈ R.vertices := by
  have hSu := hsubS S.start (start_mem S)
  have hTv := hsubT T.finish (finish_mem T)
  obtain ⟨A,hA,hAs,hAt⟩ := reaches_route G _ _ (reach_prefix G P hP S.start hSu)
  obtain ⟨B,hB,hBs,hBt⟩ := reaches_route G _ _ hST
  obtain ⟨C,hC,hCs,hCt⟩ := reaches_route G _ _ (reach_suffix G Q hQ T.finish hTv)
  have heAB : A.finish=B.start := hAt.trans hBs.symm
  have heBC : (cat A B).finish=C.start := (cat_finish A B heAB).trans (hBt.trans hCs.symm)
  have hAB := cat_path G A B hA hB heAB
  refine ⟨cat (cat A B) C,⟨cat_path G _ _ hAB hC heBC,hAs,
    (cat_finish _ _ heBC).trans hCt⟩,?_,?_⟩
  · exact cat_mem_left _ C _ (cat_mem_left A B _ (by rw [← hAt];exact finish_mem A))
  · exact cat_mem_left _ C _ (cat_mem_right A B heAB _ (by rw [← hBt];exact finish_mem B))

private theorem take_layer_bound {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P : Route V) (hP : IsPath G P) (i : ℕ) (hi : i ≤ P.length)
    (v : V) (hv : v ∈ P.vertices.take (i+1)) : layer v ≤ layer (atV P i) := by
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hv
  rw [List.getElem?_take] at hj
  split_ifs at hj with hji
  · obtain ⟨hjlen,_⟩ := List.getElem?_eq_some_iff.mp hj
    have hjP : j ≤ P.length := by simp [Route.vertices,Route.length] at hjlen ⊢;omega
    have hvj : v=atV P j := by simp [atV,hj]
    rw [hvj,path_layer G layer hl P hP j hjP,path_layer G layer hl P hP i hi]
    omega

private theorem drop_layer_bound {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P : Route V) (hP : IsPath G P) (i : ℕ) (hi : i ≤ P.length)
    (v : V) (hv : v ∈ P.vertices.drop (i+1)) : layer (atV P i) < layer v := by
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hv
  rw [List.getElem?_drop] at hj
  obtain ⟨hjlen,_⟩ := List.getElem?_eq_some_iff.mp hj
  have hjP : i+1+j ≤ P.length := by simp [Route.vertices,Route.length] at hjlen ⊢;omega
  have hvj : v=atV P (i+1+j) := by simp [atV,hj]
  rw [hvj,path_layer G layer hl P hP _ hjP,path_layer G layer hl P hP i hi]
  omega

private theorem splice_between {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P Q R : Route V) (hP : IsPath G P) (hQ : IsPath G Q) (hsp : Splices P Q R)
    (u v : V) (huP : u ∈ P.vertices) (hvQ : v ∈ Q.vertices)
    (huR : u ∈ R.vertices) (hvR : v ∈ R.vertices) (huv : layer u ≤ layer v) :
    ∃ w, w ∈ P.vertices ∧ w ∈ Q.vertices ∧ layer u ≤ layer w ∧ layer w ≤ layer v := by
  obtain ⟨i,j,hi,hj,hshared,heq⟩ := hsp
  have hi' : i ≤ P.length := by simp [Route.vertices,Route.length] at hi ⊢;omega
  have hj' : j ≤ Q.length := by simp [Route.vertices,Route.length] at hj ⊢;omega
  rw [atV_some P i hi',atV_some Q j hj'] at hshared
  have hww : atV P i=atV Q j := Option.some.inj hshared
  have hwP := atV_mem P i hi'
  have hwQ : atV P i ∈ Q.vertices := by rw [hww];exact atV_mem Q j hj'
  have after (x : V) (hx : x ∈ R.vertices) (hh : layer (atV P i) ≤ layer x) : x ∈ Q.vertices := by
    rw [heq] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have hb := take_layer_bound G layer hl P hP i hi' x hx
      have he := layer_injective G layer hl P hP x (atV P i) (List.mem_of_mem_take hx) hwP (by omega)
      rwa [he]
    · exact List.mem_of_mem_drop hx
  have before (x : V) (hx : x ∈ R.vertices) (hh : layer x ≤ layer (atV P i)) : x ∈ P.vertices := by
    rw [heq] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_of_mem_take hx
    · have hb := drop_layer_bound G layer hl Q hQ j hj' x hx
      rw [← hww] at hb
      omega
  by_cases hlu : layer (atV P i) ≤ layer u
  · exact ⟨u,huP,after u huR hlu,by omega,huv⟩
  · by_cases hlv : layer v ≤ layer (atV P i)
    · exact ⟨v,before v hvR hlv,hvQ,huv,by omega⟩
    · exact ⟨atV P i,hwP,hwQ,by omega,by omega⟩

private theorem common_fill {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P Q : Route V) (hP : IsPath G P) (hQ : IsPath G Q)
    (uQ : ∀ R, IsPath G R → R.start=Q.start → R.finish=Q.finish → R=Q)
    (u v : V) (huP : u ∈ P.vertices) (huQ : u ∈ Q.vertices)
    (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices) (ell : ℕ)
    (hlo : layer u ≤ ell) (hhi : ell ≤ layer v) :
    ∃ w, w ∈ P.vertices ∧ w ∈ Q.vertices ∧ layer w=ell := by
  have hstart := reach_layer_le G layer hl _ _ (reach_prefix G P hP u huP)
  have hfinish := reach_layer_le G layer hl _ _ (reach_suffix G P hP v hvP)
  obtain ⟨w,hwP,hwell⟩ := vertex_at_layer G layer hl P hP ell (by omega) (by omega)
  refine ⟨w,hwP,?_,hwell⟩
  apply unique_through G Q uQ w
  · exact (reach_prefix G Q hQ u huQ).trans (reach_on_path G layer hl P hP u w huP hwP (by omega))
  · exact (reach_on_path G layer hl P hP w v hwP hvP (by omega)).trans (reach_suffix G Q hQ v hvQ)

private theorem subpaths_meet {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P Q S T : Route V) (hP : IsPath G P) (hQ : IsPath G Q)
    (uQ : ∀ R, IsPath G R → R.start=Q.start → R.finish=Q.finish → R=Q)
    (hS : IsPath G S) (hT : IsPath G T)
    (hsubS : ∀ v ∈ S.vertices, v ∈ P.vertices) (hsubT : ∀ v ∈ T.vertices, v ∈ Q.vertices)
    (sp : CompatiblePair G P Q → ∀ R, IsCrossPath G P Q R → Splices P Q R)
    (sq : CompatiblePair G Q P → ∀ R, IsCrossPath G Q P R → Splices Q P R)
    (hc : CompatiblePair G S T) : ∃ v, v ∈ S.vertices ∧ v ∈ T.vertices := by
  obtain ⟨R,hR,hSuR,hTvR⟩ := extended_cross G P Q S T hP hQ hsubS hsubT hc.1
  obtain ⟨U,hU,hTuU,hSvU⟩ := extended_cross G Q P T S hQ hP hsubT hsubS hc.2
  have hreachR := path_reaches G R hR.1
  have hreachU := path_reaches G U hU.1
  rw [hR.2.1,hR.2.2] at hreachR
  rw [hU.2.1,hU.2.2] at hreachU
  have hparent : CompatiblePair G P Q := ⟨hreachR,hreachU⟩
  have hparent' : CompatiblePair G Q P := ⟨hreachU,hreachR⟩
  have hST := reach_layer_le G layer hl _ _ hc.1
  have hTS := reach_layer_le G layer hl _ _ hc.2
  obtain ⟨a,haP,haQ,halo,hahi⟩ := splice_between G layer hl P Q R hP hQ (sp hparent R hR)
    S.start T.finish (hsubS _ (start_mem S)) (hsubT _ (finish_mem T)) hSuR hTvR hST
  obtain ⟨b,hbQ,hbP,hblo,hbhi⟩ := splice_between G layer hl Q P U hQ hP (sq hparent' U hU)
    T.start S.finish (hsubT _ (start_mem T)) (hsubS _ (finish_mem S)) hTuU hSvU hTS
  have hSS := reach_layer_le G layer hl _ _ (path_reaches G S hS)
  have hTT := reach_layer_le G layer hl _ _ (path_reaches G T hT)
  let ell := max (max (layer S.start) (layer T.start)) (min (layer a) (layer b))
  have helllo : min (layer a) (layer b) ≤ ell := by dsimp [ell];omega
  have hellhi : ell ≤ max (layer a) (layer b) := by dsimp [ell];omega
  have hellSlo : layer S.start ≤ ell := by dsimp [ell];omega
  have hellShi : ell ≤ layer S.finish := by dsimp [ell];omega
  have hellTlo : layer T.start ≤ ell := by dsimp [ell];omega
  have hellThi : ell ≤ layer T.finish := by dsimp [ell];omega
  have hex : ∃ w, w ∈ P.vertices ∧ w ∈ Q.vertices ∧ layer w=ell := by
    by_cases hab : layer a ≤ layer b
    · exact common_fill G layer hl P Q hP hQ uQ a b haP haQ hbP hbQ ell (by omega) (by omega)
    · exact common_fill G layer hl P Q hP hQ uQ b a hbP hbQ haP haQ ell (by omega) (by omega)
  obtain ⟨w,hwP,hwQ,hwell⟩ := hex
  refine ⟨w,?_,?_⟩
  · exact member_in_subpath G layer hl P S hP hS hsubS w hwP (by omega) (by omega)
  · exact member_in_subpath G layer hl Q T hQ hT hsubT w hwQ (by omega) (by omega)

private theorem layer_coordinate (L q ell : ℕ) (r : ℤ) (v : Point)
    (hv : v ∈ layerBox L q ell r) : v 0 = (ell:ℤ) := by
  have hh := Fintype.mem_piFinset.mp hv 0
  simpa using hh

private theorem construction_layered (L q : ℕ) :
    IsLayered (construction L q) (fun v => (v 0).toNat) := by
  intro v w he
  obtain ⟨hv,hw,hL,t,ht⟩ := he
  have hv0 : 0 ≤ v 0 := by
    rcases Finset.mem_union.mp hv with hv | hv
    · rw [layer_coordinate L q 1 1 v hv];omega
    · obtain ⟨ell,hell,hv⟩ := Finset.mem_biUnion.mp hv
      rw [layer_coordinate L q ell 2 v hv];omega
  have hh : w 0 = v 0+1 := by rw [ht];simp [step,update]
  change (w 0).toNat=(v 0).toNat+1
  omega

 theorem solution (L q : ℕ) (h : Admissible L q) (subpaths : Finset (Route Point))
    (hs : ∀ R ∈ subpaths, ∃ P ∈ criticalPaths L q, IsSubpath R P) :
    P1 (construction L q) subpaths ∧ P2 (construction L q) subpaths := by
  have hp1 := claim_2_6 L q h
  let layer : Point → ℕ := fun v => (v 0).toNat
  have hl : IsLayered (construction L q) layer := construction_layered L q
  constructor
  · intro S hS
    obtain ⟨P,hP,hSP⟩ := hs S hS
    have hpP := hp1 P hP
    exact subpath_unique (construction L q) layer hl P S hpP.1 hpP.2 hSP
  · intro S hS T hT hc
    obtain ⟨P,hP,hSP⟩ := hs S hS
    obtain ⟨Q,hQ,hTQ⟩ := hs T hT
    have hpP := hp1 P hP
    have hpQ := hp1 Q hQ
    have hsS := subpath_path (construction L q) P S hpP.1 hSP
    have hsT := subpath_path (construction L q) Q T hpQ.1 hTQ
    have hsubS := subpath_subset P S hSP
    have hsubT := subpath_subset Q T hTQ
    obtain ⟨sab,hsab,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨tab,htab,rfl⟩ := Finset.mem_image.mp hQ
    let DP : CriticalData q := ⟨sab.1,sab.2.1,sab.2.2⟩
    let DQ : CriticalData q := ⟨tab.1,tab.2.1,tab.2.2⟩
    have hDP : DP.Valid L := (Finset.mem_product.mp hsab).1
    have hDQ : DQ.Valid L := (Finset.mem_product.mp htab).1
    apply subpaths_meet (construction L q) layer hl (DP.route L) (DQ.route L) S T
      hpP.1 hpQ.1 hpQ.2 hsS hsT hsubS hsubT ?_ ?_ hc
    · intro hcompat R hR
      exact claim_3_8 L q h DP DQ hDP hDQ hcompat R hR
    · intro hcompat R hR
      exact claim_3_8 L q h DQ DP hDQ hDP hcompat R hR
