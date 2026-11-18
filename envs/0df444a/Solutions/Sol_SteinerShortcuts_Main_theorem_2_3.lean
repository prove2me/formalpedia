-- Prove2me | solution 1 for SteinerShortcuts.Main.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:57:05.84157+00:00
-- url     : https://prove2.me/submissions/caa91a8d-017a-4276-8c82-d29ca2d032b6

import Definitions.Def_SteinerShortcuts_Main_Replacement
import Theorems.Thm_SteinerShortcuts_Main_lemma_2_4
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

private structure RepSetup (V W : Type) [Fintype V] [Fintype W] where
  G : Digraph V
  layer : V → ℕ
  layered : IsLayered G layer
  paths : Finset (Route V)
  unique : P1 G paths
  overlap : P2 G paths
  extra : Finset ((V ⊕ W) × (V ⊕ W))
  shortcut : IsSteinerShortcut G extra
  chosen : Route V → Route (V ⊕ W)
  selection : ShortestSelection G extra paths chosen

private noncomputable def fam {V W : Type} [Fintype V] [Fintype W] (D : RepSetup V W) (x : V ⊕ W) :=
  vertexFamily D.paths D.chosen x
private noncomputable def cand {V W : Type} [Fintype V] [Fintype W] (D : RepSetup V W) (x : V ⊕ W) :=
  replacements D.paths D.chosen x
private noncomputable def lo {V W : Type} [Fintype V] [Fintype W] (D : RepSetup V W) (x : V ⊕ W) :=
  leftLayer D.layer D.paths D.chosen x
private noncomputable def hi {V W : Type} [Fintype V] [Fintype W] (D : RepSetup V W) (x : V ⊕ W) :=
  rightLayer D.layer D.paths D.chosen x
private noncomputable def used {V W : Type} [Fintype V] [Fintype W] (D : RepSetup V W) :=
  prunedEdges D.extra D.paths D.chosen

private theorem arc_vertices {V : Type} (P : Route V) (e : V × V) (he : e ∈ P.arcs) :
    e.1 ∈ P.vertices ∧ e.2 ∈ P.vertices := by
  have hh : e.1 ∈ P.vertices ∧ e.2 ∈ P.tail := List.of_mem_zip he
  exact ⟨hh.1,by simp [Route.vertices,hh.2]⟩

private theorem fam_subset {V W : Type} [Fintype V] [Fintype W] (D : RepSetup V W) (x : V ⊕ W) :
    fam D x ⊆ D.paths := Finset.filter_subset _ _

private theorem fam_compatible {V W : Type} [Fintype V] [Fintype W] (D : RepSetup V W) (x : V ⊕ W) :
    CompatibleFamily D.G (fam D x) := by
  intro P hP Q hQ
  have hPx := (Finset.mem_filter.mp hP).2
  have hQx := (Finset.mem_filter.mp hQ).2
  have hp := D.selection P (fam_subset D x hP)
  have hq := D.selection Q (fam_subset D x hQ)
  have h1 := reach_prefix (augment D.G D.extra) (D.chosen P) hp.1 x hPx
  have h2 := reach_suffix (augment D.G D.extra) (D.chosen Q) hq.1 x hQx
  rw [hp.2.1] at h1
  rw [hq.2.2.1] at h2
  exact (D.shortcut P.start Q.finish).mpr (h1.trans h2)

private theorem chosen_original_mem {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (P : Route V) (hP : P ∈ D.paths) (v : V)
    (hv : Sum.inl v ∈ (D.chosen P).vertices) : v ∈ P.vertices := by
  have hp := D.selection P hP
  have h1 := reach_prefix (augment D.G D.extra) (D.chosen P) hp.1 (Sum.inl v) hv
  have h2 := reach_suffix (augment D.G D.extra) (D.chosen P) hp.1 (Sum.inl v) hv
  rw [hp.2.1] at h1
  rw [hp.2.2.1] at h2
  exact unique_through D.G P (D.unique P hP).2 v
    ((D.shortcut P.start v).mpr h1) ((D.shortcut v P.finish).mpr h2)

private theorem candidate_member {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (x : V ⊕ W) (v : V) (hv : v ∈ cand D x) (P : Route V)
    (hP : P ∈ fam D x) : v ∈ P.vertices := by
  cases x with
  | inl u =>
    have he : v=u := by simpa [cand,replacements] using hv
    subst v
    exact chosen_original_mem D P (fam_subset D _ hP) u ((Finset.mem_filter.mp hP).2)
  | inr w => exact (Finset.mem_filter.mp hv).2 P hP

private theorem candidate_nonempty {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (x : V ⊕ W) (hx : (fam D x).Nonempty) : (cand D x).Nonempty := by
  cases x with
  | inl u => exact ⟨u,by simp [cand,replacements]⟩
  | inr w =>
    obtain ⟨v,hv⟩ := lemma_2_4 D.G D.layer D.layered D.paths D.unique D.overlap
      (fam D (Sum.inr w)) (fam_subset D _) hx (fam_compatible D _)
    exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩

private theorem component_edge_family {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (C : Finset W) (x y : V ⊕ W)
    (he : (componentGraph (used D) C).Adj x y) : ∃ P, P ∈ fam D x ∧ P ∈ fam D y := by
  have hp := (Finset.mem_filter.mp he).1
  obtain ⟨P,hP,hparc⟩ := (Finset.mem_filter.mp hp).2
  have hxy := arc_vertices (D.chosen P) (x,y) hparc
  exact ⟨P,Finset.mem_filter.mpr ⟨hP,hxy.1⟩,Finset.mem_filter.mpr ⟨hP,hxy.2⟩⟩

private theorem component_family_nonempty {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (C : Finset W) (x : V ⊕ W)
    (hx : x ∈ componentVertices (used D) C) : (fam D x).Nonempty := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨e,he,hex⟩ := Finset.mem_image.mp hx
    have hh := component_edge_family D C e.1 e.2 he
    obtain ⟨P,hP,hQ⟩ := hh
    rw [hex] at hP
    exact ⟨P,hP⟩
  · obtain ⟨e,he,hex⟩ := Finset.mem_image.mp hx
    have hh := component_edge_family D C e.1 e.2 he
    obtain ⟨P,hP,hQ⟩ := hh
    rw [hex] at hQ
    exact ⟨P,hQ⟩

private theorem candidate_interval {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (x : V ⊕ W) (P : Route V) (hP : P ∈ fam D x)
    (a b w : V) (ha : a ∈ cand D x) (hb : b ∈ cand D x) (hw : w ∈ P.vertices)
    (hlo : D.layer a ≤ D.layer w) (hhi : D.layer w ≤ D.layer b) : w ∈ cand D x := by
  have hp := (D.unique P (fam_subset D x hP)).1
  have haP := candidate_member D x a ha P hP
  have hbP := candidate_member D x b hb P hP
  cases x with
  | inl u =>
    have hau : a=u := by simpa [cand,replacements] using ha
    have hbu : b=u := by simpa [cand,replacements] using hb
    rw [hau] at hlo
    rw [hbu] at hhi
    have hwu : w=u := layer_injective D.G D.layer D.layered P hp w u hw
      (by simpa [hau] using haP) (by omega)
    simp [cand,replacements,hwu]
  | inr z =>
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro Q hQ
    have hq := D.unique Q (fam_subset D _ hQ)
    have haQ := candidate_member D (Sum.inr z) a ha Q hQ
    have hbQ := candidate_member D (Sum.inr z) b hb Q hQ
    apply unique_through D.G Q hq.2 w
    · exact (reach_prefix D.G Q hq.1 a haQ).trans (reach_on_path D.G D.layer D.layered P hp a w haP hw hlo)
    · exact (reach_on_path D.G D.layer D.layered P hp w b hw hbP hhi).trans (reach_suffix D.G Q hq.1 b hbQ)

private theorem lo_min {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (x : V ⊕ W) (hx : (cand D x).Nonempty) :
    lo D x = ((cand D x).image D.layer).min' (hx.image D.layer) := by
  change (if h : ((cand D x).image D.layer).Nonempty then
    ((cand D x).image D.layer).min' h else 0) = _
  rw [dif_pos (hx.image D.layer)]

private theorem lo_mem {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (x : V ⊕ W) (hx : (cand D x).Nonempty) :
    ∃ v ∈ cand D x, D.layer v=lo D x := by
  have hh := Finset.min'_mem ((cand D x).image D.layer) (hx.image D.layer)
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hh
  exact ⟨v,hv,he.trans (lo_min D x hx).symm⟩

private theorem lo_le {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (x : V ⊕ W) (hx : (cand D x).Nonempty) (v : V) (hv : v ∈ cand D x) :
    lo D x ≤ D.layer v := by
  rw [lo_min D x hx]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)

private theorem le_hi {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (x : V ⊕ W) (v : V) (hv : v ∈ cand D x) : D.layer v ≤ hi D x := by
  exact Finset.le_sup hv

private theorem hi_mem {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (x : V ⊕ W) (hx : (cand D x).Nonempty) :
    ∃ v ∈ cand D x, D.layer v=hi D x := by
  obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image (cand D x) D.layer hx
  refine ⟨v,hv,Nat.le_antisymm (le_hi D x v hv) ?_⟩
  exact Finset.sup_le hmax

private theorem candidate_at {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (x : V ⊕ W) (hx : (fam D x).Nonempty)
    (ell : ℕ) (hlo : lo D x ≤ ell) (hhi : ell ≤ hi D x) :
    ∃ v ∈ cand D x, D.layer v=ell := by
  have hc := candidate_nonempty D x hx
  obtain ⟨a,ha,hal⟩ := lo_mem D x hc
  obtain ⟨b,hb,hbl⟩ := hi_mem D x hc
  obtain ⟨P,hP⟩ := hx
  have hp := (D.unique P (fam_subset D x hP)).1
  have haP := candidate_member D x a ha P hP
  have hbP := candidate_member D x b hb P hP
  have hstart := reach_layer_le D.G D.layer D.layered _ _ (reach_prefix D.G P hp a haP)
  have hfinish := reach_layer_le D.G D.layer D.layered _ _ (reach_suffix D.G P hp b hbP)
  obtain ⟨v,hv,hvell⟩ := vertex_at_layer D.G D.layer D.layered P hp ell (by omega) (by omega)
  refine ⟨v,candidate_interval D x P hP a b v ha hb hv (by omega) (by omega),hvell⟩

private theorem reach_eq_or_lt {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (u v : V) (hr : Reaches G u v) : u=v ∨ layer u < layer v := by
  induction hr with
  | refl => exact Or.inl rfl
  | tail hxy hyz ih =>
    have hh := hl _ _ hyz
    have hh' := reach_layer_le G layer hl _ _ hxy
    exact Or.inr (by omega)

private theorem reach_antisymm {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (u v : V) (h1 : Reaches G u v) (h2 : Reaches G v u) : u=v := by
  rcases reach_eq_or_lt G layer hl u v h1 with he | hh
  · exact he
  · have hh' := reach_layer_le G layer hl v u h2
    omega

private theorem fam_prefix {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (x : V ⊕ W) (P : Route V) (hP : P ∈ fam D x) :
    Reaches (augment D.G D.extra) (Sum.inl P.start) x := by
  have hp := D.selection P (fam_subset D x hP)
  have hh := reach_prefix (augment D.G D.extra) (D.chosen P) hp.1 x ((Finset.mem_filter.mp hP).2)
  rwa [hp.2.1] at hh

private theorem fam_suffix {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (x : V ⊕ W) (P : Route V) (hP : P ∈ fam D x) :
    Reaches (augment D.G D.extra) x (Sum.inl P.finish) := by
  have hp := D.selection P (fam_subset D x hP)
  have hh := reach_suffix (augment D.G D.extra) (D.chosen P) hp.1 x ((Finset.mem_filter.mp hP).2)
  rwa [hp.2.2.1] at hh

private theorem candidate_intersection {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (u x : V ⊕ W) (hu : (fam D u).Nonempty) (hx : (fam D x).Nonempty)
    (wu wx : V) (hwu : wu ∈ cand D u) (hwx : wx ∈ cand D x)
    (hforward : Reaches (augment D.G D.extra) u x) (hback : Reaches D.G wx wu) :
    ∃ v, v ∈ cand D u ∧ v ∈ cand D x := by
  classical
  cases u with
  | inl u =>
    have hwu' : wu=u := by simpa [cand,replacements] using hwu
    cases x with
    | inl x =>
      have hwx' : wx=x := by simpa [cand,replacements] using hwx
      have hux := (D.shortcut u x).mpr hforward
      have hxu : Reaches D.G x u := by simpa [hwu',hwx'] using hback
      have he := reach_antisymm D.G D.layer D.layered u x hux hxu
      exact ⟨u,by simp [cand,replacements],by simpa [cand,replacements] using he⟩
    | inr x =>
      refine ⟨u,by simp [cand,replacements],?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro Q hQ
      have hq := D.unique Q (fam_subset D _ hQ)
      have hwxQ := candidate_member D (Sum.inr x) wx hwx Q hQ
      have h1 := (reach_prefix D.G Q hq.1 wx hwxQ).trans hback
      rw [hwu'] at h1
      have h2 := (D.shortcut u Q.finish).mpr (hforward.trans (fam_suffix D _ Q hQ))
      exact unique_through D.G Q hq.2 u h1 h2
  | inr u =>
    cases x with
    | inl x =>
      have hwx' : wx=x := by simpa [cand,replacements] using hwx
      refine ⟨x,?_,by simp [cand,replacements]⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro P hP
      have hp := D.unique P (fam_subset D _ hP)
      have hwuP := candidate_member D (Sum.inr u) wu hwu P hP
      have h1 := (D.shortcut P.start x).mpr ((fam_prefix D _ P hP).trans hforward)
      have h2 := hback.trans (reach_suffix D.G P hp.1 wu hwuP)
      rw [hwx'] at h2
      exact unique_through D.G P hp.2 x h1 h2
    | inr x =>
      have forward (P : Route V) (hP : P ∈ fam D (Sum.inr u))
          (Q : Route V) (hQ : Q ∈ fam D (Sum.inr x)) : Reaches D.G P.start Q.finish :=
        (D.shortcut P.start Q.finish).mpr
          ((fam_prefix D _ P hP).trans (hforward.trans (fam_suffix D _ Q hQ)))
      have back (Q : Route V) (hQ : Q ∈ fam D (Sum.inr x))
          (P : Route V) (hP : P ∈ fam D (Sum.inr u)) : Reaches D.G Q.start P.finish := by
        have hq := (D.unique Q (fam_subset D _ hQ)).1
        have hp := (D.unique P (fam_subset D _ hP)).1
        have hwxQ := candidate_member D _ wx hwx Q hQ
        have hwuP := candidate_member D _ wu hwu P hP
        exact (reach_prefix D.G Q hq wx hwxQ).trans (hback.trans (reach_suffix D.G P hp wu hwuP))
      have hsubset : fam D (Sum.inr u) ∪ fam D (Sum.inr x) ⊆ D.paths := by
        intro P hP
        rcases Finset.mem_union.mp hP with hP | hP
        · exact fam_subset D _ hP
        · exact fam_subset D _ hP
      have hcomp : CompatibleFamily D.G (fam D (Sum.inr u) ∪ fam D (Sum.inr x)) := by
        intro P hP Q hQ
        rcases Finset.mem_union.mp hP with hP | hP
        · rcases Finset.mem_union.mp hQ with hQ | hQ
          · exact fam_compatible D _ P hP Q hQ
          · exact forward P hP Q hQ
        · rcases Finset.mem_union.mp hQ with hQ | hQ
          · exact back P hP Q hQ
          · exact fam_compatible D _ P hP Q hQ
      obtain ⟨P,hP⟩ := hu
      have hne : (fam D (Sum.inr u) ∪ fam D (Sum.inr x)).Nonempty :=
        ⟨P,Finset.mem_union_left _ hP⟩
      obtain ⟨v,hv⟩ := lemma_2_4 D.G D.layer D.layered D.paths D.unique D.overlap _ hsubset hne hcomp
      refine ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
      · intro P hP;exact hv P (Finset.mem_union_left _ hP)
      · intro Q hQ;exact hv Q (Finset.mem_union_right _ hQ)

private theorem component_edge_vertices {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (C : Finset W) (x y : V ⊕ W)
    (he : (componentGraph (used D) C).Adj x y) :
    x ∈ componentVertices (used D) C ∧ y ∈ componentVertices (used D) C := by
  exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(x,y),he,rfl⟩),
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x,y),he,rfl⟩)⟩

private theorem component_reach_augment {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (C : Finset W) (x y : V ⊕ W)
    (hr : Reaches (componentGraph (used D) C) x y) : Reaches (augment D.G D.extra) x y := by
  induction hr with
  | refl => exact .refl
  | tail hxy hyz ih =>
    have hp := (Finset.mem_filter.mp hyz).1
    have he := (Finset.mem_filter.mp hp).1
    exact ih.tail (Or.inl he)

private theorem first_exit {A : Type} (r : A → A → Prop) (p : A → Prop)
    (u y : A) (hr : Relation.ReflTransGen r u y) (hu : p u) (hy : ¬ p y) :
    ∃ v x, Relation.ReflTransGen r u v ∧ r v x ∧ Relation.ReflTransGen r x y ∧ p v ∧ ¬p x := by
  classical
  revert hu
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => intro hu;exact False.elim (hy hu)
  | @head a b hab hby ih =>
    intro ha
    by_cases hb : p b
    · obtain ⟨v,x,hbv,hvx,hxy,hpv,hnx⟩ := ih hb
      exact ⟨v,x,Relation.ReflTransGen.head hab hbv,hvx,hxy,hpv,hnx⟩
    · exact ⟨a,b,.refl,hab,hby,ha,hb⟩

private theorem ancestor_max_mem {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (C : Finset W) (y : V ⊕ W)
    (hy : y ∈ componentVertices (used D) C) :
    ∃ u, u ∈ componentVertices (used D) C ∧ Reaches (componentGraph (used D) C) u y ∧
      ancestorMax D.layer D.paths D.chosen (used D) C y = lo D u := by
  let A := (componentVertices (used D) C).filter (fun u => Reaches (componentGraph (used D) C) u y)
  have hA : A.Nonempty := ⟨y,Finset.mem_filter.mpr ⟨hy,.refl⟩⟩
  obtain ⟨u,hu,hmax⟩ := Finset.exists_max_image A (lo D) hA
  refine ⟨u,(Finset.mem_filter.mp hu).1,(Finset.mem_filter.mp hu).2,?_⟩
  change A.sup (lo D) = lo D u
  exact Nat.le_antisymm (Finset.sup_le hmax) (Finset.le_sup hu)

private theorem interval_bound {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (C : Finset W) (y : V ⊕ W)
    (hy : y ∈ componentVertices (used D) C) :
    ancestorMax D.layer D.paths D.chosen (used D) C y ≤ hi D y := by
  obtain ⟨u,hu,huy,hmu⟩ := ancestor_max_mem D C y hy
  have hFu := component_family_nonempty D C u hu
  have hIu := candidate_nonempty D u hFu
  obtain ⟨wu,hwu,hwul⟩ := lo_mem D u hIu
  have hwy : wu ∈ cand D y := by
    by_contra hn
    obtain ⟨v,x,huv,hvx,hxy,hwv,hnx⟩ := first_exit (componentGraph (used D) C).Adj
      (fun z => wu ∈ cand D z) u y huy hwu hn
    have hx := (component_edge_vertices D C v x hvx).2
    have hFx := component_family_nonempty D C x hx
    have hIx := candidate_nonempty D x hFx
    obtain ⟨wx,hwx,hwxl⟩ := lo_mem D x hIx
    have hlx : lo D x ≤ ancestorMax D.layer D.paths D.chosen (used D) C y := by
      exact Finset.le_sup (Finset.mem_filter.mpr ⟨hx,hxy⟩)
    obtain ⟨P,hPv,hPx⟩ := component_edge_family D C v x hvx
    have hp := (D.unique P (fam_subset D x hPx)).1
    have hwuP := candidate_member D v wu hwv P hPv
    have hwxP := candidate_member D x wx hwx P hPx
    have hback := reach_on_path D.G D.layer D.layered P hp wx wu hwxP hwuP (by omega)
    have hforward := component_reach_augment D C u x (huv.tail hvx)
    obtain ⟨w,hwU,hwX⟩ := candidate_intersection D u x hFu hFx wu wx hwu hwx hforward hback
    have hlow := lo_le D u hIu w hwU
    have hh := candidate_interval D x P hPx wx w wu hwx hwX hwuP (by omega) (by omega)
    exact hnx hh
  have hh := le_hi D y wu hwy
  rw [hwul] at hh
  rwa [hmu]

private noncomputable def mu {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (C : Finset W) (x : V ⊕ W) : ℕ :=
  ancestorMax D.layer D.paths D.chosen (used D) C x

private theorem lo_le_mu {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (C : Finset W) (x : V ⊕ W)
    (hx : x ∈ componentVertices (used D) C) : lo D x ≤ mu D C x := by
  change lo D x ≤ ((componentVertices (used D) C).filter
    (fun u => Reaches (componentGraph (used D) C) u x)).sup (lo D)
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨hx,.refl⟩)

private theorem mu_edge_mono {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (C : Finset W) (x y : V ⊕ W)
    (he : (componentGraph (used D) C).Adj x y) : mu D C x ≤ mu D C y := by
  change ((componentVertices (used D) C).filter (fun u => Reaches (componentGraph (used D) C) u x)).sup (lo D) ≤
    ((componentVertices (used D) C).filter (fun u => Reaches (componentGraph (used D) C) u y)).sup (lo D)
  apply Finset.sup_le
  intro u hu
  have hh := Finset.mem_filter.mp hu
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨hh.1,hh.2.tail he⟩)

private theorem mu_original {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (C : Finset W) (v : V)
    (hv : Sum.inl v ∈ componentVertices (used D) C) : mu D C (Sum.inl v)=D.layer v := by
  have hlo : lo D (Sum.inl v)=D.layer v := by simp [lo,leftLayer,replacements]
  have hhi : hi D (Sum.inl v)=D.layer v := by simp [hi,rightLayer,replacements]
  have hmlo := lo_le_mu D C (Sum.inl v) hv
  have hmhi : mu D C (Sum.inl v) ≤ hi D (Sum.inl v) := interval_bound D C (Sum.inl v) hv
  omega

private theorem replacement_map {V W : Type} [Fintype V] [Fintype W]
    (D : RepSetup V W) (v0 : V) :
    ∃ f : V ⊕ W → V, (∀ v, f (Sum.inl v)=v) ∧
      ∀ e ∈ used D, Reaches D.G (f e.1) (f e.2) := by
  classical
  let C : Finset W := Finset.univ
  let H := componentVertices (used D) C
  have hex : ∀ x : V ⊕ W, ∃ v : V, x ∈ H → v ∈ cand D x ∧ D.layer v=mu D C x := by
    intro x
    by_cases hx : x ∈ H
    · obtain ⟨v,hv,hvl⟩ := candidate_at D x (component_family_nonempty D C x hx)
        (mu D C x) (lo_le_mu D C x hx) (interval_bound D C x hx)
      exact ⟨v,fun _ => ⟨hv,hvl⟩⟩
    · exact ⟨v0,fun hh => False.elim (hx hh)⟩
  choose raw hraw using hex
  let f : V ⊕ W → V := fun x => match x with | .inl v => v | .inr w => raw (Sum.inr w)
  have hf (x : V ⊕ W) (hx : x ∈ H) : f x ∈ cand D x ∧ D.layer (f x)=mu D C x := by
    cases x with
    | inl v => exact ⟨by simp [f,cand,replacements],(mu_original D C v hx).symm⟩
    | inr w => exact hraw (Sum.inr w) hx
  have good (x y : V ⊕ W) (he : (componentGraph (used D) C).Adj x y) : Reaches D.G (f x) (f y) := by
    have hxy := component_edge_vertices D C x y he
    have hfx := hf x hxy.1
    have hfy := hf y hxy.2
    obtain ⟨P,hPx,hPy⟩ := component_edge_family D C x y he
    have hp := (D.unique P (fam_subset D x hPx)).1
    apply reach_on_path D.G D.layer D.layered P hp (f x) (f y)
      (candidate_member D x (f x) hfx.1 P hPx) (candidate_member D y (f y) hfy.1 P hPy)
    rw [hfx.2,hfy.2]
    exact mu_edge_mono D C x y he
  refine ⟨f,fun _ => rfl,?_⟩
  intro e he
  rcases e with ⟨x,y⟩
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      have hE : (Sum.inl u,Sum.inl v) ∈ D.extra := (Finset.mem_filter.mp he).1
      have hh : Reaches (augment D.G D.extra) (Sum.inl u) (Sum.inl v) := .single (Or.inl hE)
      exact (D.shortcut u v).mpr hh
    | inr w =>
      change Reaches D.G (f (Sum.inl u)) (f (Sum.inr w))
      apply good (Sum.inl u) (Sum.inr w)
      exact Finset.mem_filter.mpr ⟨he,⟨w,Finset.mem_univ _,Or.inr rfl⟩⟩
  | inr w =>
    change Reaches D.G (f (Sum.inr w)) (f y)
    apply good (Sum.inr w) y
    exact Finset.mem_filter.mpr ⟨he,⟨w,Finset.mem_univ _,Or.inl rfl⟩⟩

private theorem cat_length {V : Type} (P Q : Route V) : (cat P Q).length=P.length+Q.length := by
  simp [cat,Route.length]

private theorem walk_trans {V : Type} (G : Digraph V) {k l : ℕ} {u v w : V}
    (h1 : PredAdvice.WalkLen G k u v) (h2 : PredAdvice.WalkLen G l v w) :
    PredAdvice.WalkLen G (k+l) u w := by
  induction h2 with
  | refl => simpa using h1
  | tail hxy hyz ih => exact .tail (ih h1) hyz

private theorem path_walk {V : Type} (G : Digraph V) (P : Route V) (hp : IsPath G P) :
    PredAdvice.WalkLen G P.length P.start P.finish := by
  rcases P with ⟨a,l⟩
  induction l generalizing a with
  | nil => exact .refl a
  | cons b l ih =>
    have hh := List.isChain_cons_cons.mp hp
    have hrest := ih b hh.2
    have hedge : PredAdvice.WalkLen G 1 a b := .tail (.refl a) hh.1
    have hw := walk_trans G hedge hrest
    simpa only [Route.length,Route.finish,List.length_cons,List.getLastD_cons,Nat.add_comm] using hw

private theorem walk_route {V : Type} (G : Digraph V) {k : ℕ} {u v : V}
    (hw : PredAdvice.WalkLen G k u v) :
    ∃ P : Route V, IsPath G P ∧ P.start=u ∧ P.finish=v ∧ P.length=k := by
  induction hw with
  | refl u => exact ⟨⟨u,[]⟩,List.IsChain.singleton _,rfl,rfl,rfl⟩
  | @tail k u x y hxy hyz ih =>
    obtain ⟨P,hP,hs,ht,hlen⟩ := ih
    let Q : Route V := ⟨x,[y]⟩
    have hQ : IsPath G Q := by simpa [Q,IsPath,Route.vertices] using hyz
    have he : P.finish=Q.start := ht
    refine ⟨cat P Q,cat_path G P Q hP hQ he,hs,cat_finish P Q he,?_⟩
    rw [cat_length,hlen]
    rfl

private theorem reaches_walk {V : Type} (G : Digraph V) (u v : V) (hr : Reaches G u v) :
    ∃ k, PredAdvice.WalkLen G k u v := by
  induction hr with
  | refl => exact ⟨0,.refl _⟩
  | tail hxy hyz ih => obtain ⟨k,hk⟩:=ih;exact ⟨k+1,.tail hk hyz⟩

private theorem dist_le_walk {V : Type} (G : Digraph V) {k : ℕ} {u v : V}
    (hw : PredAdvice.WalkLen G k u v) : PredAdvice.dist G u v ≤ (k:ℕ∞) := by
  exact iInf_le_of_le k (iInf_le_of_le hw le_rfl)

private theorem dist_le_path {V : Type} (G : Digraph V) (P : Route V) (hp : IsPath G P) :
    PredAdvice.dist G P.start P.finish ≤ (P.length:ℕ∞) := dist_le_walk G (path_walk G P hp)

private theorem dist_finite {V : Type} (G : Digraph V) (u v : V) (hr : Reaches G u v) :
    PredAdvice.dist G u v ≠ ⊤ := by
  obtain ⟨k,hk⟩ := reaches_walk G u v hr
  have hh : (k:ℕ∞) < ⊤ := by simp
  exact ne_top_of_lt (lt_of_le_of_lt (dist_le_walk G hk) hh)

private theorem shortest_route {V : Type} (G : Digraph V) (u v : V) (hr : Reaches G u v) :
    ∃ P : Route V, IsPath G P ∧ P.start=u ∧ P.finish=v ∧ (P.length:ℕ∞)=PredAdvice.dist G u v := by
  have hex := reaches_walk G u v hr
  let k := Nat.find hex
  have hk : PredAdvice.WalkLen G k u v := Nat.find_spec hex
  have hmin : ∀ n, PredAdvice.WalkLen G n u v → k ≤ n := fun n hn => Nat.find_min' hex hn
  have heq : PredAdvice.dist G u v = (k:ℕ∞) := by
    apply le_antisymm (dist_le_walk G hk)
    apply le_iInf
    intro n
    apply le_iInf
    intro hn
    exact_mod_cast hmin n hn
  obtain ⟨P,hP,hs,ht,hlen⟩ := walk_route G hk
  exact ⟨P,hP,hs,ht,by rw [hlen,heq]⟩

private theorem directed_dist_pos {V : Type} (G : Digraph V) (u v : V) (hne : u ≠ v) :
    (1:ℕ∞) ≤ PredAdvice.dist G u v := by
  apply le_iInf
  intro k
  apply le_iInf
  intro hw
  cases k with
  | zero => cases hw;exact False.elim (hne rfl)
  | succ k => exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)

private theorem dist_toNat_le_diameter {V : Type} [Fintype V] (G : Digraph V) (u v : V)
    (hf : PredAdvice.dist G u v ≠ ⊤) : (PredAdvice.dist G u v).toNat ≤ diameter G := by
  unfold diameter
  apply Finset.le_sup_of_le (Finset.mem_univ u)
  apply Finset.le_sup_of_le (Finset.mem_univ v)
  rw [if_neg hf]

private theorem diameter_positive {V : Type} [Fintype V] (G : Digraph V) (u v : V)
    (hr : Reaches G u v) (hne : u ≠ v) : 1 ≤ diameter G := by
  have hf := dist_finite G u v hr
  have hp := directed_dist_pos G u v hne
  have hnat : 1 ≤ (PredAdvice.dist G u v).toNat := by
    have hh := ENat.natCast_toNat hf
    rw [← hh] at hp
    exact_mod_cast hp
  exact hnat.trans (dist_toNat_le_diameter G u v hf)

private theorem dist_le_diameter {V : Type} [Fintype V] (G : Digraph V) (u v : V)
    (hr : Reaches G u v) : PredAdvice.dist G u v ≤ (diameter G:ℕ∞) := by
  have hf := dist_finite G u v hr
  rw [← ENat.natCast_toNat hf]
  exact_mod_cast dist_toNat_le_diameter G u v hf

private def mapRoute {V U : Type} (f : V → U) (P : Route V) : Route U := ⟨f P.start,P.tail.map f⟩

private theorem map_vertices {V U : Type} (f : V → U) (P : Route V) :
    (mapRoute f P).vertices=P.vertices.map f := by simp [mapRoute,Route.vertices]

private theorem map_finish {V U : Type} (f : V → U) (P : Route V) :
    (mapRoute f P).finish=f P.finish := by simp only [mapRoute,Route.finish,List.getLastD_map]

private theorem map_length {V U : Type} (f : V → U) (P : Route V) :
    (mapRoute f P).length=P.length := by simp [mapRoute,Route.length]

private theorem chain_zip {V : Type} (r : V → V → Prop) (a : V) (l : List V) :
    (a::l).IsChain r ↔ ∀ e ∈ (a::l).zip l, r e.1 e.2 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp [List.isChain_cons_cons,ih]

private theorem map_path {V U : Type} (G : Digraph U) (f : V → U) (P : Route V)
    (he : ∀ e ∈ P.arcs, G.Adj (f e.1) (f e.2)) : IsPath G (mapRoute f P) := by
  unfold IsPath
  rw [map_vertices,List.isChain_map]
  exact (chain_zip _ _ _).mpr he

private theorem shortcut_of_added_reaches {V : Type} (G : Digraph V) (E : Finset (V × V))
    (hE : ∀ e ∈ E, Reaches G e.1 e.2) : IsShortcut G E := by
  intro u v
  constructor
  · intro hr
    induction hr with
    | refl => exact .refl
    | tail hxy hyz ih => exact ih.tail (Or.inl hyz)
  · intro hr
    induction hr with
    | refl => exact .refl
    | tail hxy hyz ih =>
      rcases hyz with hyz | hyz
      · exact ih.tail hyz
      · exact ih.trans (hE _ hyz)


theorem solution {V W : Type} [Fintype V] [Fintype W]
    (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (paths : Finset (Route V)) (D : ℕ) (hlen : ∀ P ∈ paths, P.length = D)
    (hp1 : P1 G paths) (hp2 : P2 G paths)
    (extra : Finset ((V ⊕ W) × (V ⊕ W))) (he : IsSteinerShortcut G extra) :
    ∃ nonSteiner : Finset (V × V), IsShortcut G nonSteiner ∧ nonSteiner.card ≤ extra.card ∧
      ∀ P ∈ paths, PredAdvice.dist (addEdges G nonSteiner) P.start P.finish ≤
        PredAdvice.dist (augment G extra) (Sum.inl P.start) (Sum.inl P.finish) := by
  classical
  by_cases hne : paths.Nonempty
  · obtain ⟨P0,hP0⟩ := hne
    have hex : ∀ P : Route V, ∃ Q : Route (V ⊕ W), P ∈ paths →
        IsPath (augment G extra) Q ∧ Q.start=Sum.inl P.start ∧ Q.finish=Sum.inl P.finish ∧
          (Q.length:ℕ∞)=PredAdvice.dist (augment G extra) (Sum.inl P.start) (Sum.inl P.finish) := by
      intro P
      by_cases hP : P ∈ paths
      · have hr := path_reaches G P (hp1 P hP).1
        have hr' := (he P.start P.finish).mp hr
        obtain ⟨Q,hQ,hs,ht,hlen⟩ := shortest_route (augment G extra) (Sum.inl P.start) (Sum.inl P.finish) hr'
        exact ⟨Q,fun _ => ⟨hQ,hs,ht,hlen⟩⟩
      · exact ⟨⟨Sum.inl P.start,[]⟩,fun hh => False.elim (hP hh)⟩
    choose chosen hchosen using hex
    have hsel : ShortestSelection G extra paths chosen := hchosen
    let D0 : RepSetup V W := ⟨G,layer,hl,paths,hp1,hp2,extra,he,chosen,hsel⟩
    obtain ⟨f,hfix,hf⟩ := replacement_map D0 P0.start
    let E : Finset (V × V) := (used D0).image (fun e => (f e.1,f e.2))
    have hE : ∀ e ∈ E, Reaches G e.1 e.2 := by
      intro e he
      obtain ⟨e',he',rfl⟩ := Finset.mem_image.mp he
      exact hf e' he'
    have hShortcut : IsShortcut G E := shortcut_of_added_reaches G E hE
    have hcard : E.card ≤ extra.card := by
      calc E.card ≤ (used D0).card := Finset.card_image_le
           _ ≤ extra.card := Finset.card_filter_le _ _
    refine ⟨E,hShortcut,hcard,?_⟩
    intro P hP
    have hselP := hchosen P hP
    have hpmap : IsPath (addEdges G E) (mapRoute f (chosen P)) := by
      apply map_path
      intro e he
      have ha := (chain_zip (augment G extra).Adj (chosen P).start (chosen P).tail).mp hselP.1 e he
      rcases ha with hEx | ⟨u,v,hu,hv,hG⟩
      · apply Or.inr
        apply Finset.mem_image.mpr
        refine ⟨e,?_,rfl⟩
        exact Finset.mem_filter.mpr ⟨hEx,⟨P,hP,he⟩⟩
      · apply Or.inl
        rw [hu,hv,hfix u,hfix v]
        exact hG
    have hs : (mapRoute f (chosen P)).start=P.start := by
      change f (chosen P).start=P.start
      rw [hselP.2.1,hfix P.start]
    have ht : (mapRoute f (chosen P)).finish=P.finish := by
      rw [map_finish,hselP.2.2.1,hfix P.finish]
    have hh := dist_le_path (addEdges G E) (mapRoute f (chosen P)) hpmap
    rw [hs,ht,map_length,hselP.2.2.2] at hh
    exact hh
  · have hEmpty : paths=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst paths
    refine ⟨∅,shortcut_of_added_reaches G ∅ (by simp),by simp,?_⟩
    simp



