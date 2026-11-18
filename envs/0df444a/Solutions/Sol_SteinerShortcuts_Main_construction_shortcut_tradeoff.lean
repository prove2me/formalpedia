-- Prove2me | solution 1 for SteinerShortcuts.Main.construction_shortcut_tradeoff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:15:39.216178+00:00
-- url     : https://prove2.me/submissions/44a17c4e-2987-47c7-b87f-0d67e39e7b2e

import Theorems.Thm_SteinerShortcuts_Main_claim_2_6
import Theorems.Thm_SteinerShortcuts_Main_claim_2_7
import Theorems.Thm_SteinerShortcuts_Main_claim_3_9
import Theorems.Thm_SteinerShortcuts_Main_theorem_2_3
import Theorems.Thm_SteinerShortcuts_Main_critical_paths_valid
import Definitions.Def_SteinerShortcuts_Main_Construction
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

private theorem route_map_start {V U : Type} (f : V → U) (P : Route V) :
    (mapRoute f P).start=f P.start := rfl

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

private theorem map_reaches {V U : Type} (G : Digraph V) (H : Digraph U) (f : V → U)
    (hf : ∀ u v, G.Adj u v → H.Adj (f u) (f v)) (u v : V) (hr : Reaches G u v) :
    Reaches H (f u) (f v) := by
  induction hr with
  | refl => exact .refl
  | tail hxy hyz ih => exact ih.tail (hf _ _ hyz)

private theorem map_path_iff {V U : Type} (G : Digraph V) (H : Digraph U) (f : V → U)
    (hf : ∀ u v, G.Adj u v ↔ H.Adj (f u) (f v)) (P : Route V) :
    IsPath H (mapRoute f P) ↔ IsPath G P := by
  unfold IsPath
  rw [map_vertices,List.isChain_map]
  constructor
  · intro hh;exact hh.imp (fun {u v} h => (hf u v).mpr h)
  · intro hh;exact hh.imp (fun {u v} h => (hf u v).mp h)

private theorem map_route_injective {V U : Type} (f : V → U) (hf : Function.Injective f) :
    Function.Injective (mapRoute f) := by
  intro P Q he
  apply route_ext
  apply List.map_injective_iff.mpr hf
  simpa only [map_vertices] using congrArg Route.vertices he

private theorem pullback_properties {V U : Type} [DecidableEq U] (G : Digraph V) (H : Digraph U) (f : V → U)
    (hf : Function.Injective f) (hAdj : ∀ u v, G.Adj u v ↔ H.Adj (f u) (f v))
    (paths : Finset (Route V)) (hp1 : P1 H (paths.image (mapRoute f)))
    (hp2 : P2 H (paths.image (mapRoute f))) : P1 G paths ∧ P2 G paths := by
  classical
  constructor
  · intro P hP
    have hm : mapRoute f P ∈ paths.image (mapRoute f) := Finset.mem_image.mpr ⟨P,hP,rfl⟩
    have hh := hp1 _ hm
    refine ⟨(map_path_iff G H f hAdj P).mp hh.1,?_⟩
    intro Q hQ hs ht
    apply map_route_injective f hf
    apply hh.2 (mapRoute f Q) ((map_path_iff G H f hAdj Q).mpr hQ)
    · change f Q.start=f P.start;rw [hs]
    · rw [map_finish,map_finish,ht]
  · intro P hP Q hQ hc
    have hMP : mapRoute f P ∈ paths.image (mapRoute f) := Finset.mem_image.mpr ⟨P,hP,rfl⟩
    have hMQ : mapRoute f Q ∈ paths.image (mapRoute f) := Finset.mem_image.mpr ⟨Q,hQ,rfl⟩
    have hC : CompatiblePair H (mapRoute f P) (mapRoute f Q) := by
      constructor
      · simpa only [map_finish,route_map_start] using map_reaches G H f (fun u v h => (hAdj u v).mp h) _ _ hc.1
      · simpa only [map_finish,route_map_start] using map_reaches G H f (fun u v h => (hAdj u v).mp h) _ _ hc.2
    obtain ⟨v,hvP,hvQ⟩ := hp2 _ hMP _ hMQ hC
    rw [map_vertices] at hvP hvQ
    obtain ⟨p,hp,hpv⟩ := List.mem_map.mp hvP
    obtain ⟨q,hq,hqv⟩ := List.mem_map.mp hvQ
    have he : p=q := hf (hpv.trans hqv.symm)
    exact ⟨p,hp,by simpa [he] using hq⟩

private def chunkRoute {V : Type} (P : Route V) (i d : ℕ) : Route V :=
  ⟨atV P i,(P.vertices.drop (i+1)).take d⟩

private theorem segment_vertices {V : Type} (P : Route V) (i d : ℕ) (hi : i ≤ P.length) :
    (chunkRoute P i d).vertices=(P.vertices.drop i).take (d+1) := by
  have hi' : i < P.vertices.length := by simp [Route.vertices,Route.length] at *;omega
  have hAt : atV P i=P.vertices[i] := by simp [atV,List.getElem?_eq_getElem hi']
  rw [List.drop_eq_getElem_cons hi']
  simp [chunkRoute,Route.vertices,hAt]

private theorem segment_length {V : Type} (P : Route V) (i d : ℕ) (hb : i+d ≤ P.length) :
    (chunkRoute P i d).length=d := by
  simp only [chunkRoute,Route.length,List.length_take,List.length_drop]
  apply Nat.min_eq_left
  simp [Route.vertices,Route.length] at *
  omega

private theorem segment_atV {V : Type} (P : Route V) (i d : ℕ) (hb : i+d ≤ P.length)
    (k : ℕ) (hk : k ≤ d) : atV (chunkRoute P i d) k=atV P (i+k) := by
  change ((chunkRoute P i d).vertices[k]?).getD (chunkRoute P i d).start = _
  rw [segment_vertices P i d (by omega),List.getElem?_take,if_pos (by omega : k<d+1),List.getElem?_drop,
    atV_some P (i+k) (by omega)]
  rfl

private theorem segment_finish {V : Type} (P : Route V) (i d : ℕ) (hb : i+d ≤ P.length) :
    (chunkRoute P i d).finish=atV P (i+d) := by
  rw [← atV_finish,segment_length P i d hb,segment_atV P i d hb d (by omega)]

private theorem segment_subpath {V : Type} (P : Route V) (i d : ℕ) (hb : i+d ≤ P.length) :
    IsSubpath (chunkRoute P i d) P := by
  refine ⟨P.vertices.take i,P.vertices.drop (i+d+1),?_⟩
  rw [segment_vertices P i d (by omega)]
  have h1 := List.take_append_drop i P.vertices
  have h2 := List.take_append_drop (d+1) (P.vertices.drop i)
  rw [List.drop_drop] at h2
  calc P.vertices = P.vertices.take i++P.vertices.drop i := h1.symm
       _ = P.vertices.take i++((P.vertices.drop i).take (d+1)++P.vertices.drop (i+d+1)) := by
         exact congrArg (fun l => P.vertices.take i++l) h2.symm
       _ = _ := by simp only [List.append_assoc]

private theorem route_edge {V : Type} (P : Route V) (i : ℕ) (hi : i < P.length) :
    ∃ u v, P.vertices[i]?=some u ∧ P.vertices[i+1]?=some v ∧ (u,v) ∈ P.arcs := by
  have hiv : i < P.vertices.length := by simp [Route.vertices,Route.length] at *;omega
  have hit : i < P.tail.length := hi
  have hia : i < P.arcs.length := by simpa [Route.arcs,Route.vertices,Route.length] using hi
  refine ⟨P.vertices[i],P.tail[i],List.getElem?_eq_getElem hiv,?_,?_⟩
  · simpa only [Route.vertices,List.getElem?_cons_succ] using List.getElem?_eq_getElem hit
  · have hh := List.getElem_mem hia
    simpa only [Route.arcs,List.getElem_zip] using hh

private theorem route_arc_atV {V : Type} (P : Route V) (i : ℕ) (hi : i < P.length) :
    (atV P i,atV P (i+1)) ∈ P.arcs := by
  obtain ⟨u,v,hu,hv,he⟩ := route_edge P i hi
  simpa [atV,hu,hv] using he

private theorem arc_vertices {V : Type} (P : Route V) (e : V × V) (he : e ∈ P.arcs) :
    e.1 ∈ P.vertices ∧ e.2 ∈ P.vertices := by
  have hh : e.1 ∈ P.vertices ∧ e.2 ∈ P.tail := List.of_mem_zip he
  exact ⟨hh.1,by simp [Route.vertices,hh.2]⟩

private theorem adj_arc_on_path {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P : Route V) (hp : IsPath G P) (u v : V) (hu : u ∈ P.vertices) (hv : v ∈ P.vertices)
    (ha : G.Adj u v) : (u,v) ∈ P.arcs := by
  obtain ⟨i,hi,rfl⟩ := mem_atV P u hu
  obtain ⟨j,hj,rfl⟩ := mem_atV P v hv
  have hli := path_layer G layer hl P hp i hi
  have hlj := path_layer G layer hl P hp j hj
  have hstep := hl _ _ ha
  have he : j=i+1 := by omega
  subst j
  exact route_arc_atV P i (by omega)

private theorem same_parent_of_long_overlap {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (paths : Finset (Route V)) (hp1 : P1 G paths) (hp3 : P3 paths 1)
    (P Q : Route V) (hP : P ∈ paths) (hQ : Q ∈ paths)
    (u v : V) (huP : u ∈ P.vertices) (huQ : u ∈ Q.vertices)
    (hvP : v ∈ P.vertices) (hvQ : v ∈ Q.vertices) (hgap : layer u+2 ≤ layer v) : P=Q := by
  classical
  by_contra hne
  have hp := hp1 P hP
  have hq := hp1 Q hQ
  obtain ⟨i,hi,rfl⟩ := mem_atV P u huP
  obtain ⟨j,hj,rfl⟩ := mem_atV P v hvP
  have hli := path_layer G layer hl P hp.1 i hi
  have hlj := path_layer G layer hl P hp.1 j hj
  have hij : i+2 ≤ j := by omega
  have h1P := atV_mem P (i+1) (by omega)
  have h2P := atV_mem P (i+2) (by omega)
  have h1Q : atV P (i+1) ∈ Q.vertices := by
    apply unique_through G Q hq.2 _
    · exact (reach_prefix G Q hq.1 _ huQ).trans (reach_indices G P hp.1 i (i+1) (by omega) (by omega))
    · exact (reach_indices G P hp.1 (i+1) j (by omega) hj).trans (reach_suffix G Q hq.1 _ hvQ)
  have h2Q : atV P (i+2) ∈ Q.vertices := by
    apply unique_through G Q hq.2 _
    · exact (reach_prefix G Q hq.1 _ huQ).trans (reach_indices G P hp.1 i (i+2) (by omega) (by omega))
    · exact (reach_indices G P hp.1 (i+2) j (by omega) hj).trans (reach_suffix G Q hq.1 _ hvQ)
  have ha0 := adj_atV G P hp.1 i (by omega)
  have ha1 := adj_atV G P hp.1 (i+1) (by omega)
  have he0P := route_arc_atV P i (by omega)
  have he1P := route_arc_atV P (i+1) (by omega)
  have he0Q := adj_arc_on_path G layer hl Q hq.1 _ _ huQ h1Q ha0
  have he1Q := adj_arc_on_path G layer hl Q hq.1 _ _ h1Q h2Q ha1
  have hm0 : (atV P i,atV P (i+1)) ∈ P.arcs.toFinset ∩ Q.arcs.toFinset := by
    simp only [Finset.mem_inter,List.mem_toFinset];exact ⟨he0P,he0Q⟩
  have hm1 : (atV P (i+1),atV P (i+2)) ∈ P.arcs.toFinset ∩ Q.arcs.toFinset := by
    simp only [Finset.mem_inter,List.mem_toFinset];exact ⟨he1P,he1Q⟩
  have he := Finset.card_le_one.mp (hp3 P hP Q hQ hne) _ hm0 _ hm1
  have hvertices := congrArg Prod.fst he
  change atV P i=atV P (i+1) at hvertices
  have hnext := path_layer G layer hl P hp.1 (i+1) (by omega)
  rw [hvertices] at hli
  omega

private theorem small_steps_layer {V : Type} (P : Route V) (layer : V → ℕ)
    (hs : ∀ e ∈ P.arcs, layer e.2 ≤ layer e.1+1) : layer P.finish ≤ layer P.start+P.length := by
  rcases P with ⟨a,l⟩
  induction l generalizing a with
  | nil => simp [Route.finish,Route.length]
  | cons b l ih =>
    have hab := hs (a,b) (by simp [Route.arcs,Route.vertices])
    have htail : ∀ e ∈ (⟨b,l⟩ : Route V).arcs, layer e.2 ≤ layer e.1+1 := by
      intro e he
      apply hs e
      simpa [Route.arcs,Route.vertices] using (List.mem_cons_of_mem (a,b) he)
    have hh := ih b htail
    simp only [Route.finish,List.getLastD_cons,Route.length,List.length_cons] at *
    omega

private theorem needed_edge {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (R : Route V) (hR : IsPath G R)
    (hunique : ∀ Q, IsPath G Q → Q.start=R.start → Q.finish=R.finish → Q=R)
    (E : Finset (V × V)) (hE : IsShortcut G E) (D : ℕ) (hD : D < R.length)
    (hd : PredAdvice.dist (addEdges G E) R.start R.finish ≤ (D:ℕ∞)) :
    ∃ e ∈ E, layer e.1+2 ≤ layer e.2 ∧ e.1 ∈ R.vertices ∧ e.2 ∈ R.vertices := by
  have hr := (hE R.start R.finish).mp (path_reaches G R hR)
  obtain ⟨Q,hQ,hs,ht,hlen⟩ := shortest_route (addEdges G E) R.start R.finish hr
  have hlenD : Q.length ≤ D := by exact_mod_cast (show (Q.length:ℕ∞) ≤ (D:ℕ∞) by rw [hlen];exact hd)
  have hQsub : ∀ v ∈ Q.vertices, v ∈ R.vertices := by
    intro v hv
    apply unique_through G R hunique v
    · have hh := reach_prefix (addEdges G E) Q hQ v hv
      rw [hs] at hh
      exact (hE R.start v).mpr hh
    · have hh := reach_suffix (addEdges G E) Q hQ v hv
      rw [ht] at hh
      exact (hE v R.finish).mpr hh
  have hex : ∃ e ∈ Q.arcs, layer e.1+2 ≤ layer e.2 := by
    by_contra hn
    have hsmall : ∀ e ∈ Q.arcs, layer e.2 ≤ layer e.1+1 := by
      intro e he
      by_contra hh
      exact hn ⟨e,he,by omega⟩
    have hh := small_steps_layer Q layer hsmall
    have hRlayer := path_layer G layer hl R hR R.length (by omega)
    rw [atV_finish] at hRlayer
    rw [hs,ht] at hh
    omega
  obtain ⟨e,he,hjump⟩ := hex
  have ha := (chain_zip (addEdges G E).Adj Q.start Q.tail).mp hQ e he
  have hmemE : e ∈ E := by
    rcases ha with ha | ha
    · have hh := hl _ _ ha;omega
    · exact ha
  have hv := arc_vertices Q e he
  exact ⟨e,hmemE,hjump,hQsub e.1 hv.1,hQsub e.2 hv.2⟩

private theorem segment_layer_range {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P : Route V) (hp : IsPath G P) (i d : ℕ) (hb : i+d ≤ P.length)
    (w : V) (hw : w ∈ (chunkRoute P i d).vertices) :
    layer P.start+i ≤ layer w ∧ layer w ≤ layer P.start+i+d := by
  have hR := subpath_path G P (chunkRoute P i d) hp (segment_subpath P i d hb)
  have hlo := reach_layer_le G layer hl _ _ (reach_prefix G _ hR w hw)
  have hhi := reach_layer_le G layer hl _ _ (reach_suffix G _ hR w hw)
  change layer (atV P i) ≤ layer w at hlo
  rw [segment_finish P i d hb,path_layer G layer hl P hp (i+d) hb] at hhi
  rw [path_layer G layer hl P hp i (by omega)] at hlo
  constructor <;> omega

private theorem same_block {V : Type} (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (P : Route V) (hp : IsPath G P) (d t s : ℕ)
    (ht : d*t+d ≤ P.length) (hs : d*s+d ≤ P.length) (u v : V)
    (hut : u ∈ (chunkRoute P (d*t) d).vertices) (hvt : v ∈ (chunkRoute P (d*t) d).vertices)
    (hus : u ∈ (chunkRoute P (d*s) d).vertices) (hvs : v ∈ (chunkRoute P (d*s) d).vertices)
    (hgap : layer u+2 ≤ layer v) : t=s := by
  have hUt := segment_layer_range G layer hl P hp (d*t) d ht u hut
  have hVt := segment_layer_range G layer hl P hp (d*t) d ht v hvt
  have hUs := segment_layer_range G layer hl P hp (d*s) d hs u hus
  have hVs := segment_layer_range G layer hl P hp (d*s) d hs v hvs
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hm := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hlt)
    rw [Nat.mul_succ] at hm
    omega
  · have hm := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hlt)
    rw [Nat.mul_succ] at hm
    omega

private theorem box_nonneg (L q : ℕ) (i : Fin 21) : 0 ≤ boxBounds L q i := by
  fin_cases i <;> simp [boxBounds] <;> positivity

private noncomputable def zeroSource : Point := fun i => if i=0 then 1 else 0

private theorem zero_source_mem (L q : ℕ) : zeroSource ∈ sources L q := by
  apply Fintype.mem_piFinset.mpr
  intro i
  by_cases h0 : i=0
  · subst i;norm_num [zeroSource]
  by_cases h1 : i=1
  · subst i;norm_num [zeroSource,Fin.ext_iff]
  by_cases h2 : i=2
  · subst i;norm_num [zeroSource,Fin.ext_iff]
  simpa [zeroSource,h0,h1,h2] using box_nonneg L q i

private noncomputable def baseVertex (L q : ℕ) : Vertex L q :=
  ⟨zeroSource,Finset.mem_union_left _ (zero_source_mem L q)⟩

private noncomputable def liftPoint (L q : ℕ) (v : Point) : Vertex L q :=
  if hv : v ∈ vertices L q then ⟨v,hv⟩ else baseVertex L q

private theorem lift_val (L q : ℕ) (P : Route Point) (hp : ∀ v ∈ P.vertices, v ∈ vertices L q) :
    mapRoute (fun v : Vertex L q => v.val) (mapRoute (liftPoint L q) P)=P := by
  apply route_ext
  rw [map_vertices,map_vertices,List.map_map]
  have hh : P.vertices.map ((fun v : Vertex L q => v.val) ∘ liftPoint L q)=P.vertices.map id :=
    List.map_congr_left (fun v hv => by simp [liftPoint,hp v hv])
  simpa using hh

private theorem lift_path (L q : ℕ) (P : Route Point) (hP : IsPath (construction L q) P)
    (hp : ∀ v ∈ P.vertices, v ∈ vertices L q) :
    IsPath (finiteConstruction L q) (mapRoute (liftPoint L q) P) := by
  apply (map_path_iff (finiteConstruction L q) (construction L q) (fun v : Vertex L q => v.val)
    (fun _ _ => Iff.rfl) _).mp
  rw [lift_val L q P hp]
  exact hP

private def pointLayer (v : Point) : ℕ := (v 0).toNat

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

private theorem critical_metadata (L q : ℕ) (P : Route Point) (hP : P ∈ criticalPaths L q) :
    P.length=L-1 ∧ pointLayer P.start=1 := by
  obtain ⟨sab,hsab,rfl⟩ := Finset.mem_image.mp hP
  constructor
  · simp [critical,Route.length]
  · have hh := layer_coordinate L q 1 1 sab.1 (Finset.mem_product.mp hsab).1
    change (sab.1 0).toNat=1
    rw [hh]
    rfl

private theorem construction_diameter_positive (L q : ℕ) (h : Admissible L q)
    (W : Type) [Fintype W] (extra : Finset ((Vertex L q ⊕ W) × (Vertex L q ⊕ W)))
    (he : IsSteinerShortcut (finiteConstruction L q) extra) :
    1 ≤ diameter (augment (finiteConstruction L q) extra) := by
  let t : Fin q := ⟨0,h.2.2.1.pos⟩
  let P := critical L q zeroSource t t
  have hm : P ∈ criticalPaths L q := by
    apply Finset.mem_image.mpr
    refine ⟨(zeroSource,(t,t)),?_,rfl⟩
    simp [zero_source_mem L q]
  have hp := critical_paths_valid L q h P hm
  let R := mapRoute (liftPoint L q) P
  have hR : IsPath (finiteConstruction L q) R := lift_path L q P hp.1 hp.2
  let layer : Vertex L q → ℕ := fun v => pointLayer v.val
  have hl : IsLayered (finiteConstruction L q) layer := by
    intro u v huv
    exact construction_layered L q u.val v.val huv
  have hlen : R.length=L-1 := by rw [map_length];exact (critical_metadata L q P hm).1
  have hh := path_layer (finiteConstruction L q) layer hl R hR R.length (by omega)
  rw [atV_finish,hlen] at hh
  have hne : R.start ≠ R.finish := by
    intro heq
    rw [heq] at hh
    have hL := h.1
    omega
  exact diameter_positive (augment (finiteConstruction L q) extra) (Sum.inl R.start) (Sum.inl R.finish)
    ((he R.start R.finish).mp (path_reaches (finiteConstruction L q) R hR))
    (fun heq => hne (Sum.inl.inj heq))

 theorem solution (L q : ℕ) (h : Admissible L q) (W : Type) [Fintype W]
    (extra : Finset ((Vertex L q ⊕ W) × (Vertex L q ⊕ W)))
    (he : IsSteinerShortcut (finiteConstruction L q) extra) :
    1 ≤ diameter (augment (finiteConstruction L q) extra) ∧
      (criticalPaths L q).card * ((L-1)/(diameter (augment (finiteConstruction L q) extra)+1)) ≤ extra.card := by
  classical
  let D := diameter (augment (finiteConstruction L q) extra)
  let d := D+1
  let count := (L-1)/d
  let dom := criticalPaths L q ×ˢ Finset.range count
  let R0 : Route Point × ℕ → Route Point := fun x => chunkRoute x.1 (d*x.2) d
  let R1 : Route Point × ℕ → Route (Vertex L q) := fun x => mapRoute (liftPoint L q) (R0 x)
  let F := dom.image R1
  have bounds (x : Route Point × ℕ) (hx : x ∈ dom) : d*x.2+d ≤ x.1.length := by
    have hP := (Finset.mem_product.mp hx).1
    have hk := Finset.mem_range.mp (Finset.mem_product.mp hx).2
    have hm1 := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hk)
    rw [Nat.mul_succ] at hm1
    have hm2 : d*count ≤ L-1 := by simpa only [Nat.mul_comm] using Nat.mul_div_le (L-1) d
    rw [(critical_metadata L q x.1 hP).1]
    omega
  have raw_sub (x : Route Point × ℕ) (hx : x ∈ dom) : IsSubpath (R0 x) x.1 :=
    segment_subpath x.1 (d*x.2) d (bounds x hx)
  have raw_contained (x : Route Point × ℕ) (hx : x ∈ dom) :
      ∀ v ∈ (R0 x).vertices, v ∈ vertices L q := by
    have hp := (critical_paths_valid L q h x.1 (Finset.mem_product.mp hx).1).2
    intro v hv
    exact hp v (subpath_subset x.1 (R0 x) (raw_sub x hx) v hv)
  have raw_val (x : Route Point × ℕ) (hx : x ∈ dom) :
      mapRoute (fun v : Vertex L q => v.val) (R1 x)=R0 x := lift_val L q (R0 x) (raw_contained x hx)
  have raw_len (x : Route Point × ℕ) (hx : x ∈ dom) : (R1 x).length=d := by
    change (mapRoute (liftPoint L q) (chunkRoute x.1 (d*x.2) d)).length=d
    rw [map_length,segment_length x.1 (d*x.2) d (bounds x hx)]
  have hfamily : ∀ S ∈ F.image (mapRoute (fun v : Vertex L q => v.val)),
      ∃ P ∈ criticalPaths L q, IsSubpath S P := by
    intro S hS
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hR
    rw [raw_val x hx]
    exact ⟨x.1,(Finset.mem_product.mp hx).1,raw_sub x hx⟩
  have hpoint := claim_3_9 L q h (F.image (mapRoute (fun v : Vertex L q => v.val))) hfamily
  have hfinite := pullback_properties (finiteConstruction L q) (construction L q) (fun v : Vertex L q => v.val)
    (fun a b heq => Subtype.ext heq) (fun _ _ => Iff.rfl) F hpoint.1 hpoint.2
  have hlen : ∀ R ∈ F, R.length=d := by
    intro R hR
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hR
    exact raw_len x hx
  let layer : Vertex L q → ℕ := fun v => pointLayer v.val
  have hl : IsLayered (finiteConstruction L q) layer := by
    intro u v huv
    exact construction_layered L q u.val v.val huv
  have hlP : IsLayered (construction L q) pointLayer := construction_layered L q
  obtain ⟨E,hShortcut,hcard,hDist⟩ := theorem_2_3 (finiteConstruction L q) layer hl F d hlen
    hfinite.1 hfinite.2 extra he
  have needed (x : Route Point × ℕ) (hx : x ∈ dom) :
      ∃ e ∈ E, pointLayer e.1.val+2 ≤ pointLayer e.2.val ∧
        e.1.val ∈ (R0 x).vertices ∧ e.2.val ∈ (R0 x).vertices := by
    have hm : R1 x ∈ F := Finset.mem_image.mpr ⟨x,hx,rfl⟩
    have hR := hfinite.1 (R1 x) hm
    have hr := (he (R1 x).start (R1 x).finish).mp (path_reaches (finiteConstruction L q) (R1 x) hR.1)
    have hdiam : PredAdvice.dist (augment (finiteConstruction L q) extra)
        (Sum.inl (R1 x).start) (Sum.inl (R1 x).finish) ≤ (D:ℕ∞) :=
      dist_le_diameter (augment (finiteConstruction L q) extra) _ _ hr
    have hd := (hDist (R1 x) hm).trans hdiam
    obtain ⟨e,heE,hjump,hu,hv⟩ := needed_edge (finiteConstruction L q) layer hl (R1 x) hR.1 hR.2 E
      hShortcut D (by rw [raw_len x hx];dsimp [d];omega) hd
    have hu' : e.1.val ∈ (mapRoute (fun v : Vertex L q => v.val) (R1 x)).vertices := by
      rw [map_vertices]
      exact List.mem_map.mpr ⟨e.1,hu,rfl⟩
    have hv' : e.2.val ∈ (mapRoute (fun v : Vertex L q => v.val) (R1 x)).vertices := by
      rw [map_vertices]
      exact List.mem_map.mpr ⟨e.2,hv,rfl⟩
    rw [raw_val x hx] at hu' hv'
    exact ⟨e,heE,hjump,hu',hv'⟩
  have hex : ∀ x : Route Point × ℕ, ∃ e : Vertex L q × Vertex L q,
      x ∈ dom → e ∈ E ∧ pointLayer e.1.val+2 ≤ pointLayer e.2.val ∧
        e.1.val ∈ (R0 x).vertices ∧ e.2.val ∈ (R0 x).vertices := by
    intro x
    by_cases hx : x ∈ dom
    · obtain ⟨e,he,hjump,hu,hv⟩ := needed x hx
      exact ⟨e,fun _ => ⟨he,hjump,hu,hv⟩⟩
    · exact ⟨(baseVertex L q,baseVertex L q),fun hh => False.elim (hx hh)⟩
  choose charge hcharge using hex
  have hinj : Set.InjOn charge dom := by
    intro x hx y hy heq
    have hX := hcharge x hx
    have hY := hcharge y hy
    rw [← heq] at hY
    rcases x with ⟨P,t⟩
    rcases y with ⟨Q,s⟩
    have hP := (Finset.mem_product.mp hx).1
    have hQ := (Finset.mem_product.mp hy).1
    have hPQ := same_parent_of_long_overlap (construction L q) pointLayer hlP (criticalPaths L q)
      (claim_2_6 L q h) (claim_2_7 L q h) P Q hP hQ (charge (P,t)).1.val (charge (P,t)).2.val
      (subpath_subset P (R0 (P,t)) (raw_sub (P,t) hx) _ hX.2.2.1)
      (subpath_subset Q (R0 (Q,s)) (raw_sub (Q,s) hy) _ hY.2.2.1)
      (subpath_subset P (R0 (P,t)) (raw_sub (P,t) hx) _ hX.2.2.2)
      (subpath_subset Q (R0 (Q,s)) (raw_sub (Q,s) hy) _ hY.2.2.2) hX.2.1
    subst Q
    have hts := same_block (construction L q) pointLayer hlP P ((claim_2_6 L q h) P hP).1
      d t s (bounds (P,t) hx) (bounds (P,s) hy) (charge (P,t)).1.val (charge (P,t)).2.val
      hX.2.2.1 hX.2.2.2 hY.2.2.1 hY.2.2.2 hX.2.1
    exact Prod.ext rfl hts
  have hcount := Finset.card_le_card_of_injOn charge (fun x hx => (hcharge x hx).1) hinj
  refine ⟨construction_diameter_positive L q h W extra he,?_⟩
  change (criticalPaths L q).card*((L-1)/d) ≤ extra.card
  calc (criticalPaths L q).card*((L-1)/d) = dom.card := by simp [dom,count]
       _ ≤ E.card := hcount
       _ ≤ extra.card := hcard
