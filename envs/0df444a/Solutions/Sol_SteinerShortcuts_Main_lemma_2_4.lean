-- Prove2me | solution 1 for SteinerShortcuts.Main.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:29:13.928765+00:00
-- url     : https://prove2.me/submissions/17d0c16f-63c8-4fb1-a282-d9708188514f

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

 theorem solution {V : Type} [Fintype V] (G : Digraph V) (layer : V → ℕ)
    (hl : IsLayered G layer) (paths : Finset (Route V)) (hp1 : P1 G paths) (hp2 : P2 G paths)
    (F : Finset (Route V)) (hf : F ⊆ paths) (hne : F.Nonempty) (hc : CompatibleFamily G F) :
    ∃ v : V, ∀ P ∈ F, v ∈ P.vertices := by
  classical
  obtain ⟨A,hA⟩ := hne
  have hpair (P : Route V) (hP : P ∈ F) (Q : Route V) (hQ : Q ∈ F) :
      ∃ v, v ∈ P.vertices ∧ v ∈ Q.vertices :=
    hp2 P (hf hP) Q (hf hQ) ⟨hc P hP Q hQ,hc Q hQ P hP⟩
  have hleft : ∀ P : Route V, ∃ v : V, P ∈ F →
      v ∈ A.vertices ∧ v ∈ P.vertices ∧
      ∀ w, w ∈ A.vertices → w ∈ P.vertices → layer v ≤ layer w := by
    intro P
    by_cases hP : P ∈ F
    · obtain ⟨x,hxA,hxP⟩ := hpair A hA P hP
      let I := A.vertices.toFinset ∩ P.vertices.toFinset
      have hI : I.Nonempty := ⟨x,by simp [I,hxA,hxP]⟩
      obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image I layer hI
      have hvA : v ∈ A.vertices := List.mem_toFinset.mp (Finset.mem_inter.mp hv).1
      have hvP : v ∈ P.vertices := List.mem_toFinset.mp (Finset.mem_inter.mp hv).2
      refine ⟨v,fun _ => ⟨hvA,hvP,?_⟩⟩
      intro w hwA hwP
      exact hmin w (by simp [I,hwA,hwP])
    · exact ⟨A.start,fun hh => False.elim (hP hh)⟩
  choose left hleft using hleft
  obtain ⟨B,hB,hmax⟩ := Finset.exists_max_image F (fun P => layer (left P)) ⟨A,hA⟩
  have hleftB := hleft B hB
  refine ⟨left B,?_⟩
  intro P hP
  have hleftP := hleft P hP
  obtain ⟨z,hzB,hzP⟩ := hpair B hB P hP
  have hpA := hp1 A (hf hA)
  have hpB := hp1 B (hf hB)
  have hpP := hp1 P (hf hP)
  obtain ⟨w,hwA,hwB,hwP⟩ := triangle_common G layer hl A B P hpA.1 hpB.1 hpP.1
    hpA.2 hpB.2 hpP.2 (left B) (left P) z hleftB.1 hleftB.2.1
    hleftP.1 hleftP.2.1 hzB hzP
  have hlPB := hmax P hP
  have hlBw := hleftB.2.2 w hwA hwB
  apply unique_through G P hpP.2 (left B)
  · exact (reach_prefix G P hpP.1 (left P) hleftP.2.1).trans
      (reach_on_path G layer hl A hpA.1 (left P) (left B) hleftP.1 hleftB.1 hlPB)
  · exact (reach_on_path G layer hl A hpA.1 (left B) w hleftB.1 hwA hlBw).trans
      (reach_suffix G P hpP.1 w hwP)
