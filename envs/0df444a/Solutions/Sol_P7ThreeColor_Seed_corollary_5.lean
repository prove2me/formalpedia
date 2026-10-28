-- Prove2me | solution 1 for P7ThreeColor.Seed.corollary_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T10:10:24.701693+00:00
-- url     : https://prove2.me/submissions/be9917ba-185d-4885-9507-9bb89d1eb39a

import Mathlib
import Definitions.Def_P7ThreeColor_Seed_Basic


set_option autoImplicit false
open SimpleGraph Finset
namespace P7Proof
open P7ThreeColor.Seed
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

noncomputable def pathSet {m : ℕ} (p : pathGraph m ↪g G) : Finset V := univ.image p

@[simp] theorem mem_pathSet {m : ℕ} (p : pathGraph m ↪g G) (v : V) :
    v ∈ pathSet p ↔ ∃ i, p i = v := by classical simp [pathSet]

@[simp] theorem path_mem {m : ℕ} (p : pathGraph m ↪g G) (i : Fin m) :
    p i ∈ pathSet p := (mem_pathSet p _).2 ⟨i,rfl⟩

@[simp] theorem card_pathSet {m : ℕ} (p : pathGraph m ↪g G) :
    (pathSet p).card = m := by
  classical
  simp [pathSet, Finset.card_image_of_injective, p.injective]

noncomputable def pathSet_embedding {m : ℕ} (p : pathGraph m ↪g G) :
    pathGraph m ↪g G.induce (pathSet p : Set V) where
  toFun i := ⟨p i, path_mem p i⟩
  inj' := fun _ _ h => p.injective (congrArg Subtype.val h)
  map_rel_iff' := p.map_rel_iff

theorem induced_pathSet_connected {m : ℕ} (hm : 0 < m) (p : pathGraph m ↪g G) :
    (G.induce (pathSet p : Set V)).Connected := by
  have : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  apply (Connected.map (pathSet_embedding p).toHom ?_ ⟨pathGraph_preconnected m⟩)
  rintro ⟨v,hv⟩
  obtain ⟨i,hi⟩ := (mem_pathSet p v).1 hv
  exact ⟨i, Subtype.ext hi⟩

def initialPath (m : ℕ) : pathGraph m ↪g pathGraph (m+1) where
  toFun := Fin.castSucc
  inj' := Fin.castSucc_injective m
  map_rel_iff' := by intros; simp [pathGraph_adj]

noncomputable def reversePath {m : ℕ} (p : pathGraph m ↪g G) : pathGraph m ↪g G where
  toFun i := p i.rev
  inj' := by
    intro i j h
    have hh := congrArg Fin.rev (p.injective h)
    simpa using hh
  map_rel_iff' := by
    intro i j
    change G.Adj (p i.rev) (p j.rev) ↔ (pathGraph m).Adj i j
    rw [p.map_rel_iff, pathGraph_adj, pathGraph_adj]
    simp only [Fin.val_rev]
    have := i.isLt
    have := j.isLt
    omega

omit [DecidableEq V] in
@[simp] theorem reversePath_apply {m : ℕ} (p : pathGraph m ↪g G) (i : Fin m) :
    reversePath p i = p i.rev := rfl

@[simp] theorem pathSet_reverse {m : ℕ} (p : pathGraph m ↪g G) :
    pathSet (reversePath p) = pathSet p := by
  ext v
  simp only [mem_pathSet, reversePath_apply]
  exact ⟨fun ⟨i,h⟩ => ⟨i.rev,h⟩, fun ⟨i,h⟩ => ⟨i.rev,by simpa using h⟩⟩

noncomputable def prependPath {m : ℕ} (p : pathGraph m ↪g G) (y : V)
    (hy : y ∉ pathSet p) (ha : ∀ i, G.Adj y (p i) ↔ i.val = 0) :
    pathGraph (m+1) ↪g G where
  toFun := Fin.cases y p
  inj' := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _; rfl
      · intro hij
        exact False.elim (hy ((mem_pathSet p y).2 ⟨j,hij.symm⟩))
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exact False.elim (hy ((mem_pathSet p y).2 ⟨i,hij⟩))
      · intro hij
        exact congrArg Fin.succ (p.injective hij)
  map_rel_iff' := by
    intro i j
    change G.Adj (Fin.cases y p i) (Fin.cases y p j) ↔ (pathGraph (m+1)).Adj i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simpa [pathGraph_adj] using ha j
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa [pathGraph_adj, G.adj_comm] using ha i
      · change G.Adj (p i) (p j) ↔ _
        rw [p.map_rel_iff]
        simp [pathGraph_adj]

@[simp] theorem prependPath_zero {m : ℕ} (p : pathGraph m ↪g G) (y : V)
    (hy : y ∉ pathSet p) (ha : ∀ i, G.Adj y (p i) ↔ i.val = 0) :
    prependPath p y hy ha 0 = y := rfl

@[simp] theorem prependPath_succ {m : ℕ} (p : pathGraph m ↪g G) (y : V)
    (hy : y ∉ pathSet p) (ha : ∀ i, G.Adj y (p i) ↔ i.val = 0) (i : Fin m) :
    prependPath p y hy ha i.succ = p i := rfl

theorem pathSet_prepend {m : ℕ} (p : pathGraph m ↪g G) (y : V)
    (hy : y ∉ pathSet p) (ha : ∀ i, G.Adj y (p i) ↔ i.val = 0) :
    pathSet (prependPath p y hy ha) = insert y (pathSet p) := by
  ext v
  simp only [mem_pathSet, mem_insert]
  constructor
  · rintro ⟨i,hi⟩
    exact Fin.cases (fun h => Or.inl h.symm) (fun j h => Or.inr ⟨j,h⟩) i hi
  · rintro (rfl | ⟨i,rfl⟩)
    · exact ⟨0,rfl⟩
    · exact ⟨i.succ,rfl⟩

theorem pathSet_initial {m : ℕ} (p : pathGraph (m+1) ↪g G) :
    pathSet (p.comp (initialPath m)) = (pathSet p).erase (p (Fin.last m)) := by
  ext v
  simp only [mem_pathSet, mem_erase]
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨?_, ⟨i.castSucc,rfl⟩⟩
    intro h
    have hh := congrArg Fin.val (p.injective h)
    change i.val = m at hh
    omega
  · rintro ⟨hne, i, rfl⟩
    have hi : i.val < m := by
      by_contra h
      have : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      exact hne (congrArg p this)
    exact ⟨⟨i.val,hi⟩, congrArg p (Fin.ext rfl)⟩

noncomputable def shiftPath {m : ℕ} (p : pathGraph m ↪g G) (y : V)
    (hy : y ∉ pathSet p) (ha : ∀ i, G.Adj y (p i) ↔ i.val = 0) :
    pathGraph m ↪g G := (prependPath p y hy ha).comp (initialPath m)

noncomputable def appendPath {m : ℕ} (p : pathGraph m ↪g G) (z : V)
    (hz : z ∉ pathSet p) (ha : ∀ i, G.Adj z (p i) ↔ i.val + 1 = m) :
    pathGraph (m+1) ↪g G :=
  reversePath (prependPath (reversePath p) z (by simpa using hz) (by
    intro i
    change G.Adj z (p i.rev) ↔ i.val = 0
    rw [ha]
    simp only [Fin.val_rev]
    have := i.isLt
    omega))

@[simp] theorem appendPath_last {m : ℕ} (p : pathGraph m ↪g G) (z : V)
    (hz : z ∉ pathSet p) (ha : ∀ i, G.Adj z (p i) ↔ i.val + 1 = m) :
    appendPath p z hz ha (Fin.last m) = z := by
  simp [appendPath]

@[simp] theorem appendPath_castSucc {m : ℕ} (p : pathGraph m ↪g G) (z : V)
    (hz : z ∉ pathSet p) (ha : ∀ i, G.Adj z (p i) ↔ i.val + 1 = m) (i : Fin m) :
    appendPath p z hz ha i.castSucc = p i := by
  have hi : i.castSucc.rev = i.rev.succ := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
    have := i.isLt
    omega
  simp [appendPath,hi]

theorem pathSet_append {m : ℕ} (p : pathGraph m ↪g G) (z : V)
    (hz : z ∉ pathSet p) (ha : ∀ i, G.Adj z (p i) ↔ i.val + 1 = m) :
    pathSet (appendPath p z hz ha) = insert z (pathSet p) := by
  simp [appendPath,pathSet_prepend]

theorem shiftPath_zero {m : ℕ} (hm : 0 < m) (p : pathGraph m ↪g G) (y : V)
    (hy : y ∉ pathSet p) (ha : ∀ i, G.Adj y (p i) ↔ i.val = 0) :
    shiftPath p y hy ha ⟨0,hm⟩ = y := rfl

theorem shiftPath_next {m : ℕ} (p : pathGraph m ↪g G) (y : V)
    (hy : y ∉ pathSet p) (ha : ∀ i, G.Adj y (p i) ↔ i.val = 0)
    (i : Fin m) (hi : i.val+1 < m) :
    shiftPath p y hy ha ⟨i.val+1,hi⟩ = p i := by
  change prependPath p y hy ha ⟨i.val+1,by omega⟩ = p i
  exact prependPath_succ p y hy ha i

theorem pathSet_shift {m : ℕ} (hm : 0 < m) (p : pathGraph m ↪g G) (y : V)
    (hy : y ∉ pathSet p) (ha : ∀ i, G.Adj y (p i) ↔ i.val = 0) :
    pathSet (shiftPath p y hy ha) =
      (insert y (pathSet p)).erase (p ⟨m-1,by omega⟩) := by
  rw [shiftPath,pathSet_initial,pathSet_prepend]
  have hi : Fin.last m = (⟨m-1,by omega⟩ : Fin m).succ := by
    apply Fin.ext
    simp only [Fin.val_last,Fin.val_succ]
    omega
  rw [hi,prependPath_succ]

omit [DecidableEq V] in
theorem pfree_induce {m : ℕ} (h : PFree m G) (S : Finset V) :
    PFree m (G.induce (S : Set V)) := by
  rintro ⟨p⟩
  exact h ⟨(Embedding.induce (S : Set V)).comp p⟩

end P7Proof


set_option autoImplicit false
open SimpleGraph Finset
namespace P7Proof
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem connected_crossing (X A : Finset V)
    (hX : (G.induce (X : Set V)).Connected) (hAX : A ⊆ X)
    (hA : A.Nonempty) (b : V) (hb : b ∈ X) (hbA : b ∉ A) :
    ∃ a ∈ A, ∃ c ∈ X, c ∉ A ∧ G.Adj a c := by
  classical
  by_contra! h
  have step : ∀ a ∈ A, ∀ c ∈ X, G.Adj a c → c ∈ A := by
    intro a ha c hc hac
    by_contra hn
    exact h a ha c hc hn hac
  obtain ⟨a,ha⟩ := hA
  obtain ⟨w⟩ := hX ⟨a,hAX ha⟩ ⟨b,hb⟩
  have closed : ∀ {u v : (X : Set V)}, (G.induce (X : Set V)).Walk u v →
      u.val ∈ A → v.val ∈ A := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons u v w huv q ih => exact fun hu => ih (step u.val hu v.val v.property huv)
  exact hbA (closed w ha)

theorem endpoint_delete_or_extend {m : ℕ} (hm : 2 ≤ m) (p : pathGraph m ↪g G)
    (X : Finset V) (hX : (G.induce (X : Set V)).Connected) (hsub : pathSet p ⊆ X) :
    (G.induce ((X.erase (p ⟨0,by omega⟩)) : Set V)).Connected ∨
      ∃ y ∈ X, y ∉ pathSet p ∧ ∀ i, G.Adj y (p i) ↔ i.val = 0 := by
  classical
  let first : Fin m := ⟨0,by omega⟩
  let second : Fin m := ⟨1,by omega⟩
  let D := X.erase (p first)
  have memD (i : Fin m) (hi : 0 < i.val) : p i ∈ D := by
    refine mem_erase.mpr ⟨?_,hsub (path_mem p i)⟩
    intro h
    have := congrArg Fin.val (p.injective h)
    change i.val=0 at this
    omega
  let base : (D : Set V) := ⟨p second,memD second (by change 0 < 1; omega)⟩
  by_cases hc : (G.induce (D : Set V)).Connected
  · exact Or.inl hc
  right
  have other : ∃ b : (D : Set V), ¬ (G.induce (D : Set V)).Reachable base b := by
    by_contra! hall
    have : Nonempty (D : Set V) := ⟨base⟩
    exact hc ⟨fun u v => (hall u).symm.trans (hall v)⟩
  obtain ⟨b,hb⟩ := other
  let C : Finset V := D.filter fun v => ∃ hv : v∈D,
    (G.induce (D : Set V)).Reachable base ⟨v,hv⟩
  have memC (v : V) : v∈C ↔ ∃ hv : v∈D,
      (G.induce (D : Set V)).Reachable base ⟨v,hv⟩ := by
    simp only [C,mem_filter]
    exact ⟨fun h=>h.2,fun h=>⟨h.choose,h⟩⟩
  have tailC : ∀ i : Fin m, 0 < i.val → p i∈C := by
    let q : pathGraph (m-1) ↪g G.induce (D : Set V) := {
      toFun := fun i => ⟨p ⟨i.val+1,by have:=i.isLt;omega⟩,memD ⟨i.val+1,by have:=i.isLt;omega⟩ (by change 0 < i.val+1; omega)⟩
      inj' := by
        intro i j h
        have h' := congrArg Fin.val (p.injective (congrArg (fun v : (D:Set V)=>v.val) h))
        apply Fin.ext
        simpa using h'
      map_rel_iff' := by
        intro i j
        change G.Adj (p ⟨i.val+1,_⟩) (p ⟨j.val+1,_⟩) ↔ _
        rw [p.map_rel_iff]
        simp [pathGraph_adj] }
    intro i hi
    have hreach := (pathGraph_preconnected (m-1) ⟨0,by omega⟩ ⟨i.val-1,by have:=i.isLt;omega⟩).map q.toHom
    have hstart : q ⟨0,by omega⟩ = base := by rfl
    have hend : q ⟨i.val-1,by have:=i.isLt;omega⟩ = ⟨p i,memD i hi⟩ := by
      apply Subtype.ext
      change p _ = p i
      congr 1
      apply Fin.ext
      dsimp
      omega
    change (G.induce (D : Set V)).Reachable (q ⟨0,by omega⟩) (q ⟨i.val-1,by have:=i.isLt;omega⟩) at hreach
    rw [hstart,hend] at hreach
    exact (memC _).2 ⟨memD i hi,hreach⟩
  let B := D \ C
  have hbB : b.val∈B := by
    refine mem_sdiff.mpr ⟨b.property,?_⟩
    intro hh
    obtain ⟨hv,hr⟩ := (memC _).1 hh
    exact hb hr
  have firstX : p first∈X := hsub (path_mem p first)
  have firstB : p first∉B := by simp [B,D]
  obtain ⟨y,hy,z,hz,hzB,hyz⟩ := connected_crossing X B hX
    (fun _ h=> mem_of_mem_erase (mem_sdiff.mp h).1) ⟨b.val,hbB⟩ (p first) firstX firstB
  have yD : y∈D := (mem_sdiff.mp hy).1
  have yNC : y∉C := (mem_sdiff.mp hy).2
  have zx : z=p first := by
    by_contra hne
    have zD : z∈D := mem_erase.mpr ⟨hne,hz⟩
    have zC : z∈C := by
      by_contra hn
      exact hzB (mem_sdiff.mpr ⟨zD,hn⟩)
    obtain ⟨hzD,hr⟩ := (memC _).1 zC
    exact yNC ((memC _).2 ⟨yD,hr.trans (Adj.reachable hyz.symm)⟩)
  subst z
  have yout : y∉pathSet p := by
    rintro hyP
    obtain ⟨i,rfl⟩ := (mem_pathSet p _).1 hyP
    by_cases hi : i.val=0
    · have : i=first := Fin.ext hi
      subst i
      exact (mem_erase.mp yD).1 rfl
    · exact yNC (tailC i (by omega))
  refine ⟨y,mem_of_mem_erase yD,yout,?_⟩
  intro i
  constructor
  · intro h
    by_contra hn
    obtain ⟨hiD,hr⟩ := (memC _).1 (tailC i (by omega))
    exact yNC ((memC _).2 ⟨yD,hr.trans (Adj.reachable h.symm)⟩)
  · intro hi
    have : i=first := Fin.ext hi
    simpa [this] using hyz

end P7Proof


set_option autoImplicit false

open Finset SimpleGraph
open P7ThreeColor.Seed

namespace P7Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

def MinCDS (G : SimpleGraph V) (X : Finset V) : Prop :=
  IsDominating G X ∧ (G.induce (X : Set V)).Connected ∧
    ∀ Y : Finset V, IsDominating G Y → (G.induce (Y : Set V)).Connected → X.card ≤ Y.card

theorem mem_closure (G : SimpleGraph V) (X : Finset V) (v : V) :
    v ∈ P7ThreeColor.Seed.closure G X ↔ v ∈ X ∨ ∃ x ∈ X, G.Adj v x := by
  classical
  simp only [P7ThreeColor.Seed.closure, nbhd, mem_union, mem_filter, mem_univ, true_and]
  tauto

theorem dominating_iff (G : SimpleGraph V) (X : Finset V) :
    IsDominating G X ↔ ∀ v, v ∈ X ∨ ∃ x ∈ X, G.Adj v x := by
  constructor
  · intro h v
    apply (mem_closure G X v).mp
    rw [show P7ThreeColor.Seed.closure G X = univ from h]
    exact mem_univ _
  · intro h
    apply Finset.eq_univ_of_forall
    exact fun v => (mem_closure G X v).mpr (h v)

omit [DecidableEq V] in
theorem connected_univ (G : SimpleGraph V) (hG : G.Connected) :
    (G.induce (↑(univ : Finset V) : Set V)).Connected := by
  let f : G →g G.induce (↑(univ : Finset V) : Set V) :=
    ⟨fun v => ⟨v, mem_univ v⟩, fun h => h⟩
  exact hG.map f (fun v => ⟨v.val, Subtype.ext rfl⟩)

theorem exists_minCDS (G : SimpleGraph V) (hG : G.Connected) : ∃ X, MinCDS G X := by
  classical
  let F : Finset (Finset V) := univ.filter (fun X => IsDominating G X ∧ (G.induce (X : Set V)).Connected)
  have hu : (univ : Finset V) ∈ F := by
    simp only [F, mem_filter, mem_univ, true_and]
    exact ⟨(dominating_iff G univ).mpr (fun v => Or.inl (mem_univ v)), connected_univ G hG⟩
  obtain ⟨X, hX, hmin⟩ := F.exists_min_image Finset.card ⟨univ, hu⟩
  have hx := (mem_filter.mp hX).2
  exact ⟨X, hx.1, hx.2, fun Y hd hc => hmin Y (mem_filter.mpr ⟨mem_univ _, hd, hc⟩)⟩

theorem private_neighbor (G : SimpleGraph V) (X : Finset V) (hX : MinCDS G X)
    (x : V) (hx : x ∈ X) (hdel : (G.induce ((X.erase x : Finset V) : Set V)).Connected)
    (hn : ∃ z ∈ X.erase x, G.Adj x z) :
    ∃ y, y ∉ X ∧ G.Adj y x ∧ ∀ z ∈ X, G.Adj y z → z = x := by
  classical
  have hnot : ¬ IsDominating G (X.erase x) := by
    intro hd
    exact (card_erase_lt_of_mem hx).not_ge (hX.2.2 _ hd hdel)
  rw [dominating_iff] at hnot
  push Not at hnot
  obtain ⟨y, hyn, hyadj⟩ := hnot
  have hyx : y ≠ x := by
    intro he
    obtain ⟨z, hz, ha⟩ := hn
    exact hyadj z hz (he ▸ ha)
  have hyout : y ∉ X := by
    intro hy
    exact hyn (mem_erase.mpr ⟨hyx, hy⟩)
  have ha : G.Adj y x := by
    obtain hy | ⟨z, hz, ha⟩ := (dominating_iff G X).mp hX.1 y
    · exact (hyout hy).elim
    · by_cases he : z = x
      · simpa [he] using ha
      · exact (hyadj z (mem_erase.mpr ⟨he, hz⟩) ha).elim
  refine ⟨y, hyout, ha, ?_⟩
  intro z hz haz
  by_contra he
  exact hyadj z (mem_erase.mpr ⟨he, hz⟩) haz

omit [Fintype V] in
theorem connected_insert (G : SimpleGraph V) (X : Finset V)
    (hX : (G.induce (X : Set V)).Connected) (y x : V) (hx : x ∈ X) (ha : G.Adj y x) :
    (G.induce (↑(insert y X) : Set V)).Connected := by
  have hsingle : (G.induce ({y} : Set V)).Preconnected := .of_subsingleton
  have h := G.connected_induce_union hsingle hX.preconnected (Set.mem_singleton y) hx ha
  have he : (↑(insert y X) : Set V) = {y} ∪ (X : Set V) := by
    ext z
    simp
  rw [he]
  exact h

theorem minCDS_of_card (G : SimpleGraph V) (X Y : Finset V) (hX : MinCDS G X)
    (hd : IsDominating G Y) (hc : (G.induce (Y : Set V)).Connected) (he : Y.card = X.card) :
    MinCDS G Y := by
  exact ⟨hd, hc, fun Z hz hzc => he ▸ hX.2.2 Z hz hzc⟩

omit [Fintype V] in
theorem connected_no_cross (G : SimpleGraph V) (X R : Finset V)
    (hc : (G.induce (X : Set V)).Connected) (hsub : R ⊆ X)
    (hcross : ∀ r ∈ R, ∀ x ∈ X, x ∉ R → ¬ G.Adj r x)
    (hp : ∃ p ∈ X, p ∉ R) : R = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨p, hpx, hpr⟩ := hp
  obtain ⟨w⟩ := hc ⟨r, hsub hr⟩ ⟨p, hpx⟩
  have transport : ∀ {u v : {x // x ∈ (X : Set V)}},
      (G.induce (X : Set V)).Walk u v → u.val ∈ R → v.val ∈ R := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons u v w ha _ ih =>
      intro hu
      apply ih
      by_contra hv
      exact hcross u.val hu v.val v.property hv ha
  exact hpr (transport w hr)

end P7Proof


set_option autoImplicit false
open SimpleGraph Finset
open P7ThreeColor.Seed
namespace P7Proof
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem path_private (m : ℕ) (hm : 2 ≤ m) (X : Finset V) (hX : MinCDS G X)
    (p : pathGraph m ↪g G) (hs : pathSet p ⊆ X)
    (hc : (G.induce (↑(X.erase (p ⟨0,by omega⟩)) : Set V)).Connected) :
    ∃ y, y ∉ X ∧ (∀ i, G.Adj y (p i) ↔ i.val = 0) ∧
      (∀ z ∈ X, G.Adj y z → z = p ⟨0,by omega⟩) := by
  have h0 : p ⟨0,by omega⟩ ∈ X := hs (path_mem p _)
  obtain ⟨y, hy, ha, hp⟩ := private_neighbor G X hX (p ⟨0,by omega⟩) h0 hc (by
    refine ⟨p ⟨1,by omega⟩, mem_erase.mpr ⟨?_, hs (path_mem p _)⟩, ?_⟩
    · intro he
      have := congrArg Fin.val (p.injective he)
      simp at this
    · rw [p.map_rel_iff, pathGraph_adj]
      exact Or.inl rfl)
  refine ⟨y, hy, ?_, hp⟩
  intro i
  constructor
  · intro hai
    have he := p.injective (hp (p i) (hs (path_mem p i)) hai)
    exact congrArg Fin.val he
  · intro hi
    have he : i = ⟨0,by omega⟩ := Fin.ext hi
    simpa only [he] using ha

theorem minimum_internal_free (m : ℕ) (hm : 2 ≤ m) (hfree : PFree (m+2) G)
    (X : Finset V) (hX : MinCDS G X) : PFree (m+1) (G.induce (X : Set V)) := by
  rintro ⟨q⟩
  let p := (Embedding.induce (X : Set V)).comp q
  have hs : pathSet p ⊆ X := by
    intro v hv
    obtain ⟨i,rfl⟩ := (mem_pathSet p v).mp hv
    exact (q i).property
  rcases endpoint_delete_or_extend (by omega : 2 ≤ m+1) p X hX.2.1 hs with hc | ⟨y,hy,hyp,ha⟩
  · obtain ⟨y,hy,ha,_⟩ := path_private (m+1) (by omega) X hX p hs hc
    exact hfree ⟨prependPath p y (fun hp => hy (hs hp)) ha⟩
  · exact hfree ⟨prependPath p y hyp ha⟩

theorem endpoint_connected (m : ℕ) (hm : 2 ≤ m) (hfree : PFree (m+2) G)
    (X : Finset V) (hX : MinCDS G X) (p : pathGraph m ↪g G) (hs : pathSet p ⊆ X) :
    (G.induce (↑(X.erase (p ⟨0,by omega⟩)) : Set V)).Connected := by
  rcases endpoint_delete_or_extend hm p X hX.2.1 hs with hc | ⟨y,hy,hyp,ha⟩
  · exact hc
  · exfalso
    apply minimum_internal_free m hm hfree X hX
    let q := prependPath p y hyp ha
    have hq : pathSet q ⊆ X := by
      rw [show pathSet q = insert y (pathSet p) from pathSet_prepend p y hyp ha]
      exact insert_subset hy hs
    exact ⟨(G.induceHomOfLE hq).comp (pathSet_embedding q)⟩

theorem path_swap (m : ℕ) (hm : 2 ≤ m) (hfree : PFree (m+2) G)
    (X : Finset V) (hX : MinCDS G X) (p : pathGraph m ↪g G) (hs : pathSet p ⊆ X)
    (y : V) (hy : y ∉ X) (ha : ∀ i, G.Adj y (p i) ↔ i.val = 0) :
    MinCDS G ((insert y X).erase (p ⟨m-1,by omega⟩)) := by
  classical
  let last : Fin m := ⟨m-1,by omega⟩
  let first : Fin m := ⟨0,by omega⟩
  let Y := (insert y X).erase (p last)
  have hlast : p last ∈ X := hs (path_mem p last)
  have hfirst : p first ∈ X.erase (p last) := by
    refine mem_erase.mpr ⟨?_, hs (path_mem p first)⟩
    intro he
    have := congrArg Fin.val (p.injective he)
    dsimp [first,last] at this
    omega
  have hylast : y ≠ p last := fun he => hy (he ▸ hlast)
  have hset : Y = insert y (X.erase (p last)) := by
    ext z
    simp only [Y, mem_erase, mem_insert]
    aesop
  have hc : (G.induce (Y : Set V)).Connected := by
    have hr := endpoint_connected m hm hfree X hX (reversePath p) (by simpa using hs)
    have hr' : (G.induce (↑(X.erase (p last)) : Set V)).Connected := by
      have hre : reversePath p ⟨0,by omega⟩ = p last := by
        change p _ = p last
        congr 1
      rw [hre] at hr
      exact hr
    rw [hset]
    exact connected_insert G _ hr' y (p first) hfirst ((ha first).mpr rfl)
  have hd : IsDominating G Y := by
    by_contra hn
    rw [dominating_iff] at hn
    push Not at hn
    obtain ⟨z,hzn,hza⟩ := hn
    have hyY : y ∈ Y := by rw [hset]; exact mem_insert_self _ _
    have hzny : z ≠ y := fun he => hzn (he ▸ hyY)
    have hzout : z ∉ X := by
      intro hz
      have he : z = p last := by
        by_contra he
        exact hzn (mem_erase.mpr ⟨he,mem_insert_of_mem hz⟩)
      let prev : Fin m := ⟨m-2,by omega⟩
      have hpY : p prev ∈ Y := by
        apply mem_erase.mpr
        constructor
        · intro he'
          have := congrArg Fin.val (p.injective he')
          dsimp [prev,last] at this
          omega
        · exact mem_insert_of_mem (hs (path_mem p prev))
      apply hza (p prev) hpY
      rw [he,p.map_rel_iff,pathGraph_adj]
      right
      dsimp [prev,last]
      omega
    have hzl : G.Adj z (p last) := by
      rcases (dominating_iff G X).mp hX.1 z with hz | ⟨x,hx,hzx⟩
      · exact (hzout hz).elim
      · by_cases he : x = p last
        · simpa only [he] using hzx
        · exact (hza x (mem_erase.mpr ⟨he,mem_insert_of_mem hx⟩) hzx).elim
    let q := prependPath p y (fun hh => hy (hs hh)) ha
    have hzq : z ∉ pathSet q := by
      rw [show pathSet q = insert y (pathSet p) from pathSet_prepend _ _ _ _]
      simp only [mem_insert, not_or]
      exact ⟨hzny,fun hh => hzout (hs hh)⟩
    have hqz : ∀ i : Fin (m+1), G.Adj z (q i) ↔ i.val+1=m+1 := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change G.Adj z y ↔ 0+1=m+1
        constructor
        · intro hh; exact (hza y hyY hh).elim
        · intro hh; omega
      · change G.Adj z (p j) ↔ (j.val+1)+1=m+1
        constructor
        · intro hzj
          have he : j = last := by
            apply p.injective
            by_contra hh
            exact hza (p j) (mem_erase.mpr ⟨hh,mem_insert_of_mem (hs (path_mem p j))⟩) hzj
          rw [he]
          dsimp [last]
          omega
        · intro hj
          have he : j = last := Fin.ext (by dsimp [last]; omega)
          simpa only [he] using hzl
    exact hfree ⟨appendPath q z hzq hqz⟩
  apply minCDS_of_card G X Y hX hd hc
  change ((insert y X).erase (p last)).card = X.card
  rw [card_erase_of_mem (mem_insert_of_mem hlast),card_insert_of_notMem hy]
  omega

theorem rotate_prefix (m : ℕ) (hm : 2 ≤ m) (hfree : PFree (m+2) G)
    (R X : Finset V) (hX : MinCDS G X) (p : pathGraph m ↪g G)
    (he : X = R ∪ pathSet p) (hd : Disjoint R (pathSet p)) :
    ∀ r : ℕ, ∃ Y : Finset V, ∃ q : pathGraph m ↪g G,
      MinCDS G Y ∧ Y = R ∪ pathSet q ∧ Disjoint R (pathSet q) ∧
      ∀ i : Fin m, i.val < r → ∀ z ∈ R, ¬ G.Adj (q i) z := by
  classical
  intro r
  induction r with
  | zero => exact ⟨X,p,hX,he,hd,fun i hi => (Nat.not_lt_zero i.val hi).elim⟩
  | succ r ih =>
    obtain ⟨Y,q,hY,heY,hdY,hanti⟩ := ih
    have hs : pathSet q ⊆ Y := by rw [heY]; exact subset_union_right
    have hRY : R ⊆ Y := by rw [heY]; exact subset_union_left
    obtain ⟨y,hy,ha,hpriv⟩ := path_private m hm Y hY q hs (endpoint_connected m hm hfree Y hY q hs)
    let last : Fin m := ⟨m-1,by omega⟩
    let Z := (insert y Y).erase (q last)
    let q' := shiftPath q y (fun h => hy (hs h)) ha
    have hZ : MinCDS G Z := path_swap m hm hfree Y hY q hs y hy ha
    have hset : pathSet q' = (insert y (pathSet q)).erase (q last) := pathSet_shift (by omega) q y _ ha
    have hyR : y ∉ R := fun hh => hy (hRY hh)
    have hlR : q last ∉ R := fun hh => Finset.disjoint_left.mp hdY hh (path_mem q last)
    have hZeq : Z = R ∪ pathSet q' := by
      rw [hset]
      ext v
      simp only [Z,heY,mem_erase,mem_insert,mem_union]
      by_cases hv : v = q last
      · subst v; simp [hlR]
      · tauto
    have hdis : Disjoint R (pathSet q') := by
      apply Finset.disjoint_left.mpr
      intro v hv hvq
      rw [hset] at hvq
      rcases mem_insert.mp (mem_erase.mp hvq).2 with rfl | hh
      · exact hyR hv
      · exact Finset.disjoint_left.mp hdY hv hh
    refine ⟨Z,q',hZ,hZeq,hdis,?_⟩
    intro i hi z hz
    by_cases hi0 : i.val = 0
    · have he0 : i = ⟨0,by omega⟩ := Fin.ext hi0
      rw [he0,show q' ⟨0,by omega⟩ = y from shiftPath_zero (by omega) q y _ ha]
      intro haz
      have hez := hpriv z (hRY hz) haz
      exact Finset.disjoint_left.mp hdY hz (hez ▸ path_mem q ⟨0,by omega⟩)
    · let j : Fin m := ⟨i.val-1,by have := i.isLt; omega⟩
      have hji : j.val+1 < m := by dsimp [j]; have := i.isLt; omega
      have hei : i = ⟨j.val+1,hji⟩ := Fin.ext (by dsimp [j]; omega)
      rw [hei,show q' ⟨j.val+1,hji⟩ = q j from shiftPath_next q y _ ha j hji]
      exact hanti j (by dsimp [j]; omega) z hz

theorem minimum_structure (G : SimpleGraph V) (m : ℕ) (hm : 2 ≤ m)
    (hfree : PFree (m+2) G) (X : Finset V) (hX : MinCDS G X) :
    PFree m (G.induce (X : Set V)) ∨ ∃ p : pathGraph m ↪g G, X = pathSet p := by
  classical
  by_cases hf : PFree m (G.induce (X : Set V))
  · exact Or.inl hf
  right
  obtain ⟨q⟩ : Nonempty (pathGraph m ↪g G.induce (X : Set V)) := by
    simpa only [PFree, IsIndContained, not_not] using hf
  let p := (Embedding.induce (X : Set V)).comp q
  have hs : pathSet p ⊆ X := by
    intro v hv
    obtain ⟨i,rfl⟩ := (mem_pathSet p v).mp hv
    exact (q i).property
  let R := X \ pathSet p
  have he : X = R ∪ pathSet p := by exact (sdiff_union_of_subset hs).symm
  have hd : Disjoint R (pathSet p) := sdiff_disjoint
  obtain ⟨Y,s,hY,hYs,hds,hanti⟩ := rotate_prefix m hm hfree R X hX p he hd m
  have hR : R = ∅ := by
    apply connected_no_cross G Y R hY.2.1 (by rw [hYs]; exact subset_union_left)
    · intro z hz v hv hvR hav
      rw [hYs] at hv
      have hvs := (mem_union.mp hv).resolve_left hvR
      obtain ⟨i,rfl⟩ := (mem_pathSet s v).mp hvs
      exact hanti i i.isLt z hz hav.symm
    · refine ⟨s ⟨0,by omega⟩, ?_, ?_⟩
      · rw [hYs]; exact mem_union_right _ (path_mem s _)
      · intro hz
        exact Finset.disjoint_left.mp hds hz (path_mem s _)
  refine ⟨p,?_⟩
  rw [he,hR,empty_union]

end P7Proof


set_option autoImplicit false
open SimpleGraph Finset
open P7ThreeColor.Seed
namespace P7Proof

theorem p3free_complete {W : Type*} (H : SimpleGraph W) (hc : H.Connected)
    (h3 : PFree 3 H) : ∀ u v, u ≠ v → H.Adj u v := by
  have ht : ∀ u v w, H.Adj u v → H.Adj v w → u = w ∨ H.Adj u w := by
    intro u v w huv hvw
    by_cases he : u = w
    · exact Or.inl he
    by_cases ha : H.Adj u w
    · exact Or.inr ha
    exfalso
    apply h3
    let f : Fin 3 → W := ![u,v,w]
    have hu : u ≠ v := huv.ne
    have hv : v ≠ w := hvw.ne
    refine ⟨{ toFun := f, inj' := ?_, map_rel_iff' := ?_ }⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f]
    · intro i j
      change H.Adj (f i) (f j) ↔ (pathGraph 3).Adj i j
      fin_cases i <;> fin_cases j <;> simp [f, pathGraph_adj, huv, hvw, ha, H.adj_comm]
  intro u v huv
  obtain ⟨p⟩ := hc u v
  have hall : ∀ {a b}, H.Walk a b → a = b ∨ H.Adj a b := by
    intro a b p
    induction p with
    | nil => exact Or.inl rfl
    | @cons a b c hab _ ih =>
      rcases ih with rfl | hbc
      · exact Or.inr hab
      · exact ht a b c hab hbc
  exact (hall p).resolve_left huv

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem two_domination (G : SimpleGraph V) (X T : Finset V)
    (hd : IsDominating G X) (_hTX : T ⊆ X)
    (hdom : ∀ x ∈ X, x ∈ T ∨ ∃ t ∈ T, G.Adj x t) : IsTwoDominating G T := by
  apply (dominating_iff G _).mpr
  intro v
  have hXC : ∀ x ∈ X, x ∈ P7ThreeColor.Seed.closure G T :=
    fun x hx => (mem_closure G T x).mpr (hdom x hx)
  rcases (dominating_iff G X).mp hd v with hv | ⟨x,hx,ha⟩
  · exact Or.inl (hXC v hv)
  · exact Or.inr ⟨x,hXC x hx,ha⟩

theorem subtype_seed (G : SimpleGraph V) (X : Finset V)
    (hd : IsDominating G X) (T : Finset {v // v ∈ (X : Set V)})
    (hT : IsDominating (G.induce (X : Set V)) T)
    (hc : ((G.induce (X : Set V)).induce (T : Set {v // v ∈ (X : Set V)})).Connected)
    (hcard : T.card ≤ 3) :
    ∃ S : Finset V, S.card ≤ 3 ∧ (G.induce (S : Set V)).Connected ∧ IsTwoDominating G S := by
  classical
  let S := T.image Subtype.val
  have hSX : S ⊆ X := by
    intro v hv
    obtain ⟨x,_,rfl⟩ := mem_image.mp hv
    exact x.property
  have hconn : (G.induce (S : Set V)).Connected := by
    let f : ((G.induce (X : Set V)).induce (T : Set {v // v ∈ (X : Set V)})) →g
        G.induce (S : Set V) :=
      ⟨fun x => ⟨x.val.val, mem_image.mpr ⟨x.val, x.property, rfl⟩⟩, fun ha => ha⟩
    apply hc.map f
    intro v
    obtain ⟨x,hx,he⟩ := mem_image.mp v.property
    exact ⟨⟨x,hx⟩, Subtype.ext he⟩
  refine ⟨S, ?_, hconn, two_domination G X S hd hSX ?_⟩
  · exact (card_image_le).trans hcard
  · intro x hx
    rcases (dominating_iff (G.induce (X : Set V)) T).mp hT ⟨x,hx⟩ with ht | ⟨t,ht,ha⟩
    · exact Or.inl (mem_image.mpr ⟨⟨x,hx⟩,ht,rfl⟩)
    · exact Or.inr ⟨t.val,mem_image.mpr ⟨t,ht,rfl⟩,ha⟩

theorem p5_small_seed (G : SimpleGraph V) (p : pathGraph 5 ↪g G)
    (hd : IsDominating G (pathSet p)) :
    ∃ S : Finset V, S.card ≤ 3 ∧ (G.induce (S : Set V)).Connected ∧ IsTwoDominating G S := by
  classical
  let q : pathGraph 3 ↪g G := {
    toFun := fun i => p ⟨i.val+1, by omega⟩
    inj' := fun i j he => Fin.ext (by have := congrArg Fin.val (p.injective he); simpa using this)
    map_rel_iff' := by
      intro i j
      change G.Adj (p _) (p _) ↔ _
      rw [p.map_rel_iff,pathGraph_adj,pathGraph_adj]
      simp }
  have hs : pathSet q ⊆ pathSet p := by
    intro v hv
    obtain ⟨i,rfl⟩ := (mem_pathSet q v).mp hv
    exact path_mem p _
  refine ⟨pathSet q, (card_pathSet q).le, induced_pathSet_connected (by decide) q,
    two_domination G (pathSet p) (pathSet q) hd hs ?_⟩
  intro v hv
  obtain ⟨i,rfl⟩ := (mem_pathSet p v).mp hv
  fin_cases i
  · right
    refine ⟨q 0,path_mem q 0,?_⟩
    change G.Adj (p 0) (p 1)
    rw [p.map_rel_iff,pathGraph_adj]
    decide
  · left; exact path_mem q 0
  · left; exact path_mem q 1
  · left; exact path_mem q 2
  · right
    refine ⟨q 2,path_mem q 2,?_⟩
    change G.Adj (p 4) (p 3)
    rw [p.map_rel_iff,pathGraph_adj]
    decide

theorem complete_card_le_three {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (ha : ∀ u v, u ≠ v → H.Adj u v) (h4 : H.CliqueFree 4) :
    Fintype.card W ≤ 3 := by
  by_contra hn
  have hc : 4 ≤ (univ : Finset W).card := by simpa using (show 4 ≤ Fintype.card W by omega)
  obtain ⟨T,_,hT⟩ := exists_subset_card_eq hc
  apply h4 T
  refine ⟨?_,hT⟩
  intro u hu v hv huv
  exact ha u v huv

theorem small_seed_of_structure (G : SimpleGraph V) (hG : G.Connected)
    (h7 : PFree 7 G) (h4 : G.CliqueFree 4) :
    ∃ S : Finset V, S.card ≤ 3 ∧ (G.induce (S : Set V)).Connected ∧ IsTwoDominating G S := by
  classical
  obtain ⟨X,hX⟩ := exists_minCDS G hG
  rcases minimum_structure G 5 (by decide) h7 X hX with h5 | ⟨p,hp⟩
  · obtain ⟨Y,hY⟩ := exists_minCDS (G.induce (X : Set V)) hX.2.1
    have h4X : (G.induce (X : Set V)).CliqueFree 4 :=
      h4.comap (Embedding.induce (X : Set V)).isContained
    apply subtype_seed G X hX.1 Y hY.1 hY.2.1
    rcases minimum_structure (G.induce (X : Set V)) 3 (by decide) h5 Y hY with h3 | ⟨q,hq⟩
    · have h4Y := h4X.comap (Embedding.induce (Y : Set {v // v ∈ (X : Set V)})).isContained
      have hb := complete_card_le_three _ (p3free_complete _ hY.2.1 h3) h4Y
      simpa using hb
    · rw [hq,card_pathSet]
  · apply p5_small_seed G p
    simpa only [hp] using hX.1

end P7Proof


set_option autoImplicit false

namespace P7ThreeColor.Seed

/-- First statement of Corollary 5, p. 6. -/
theorem corollary_5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (h7 : PFree 7 G) :
    (∃ S : Finset V, S.card ≤ 3 ∧ (G.induce (S : Set V)).Connected ∧
      IsTwoDominating G S) ∨ ¬ G.CliqueFree 4 := by
  classical
  by_cases h4 : G.CliqueFree 4
  · exact Or.inl (P7Proof.small_seed_of_structure G hG h7 h4)
  · exact Or.inr h4

end P7ThreeColor.Seed

open P7ThreeColor.Seed in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (h7 : PFree 7 G) :
    (∃ S : Finset V, S.card ≤ 3 ∧ (G.induce (S : Set V)).Connected ∧
      IsTwoDominating G S) ∨ ¬ G.CliqueFree 4 :=
  P7ThreeColor.Seed.corollary_5 G hG h7

