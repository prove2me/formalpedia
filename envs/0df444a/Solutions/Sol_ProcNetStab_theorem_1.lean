-- Prove2me | solution 1 for ProcNetStab.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T12:22:17.509948+00:00
-- url     : https://prove2.me/submissions/4efaf516-6af2-4c92-9de9-0c9f6cb3f4a1

import Mathlib
import Definitions.Def_ProcNetStab_Rationalizable
import Definitions.Def_ProcNetStab_KWARPS

set_option autoImplicit false


set_option autoImplicit false

namespace S06P054

open ProcNetStab

theorem kIso_refl {V T : Type*} (L : V → T) (g : SimpleGraph V)
    (k : ℕ) (i : V) (h : SimpleGraph V) (hadj : IsAdjacentNet g h) :
    KIso L g k i h i h := by
  exact ⟨hadj, hadj, SimpleGraph.Iso.refl, rfl, fun _ => rfl⟩

theorem kIso_symm {V T : Type*} {L : V → T} {g : SimpleGraph V}
    {k : ℕ} {i i' : V} {h h' : SimpleGraph V}
    (hiso : KIso L g k i h i' h') : KIso L g k i' h' i h := by
  rcases hiso with ⟨hh, hh', σ, hroot, htype⟩
  refine ⟨hh', hh, σ.symm, ?_, ?_⟩
  · have hr : σ ⟨i, mem_ball_self h k i⟩ = ⟨i', mem_ball_self h' k i'⟩ :=
      Subtype.ext hroot
    rw [← hr]
    simp
  · intro u
    simpa using (htype (σ.symm u)).symm

theorem kIso_trans {V T : Type*} {L : V → T} {g : SimpleGraph V}
    {k : ℕ} {i i' i'' : V} {h h' h'' : SimpleGraph V}
    (hiso : KIso L g k i h i' h') (hiso' : KIso L g k i' h' i'' h'') :
    KIso L g k i h i'' h'' := by
  rcases hiso with ⟨hh, _, σ, hroot, htype⟩
  rcases hiso' with ⟨_, hh'', τ, hroot', htype'⟩
  refine ⟨hh, hh'', σ.trans τ, ?_, ?_⟩
  · have hr : σ ⟨i, mem_ball_self h k i⟩ = ⟨i', mem_ball_self h' k i'⟩ :=
      Subtype.ext hroot
    change (τ (σ ⟨i, mem_ball_self h k i⟩) : V) = i''
    rw [hr]
    exact hroot'
  · intro u
    exact (htype u).trans (htype' (σ u))

/-- The root has a neighborhood class already present in the observed graph. -/
def Good {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ)
    (a : V) (h : SimpleGraph V) : Prop :=
  ∃ i, KIso L g k i g a h

theorem good_observed {V T : Type*} (L : V → T) (g : SimpleGraph V)
    (k : ℕ) (a : V) : Good L g k a g :=
  ⟨a, kIso_refl L g k a g (Or.inl rfl)⟩

theorem good_iff_of_kIso {V T : Type*} {L : V → T} {g : SimpleGraph V}
    {k : ℕ} {a a' : V} {h h' : SimpleGraph V}
    (hiso : KIso L g k a h a' h') : Good L g k a h ↔ Good L g k a' h' := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, kIso_trans hi hiso⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, kIso_trans hi (kIso_symm hiso)⟩

/-- A weak preference giving the observed neighborhood classes utility one. -/
def binaryPref {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ)
    (a : V) (h h' : SimpleGraph V) : Prop :=
  Good L g k a h' → Good L g k a h

theorem binaryPref_weakOrder {V T : Type*} (L : V → T) (g : SimpleGraph V)
    (k : ℕ) (a : V) : IsWeakOrder (binaryPref L g k a) := by
  classical
  constructor
  · intro h h'
    unfold binaryPref
    tauto
  · intro h h' h'' h₁ h₂ hgood
    exact h₁ (h₂ hgood)

theorem binaryPref_anonymous {V T : Type*} (L : V → T) (g : SimpleGraph V)
    (k : ℕ) : KAnonymous L g k (binaryPref L g k) := by
  classical
  intro i i' j j' h h' htop hdel
  have hgood := good_iff_of_kIso htop
  have hgooddel := good_iff_of_kIso hdel
  unfold strictPart binaryPref
  tauto

theorem binaryPref_stable {V T : Type*} (L : V → T) (g : SimpleGraph V)
    (k : ℕ) (hw : KWARPS L g k) : PairwiseStable g (binaryPref L g k) := by
  classical
  constructor
  · intro i j _
    exact ⟨fun _ => good_observed L g k i, fun _ => good_observed L g k j⟩
  · intro i j hne hnadj
    have hi := good_observed L g k i
    have hj := good_observed L g k j
    have hnot : ¬ (Good L g k i (addLink g i j) ∧ Good L g k j (addLink g i j)) := by
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact hw ⟨a, b, i, j, hne, hnadj, ha, hb⟩
    unfold strictPart binaryPref
    tauto

theorem kwarps_rationalizable {V T : Type*} (L : V → T) (g : SimpleGraph V)
    (k : ℕ) (hw : KWARPS L g k) : Rationalizable L g k := by
  exact ⟨binaryPref L g k, binaryPref_weakOrder L g k,
    binaryPref_anonymous L g k, binaryPref_stable L g k hw⟩

end S06P054


open ProcNetStab

namespace S06P054

theorem addLink_comm {V : Type*} (g : SimpleGraph V) (i j : V) :
    addLink g i j = addLink g j i := by
  simp only [addLink, SimpleGraph.edge_comm]

theorem delLink_self {V : Type*} (g : SimpleGraph V) (i : V) :
    delLink g i i = g := by
  apply SimpleGraph.deleteEdges_of_subset_diagSet
  simp

theorem delLink_addLink {V : Type*} (g : SimpleGraph V) (i j : V)
    (hno : ¬ g.Adj i j) : delLink (addLink g i j) i j = g := by
  ext u v
  simp only [delLink, SimpleGraph.deleteEdges_adj, addLink, SimpleGraph.sup_adj,
    SimpleGraph.edge_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨h | h, hne⟩
    · exact h
    · aesop
  · intro h
    refine ⟨Or.inl h, ?_⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hno h
    · exact hno h.symm

theorem mem_ball_zero {V : Type*} (g : SimpleGraph V) (i v : V) :
    v ∈ ball g 0 i ↔ v = i := by
  constructor
  · intro hv
    change g.edist i v ≤ 0 at hv
    exact (SimpleGraph.edist_eq_zero_iff.mp (le_antisymm hv zero_le)).symm
  · intro hv
    rw [hv]
    exact mem_ball_self g 0 i

theorem kIso_zero {V T : Type*} (L : V → T) (g h h' : SimpleGraph V)
    (i i' : V) (hh : IsAdjacentNet g h) (hh' : IsAdjacentNet g h')
    (hL : L i = L i') : KIso L g 0 i h i' h' := by
  let e : ball h 0 i ≃ ball h' 0 i' :=
    { toFun := fun _ => ⟨i', mem_ball_self h' 0 i'⟩
      invFun := fun _ => ⟨i, mem_ball_self h 0 i⟩
      left_inv := by
        intro u
        apply Subtype.ext
        exact ((mem_ball_zero h i u).mp u.property).symm
      right_inv := by
        intro u
        apply Subtype.ext
        exact ((mem_ball_zero h' i' u).mp u.property).symm }
  let σ : kNbhd h 0 i ≃g kNbhd h' 0 i' :=
    { toEquiv := e
      map_rel_iff' := by
        intro u v
        change h'.Adj i' i' ↔ h.Adj (u : V) (v : V)
        rw [(mem_ball_zero h i u).mp u.property, (mem_ball_zero h i v).mp v.property]
        simp }
  refine ⟨hh, hh', σ, rfl, ?_⟩
  intro u
  change L (u : V) = L i'
  rw [(mem_ball_zero h i u).mp u.property]
  exact hL

theorem rationalizable_kwarps_zero {V T : Type*} (L : V → T) (g : SimpleGraph V)
    (hr : Rationalizable L g 0) : KWARPS L g 0 := by
  rcases hr with ⟨pref, hweak, hanon, hstable⟩
  rintro ⟨i, j, i', j', hne, hno, hi, hj⟩
  have weak_add (a b : V) (hab : a ≠ b) (hnot : ¬ g.Adj a b) :
      pref a (addLink g a b) g := by
    have hobs : IsAdjacentNet g g := Or.inl rfl
    have hadd : IsAdjacentNet g (addLink g a b) :=
      Or.inr (Or.inl ⟨a, b, hab, hnot, rfl⟩)
    have h1 := kIso_zero L g g (addLink g a b) a a hobs hadd rfl
    have h2 : KIso L g 0 a (delLink g a a) a (delLink (addLink g a b) a b) := by
      rw [delLink_self, delLink_addLink g a b hnot]
      exact kIso_zero L g g g a a hobs hobs rfl
    rcases hanon a a a b g (addLink g a b) h1 h2 with hw | hs
    · simpa only [delLink_addLink g a b hnot] using hw.2
    · have hrefl : pref a g g := (hweak a).1 g g |>.elim id id
      exact False.elim (hs.1.2 (by simpa only [delLink_self] using hrefl))
  rcases hstable.2 i' j' hne hno with hs | hs
  · exact hs.2 (weak_add i' j' hne hno)
  · apply hs.2
    rw [addLink_comm g i' j']
    exact weak_add j' i' hne.symm (fun h => hno h.symm)

theorem rationalizable_kwarps_of_transport {V T : Type*} (L : V → T)
    (g : SimpleGraph V) (k : ℕ)
    (transport : ∀ (i i' j' : V), i' ≠ j' → ¬ g.Adj i' j' →
      KIso L g k i g i' (addLink g i' j') →
        ∃ r, g.Adj i r ∧ KIso L g k i (delLink g i r) i' g)
    (hr : Rationalizable L g k) : KWARPS L g k := by
  rcases hr with ⟨pref, hweak, hanon, hstable⟩
  rintro ⟨i, j, i', j', hne, hno, hi, hj⟩
  have weak_add (a a' b' : V) (hne' : a' ≠ b') (hno' : ¬ g.Adj a' b')
      (hiso : KIso L g k a g a' (addLink g a' b')) :
      pref a' (addLink g a' b') g := by
    obtain ⟨r, har, hdel⟩ := transport a a' b' hne' hno' hiso
    have hdel' : KIso L g k a (delLink g a r) a'
        (delLink (addLink g a' b') a' b') := by
      simpa only [delLink_addLink g a' b' hno'] using hdel
    rcases hanon a a' r b' g (addLink g a' b') hiso hdel' with hw | hs
    · simpa only [delLink_addLink g a' b' hno'] using hw.2
    · exact False.elim (hs.1.2 ((hstable.1 a r har).1))
  rcases hstable.2 i' j' hne hno with hs | hs
  · exact hs.2 (weak_add i i' j' hne hno hi)
  · apply hs.2
    rw [addLink_comm g i' j']
    apply weak_add j j' i' hne.symm (fun h => hno h.symm)
    simpa only [addLink_comm g i' j'] using hj

end S06P054

open SimpleGraph ProcNetStab

namespace S06P054Transport

lemma ball_iff_walk {V : Type*} (G : SimpleGraph V) (k : ℕ) (u v : V) :
    v ∈ ProcNetStab.ball G k u ↔ ∃ p : G.Walk u v, p.length ≤ k := by
  constructor
  · intro hv
    have ht : G.edist u v ≠ ⊤ := by
      intro he
      have h := hv
      change G.edist u v ≤ (k : ℕ∞) at h
      rw [he] at h
      simpa using h
    obtain ⟨p, hp⟩ := G.exists_walk_of_edist_ne_top ht
    refine ⟨p, ?_⟩
    have h : (p.length : ℕ∞) ≤ (k : ℕ∞) := hp.trans_le hv
    exact_mod_cast h
  · rintro ⟨p, hp⟩
    exact p.edist_le.trans (by exact_mod_cast hp)

lemma hom_edist_le {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (u v : V) : H.edist (f u) (f v) ≤ G.edist u v := by
  change H.edist (f u) (f v) ≤ ⨅ p : G.Walk u v, (p.length : ℕ∞)
  refine le_iInf fun p => ?_
  simpa using (p.map f).edist_le

lemma iso_edist {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (u v : V) : H.edist (f u) (f v) = G.edist u v := by
  apply le_antisymm (hom_edist_le f.toHom u v)
  simpa using hom_edist_le f.symm.toHom (f u) (f v)

lemma walk_support_ball {V : Type*} {F G : SimpleGraph V} (hFG : F ≤ G)
    {k : ℕ} {u v : V} (p : F.Walk u v) (hp : p.length ≤ k) :
    ∀ x ∈ p.support, x ∈ ProcNetStab.ball G k u := by
  classical
  intro x hx
  apply (ball_iff_walk G k u x).2
  refine ⟨(p.takeUntil x hx).map (.ofLE hFG), ?_⟩
  simpa using (p.length_takeUntil_le_length hx).trans hp

lemma walk_induce_length {V : Type*} {G : SimpleGraph V} (S : Set V)
    {u v : V} (p : G.Walk u v) :
    ∀ (hp : ∀ x ∈ p.support, x ∈ S), (p.induce S hp).length = p.length := by
  induction p with
  | nil => intro hp; rfl
  | cons h p ih =>
    intro hp
    simp only [SimpleGraph.Walk.induce_cons, SimpleGraph.Walk.length_cons]
    exact congrArg Nat.succ (ih (fun x hx => hp x (by simp [hx])))

lemma induced_ball_iff {V : Type*} {F G : SimpleGraph V} (hFG : F ≤ G)
    (k : ℕ) (u : V) (v : ProcNetStab.ball G k u) :
    v.val ∈ ProcNetStab.ball F k u ↔
      (F.induce (ProcNetStab.ball G k u)).edist
        ⟨u, mem_ball_self G k u⟩ v ≤ (k : ℕ∞) := by
  constructor
  · intro hv
    obtain ⟨p, hp⟩ := (ball_iff_walk F k u v.val).1 hv
    let q := p.induce (ProcNetStab.ball G k u) (walk_support_ball hFG p hp)
    have hlen : q.length = p.length := walk_induce_length _ p _
    exact q.edist_le.trans (by rw [hlen]; exact_mod_cast hp)
  · intro hv
    have h := hom_edist_le (SimpleGraph.Embedding.induce
      (G := F) (ProcNetStab.ball G k u)).toHom
        (⟨u, mem_ball_self G k u⟩ : ProcNetStab.ball G k u) v
    exact h.trans hv

lemma delete_induced_iso {V : Type*} {G H : SimpleGraph V}
    (k : ℕ) (i i' r r' : V)
    (hr : r ∈ ProcNetStab.ball G k i) (hr' : r' ∈ ProcNetStab.ball H k i')
    (σ : kNbhd G k i ≃g kNbhd H k i')
    (hroot : (σ ⟨i, mem_ball_self G k i⟩ : V) = i')
    (hrimage : (σ ⟨r, hr⟩ : V) = r') :
    ∃ τ : (delLink G i r).induce (ProcNetStab.ball G k i) ≃g
        (delLink H i' r').induce (ProcNetStab.ball H k i'),
      ∀ u : ProcNetStab.ball G k i, τ u = σ u := by
  have heq (a b : ProcNetStab.ball G k i) :
      (σ a : V) = (σ b : V) ↔ (a : V) = (b : V) := by
    constructor
    · intro h
      exact congrArg Subtype.val (σ.injective (Subtype.ext h))
    · intro h
      exact congrArg (fun x => (σ x : V)) (Subtype.ext h)
  have heroot (a : ProcNetStab.ball G k i) :
      (σ a : V) = i' ↔ (a : V) = i := by
    simpa only [hroot] using heq a ⟨i, mem_ball_self G k i⟩
  have her (a : ProcNetStab.ball G k i) :
      (σ a : V) = r' ↔ (a : V) = r := by
    simpa only [hrimage] using heq a ⟨r, hr⟩
  let τ : (delLink G i r).induce (ProcNetStab.ball G k i) ≃g
      (delLink H i' r').induce (ProcNetStab.ball H k i') :=
    { toEquiv := σ.toEquiv
      map_rel_iff' := by
        intro a b
        have hadj : H.Adj (σ a : V) (σ b : V) ↔ G.Adj a b := σ.map_adj_iff
        change (delLink H i' r').Adj (σ a : V) (σ b : V) ↔
          (delLink G i r).Adj a b
        simp only [delLink, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
          Sym2.eq_iff, hadj, heroot, her] }
  exact ⟨τ, fun _ => rfl⟩


end S06P054Transport


set_option autoImplicit false

open SimpleGraph ProcNetStab

namespace S06P054Transport

theorem restrict_induced_ball_iso {V W : Type*}
    {F G : SimpleGraph V} {J H : SimpleGraph W} (hFG : F ≤ G) (hJH : J ≤ H)
    (k : ℕ) (i : V) (j : W)
    (σ : (F.induce (ProcNetStab.ball G k i)) ≃g
      (J.induce (ProcNetStab.ball H k j)))
    (hroot : (σ ⟨i, mem_ball_self G k i⟩ : W) = j) :
    ∃ τ : kNbhd F k i ≃g kNbhd J k j,
      (τ ⟨i, mem_ball_self F k i⟩ : W) = j ∧
      ∀ u : ProcNetStab.ball F k i,
        (τ u : W) = (σ ⟨u.val, (SimpleGraph.edist_anti hFG).trans u.property⟩ : W) := by
  have hr : σ ⟨i, mem_ball_self G k i⟩ = ⟨j, mem_ball_self H k j⟩ :=
    Subtype.ext hroot
  have hmem (u : ProcNetStab.ball G k i) :
      u.val ∈ ProcNetStab.ball F k i ↔ (σ u).val ∈ ProcNetStab.ball J k j := by
    have hd := iso_edist σ ⟨i, mem_ball_self G k i⟩ u
    rw [hr] at hd
    rw [induced_ball_iff hFG k i u, induced_ball_iff hJH k j (σ u), hd]
  let upF (u : ProcNetStab.ball F k i) : ProcNetStab.ball G k i :=
    ⟨u.val, (SimpleGraph.edist_anti hFG).trans u.property⟩
  let upJ (v : ProcNetStab.ball J k j) : ProcNetStab.ball H k j :=
    ⟨v.val, (SimpleGraph.edist_anti hJH).trans v.property⟩
  let τ : kNbhd F k i ≃g kNbhd J k j :=
    { toFun := fun u => ⟨(σ (upF u)).val, (hmem (upF u)).mp u.property⟩
      invFun := fun v => ⟨(σ.symm (upJ v)).val,
        (hmem (σ.symm (upJ v))).mpr
          (by simpa only [RelIso.apply_symm_apply] using v.property)⟩
      left_inv := by
        intro u
        apply Subtype.ext
        change (σ.symm (σ (upF u)) : V) = u.val
        simp [upF]
      right_inv := by
        intro v
        apply Subtype.ext
        change (σ (σ.symm (upJ v)) : W) = v.val
        simp [upJ]
      map_rel_iff' := by
        intro u v
        exact σ.map_rel_iff }
  refine ⟨τ, ?_, ?_⟩
  · exact hroot
  · intro u
    rfl

end S06P054Transport

namespace S06P054Transport
lemma delete_transport {V T : Type*} (L : V → T) (g : SimpleGraph V)
    (k : ℕ) (hk : 1 ≤ k) (i i' j' : V)
    (hne : i' ≠ j') (hnon : ¬ g.Adj i' j')
    (hiso : KIso L g k i g i' (addLink g i' j')) :
    ∃ r, g.Adj i r ∧ KIso L g k i (delLink g i r) i' g := by
  classical
  rcases hiso with ⟨_, _, σ, hroot, htypes⟩
  have hnew : (addLink g i' j').Adj i' j' := by
    exact Or.inr ((SimpleGraph.edge_adj i' j' i' j').2 ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
  have hjball : j' ∈ ProcNetStab.ball (addLink g i' j') k i' := by
    change (addLink g i' j').edist i' j' ≤ (k : ℕ∞)
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr hnew]
    exact_mod_cast hk
  let r : ProcNetStab.ball g k i := σ.symm ⟨j', hjball⟩
  have hrimage : (σ r : V) = j' := by simp [r]
  have hradj : g.Adj i r.val := by
    apply (σ.map_adj_iff (v := ⟨i, mem_ball_self g k i⟩) (w := r)).mp
    change (addLink g i' j').Adj (σ ⟨i, mem_ball_self g k i⟩ : V) (σ r : V)
    rwa [hroot, hrimage]
  obtain ⟨δ, hδ⟩ := delete_induced_iso k i i' r.val j' r.property hjball σ hroot hrimage
  have hδroot : (δ ⟨i, mem_ball_self g k i⟩ : V) = i' := by
    rw [hδ]
    exact hroot
  have hFG : delLink g i r.val ≤ g := g.deleteEdges_le _
  have hJH : delLink (addLink g i' j') i' j' ≤ addLink g i' j' :=
    (addLink g i' j').deleteEdges_le _
  obtain ⟨τ, hτroot, hτval⟩ := restrict_induced_ball_iso hFG hJH k i i' δ hδroot
  have hcancel : delLink (addLink g i' j') i' j' = g := by
    ext u v
    simp only [delLink, SimpleGraph.deleteEdges_adj, addLink, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨h | h, hne'⟩
      · exact h
      · aesop
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hnon h
      · exact hnon h.symm
  have hresult : KIso L g k i (delLink g i r.val) i'
      (delLink (addLink g i' j') i' j') := by
    refine ⟨Or.inr (Or.inr ⟨i, r.val, hradj, rfl⟩), Or.inl hcancel,
      τ, hτroot, ?_⟩
    intro u
    let uold : ProcNetStab.ball g k i :=
      ⟨u.val, (SimpleGraph.edist_anti hFG).trans u.property⟩
    calc
      L (u : V) = L (σ uold : V) := htypes uold
      _ = L (δ uold : V) := congrArg L (congrArg Subtype.val (hδ uold).symm)
      _ = L (τ u : V) := congrArg L (hτval u).symm
  exact ⟨r.val, hradj, by simpa only [hcancel] using hresult⟩

end S06P054Transport

open ProcNetStab

theorem solution {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ) :
    Rationalizable L g k ↔ KWARPS L g k := by
  constructor
  · intro hr
    by_cases hk : k = 0
    · subst k
      exact S06P054.rationalizable_kwarps_zero L g hr
    · exact S06P054.rationalizable_kwarps_of_transport L g k
        (S06P054Transport.delete_transport L g k (Nat.one_le_iff_ne_zero.mpr hk)) hr
  · exact S06P054.kwarps_rationalizable L g k

#print axioms solution
