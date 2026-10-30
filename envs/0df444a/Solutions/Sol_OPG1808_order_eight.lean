-- Prove2me | solution 1 for OPG1808.order_eight
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T02:35:38.331802+00:00
-- url     : https://prove2.me/submissions/f6a0397a-4f82-4451-939c-7a802a6f522b

import Theorems.Thm_OPG1808_order_eight_normalized_cycle_prefix01
import Theorems.Thm_OPG1808_order_eight_normalized_cycle_prefix000
import Theorems.Thm_OPG1808_order_eight_normalized_cycle_prefix001
import Theorems.Thm_OPG1808_order_seven
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Logic.Equiv.Fin.Rotate
import Definitions.Def_opg1808_colored_tournaments
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.PiLex

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CanonicalEightParent

section

open Function

namespace OPG1808Audit

universe u

/-- Every map on a nonempty finite type has a positive-period point. -/
theorem exists_periodic_point {V : Type u} [Fintype V] [Nonempty V] (f : V → V) :
    ∃ a : V, ∃ p : ℕ, 0 < p ∧ IsPeriodicPt f p a := by
  classical
  let x : V := Classical.arbitrary V
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card V + 1) ↦ f^[i.val] x) (by simp)
  have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨f^[i.val] x, j.val - i.val, Nat.sub_pos_of_lt hlt, ?_⟩
    change f^[j.val - i.val] (f^[i.val] x) = f^[i.val] x
    rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact heq.symm
  · refine ⟨f^[j.val] x, i.val - j.val, Nat.sub_pos_of_lt hlt, ?_⟩
    change f^[i.val - j.val] (f^[j.val] x) = f^[j.val] x
    rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact heq

/-- A finite relation with an incoming predecessor at every vertex has a simple directed cycle.
The indexing follows the chosen predecessor map, so relation arrows point backwards. -/
theorem exists_simple_cycle_of_predecessor {V : Type u} [Fintype V] [Nonempty V]
    (R : V → V → Prop) (hpred : ∀ v : V, ∃ w : V, R w v) :
    ∃ m : ℕ, 0 < m ∧ m ≤ Fintype.card V ∧
      ∃ e : Fin m → V, Function.Injective e ∧
        ∀ i : Fin m, R (e (finRotate m i)) (e i) := by
  classical
  let f : V → V := fun v ↦ Classical.choose (hpred v)
  have hf : ∀ v : V, R (f v) v := fun v ↦ Classical.choose_spec (hpred v)
  obtain ⟨a, p, hp, hperiod⟩ := exists_periodic_point f
  let m := minimalPeriod f a
  have hm : 0 < m := hperiod.minimalPeriod_pos hp
  have hcard : m ≤ Fintype.card V := minimalPeriod_le_card
  let e : Fin m → V := fun i ↦ f^[i.val] a
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact iterate_injOn_Iio_minimalPeriod i.isLt j.isLt hij
  have hs : ∀ i : Fin m, e (finRotate m i) = f (e i) := by
    intro i
    have hrot : (finRotate m i).val = (i.val + 1) % m := by
      let inst : NeZero m := ⟨Nat.ne_of_gt hm⟩
      rw [finRotate_apply, Fin.val_add, Fin.val_one']
      simp only [Nat.add_mod, Nat.mod_mod]
    change f^[(finRotate m i).val] a = f (f^[i.val] a)
    rw [hrot, (isPeriodicPt_minimalPeriod f a).iterate_mod_apply, iterate_succ_apply']
  refine ⟨m, hm, hcard, e, he, ?_⟩
  intro i
  rw [hs]
  exact hf (e i)

/-- Reversing the indexing makes the arrows follow `finRotate`, as in a SAT cycle. -/
theorem exists_forward_simple_cycle_of_predecessor {V : Type u} [Fintype V] [Nonempty V]
    (R : V → V → Prop) (hpred : ∀ v : V, ∃ w : V, R w v) :
    ∃ m : ℕ, 0 < m ∧ m ≤ Fintype.card V ∧
      ∃ e : Fin m → V, Function.Injective e ∧
        ∀ i : Fin m, R (e i) (e (finRotate m i)) := by
  obtain ⟨m, hm, hcard, e, he, hcycle⟩ := exists_simple_cycle_of_predecessor R hpred
  let inst : NeZero m := ⟨Nat.ne_of_gt hm⟩
  refine ⟨m, hm, hcard, (fun i ↦ e (-i)), he.comp neg_injective, ?_⟩
  intro i
  have hrev : finRotate m (-(finRotate m i)) = -i := by
    simp [finRotate_apply, add_assoc]
  simpa only [hrev] using hcycle (-(finRotate m i))

end OPG1808Audit
end

section

open OPG1808

namespace OPG1808Audit

universe u v

/-- Monochromatic paths in an induced graph give paths in the original graph. -/
theorem monochromatically_reaches_map {V : Type u} {W : Type v}
    (D : Digraph V) (color : ArcColoring V) (e : W → V) {s t : W}
    (h : MonochromaticallyReaches (fun i j ↦ D (e i) (e j))
      (fun i j ↦ color (e i) (e j)) s t) :
    MonochromaticallyReaches D color (e s) (e t) := by
  obtain ⟨k, hpath⟩ := h
  exact ⟨k, hpath.lift e (fun _ _ h ↦ h)⟩

/-- Tournament structure restricts along an injective vertex map. -/
theorem is_tournament_map {V : Type u} {W : Type v}
    (D : Digraph V) (e : W → V) (he : Function.Injective e) (ht : IsTournament D) :
    IsTournament (fun i j ↦ D (e i) (e j)) := by
  constructor
  · intro i
    exact ht.1 (e i)
  · intro i j hij
    exact ht.2 (fun h ↦ hij (he h))

/-- A rainbow directed triangle in an induced graph is one in the original graph. -/
theorem no_rainbow_map {V : Type u} {W : Type v}
    (D : Digraph V) (color : ArcColoring V) (e : W → V) (he : Function.Injective e)
    (h : ¬HasRainbowDirectedTriangle D color) :
    ¬HasRainbowDirectedTriangle (fun i j ↦ D (e i) (e j))
      (fun i j ↦ color (e i) (e j)) := by
  rintro ⟨a, b, c, hab, hbc, hca, hDab, hDbc, hDca, hCab, hCbc, hCca⟩
  exact h ⟨e a, e b, e c, he.ne hab, he.ne hbc, he.ne hca,
    hDab, hDbc, hDca, hCab, hCbc, hCca⟩

/-- A no-source tournament contains an injectively labelled physical cycle whose
vertices cannot reach their cycle predecessors monochromatically. No minimality
or positive non-predecessor reachability assumption is needed. -/
theorem missing_predecessor_cycle_of_no_source
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (ht : IsTournament D) (hnosource : ¬∃ s : V, IsMonochromaticSource D color s) :
    ∃ m : ℕ, 3 ≤ m ∧ m ≤ Fintype.card V ∧
      ∃ e : Fin m → V, Function.Injective e ∧
        ∀ i : Fin m, D (e i) (e (finRotate m i)) ∧
          ¬MonochromaticallyReaches D color (e (finRotate m i)) (e i) := by
  classical
  let R : V → V → Prop := fun u v ↦ ¬MonochromaticallyReaches D color v u
  have hpred : ∀ v : V, ∃ w : V, R w v := by
    intro v
    by_contra hmiss
    apply hnosource
    refine ⟨v, fun w ↦ ?_⟩
    by_contra hw
    exact hmiss ⟨w, hw⟩
  obtain ⟨m, hm, hcard, e, he, hcycle⟩ := exists_forward_simple_cycle_of_predecessor R hpred
  have hne : ∀ i : Fin m, e i ≠ e (finRotate m i) := by
    intro i hEq
    apply hcycle i
    rw [← hEq]
    exact ⟨0, .refl⟩
  have harc : ∀ i : Fin m, D (e i) (e (finRotate m i)) := by
    intro i
    rcases (ht.2 (hne i)).1 with hforward | hbackward
    · exact hforward
    · exact False.elim (hcycle i ⟨color (e (finRotate m i)) (e i), .single ⟨hbackward, rfl⟩⟩)
  have hm1 : m ≠ 1 := by
    intro heq
    subst m
    exact hne 0 (congrArg e (Subsingleton.elim _ _))
  have hm2 : m ≠ 2 := by
    intro heq
    subst m
    have hrot0 : finRotate 2 (0 : Fin 2) = 1 := by decide
    have hrot1 : finRotate 2 (1 : Fin 2) = 0 := by decide
    have h01 : D (e 0) (e 1) := by simpa only [hrot0] using harc 0
    have h10 : D (e 1) (e 0) := by simpa only [hrot1] using harc 1
    exact (ht.2 (he.ne (by decide : (0 : Fin 2) ≠ 1))).2 ⟨h01, h10⟩
  refine ⟨m, by omega, hcard, e, he, ?_⟩
  intro i
  exact ⟨harc i, hcycle i⟩

end OPG1808Audit
end

section

open OPG1808

namespace OPG1808Audit

universe u

/-- Every rotation/palette orbit contains a word of minimal natural-valued rank.
Its rank is minimal even when the orbit is computed again from that word. -/
theorem exists_rotation_color_rank_min {n : ℕ} [NeZero n]
    (w : Fin n → Fin 3) (rank : (Fin n → Fin 3) → ℕ) :
    ∃ r : Fin n, ∃ σ : Equiv.Perm (Fin 3),
      let w' : Fin n → Fin 3 := fun i ↦ σ (w (i + r))
      ∀ s : Fin n, ∀ τ : Equiv.Perm (Fin 3),
        rank w' ≤ rank (fun i ↦ τ (w' (i + s))) := by
  classical
  let P : ℕ → Prop := fun k ↦
    ∃ r : Fin n, ∃ σ : Equiv.Perm (Fin 3), rank (fun i ↦ σ (w (i + r))) = k
  have hex : ∃ k, P k := by
    refine ⟨rank w, 0, Equiv.refl _, ?_⟩
    simp only [add_zero, Equiv.refl_apply]
  obtain ⟨r, σ, hmin⟩ := Nat.find_spec hex
  refine ⟨r, σ, ?_⟩
  dsimp only
  intro s τ
  rw [hmin]
  apply Nat.find_min' hex
  refine ⟨s + r, σ.trans τ, ?_⟩
  congr 1
  funext i
  simp only [Equiv.trans_apply, add_assoc]

/-- A bijection of the palette preserves monochromatic reachability exactly. -/
theorem monochromatically_reaches_color_equiv {V : Type u}
    (D : Digraph V) (color : ArcColoring V) (σ : Equiv.Perm (Fin 3)) (s t : V) :
    MonochromaticallyReaches D (fun x y ↦ σ (color x y)) s t ↔
      MonochromaticallyReaches D color s t := by
  constructor
  · rintro ⟨k, hpath⟩
    refine ⟨σ.symm k, Relation.ReflTransGen.mono ?_ s t hpath⟩
    intro x y h
    refine ⟨h.1, σ.injective ?_⟩
    simpa only [Equiv.apply_symm_apply] using h.2
  · rintro ⟨k, hpath⟩
    refine ⟨σ k, Relation.ReflTransGen.mono ?_ s t hpath⟩
    intro x y h
    exact ⟨h.1, congrArg σ h.2⟩

/-- Relabelling colors, even non-injectively, cannot create a rainbow triangle. -/
theorem no_rainbow_color_map {V : Type u}
    (D : Digraph V) (color : ArcColoring V) (σ : Fin 3 → Fin 3)
    (h : ¬HasRainbowDirectedTriangle D color) :
    ¬HasRainbowDirectedTriangle D (fun x y ↦ σ (color x y)) := by
  rintro ⟨a, b, c, hab, hbc, hca, hDab, hDbc, hDca, hCab, hCbc, hCca⟩
  apply h
  refine ⟨a, b, c, hab, hbc, hca, hDab, hDbc, hDca, ?_, ?_, ?_⟩
  · exact fun hc ↦ hCab (congrArg σ hc)
  · exact fun hc ↦ hCbc (congrArg σ hc)
  · exact fun hc ↦ hCca (congrArg σ hc)

/-- The color of any selected arc can be changed to zero without changing
monochromatic reachability or absence of rainbow directed triangles. -/
theorem exists_color_normalization {V : Type u}
    (D : Digraph V) (color : ArcColoring V) (a b : V) :
    ∃ σ : Equiv.Perm (Fin 3), σ (color a b) = 0 ∧
      (∀ s t : V,
        MonochromaticallyReaches D (fun x y ↦ σ (color x y)) s t ↔
          MonochromaticallyReaches D color s t) ∧
      (¬HasRainbowDirectedTriangle D color →
        ¬HasRainbowDirectedTriangle D (fun x y ↦ σ (color x y))) := by
  refine ⟨Equiv.swap (color a b) 0, ?_, ?_, ?_⟩
  · exact Equiv.swap_apply_left _ _
  · exact monochromatically_reaches_color_equiv D color _
  · exact no_rainbow_color_map D color _

end OPG1808Audit
end

section

namespace OPG1808Audit

universe v

/-- Every rotation/palette orbit contains a word minimizing any linearly ordered rank. -/
theorem exists_rotation_color_rank_min_linear_order {n : ℕ} [NeZero n]
    {α : Type v} [LinearOrder α] (w : Fin n → Fin 3)
    (rank : (Fin n → Fin 3) → α) :
    ∃ r : Fin n, ∃ σ : Equiv.Perm (Fin 3),
      let w' : Fin n → Fin 3 := fun i ↦ σ (w (i + r))
      ∀ s : Fin n, ∀ τ : Equiv.Perm (Fin 3),
        rank w' ≤ rank (fun i ↦ τ (w' (i + s))) := by
  classical
  obtain ⟨p, hmin⟩ := Finite.exists_min (fun p : Fin n × Equiv.Perm (Fin 3) ↦
    rank (fun i ↦ p.2 (w (i + p.1))))
  refine ⟨p.1, p.2, ?_⟩
  dsimp only
  intro s τ
  simpa only [Equiv.trans_apply, add_assoc] using hmin (s + p.1, p.2.trans τ)

/-- A rotation/palette orbit contains a word below each of its transforms in lex order. -/
theorem exists_rotation_color_lex_min {n : ℕ} [NeZero n] (w : Fin n → Fin 3) :
    ∃ r : Fin n, ∃ σ : Equiv.Perm (Fin 3),
      let w' : Fin n → Fin 3 := fun i ↦ σ (w (i + r))
      ∀ s : Fin n, ∀ τ : Equiv.Perm (Fin 3),
        toLex w' ≤ toLex (fun i ↦ τ (w' (i + s))) :=
  exists_rotation_color_rank_min_linear_order w toLex

/-- A lex-minimal orbit representative satisfies every equal-prefix digit comparison. -/
theorem exists_rotation_color_prefix_min {n : ℕ} [NeZero n] (w : Fin n → Fin 3) :
    ∃ r : Fin n, ∃ σ : Equiv.Perm (Fin 3),
      let w' : Fin n → Fin 3 := fun i ↦ σ (w (i + r))
      ∀ s : Fin n, ∀ τ : Equiv.Perm (Fin 3), ∀ i : Fin n,
        (∀ j : Fin n, j < i → w' j = τ (w' (j + s))) → w' i ≤ τ (w' (i + s)) := by
  obtain ⟨r, σ, hmin⟩ := exists_rotation_color_lex_min w
  refine ⟨r, σ, ?_⟩
  dsimp only at hmin ⊢
  intro s τ i hprefix
  exact Pi.apply_le_of_toLex (hmin s τ) hprefix

end OPG1808Audit
end

section

open OPG1808

namespace OPG1808Audit

universe u

/-- A finite no-source tournament restricts and relabels to a lex-normalized cyclic
obstruction. Every hypothesis is inherited from the original tournament. -/
theorem normalized_obstruction_of_no_source
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (ht : IsTournament D) (hnoRainbow : ¬HasRainbowDirectedTriangle D color)
    (hnosource : ¬∃ s : V, IsMonochromaticSource D color s) :
    ∃ m : ℕ, 3 ≤ m ∧ m ≤ Fintype.card V ∧
      ∃ D' : Digraph (Fin m), ∃ color' : ArcColoring (Fin m),
        IsTournament D' ∧ ¬HasRainbowDirectedTriangle D' color' ∧
        (∀ i : Fin m, D' i (finRotate m i) ∧
          ¬MonochromaticallyReaches D' color' (finRotate m i) i) ∧
        (∀ r : Fin m, ∀ σ : Equiv.Perm (Fin 3),
          letI : NeZero m := r.neZero
          toLex (fun i ↦ color' i (finRotate m i)) ≤
            toLex (fun i ↦ σ (color' (i + r) (finRotate m (i + r))))) := by
  classical
  obtain ⟨m, hm, hcard, e, he, hcycle⟩ :=
    missing_predecessor_cycle_of_no_source D color ht hnosource
  let inst : NeZero m := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hm)⟩
  let w : Fin m → Fin 3 := fun i ↦ color (e i) (e (finRotate m i))
  obtain ⟨r, σ, hmin⟩ := exists_rotation_color_lex_min w
  dsimp only at hmin
  let e' : Fin m → V := fun i ↦ e (i + r)
  let D' : Digraph (Fin m) := fun i j ↦ D (e' i) (e' j)
  let color' : ArcColoring (Fin m) := fun i j ↦ σ (color (e' i) (e' j))
  have he' : Function.Injective e' := by
    intro i j hij
    exact add_right_cancel (he hij)
  have hrot : ∀ i : Fin m, finRotate m (i + r) = finRotate m i + r := by
    intro i
    simp only [finRotate_apply]
    ac_rfl
  have hword : ∀ i : Fin m, color' i (finRotate m i) = σ (w (i + r)) := by
    intro i
    change σ (color (e (i + r)) (e (finRotate m i + r))) =
      σ (color (e (i + r)) (e (finRotate m (i + r))))
    rw [hrot]
  refine ⟨m, hm, hcard, D', color', is_tournament_map D e' he' ht, ?_, ?_, ?_⟩
  · exact no_rainbow_color_map D' (fun i j ↦ color (e' i) (e' j)) σ
      (no_rainbow_map D color e' he' hnoRainbow)
  · intro i
    have hc := hcycle (i + r)
    constructor
    · change D (e (i + r)) (e (finRotate m i + r))
      simpa only [hrot] using hc.1
    · intro hpath
      have hpath0 : MonochromaticallyReaches D'
          (fun a b ↦ color (e' a) (e' b)) (finRotate m i) i :=
        (monochromatically_reaches_color_equiv D' (fun a b ↦ color (e' a) (e' b))
          σ _ _).mp hpath
      have horig := monochromatically_reaches_map D color e' hpath0
      apply hc.2
      simpa only [e', hrot] using horig
  · intro s τ
    simpa only [hword] using hmin s τ

end OPG1808Audit
end

section

open OPG1808

namespace OPG1808PhysicalAssembly

universe u

/-- Internal conditional induction step. The first input is an actual source
bound on smaller finite tournaments. The second excludes normalized physical
obstructions of the next size. No Boolean-model exclusion is assumed here. -/
theorem source_up_to_succ_of_physical_exclusion
    (bound : ℕ)
    (sourceBound : ∀ (m : ℕ), 0 < m → m ≤ bound →
      ∀ (E : Digraph (Fin m)) (c : ArcColoring (Fin m)),
        IsTournament E → ¬HasRainbowDirectedTriangle E c →
          ∃ s : Fin m, IsMonochromaticSource E c s)
    (hexclude : ∀ (E : Digraph (Fin (bound + 1)))
      (c : ArcColoring (Fin (bound + 1))),
      IsTournament E → ¬HasRainbowDirectedTriangle E c →
      (∀ i : Fin (bound + 1), E i (finRotate (bound + 1) i) ∧
        ¬MonochromaticallyReaches E c (finRotate (bound + 1) i) i) →
      (∀ r : Fin (bound + 1), ∀ σ : Equiv.Perm (Fin 3),
        letI : NeZero (bound + 1) := r.neZero
        toLex (fun i ↦ c i (finRotate (bound + 1) i)) ≤
          toLex (fun i ↦ σ (c (i + r) (finRotate (bound + 1) (i + r))))) → False)
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (htournament : IsTournament D)
    (horder : Fintype.card V ≤ bound + 1)
    (hnoRainbow : ¬HasRainbowDirectedTriangle D color) :
    ∃ s : V, IsMonochromaticSource D color s := by
  classical
  by_contra hnosource
  obtain ⟨m, hm, hcard, E, c, hE, hnoE, hcycle, hmin⟩ :=
    OPG1808Audit.normalized_obstruction_of_no_source D color htournament
      hnoRainbow hnosource
  have : NeZero m := ⟨by omega⟩
  by_cases hsmall : m ≤ bound
  · obtain ⟨s, hs⟩ := sourceBound m (by omega) hsmall E c hE hnoE
    obtain ⟨i, hi⟩ := (finRotate m).surjective s
    exact (hcycle i).2 (by simpa only [hi] using hs i)
  · have hsize : m = bound + 1 := by omega
    subst m
    exact hexclude E c hE hnoE hcycle hmin

/-- Internal conditional bound-eight assembly. Only the displayed physical
order-eight exclusion remains external; all smaller obstructions are discharged
by the accepted order-seven theorem. This declaration alone is not a proof of
the unconditional order-eight source theorem. -/
theorem source_up_to_eight_of_physical_exclusion
    (h8 : ∀ (E : Digraph (Fin 8)) (c : ArcColoring (Fin 8)),
      IsTournament E → ¬HasRainbowDirectedTriangle E c →
      (∀ i : Fin 8, E i (finRotate 8 i) ∧
        ¬MonochromaticallyReaches E c (finRotate 8 i) i) →
      (∀ r : Fin 8, ∀ σ : Equiv.Perm (Fin 3),
        letI : NeZero 8 := r.neZero
        toLex (fun i ↦ c i (finRotate 8 i)) ≤
          toLex (fun i ↦ σ (c (i + r) (finRotate 8 (i + r))))) → False)
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (htournament : IsTournament D)
    (horder : Fintype.card V ≤ 8)
    (hnoRainbow : ¬HasRainbowDirectedTriangle D color) :
    ∃ s : V, IsMonochromaticSource D color s := by
  apply source_up_to_succ_of_physical_exclusion 7 _ h8 D color htournament horder hnoRainbow
  intro m hm hseven E c hE hnoE
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  exact OPG1808.order_seven E c hE (by simpa only [Fintype.card_fin] using hseven) hnoE

end OPG1808PhysicalAssembly
end

section

open OPG1808

namespace OPG1808PhysicalAssembly

universe u

/-- A rotation- and palette-minimal eight-letter word starts with one of the
three prefixes `000`, `001`, or `01`. The statement has no Boolean valuation. -/
theorem normalized_eight_prefix_cases
    (word : Fin 8 → Fin 3)
    (hmin : ∀ r : Fin 8, ∀ σ : Equiv.Perm (Fin 3),
      toLex word ≤ toLex (fun i ↦ σ (word (i + r)))) :
    (word 0 = 0 ∧ word 1 = 0 ∧ word 2 = 0 ∧ True) ∨
    (word 0 = 0 ∧ word 1 = 0 ∧ word 2 = 1 ∧ True) ∨
    (word 0 = 0 ∧ word 1 = 1 ∧ True) := by
  have hprefix : ∀ (r : Fin 8) (σ : Equiv.Perm (Fin 3)) (i : Fin 8),
      (∀ j : Fin 8, j < i → word j = σ (word (j + r))) →
        word i ≤ σ (word (i + r)) := by
    intro r σ i hp
    exact Pi.apply_le_of_toLex (hmin r σ) hp
  have hzero : word 0 = 0 := by
    have hle := hprefix 0 (Equiv.swap (word 0) 0) 0 (fun j hj ↦ by
      change j.val < (0 : Fin 8).val at hj
      simp only [Fin.val_zero] at hj
      omega)
    have hle0 : word 0 ≤ 0 := by
      simpa only [zero_add, Equiv.swap_apply_left] using hle
    apply le_antisymm hle0
    change 0 ≤ (word 0).val
    exact Nat.zero_le _
  have hnotTwo : ∀ (i : Fin 8), (∀ j : Fin 8, j < i → word j = 0) → word i ≠ 2 := by
    intro i hp htwo
    have hswap : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
    have hle := hprefix 0 (Equiv.swap (1 : Fin 3) 2) i (by
      intro j hj
      simp only [add_zero, hp j hj, hswap])
    rw [add_zero, htwo, Equiv.swap_apply_right] at hle
    exact (show ¬(2 : Fin 3) ≤ 1 by decide) hle
  by_cases hfirst : word 1 = 0
  · have hsecondNotTwo := hnotTwo 2 (by
      intro j hj
      have hcases : j = 0 ∨ j = 1 := by omega
      rcases hcases with rfl | rfl
      · exact hzero
      · exact hfirst)
    have hsecond : word 2 = 0 ∨ word 2 = 1 := by omega
    rcases hsecond with hsecond | hsecond
    · exact Or.inl ⟨hzero, hfirst, hsecond, True.intro⟩
    · exact Or.inr (Or.inl ⟨hzero, hfirst, hsecond, True.intro⟩)
  · have hfirstNotTwo := hnotTwo 1 (by
      intro j hj
      have : j = 0 := by omega
      subst j
      exact hzero)
    have hfirstOne : word 1 = 1 := by omega
    exact Or.inr (Or.inr ⟨hzero, hfirstOne, True.intro⟩)

/-- Internal assembly from the three physical prefix children. Each supplied
child has the exact physical signature used by its separate proof packet. -/
theorem source_up_to_eight_of_three_physical_prefixes
    (h000 : ∀ (D : Digraph (Fin 8)) (color : ArcColoring (Fin 8)),
      IsTournament D → ¬HasRainbowDirectedTriangle D color →
      (∀ i : Fin 8, D i (finRotate 8 i)) →
      (∀ r : Fin 8, ∀ σ : Equiv.Perm (Fin 3),
        toLex (fun i ↦ color i (finRotate 8 i)) ≤
          toLex (fun i ↦ σ (color (i + r) (finRotate 8 (i + r))))) →
      color 0 (finRotate 8 0) = 0 → color 1 (finRotate 8 1) = 0 →
      color 2 (finRotate 8 2) = 0 →
        ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i)
    (h001 : ∀ (D : Digraph (Fin 8)) (color : ArcColoring (Fin 8)),
      IsTournament D → ¬HasRainbowDirectedTriangle D color →
      (∀ i : Fin 8, D i (finRotate 8 i)) →
      (∀ r : Fin 8, ∀ σ : Equiv.Perm (Fin 3),
        toLex (fun i ↦ color i (finRotate 8 i)) ≤
          toLex (fun i ↦ σ (color (i + r) (finRotate 8 (i + r))))) →
      color 0 (finRotate 8 0) = 0 → color 1 (finRotate 8 1) = 0 →
      color 2 (finRotate 8 2) = 1 →
        ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i)
    (h01 : ∀ (D : Digraph (Fin 8)) (color : ArcColoring (Fin 8)),
      IsTournament D → ¬HasRainbowDirectedTriangle D color →
      (∀ i : Fin 8, D i (finRotate 8 i)) →
      (∀ r : Fin 8, ∀ σ : Equiv.Perm (Fin 3),
        toLex (fun i ↦ color i (finRotate 8 i)) ≤
          toLex (fun i ↦ σ (color (i + r) (finRotate 8 (i + r))))) →
      color 0 (finRotate 8 0) = 0 → color 1 (finRotate 8 1) = 1 →
        ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i)
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (htournament : IsTournament D)
    (horder : Fintype.card V ≤ 8)
    (hnoRainbow : ¬HasRainbowDirectedTriangle D color) :
    ∃ s : V, IsMonochromaticSource D color s := by
  apply source_up_to_eight_of_physical_exclusion _ D color htournament horder hnoRainbow
  intro E c hE hnoE hcycle hmin
  have hreturn : ∃ i : Fin 8, MonochromaticallyReaches E c (finRotate 8 i) i := by
    rcases normalized_eight_prefix_cases (fun i ↦ c i (finRotate 8 i)) hmin with
      ⟨h0, h1, h2, _⟩ | ⟨h0, h1, h2, _⟩ | ⟨h0, h1, _⟩
    · exact h000 E c hE hnoE (fun i ↦ (hcycle i).1) hmin h0 h1 h2
    · exact h001 E c hE hnoE (fun i ↦ (hcycle i).1) hmin h0 h1 h2
    · exact h01 E c hE hnoE (fun i ↦ (hcycle i).1) hmin h0 h1
  obtain ⟨i, hi⟩ := hreturn
  exact (hcycle i).2 hi

end OPG1808PhysicalAssembly
end

end CanonicalEightParent

open OPG1808
universe u

theorem solution
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (htournament : IsTournament D)
    (horder : Fintype.card V ≤ 8)
    (hnoRainbow : ¬HasRainbowDirectedTriangle D color) :
    ∃ s : V, IsMonochromaticSource D color s := by
  exact CanonicalEightParent.OPG1808PhysicalAssembly.source_up_to_eight_of_three_physical_prefixes
    OPG1808.order_eight_normalized_cycle_prefix000
    OPG1808.order_eight_normalized_cycle_prefix001
    OPG1808.order_eight_normalized_cycle_prefix01
    D color htournament horder hnoRainbow
