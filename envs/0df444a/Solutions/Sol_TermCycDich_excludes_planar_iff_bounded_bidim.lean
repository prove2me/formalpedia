-- Prove2me | solution 1 for TermCycDich.excludes_planar_iff_bounded_bidim
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:53:37.483798+00:00
-- url     : https://prove2.me/submissions/d7154529-3aa3-406c-b26b-9f354e76001c

import Mathlib
import Definitions.Def_TermCycDich_IsRedMinorClosed
import Definitions.Def_TermCycDich_IsAnnotatedPlanar
import Definitions.Def_TermCycDich_bidim
import Theorems.Thm_TermCycDich_all_red_grid
import Theorems.Thm_TermCycDich_isRedMinor_trans
import Theorems.Thm_PlanarQueue_Planar_planar_has_grid_minor_model

namespace AuxExcludesPlanar

open RobertsonSeymour1986.GM5 TermCycDich

def zAdj (p q : ℤ × ℤ) : Prop :=
  q = (p.1 + 1, p.2) ∨ p = (q.1 + 1, q.2) ∨ q = (p.1, p.2 + 1) ∨ p = (q.1, q.2 + 1)

def ptNorm (p : ℤ × ℤ) : ℕ := p.1.natAbs + p.2.natAbs

lemma emb_lt (p : ℤ × ℤ) (M : ℕ) (hp : ptNorm p ≤ M) :
    (p.1 + (M : ℤ)).toNat < 2 * M + 1 ∧ (p.2 + (M : ℤ)).toNat < 2 * M + 1 ∧
      0 ≤ p.1 + (M : ℤ) ∧ 0 ≤ p.2 + (M : ℤ) := by
  unfold ptNorm at hp
  omega

def embPt (M : ℕ) (p : ℤ × ℤ) (hp : ptNorm p ≤ M) :
    Fin (2 * M + 1) × Fin (2 * M + 1) :=
  (⟨(p.1 + (M : ℤ)).toNat, (emb_lt p M hp).1⟩, ⟨(p.2 + (M : ℤ)).toNat, (emb_lt p M hp).2.1⟩)

lemma embPt_inj {M : ℕ} (p q : ℤ × ℤ)
    (hp : ptNorm p ≤ M) (hq : ptNorm q ≤ M)
    (heq : embPt M p hp = embPt M q hq) : p = q := by
  rcases Prod.mk.inj heq with ⟨h1, h2⟩
  have e1 : (p.1 + (M : ℤ)).toNat = (q.1 + (M : ℤ)).toNat := Fin.mk.inj h1
  have e2 : (p.2 + (M : ℤ)).toNat = (q.2 + (M : ℤ)).toNat := Fin.mk.inj h2
  have := (emb_lt p M hp).2.2
  have := (emb_lt q M hq).2.2
  exact Prod.ext (by omega) (by omega)

lemma embPt_adj {M : ℕ} (p q : ℤ × ℤ)
    (hp : ptNorm p ≤ M) (hq : ptNorm q ≤ M)
    (hadj : zAdj p q) :
    (grid (2 * M + 1)).Adj (embPt M p hp) (embPt M q hq) := by
  have hp0 := (emb_lt p M hp).2.2
  have hq0 := (emb_lt q M hq).2.2
  have c1p : (((embPt M p hp).1 : ℕ) : ℤ) = p.1 + (M : ℤ) := by
    dsimp [embPt]; omega
  have c2p : (((embPt M p hp).2 : ℕ) : ℤ) = p.2 + (M : ℤ) := by
    dsimp [embPt]; omega
  have c1q : (((embPt M q hq).1 : ℕ) : ℤ) = q.1 + (M : ℤ) := by
    dsimp [embPt]; omega
  have c2q : (((embPt M q hq).2 : ℕ) : ℤ) = q.2 + (M : ℤ) := by
    dsimp [embPt]; omega
  change |(((embPt M p hp).1 : ℕ) : ℤ) - (((embPt M q hq).1 : ℕ) : ℤ)| +
    |(((embPt M p hp).2 : ℕ) : ℤ) - (((embPt M q hq).2 : ℕ) : ℤ)| = 1
  rw [c1p, c2p, c1q, c2q]
  rcases hadj with rfl | rfl | rfl | rfl
  · have s1 : p.1 + (M : ℤ) - (p.1 + 1 + (M : ℤ)) = -1 := by ring
    have s2 : p.2 + (M : ℤ) - (p.2 + (M : ℤ)) = 0 := by ring
    rw [s1, s2]; norm_num
  · have s1 : q.1 + 1 + (M : ℤ) - (q.1 + (M : ℤ)) = 1 := by ring
    have s2 : q.2 + (M : ℤ) - (q.2 + (M : ℤ)) = 0 := by ring
    rw [s1, s2]; norm_num
  · have s1 : p.1 + (M : ℤ) - (p.1 + (M : ℤ)) = 0 := by ring
    have s2 : p.2 + (M : ℤ) - (p.2 + 1 + (M : ℤ)) = -1 := by ring
    rw [s1, s2]; norm_num
  · have s1 : q.1 + (M : ℤ) - (q.1 + (M : ℤ)) = 0 := by ring
    have s2 : q.2 + 1 + (M : ℤ) - (q.2 + (M : ℤ)) = 1 := by ring
    rw [s1, s2]; norm_num

lemma planar_isRedMinor_grid (y : AnnotatedGraph) (hy : IsAnnotatedPlanar y) :
    ∃ cStar : ℕ, IsRedMinor y.G (↑y.R : Set (Fin y.n)) (grid cStar) Set.univ := by
  obtain ⟨B, hB_disj, hB_conn, hB_ne, hB_adj⟩ :=
    PlanarQueue.Planar.planar_has_grid_minor_model y.G hy
  let U : Finset (ℤ × ℤ) := Finset.univ.biUnion B
  let M : ℕ := U.sup ptNorm
  have hBound : ∀ {v : Fin y.n} {p : ℤ × ℤ}, p ∈ B v → ptNorm p ≤ M := by
    intro v p hp
    exact Finset.le_sup (f := ptNorm)
      (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, hp⟩)
  let β : Fin y.n → Set (Fin (2 * M + 1) × Fin (2 * M + 1)) :=
    fun v => { z | ∃ (p : ℤ × ℤ) (hp : p ∈ B v), embPt M p (hBound hp) = z }
  refine ⟨2 * M + 1, β, ?_, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨p₀, hp₀⟩ := hB_ne v
    have hne : (β v).Nonempty := ⟨embPt M p₀ (hBound hp₀), p₀, hp₀, rfl⟩
    have : Nonempty (β v) := ⟨⟨embPt M p₀ (hBound hp₀), p₀, hp₀, rfl⟩⟩
    refine ⟨hne, SimpleGraph.Connected.mk ?_⟩
    rintro ⟨z₁, p₁, hp₁, rfl⟩ ⟨z₂, p₂, hp₂, rfl⟩
    have hrt := hB_conn v p₁ hp₁ p₂ hp₂
    induction hrt with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c _ hstep ih =>
      rcases hstep with ⟨hbB, hcB, hbc⟩
      have hadj_ind : ((grid (2 * M + 1)).induce (β v)).Adj
          ⟨embPt M b (hBound hbB), b, hbB, rfl⟩
          ⟨embPt M c (hBound hcB), c, hcB, rfl⟩ :=
        embPt_adj b c (hBound hbB) (hBound hcB) hbc
      exact (ih hbB).trans (SimpleGraph.Adj.reachable hadj_ind)
  · intro v w hvw
    rw [Set.disjoint_left]
    rintro z ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
    have hpq : p = q := embPt_inj p q (hBound hp) (hBound hq) heq.symm
    subst hpq
    exact Finset.disjoint_left.mp (hB_disj v w hvw) hp hq
  · intro v w hadj
    obtain ⟨p, hp, q, hq, hpq⟩ := hB_adj v w hadj
    exact ⟨embPt M p (hBound hp), ⟨p, hp, rfl⟩,
           embPt M q (hBound hq), ⟨q, hq, rfl⟩,
           embPt_adj p q (hBound hp) (hBound hq) hpq⟩
  · intro v _
    obtain ⟨p₀, hp₀⟩ := hB_ne v
    exact ⟨embPt M p₀ (hBound hp₀), ⟨p₀, hp₀, rfl⟩, trivial⟩

lemma grid_isRedMinor_mono {a b : ℕ} (hab : a ≤ b) :
    IsRedMinor (grid a) Set.univ (grid b) Set.univ := by
  let f : Fin a × Fin a → Fin b × Fin b := fun w => (Fin.castLE hab w.1, Fin.castLE hab w.2)
  have hf_inj : Function.Injective f := by
    intro u v huv
    rcases Prod.mk.inj huv with ⟨h1, h2⟩
    exact Prod.ext (Fin.ext (by simpa [f] using congrArg Fin.val h1))
                   (Fin.ext (by simpa [f] using congrArg Fin.val h2))
  refine ⟨fun w => {f w}, ?_, ?_, ?_, ?_⟩
  · intro w
    have : Nonempty ({f w} : Set (Fin b × Fin b)) := ⟨⟨f w, rfl⟩⟩
    refine ⟨⟨f w, rfl⟩, SimpleGraph.Connected.mk ?_⟩
    intro ⟨x, hx⟩ ⟨y, hy⟩
    subst hx; subst hy
    exact SimpleGraph.Reachable.refl _
  · intro u v huv
    exact Set.disjoint_singleton.mpr (fun heq => huv (hf_inj heq))
  · intro u v hadj
    exact ⟨f u, rfl, f v, rfl, hadj⟩
  · intro w _
    exact ⟨f w, rfl, trivial⟩

lemma hasRedGrid_zero {V : Type} (G : SimpleGraph V) (R : Set V) : HasRedGrid G R 0 := by
  refine ⟨fun w => w.1.elim0, fun w => w.1.elim0, fun w => w.1.elim0,
          fun w => w.1.elim0, fun w => w.1.elim0⟩

def gridAnnotated (c : ℕ) : AnnotatedGraph where
  n := (c + 1) * (c + 1)
  G := SimpleGraph.comap finProdFinEquiv.symm (grid (c + 1))
  R := Finset.univ

lemma gridAnnotated_planar (c : ℕ) : IsAnnotatedPlanar (gridAnnotated c) := by
  obtain ⟨D⟩ := (TermCycDich.all_red_grid c).1
  let e := (finProdFinEquiv (m := c + 1) (n := c + 1)).symm
  refine ⟨{
    vertex := fun i => D.vertex (e i)
    vertex_injective := D.vertex_injective.comp e.injective
    arc := fun h => D.arc h
    arc_injective := fun h => D.arc_injective h
    arc_reverse := fun h => D.arc_reverse h
    arc_avoids_vertices := fun h t x htx =>
      (D.arc_avoids_vertices h t (e x) htx).imp (fun h1 => e.injective h1) (fun h2 => e.injective h2)
    arcs_meet_only_at_endpoints := fun h k s t hst => by
      rcases D.arcs_meet_only_at_endpoints h k s t hst with ⟨h1, h2⟩ | ⟨h1, h2⟩ | hends
      · exact Or.inl ⟨e.injective h1, e.injective h2⟩
      · exact Or.inr (Or.inl ⟨e.injective h1, e.injective h2⟩)
      · exact Or.inr (Or.inr hends)
  }⟩

lemma gridAnnotated_bidim_ge (c : ℕ) :
    c + 1 ≤ bidim (gridAnnotated c).G (↑(gridAnnotated c).R : Set (Fin (gridAnnotated c).n)) := by
  classical
  unfold bidim
  let e := finProdFinEquiv (m := c + 1) (n := c + 1)
  have hle : c + 1 ≤ Fintype.card (Fin (gridAnnotated c).n) := by
    change c + 1 ≤ Fintype.card (Fin ((c + 1) * (c + 1)))
    rw [Fintype.card_fin]
    nlinarith
  have hrg : HasRedGrid (gridAnnotated c).G
      (↑(gridAnnotated c).R : Set (Fin (gridAnnotated c).n)) (c + 1) := by
    refine ⟨fun w => {e w}, ?_, ?_, ?_, ?_⟩
    · intro w
      have : Nonempty ({e w} : Set (Fin (gridAnnotated c).n)) := ⟨⟨e w, rfl⟩⟩
      refine ⟨⟨e w, rfl⟩, SimpleGraph.Connected.mk ?_⟩
      intro ⟨x, hx⟩ ⟨y, hy⟩
      subst hx; subst hy
      exact SimpleGraph.Reachable.refl _
    · intro u v huv
      exact Set.disjoint_singleton.mpr (fun heq => huv (e.injective heq))
    · intro u v hadj
      refine ⟨e u, rfl, e v, rfl, ?_⟩
      change (grid (c + 1)).Adj (e.symm (e u)) (e.symm (e v))
      simpa using hadj
    · intro w _
      exact ⟨e w, rfl, Finset.mem_coe.mpr (Finset.mem_univ _)⟩
  convert Nat.le_findGreatest hle hrg

end AuxExcludesPlanar

theorem solution (C : Set TermCycDich.AnnotatedGraph) (hC : TermCycDich.IsRedMinorClosed C) :
    (¬ ∀ x, TermCycDich.IsAnnotatedPlanar x → x ∈ C) ↔
      ∃ c : ℕ, ∀ x ∈ C, TermCycDich.bidim x.G (↑x.R : Set (Fin x.n)) ≤ c := by
  classical
  constructor
  · intro hnot
    push Not at hnot
    rcases hnot with ⟨y, hy_plan, hy_not_mem⟩
    obtain ⟨cStar, hy_minor⟩ := AuxExcludesPlanar.planar_isRedMinor_grid y hy_plan
    refine ⟨cStar, fun x hx => ?_⟩
    by_contra hgt
    have hle : cStar ≤ TermCycDich.bidim x.G (↑x.R : Set (Fin x.n)) := by omega
    have hspec : TermCycDich.HasRedGrid x.G (↑x.R : Set (Fin x.n))
        (TermCycDich.bidim x.G (↑x.R : Set (Fin x.n))) := by
      unfold TermCycDich.bidim
      convert Nat.findGreatest_spec (P := fun k =>
        TermCycDich.HasRedGrid x.G (↑x.R : Set (Fin x.n)) k) (Nat.zero_le _)
        (AuxExcludesPlanar.hasRedGrid_zero x.G (↑x.R : Set (Fin x.n)))
    have hgrid_sub := AuxExcludesPlanar.grid_isRedMinor_mono hle
    have hy_gridk := TermCycDich.isRedMinor_trans hy_minor hgrid_sub
    have hy_x := TermCycDich.isRedMinor_trans hy_gridk hspec
    exact hy_not_mem (hC x hx y hy_x)
  · rintro ⟨c, hc⟩
    intro hall
    have hmem := hall (AuxExcludesPlanar.gridAnnotated c) (AuxExcludesPlanar.gridAnnotated_planar c)
    have hge := AuxExcludesPlanar.gridAnnotated_bidim_ge c
    have hle := hc (AuxExcludesPlanar.gridAnnotated c) hmem
    omega
