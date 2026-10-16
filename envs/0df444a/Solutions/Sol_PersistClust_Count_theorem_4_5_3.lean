-- Prove2me | solution 3 for PersistClust.Count.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T06:23:51.313459+00:00
-- url     : https://prove2.me/submissions/030c9ae2-a59e-4883-b11a-76d384c60003

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank
import Definitions.Def_PersistClust_Count_MatchingGate
import Definitions.Def_PersistClust_Count_MatchingCensus
import Theorems.Thm_PersistClust_Count_theorem_4_5_interleaving_corrected
import Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected_mult_agree_qtame
import Theorems.Thm_PersistClust_Count_theorem_4_5_gate_matching

open Bundle
open scoped ContDiff Manifold

namespace PersistClust.Count

/-!
# `theorem_4_5` (RR-6968, p. 21) — reduction to the abstract matching gate

The multi-bijection γ between `D₀f = diagram0 f` and `D₀𝓡^f_δ(L) = ripsDiagram …` with the four
`SatisfiesIIV` guarantees at threshold `α` and radius `c·δ` is reduced here, wholesale, to the
platform child `theorem_4_5_gate_matching`: the abstract gate turning a strong ε-interleaving
above α of two tame `FiltrationLaw` modules into the multi-bijection.

The concrete instantiation is
* X-side: `stageX := superlevel f`, `JX := fun t => JoinedIn (superlevel f t)`;
* Y-side: `stageY := fun t => {i : ↥L | t ≤ f (i : X)}`,
  `JY := ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ`;
* `(α, ε) := (α, c * δ)`.

The gate's conclusion `∃ γ : Copies (mult (rankFn stageX JX)) ≃ Copies (mult (rankFn stageY
JY)), SatisfiesIIV γ α ε` is definitionally the target statement, because
`diagram0 f = mult (superRank f)` with `superRank f = rankFn (superlevel f) (JoinedIn ·)` and
`ripsDiagram Dm g δ = mult (ripsRank Dm g δ)` with
`ripsRank Dm g δ = rankFn (fun t => {i | t ≤ g i}) (ripsJoined Dm g δ)`.

The four gate hypotheses are discharged as follows (all pieces below are copied from the
banked-green `Sol_PersistClust_Count_theorem_4_5.lean`, with its private copies of the
component-class interface `comps`/`compRep`/`structMap` and of `StrongInterleavingAbove`/`
IsTameModule` renamed to the platform constants of `Def_PersistClust_Count_MatchingCensus`):
* `hLawX`/`hLawY` — `t45gamma_super_filtrationLaw` / `t45gamma_rips_filtrationLaw`;
* `hTameX` — `t45gamma_super_isTameModule` (from `IsTame0 f`);
* `hTameY` — `t45gamma_rips_isTameModule` (the vertex type `↥L` is finite);
* `hIL` — `t45gamma_instance` (the concrete interleaving maps φ/ψ of component classes with
  the four commuting squares, built from the geodesic-lift/Rips-chain machinery), with the
  degenerate case `𝔽^α = ∅` (no point of grade ≥ α) handled by `t45w_degenerate_IL`: every
  stage at level ≥ α is then empty, so the interleaving exists vacuously.

This file is fully proved; the three imported stubs carry the platform's expected open
proofs.
-/

/-- The Rips module is tame: above the largest sample value the active vertex set is empty. -/
theorem t45gamma_rips_module_tame {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    ∃ s₀ : ℝ, ∀ s ≥ s₀, {i | s ≤ g i} = ∅ := by
  have hrng : (Set.range g).Finite := Set.finite_range g
  obtain ⟨M, hM⟩ := bddAbove_def.mp (Set.Finite.bddAbove hrng)
  refine ⟨M + 1, fun s hs => Set.eq_empty_iff_forall_notMem.mpr fun i hi => ?_⟩
  rw [Set.mem_setOf_eq] at hi
  have hgM := hM (g i) (Set.mem_range_self i)
  linarith

/-- An `𝔽^{t'}`-path between two arbitrary points `x, y` (with `t' ≤ f x`, `t' ≤ f y`) samples
down to a Rips chain joining the chosen samples `vsamp x`, `vsamp y` at level `t' − cδ/4`. -/
theorem t45gamma_chain_rips_gen {X : Type*} [MetricSpace X] {ι : Type*}
    (coe : ι → X) (Dm : ι → ι → ℝ) (hDm : ∀ a b, Dm a b = dist (coe a) (coe b))
    (g : ι → ℝ) (f : X → ℝ) (hgf : ∀ i, g i = f (coe i))
    (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (δ : ℝ) (hδ : 0 < δ) (t' : ℝ)
    (vsamp : X → ι) (hvsamp : ∀ z : X, t' ≤ f z → dist z (coe (vsamp z)) ≤ δ / 4)
    (x y : X) (hjoined : JoinedIn (superlevel f t') x y) :
    ripsJoined Dm g δ (t' - c * (δ / 4)) (vsamp x) (vsamp y) := by
  classical
  obtain ⟨p, hp⟩ := hjoined
  have hp' : ∀ u : unitInterval, t' ≤ f (p u) := fun u => hp u
  have hx : t' ≤ f x := by have := hp' 0; rwa [p.source] at this
  have hy : t' ≤ f y := by have := hp' 1; rwa [p.target] at this
  have huc : UniformContinuous ⇑p := CompactSpace.uniformContinuous_of_continuous p.continuous
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨d, hd0, hud⟩ := huc (δ / 4) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd0
  set N : ℕ := n + 1 with hNdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  -- partition points
  set uu : ℕ → unitInterval := fun k =>
    ⟨((min k N : ℕ) : ℝ) / (N : ℝ), by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hNpos]
      exact_mod_cast min_le_right k N⟩ with huudef
  have uu_eq : ∀ k : ℕ, k ≤ N → ((uu k : unitInterval) : ℝ) = (k : ℝ) / (N : ℝ) := by
    intro k hk
    simp only [uu, Subtype.coe_mk]
    rw [min_eq_left hk]
  set w : ℕ → ι := fun k => vsamp (p (uu k)) with hwdef
  -- grades of the chain
  have hwgrade : ∀ k : ℕ, t' - c * (δ / 4) ≤ g (w k) := by
    intro k
    have hz : t' ≤ f (p (uu k)) := hp' (uu k)
    have hdist : dist (p (uu k)) (coe (w k)) ≤ δ / 4 := hvsamp _ hz
    have hb := (abs_le.mp (hLip (coe (w k)) (p (uu k)))).1
    have hmul : c * dist (coe (w k)) (p (uu k)) ≤ c * (δ / 4) :=
      mul_le_mul_of_nonneg_left (show dist (coe (w k)) (p (uu k)) ≤ δ / 4 by
        rw [dist_comm]; exact hdist) hc
    rw [hgf (w k)]
    linarith
  have hxgrade : t' - c * (δ / 4) ≤ g (vsamp x) := by
    have hcd : dist (coe (vsamp x)) x ≤ δ / 4 := by rw [dist_comm]; exact hvsamp x hx
    have hb := (abs_le.mp (hLip (coe (vsamp x)) x)).1
    have hmul : c * dist (coe (vsamp x)) x ≤ c * (δ / 4) :=
      mul_le_mul_of_nonneg_left hcd hc
    rw [hgf (vsamp x)]
    linarith
  have hygrade : t' - c * (δ / 4) ≤ g (vsamp y) := by
    have hcd : dist (coe (vsamp y)) y ≤ δ / 4 := by rw [dist_comm]; exact hvsamp y hy
    have hb := (abs_le.mp (hLip (coe (vsamp y)) y)).1
    have hmul : c * dist (coe (vsamp y)) y ≤ c * (δ / 4) :=
      mul_le_mul_of_nonneg_left hcd hc
    rw [hgf (vsamp y)]
    linarith
  -- consecutive partition distances
  have hdist_uu : ∀ k : ℕ, k + 1 ≤ N → dist (uu k) (uu (k + 1)) = 1 / (N : ℝ) := by
    intro k hk1
    have hk : k ≤ N := le_trans (Nat.le_succ k) hk1
    rw [Subtype.dist_eq, Real.dist_eq, uu_eq k hk, uu_eq (k + 1) hk1]
    rw [show (k : ℝ) / (N : ℝ) - ((k + 1 : ℕ) : ℝ) / (N : ℝ) = -(1 / (N : ℝ)) by
      have hc1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hc1]; ring]
    rw [abs_neg, abs_of_nonneg (by positivity)]
  have hstepdist : ∀ k : ℕ, k + 1 ≤ N → dist (coe (w k)) (coe (w (k + 1))) ≤ δ := by
    intro k hk1
    have hk : k ≤ N := le_trans (Nat.le_succ k) hk1
    have hlt : dist (uu k) (uu (k + 1)) < d := by
      rw [hdist_uu k hk1, hNdef]; push_cast; exact hn
    have hpdist : dist (p (uu k)) (p (uu (k + 1))) < δ / 4 := hud hlt
    have h1 : dist (coe (w k)) (p (uu k)) ≤ δ / 4 := by
      rw [dist_comm]; exact hvsamp _ (hp' (uu k))
    have h2 : dist (p (uu (k + 1))) (coe (w (k + 1))) ≤ δ / 4 :=
      hvsamp _ (hp' (uu (k + 1)))
    have := dist_triangle4 (coe (w k)) (p (uu k)) (p (uu (k + 1))) (coe (w (k + 1)))
    linarith [le_of_lt hpdist]
  -- the chain `w 0 → w 1 → … → w N` of consecutive Rips edges
  have hpx0 : p (uu 0) = x := by
    have h0 : uu 0 = 0 := Subtype.ext (by rw [uu_eq 0 (Nat.zero_le N)]; simp)
    rw [h0, p.source]
  have hpyN : p (uu N) = y := by
    have hN1 : uu N = 1 := Subtype.ext (by rw [uu_eq N (le_refl N)]; exact div_self (ne_of_gt hNpos))
    rw [hN1, p.target]
  have hw0 : w 0 = vsamp x := by rw [hwdef]; exact congrArg vsamp hpx0
  have hwN : w N = vsamp y := by rw [hwdef]; exact congrArg vsamp hpyN
  have hchain : ∀ k : ℕ, k ≤ N → Relation.ReflTransGen
      (fun a b => t' - c * (δ / 4) ≤ g a ∧ t' - c * (δ / 4) ≤ g b ∧
        (ripsGraph Dm δ).Adj a b) (w 0) (w k) := by
    intro k
    induction k with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk1
      have hk : k ≤ N := Nat.le_of_succ_le hk1
      by_cases heq : w k = w (k + 1)
      · rw [← heq]; exact ih hk
      · refine (ih hk).tail ⟨hwgrade k, hwgrade (k + 1), ?_⟩
        refine (SimpleGraph.fromRel_adj (fun i j => Dm i j ≤ δ) (w k) (w (k + 1))).mpr
          ⟨heq, Or.inl ?_⟩
        rw [hDm]; exact hstepdist k hk1
  have hfinal := hchain N (le_refl N)
  rw [hw0] at hfinal
  rw [hwN] at hfinal
  exact ⟨hxgrade, hfinal⟩

/-! ## Filtration laws for the two modules (genuine persistence filtrations)

These are the structural laws required by `theorem_4_5_lemma_4_6_corrected_mult_agree_qtame`
(`FiltrationLaw` hypothesis) and by the rectangle-count / Extended-Stability machinery. They
record that the superlevel-set filtration and the upper-star Rips filtration are genuine
filtrations of path-components (monotone stages, equivalence relations living on the stages,
compatible with the inclusions `stage t ⊆ stage s` for `s ≤ t`). -/


/-- Reachability along a symmetric relation is symmetric. -/
theorem t45gamma_rtgen_symm {ι : Type*} {R : ι → ι → Prop}
    (hsym : ∀ a b, R a b → R b a) {i j : ι} (h : Relation.ReflTransGen R i j) :
    Relation.ReflTransGen R j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.head (hsym _ _ hbc)

/-- The Rips step relation on level `t` is symmetric (the Rips graph is undirected). -/
theorem t45gamma_RipsRel_symm {ι : Type*} (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ t : ℝ) :
    ∀ a b, (fun a b => t ≤ g a ∧ t ≤ g b ∧ (ripsGraph Dm δ).Adj a b) a b →
      (fun a b => t ≤ g a ∧ t ≤ g b ∧ (ripsGraph Dm δ).Adj a b) b a :=
  fun _ _ ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩

/-- The superlevel-set filtration is a genuine `FiltrationLaw`. -/
theorem t45gamma_super_filtrationLaw {X : Type*} [TopologicalSpace X] (f : X → ℝ) :
    FiltrationLaw (superlevel f) (fun t => JoinedIn (superlevel f t)) where
  antitone := fun s t hst x hx => hst.trans hx
  mem := fun _ _ _ h => JoinedIn.mem h
  refl := fun _ _ hx => JoinedIn.refl hx
  symm := fun _ _ _ h => JoinedIn.symm h
  trans := fun _ _ _ _ h1 h2 => JoinedIn.trans h1 h2
  compat := fun s t hst _ _ h => JoinedIn.mono h (fun z hz => hst.trans hz)

/-- The upper-star Rips filtration is a genuine `FiltrationLaw`. -/
theorem t45gamma_rips_filtrationLaw {ι : Type*} (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ : ℝ) :
    FiltrationLaw (fun t => {i | t ≤ g i}) (ripsJoined Dm g δ) where
  antitone := fun s t hst i hi => hst.trans hi
  mem := by
    intro t i j h
    obtain ⟨hgi, hrt⟩ := h
    refine ⟨hgi, ?_⟩
    induction hrt with
    | refl => exact hgi
    | tail _ hbc _ => exact hbc.2.1
  refl := fun t i hi => ⟨hi, Relation.ReflTransGen.refl⟩
  symm := by
    intro t i j h
    obtain ⟨hgi, hrt⟩ := h
    refine ⟨?_, ?_⟩
    · induction hrt with
      | refl => exact hgi
      | tail _ hbc _ => exact hbc.2.1
    · exact t45gamma_rtgen_symm (t45gamma_RipsRel_symm Dm g δ t) hrt
  trans := by
    intro t i j k hij hjk
    obtain ⟨hgi, hrt1⟩ := hij
    obtain ⟨-, hrt2⟩ := hjk
    exact ⟨hgi, Relation.ReflTransGen.trans hrt1 hrt2⟩
  compat := by
    intro s t hst i j h
    obtain ⟨hgi, hrt⟩ := h
    refine ⟨hst.trans hgi, ?_⟩
    induction hrt with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih =>
      exact ih.tail ⟨hst.trans hab.1, hst.trans hab.2.1, hab.2.2⟩


/-- Distance is preserved by an isometric embedding. -/
theorem t45gamma_isom_dist_eq {X : Type*} [MetricSpace X] {d : ℝ}
    (γ : Set.Icc (0 : ℝ) d → X) (hiso : Isometry γ) (x y : Set.Icc (0 : ℝ) d) :
    dist (γ x) (γ y) = dist x y := by
  have h := hiso x y
  rw [edist_dist, edist_dist] at h
  exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg dist_nonneg).mp h

/-- Geodesic lift: a `c`-Lipschitz function's superlevel sets are path-connected along
distance-`d` geodesics, provided `d < convexityRadius X`. -/
theorem t45gamma_lift {X : Type*} [MetricSpace X] (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (a b : X) (t : ℝ)
    (hd : ENNReal.ofReal (dist a b) < convexityRadius X)
    (ha : t + c * dist a b ≤ f a) (hb : t + c * dist a b ≤ f b) :
    JoinedIn (superlevel f t) a b := by
  classical
  have h1 : ENNReal.ofReal (dist a b) < convexityRadiusAt a :=
    lt_of_lt_of_le hd (iInf_le (fun x : X => convexityRadiusAt x) a)
  obtain ⟨r, hr0, hrsc, hrd⟩ : ∃ r, 0 ≤ r ∧ IsStronglyConvexBall a r ∧ dist a b < r := by
    by_contra hx
    push_neg at hx
    apply absurd h1
    rw [not_lt]
    refine iSup_le_iff.mpr (fun s => ?_)
    refine iSup_le_iff.mpr (fun hs0 => ?_)
    refine iSup_le_iff.mpr (fun hsc => ?_)
    exact ENNReal.ofReal_le_ofReal (hx s hs0 hsc)
  have ha_mem : a ∈ Metric.closedBall a r :=
    Metric.mem_closedBall.mpr (by rw [dist_self]; exact hr0)
  have hb_mem : b ∈ Metric.closedBall a r :=
    Metric.mem_closedBall.mpr (by rw [dist_comm]; exact le_of_lt hrd)
  obtain ⟨γ, hγ, -⟩ := (hrsc a ha_mem b hb_mem).1
  rcases hγ with ⟨hiso, hγ0, hγd⟩
  have hd0 : (0 : ℝ) ≤ dist a b := dist_nonneg
  have hmul : Continuous (fun u : unitInterval => ((u : ℝ) * dist a b : ℝ)) :=
    Continuous.mul_const continuous_subtype_val (dist a b)
  have hmem : ∀ u : unitInterval, ((u : ℝ) * dist a b) ∈ Set.Icc (0 : ℝ) (dist a b) := by
    intro u
    refine ⟨by nlinarith [u.2.1, hd0], ?_⟩
    nlinarith [u.2.1, u.2.2, hd0]
  have hgcont : Continuous (fun u : unitInterval =>
      (⟨(u : ℝ) * dist a b, hmem u⟩ : Set.Icc (0 : ℝ) (dist a b))) :=
    Continuous.subtype_mk hmul hmem
  have hcont : Continuous (fun u : unitInterval => γ (⟨(u : ℝ) * dist a b, hmem u⟩)) :=
    hiso.continuous.comp hgcont
  have hsrc : (fun u : unitInterval => γ (⟨(u : ℝ) * dist a b, hmem u⟩)) 0 = a := by
    have e0 : (⟨((0 : unitInterval) : ℝ) * dist a b, hmem 0⟩ : Set.Icc (0 : ℝ) (dist a b))
        = ⟨(0 : ℝ), le_refl 0, dist_nonneg⟩ := Subtype.ext (by simp)
    show γ (⟨((0 : unitInterval) : ℝ) * dist a b, hmem 0⟩) = a
    rw [e0, hγ0]
  have htgt : (fun u : unitInterval => γ (⟨(u : ℝ) * dist a b, hmem u⟩)) 1 = b := by
    have e1 : (⟨((1 : unitInterval) : ℝ) * dist a b, hmem 1⟩ : Set.Icc (0 : ℝ) (dist a b))
        = ⟨dist a b, dist_nonneg, le_refl (dist a b)⟩ := Subtype.ext (by simp)
    show γ (⟨((1 : unitInterval) : ℝ) * dist a b, hmem 1⟩) = b
    rw [e1, hγd]
  refine ⟨⟨⟨fun u : unitInterval => γ (⟨(u : ℝ) * dist a b, hmem u⟩), hcont⟩, hsrc, htgt⟩, fun u => ?_⟩
  show t ≤ f (γ (⟨(u : ℝ) * dist a b, hmem u⟩))
  have hu : (0 : ℝ) ≤ (u : ℝ) := u.2.1
  have hdist : dist (γ (⟨(u : ℝ) * dist a b, hmem u⟩ : Set.Icc (0 : ℝ) (dist a b))) a
      = (u : ℝ) * dist a b := by
    have h0 : dist (γ (⟨(u : ℝ) * dist a b, hmem u⟩ : Set.Icc (0 : ℝ) (dist a b)))
        (γ (⟨(0 : ℝ), le_refl 0, dist_nonneg⟩ : Set.Icc (0 : ℝ) (dist a b)))
        = dist (⟨(u : ℝ) * dist a b, hmem u⟩ : Set.Icc (0 : ℝ) (dist a b))
          (⟨(0 : ℝ), le_refl 0, dist_nonneg⟩ : Set.Icc (0 : ℝ) (dist a b)) :=
      t45gamma_isom_dist_eq γ hiso _ _
    rw [hγ0] at h0
    rw [h0, Subtype.dist_eq, Real.dist_eq]
    simp only [Subtype.coe_mk, sub_zero]
    rw [abs_of_nonneg (mul_nonneg hu hd0)]
  have hb1 : |f (γ (⟨(u : ℝ) * dist a b, hmem u⟩)) - f a| ≤ c * dist (γ (⟨(u : ℝ) * dist a b, hmem u⟩)) a :=
    hLip _ _
  rw [hdist] at hb1
  have hud : (u : ℝ) * dist a b ≤ dist a b := by
    nlinarith [u.2.1, u.2.2, hd0]
  have hcle : c * ((u : ℝ) * dist a b) ≤ c * dist a b :=
    mul_le_mul_of_nonneg_left hud hc
  have hlow := (abs_le.mp hb1).1
  linarith


/-- A single Rips-adjacent pair with grades `≥ t + cδ` lifts to an `𝔽^t`-path. -/
theorem t45gamma_step_super {X : Type*} [MetricSpace X] {ι : Type*} (coe : ι → X) (Dm : ι → ι → ℝ)
    (hDm : ∀ a b, Dm a b = dist (coe a) (coe b))
    (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (δ t : ℝ) (hconvρ : ENNReal.ofReal δ < convexityRadius X) (a b : ι)
    (h1 : t + c * δ ≤ f (coe a)) (h2 : t + c * δ ≤ f (coe b))
    (hadj : (ripsGraph Dm δ).Adj a b) :
    JoinedIn (superlevel f t) (coe a) (coe b) := by
  classical
  have hds : Dm a b ≤ δ := by
    have hadj' := (SimpleGraph.fromRel_adj (fun i j => Dm i j ≤ δ) a b).mp hadj
    rcases hadj'.2 with h | h
    · exact h
    · rw [hDm b a, dist_comm, ← hDm a b] at h
      exact h
  have hdist : dist (coe a) (coe b) ≤ δ := by rw [← hDm]; exact hds
  refine t45gamma_lift f c hc hLip (coe a) (coe b) t ?_ ?_ ?_
  · exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hdist) hconvρ
  · linarith [mul_le_mul_of_nonneg_left hdist hc]
  · linarith [mul_le_mul_of_nonneg_left hdist hc]

/-- A Rips path in `L^{t+cδ}` from `i` to `j`, starting at grade `≥ t + cδ`, lifts to an
`𝔽^t`-path joining the two sample points. -/
theorem t45gamma_chain_super {X : Type*} [MetricSpace X] {ι : Type*} (coe : ι → X) (Dm : ι → ι → ℝ)
    (hDm : ∀ a b, Dm a b = dist (coe a) (coe b))
    (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (δ t : ℝ) (hδ : 0 < δ) (hconvρ : ENNReal.ofReal δ < convexityRadius X) (i j : ι)
    (h : ripsJoined Dm (fun a => f (coe a)) δ (t + c * δ) i j) :
    JoinedIn (superlevel f t) (coe i) (coe j) := by
  classical
  obtain ⟨hi, hrt⟩ := h
  induction hrt with
  | refl => exact JoinedIn.refl (le_trans (by linarith [mul_nonneg hc hδ.le]) hi)
  | tail hab hbc ih =>
    exact ih.trans
      (t45gamma_step_super coe Dm hDm f c hc hLip δ t hconvρ _ _ hbc.1 hbc.2.1 hbc.2.2)


/-- A point and any `δ/4`-close `𝔽^β`-sample share the `𝔽^{β−cδ}`-path-component: the
interleaving square `ψ ∘ structure = structure ∘ ψ` at the component level. -/
theorem t45gamma_sample_joined {X : Type*} [MetricSpace X] {ι : Type*}
    (coe : ι → X) (f : X → ℝ) (c δ β : ℝ) (hc : 0 ≤ c) (hδ : 0 < δ)
    (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    {v : ι} {z : X} (hdist : dist z (coe v) ≤ δ / 4) (hz : β ≤ f z) :
    JoinedIn (superlevel f (β - c * δ)) z (coe v) := by
  have hcd4 : c * (δ / 4) = c * δ / 4 := by ring
  have he0 : 0 ≤ c * δ := mul_nonneg hc (le_of_lt hδ)
  have hcm : c * dist z (coe v) ≤ c * (δ / 4) := mul_le_mul_of_nonneg_left hdist hc
  rw [hcd4] at hcm
  refine t45gamma_lift f c hc hLip z (coe v) (β - c * δ)
    (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal
      (le_trans hdist (show δ / 4 ≤ δ by linarith))) hδρ) ?_ ?_
  · -- the lift grade at the point `z`
    linarith
  · -- the lift grade at the sample `v`
    have hb2 := (abs_le.mp (hLip z (coe v))).2
    linarith


/-! ## The sampling choice (building the ψ map locally)

To define `ψ_β : H₀(𝔽^β) → H₀(𝓡_δ(L^{β−ε/4}))` (`β ≥ α`) we choose, for every point of the
sampled `𝔽^α ⊇ 𝔽^β`, a `δ/4`-close sample. The choice exists whenever `L` is nonempty
(automatic when `𝔽^α ≠ ∅`, by `hL`); the degenerate case `𝔽^α = ∅` makes the conclusion of
Theorem 4.5 vacuous on the constrained quadrants (all births `< α`) and is handled separately
in the final assembly. -/
theorem t45gamma_sample_choice {X : Type*} [MetricSpace X] {f : X → ℝ} {L : Finset X}
    {α δ : ℝ} (hL : IsGeodesicSample (L : Set X) (superlevel f α) (δ / 4)) [Nonempty ↥L] :
    ∃ vs : X → ↥L, ∀ z : X, α ≤ f z → dist z ((vs z : ↥L) : X) ≤ δ / 4 := by
  classical
  have hex : ∀ z : X, ∃ v : ↥L, α ≤ f z → dist z (v : X) ≤ δ / 4 := by
    intro z
    by_cases hz : α ≤ f z
    · obtain ⟨v, hvL, hvd⟩ := hL z hz
      exact ⟨⟨v, hvL⟩, fun _ => hvd⟩
    · exact ⟨Classical.arbitrary ↥L, fun hh => absurd hh hz⟩
  choose vs hvs using hex
  exact ⟨vs, fun z hz => hvs z hz⟩

/-! ## The ψ and φ maps as well-defined maps of component classes -/



/-- Rips class-equality: vertices Rips-joined at level `t'` have equal `ryy`-classes. -/
theorem t45gamma_rclass {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ} {δ t' : ℝ}
    {i j : ↥L} (hi : t' ≤ f (i : X)) (hj : t' ≤ f (j : X))
    (hjoin : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ t' i j) :
    (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      t' i j}) i
      = (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      t' i j}) j := by
  have hlaw := t45gamma_rips_filtrationLaw
    (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
  have hsymrj := hlaw.symm hjoin
  ext w
  exact ⟨fun h => ⟨hj, hsymrj.2.trans h.2⟩, fun h => ⟨hi, hjoin.2.trans h.2⟩⟩


section
variable {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ}

/-- Representative of an `𝔽^β`-component-class, as a point of `X`. -/
noncomputable def t45gamma_xrep {X : Type*} [MetricSpace X] {f : X → ℝ} {β : ℝ}
    (xC : comps (superlevel f) (fun t => JoinedIn (superlevel f t)) β) : X :=
  compRep (superlevel f) (fun t => JoinedIn (superlevel f t)) β xC

theorem t45gamma_xrep_grade {X : Type*} [MetricSpace X] {f : X → ℝ} {β : ℝ}
    (xC : comps (superlevel f) (fun t => JoinedIn (superlevel f t)) β) :
    β ≤ f (t45gamma_xrep xC) := by
  have h := (compRep_spec (superlevel f) (fun t => JoinedIn (superlevel f t)) β xC).1
  simpa only [t45gamma_xrep, superlevel, Set.mem_setOf_eq] using h

/-- Representative of a Rips `L^β`-component-class, as a point of `↥L`. -/
noncomputable def t45gamma_yrep {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ} {δ : ℝ} {β : ℝ}
    (yC : comps (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β) : ↥L :=
  compRep (fun t => {i : ↥L | t ≤ f (i : X)})
    (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β yC

theorem t45gamma_yrep_grade {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ} {δ : ℝ} {β : ℝ}
    (yC : comps (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β) :
    β ≤ f (t45gamma_yrep yC : X) := by
  have h := (compRep_spec (fun t => {i : ↥L | t ≤ f (i : X)})
    (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β yC).1
  simpa only [t45gamma_yrep, Set.mem_setOf_eq] using h

/-- Grade of the chosen sample: `s₁ ≤ f z` (`α ≤ f z`) ⟹ `s₁ − cδ ≤ f (vs z)`. -/
theorem t45gamma_grade_sample' {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ} {α c δ s₁ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (vs : X → ↥L) (hvs : ∀ z : X, α ≤ f z → dist z ((vs z : ↥L) : X) ≤ δ / 4)
    {z : X} (hαz : α ≤ f z) (hs : s₁ ≤ f z) : s₁ - c * δ ≤ f (vs z : X) := by
  have hcd4 : c * (δ / 4) ≤ c * δ :=
    mul_le_mul_of_nonneg_left (show (δ : ℝ) / 4 ≤ δ by linarith) hc
  have hb2 := (abs_le.mp (hLip z (vs z : X))).2
  have hvsd : dist z (vs z : X) ≤ δ / 4 := hvs z hαz
  have hcm : c * dist z (vs z : X) ≤ c * (δ / 4) := mul_le_mul_of_nonneg_left hvsd hc
  linarith

/-- **φ (X→Y)**: Rips `L^{β−cδ}`-class of the sample of the `𝔽^β`-class representative. -/
noncomputable def t45gamma_phiConc2 {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ} {α c δ β : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (vs : X → ↥L) (hvs : ∀ z : X, α ≤ f z → dist z ((vs z : ↥L) : X) ≤ δ / 4)
    (hαβ : α ≤ β)
    (xC : comps (superlevel f) (fun t => JoinedIn (superlevel f t)) β) :
    comps (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) (β - c * δ) :=
  ⟨(fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      (β - c * δ) i j}) (vs (t45gamma_xrep xC)),
    ⟨vs (t45gamma_xrep xC),
      t45gamma_grade_sample' hc hδ hLip vs hvs
        (le_trans hαβ (t45gamma_xrep_grade xC)) (t45gamma_xrep_grade xC),
      rfl⟩⟩

/-- **ψ (Y→X)**: `𝔽^{β−cδ}`-class of the representative vertex of a Rips `L^β`-class. -/
noncomputable def t45gamma_psiConc {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ} {c δ β : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (yC : comps (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β) :
    comps (superlevel f) (fun t => JoinedIn (superlevel f t)) (β - c * δ) :=
  ⟨(fun z => {y | JoinedIn (superlevel f (β - c * δ)) z y}) (t45gamma_yrep yC : X),
    ⟨(t45gamma_yrep yC : X),
      le_trans (sub_le_self β (mul_nonneg hc hδ.le)) (t45gamma_yrep_grade yC),
      rfl⟩⟩

end

section
variable {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ}

/-- Square (i′) for φ: `φ_β ∘ x^{β'}_β = y^{β'−cδ}_{β−cδ} ∘ φ_{β'}`. -/
theorem t45gamma_sq1_phi {α c δ β β' : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (vs : X → ↥L) (hvs : ∀ z : X, α ≤ f z → dist z ((vs z : ↥L) : X) ≤ δ / 4)
    (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
    (x : comps (superlevel f) (fun t => JoinedIn (superlevel f t)) β') :
    t45gamma_phiConc2 hc hδ hLip vs hvs hβ
        (structMap (t45gamma_super_filtrationLaw f) hle x) =
      structMap (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ) (show β - c * δ ≤ β' - c * δ by linarith)
        (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x) := by
  classical
  have hclass_eq : (structMap (t45gamma_super_filtrationLaw f) hle x).val =
      {y1 : X | JoinedIn (superlevel f β) (t45gamma_xrep x) y1} := by
    rw [structMap_val]; rfl
  -- (B) u belongs to the β-class of z
  have hz_u : JoinedIn (superlevel f β) (t45gamma_xrep x)
      (t45gamma_xrep (structMap (t45gamma_super_filtrationLaw f) hle x)) := by
    have hspec := (compRep_spec (superlevel f) (fun t => JoinedIn (superlevel f t)) β
      (structMap (t45gamma_super_filtrationLaw f) hle x)).2
    have hspec' : (fun y => {y1 : X | JoinedIn (superlevel f β) y y1})
        (t45gamma_xrep (structMap (t45gamma_super_filtrationLaw f) hle x)) =
        (structMap (t45gamma_super_filtrationLaw f) hle x).val := hspec
    have hu_self : t45gamma_xrep (structMap (t45gamma_super_filtrationLaw f) hle x) ∈
        (fun y => {y1 : X | JoinedIn (superlevel f β) y y1})
          (t45gamma_xrep (structMap (t45gamma_super_filtrationLaw f) hle x)) :=
      (t45gamma_super_filtrationLaw f).refl
        (show t45gamma_xrep (structMap (t45gamma_super_filtrationLaw f) hle x) ∈
          superlevel f β from
          t45gamma_xrep_grade (structMap (t45gamma_super_filtrationLaw f) hle x))
    rw [hspec'] at hu_self
    rw [hclass_eq] at hu_self
    exact hu_self
  -- (a)
  have ha : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      (β - c * δ) (vs (t45gamma_xrep x))
      (vs (t45gamma_xrep (structMap (t45gamma_super_filtrationLaw f) hle x))) := by
    have hraw := t45gamma_chain_rips_gen (fun w : ↥L => (w : X))
      (fun x y : ↥L => dist (x : X) (y : X)) (fun _ _ => rfl) (fun w : ↥L => f w) f (fun _ => rfl)
      c hc hLip δ hδ β vs (fun w hw => hvs w (le_trans hβ hw))
      (t45gamma_xrep x) (t45gamma_xrep (structMap (t45gamma_super_filtrationLaw f) hle x))
      hz_u
    exact (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
      (fun x : ↥L => f x) δ).compat (show β - c * δ ≤ β - c * (δ / 4) by
        have : c * (δ / 4) ≤ c * δ :=
          mul_le_mul_of_nonneg_left (show (δ : ℝ) / 4 ≤ δ by linarith) hc
        linarith) hraw
  -- (b)
  have hb : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      (β - c * δ) (vs (t45gamma_xrep x))
      (t45gamma_yrep (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x)) := by
    have hraw : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
        (β' - c * δ) (vs (t45gamma_xrep x))
        (t45gamma_yrep (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x)) := by
      have hv_mem : t45gamma_yrep (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x) ∈
          (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x).val := by
        have hspec := (compRep_spec (fun t => {i : ↥L | t ≤ f (i : X)})
          (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ)
          (β' - c * δ) (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x)).2
        rw [← hspec]
        exact (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
          (fun x : ↥L => f x) δ).refl
          (show t45gamma_yrep (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x) ∈
            {i : ↥L | β' - c * δ ≤ f (i : X)} from
            t45gamma_yrep_grade (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x))
      exact hv_mem
    exact (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
      (fun x : ↥L => f x) δ).compat (show β - c * δ ≤ β' - c * δ by linarith) hraw
  have hu_grade : β ≤ f (t45gamma_xrep (structMap (t45gamma_super_filtrationLaw f)
      hle x)) := t45gamma_xrep_grade _
  have hu_samp_grade : β - c * δ ≤ f (vs (t45gamma_xrep
      (structMap (t45gamma_super_filtrationLaw f) hle x)) : X) :=
    t45gamma_grade_sample' hc hδ hLip vs hvs (le_trans hβ hu_grade) hu_grade
  have hv_grade : β - c * δ ≤ f (t45gamma_yrep (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x) : X) :=
    le_trans (show β - c * δ ≤ β' - c * δ by linarith)
      (t45gamma_yrep_grade (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x))
  have hjoin : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      (β - c * δ)
      (vs (t45gamma_xrep (structMap (t45gamma_super_filtrationLaw f) hle x)))
      (t45gamma_yrep (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x)) :=
    ⟨hu_samp_grade, ((t45gamma_rips_filtrationLaw _ _ _).symm ha).2.trans hb.2⟩
  have hrc := t45gamma_rclass hu_samp_grade hv_grade hjoin
  have hvalL : (t45gamma_phiConc2 hc hδ hLip vs hvs hβ
      (structMap (t45gamma_super_filtrationLaw f) hle x)).val =
      (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
        (β - c * δ) i j})
        (vs (t45gamma_xrep (structMap (t45gamma_super_filtrationLaw f) hle x))) := rfl
  have hvalR : (structMap (t45gamma_rips_filtrationLaw
      (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ)
      (show β - c * δ ≤ β' - c * δ by linarith)
      (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x)).val =
      (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
        (β - c * δ) i j})
        (t45gamma_yrep (t45gamma_phiConc2 hc hδ hLip vs hvs hβ' x)) := by
    rw [structMap_val]; rfl
  refine Subtype.ext ?_
  rw [hvalL, hvalR]
  exact hrc

end

section
variable {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ}

/-- F1: the coarsened-class representative `u` is Rips-joined at `β` to `v := yrep y`. -/
theorem t45gamma_F1 {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ} {δ : ℝ} {β β' : ℝ} (hle : β ≤ β')
    (yC : comps (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β') :
    ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ β
      (t45gamma_yrep yC) (t45gamma_yrep (structMap
        (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
          (fun x : ↥L => f x) δ) hle yC)) := by
  classical
  have hu_grade : β ≤ f ((t45gamma_yrep (structMap
      (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ) hle yC) : X)) :=
    t45gamma_yrep_grade (structMap (t45gamma_rips_filtrationLaw
      (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC)
  have hclass_eq : (structMap (t45gamma_rips_filtrationLaw
      (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC).val =
      (fun i => {j : ↥L | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ β i j}) (t45gamma_yrep yC) := by
    rw [structMap_val]; rfl
  have hspec := (compRep_spec (fun t => {i : ↥L | t ≤ f (i : X)})
    (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β
    (structMap (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
      (fun x : ↥L => f x) δ) hle yC)).2
  have hspec' : (fun i => {j : ↥L | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
      (fun x : ↥L => f x) δ β i j})
      (t45gamma_yrep (structMap (t45gamma_rips_filtrationLaw
        (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC)) =
      (structMap (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ) hle yC).val := hspec
  have hu_memb : t45gamma_yrep (structMap (t45gamma_rips_filtrationLaw
      (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC) ∈
      {i : ↥L | β ≤ f (i : X)} := by
    simpa only [t45gamma_yrep, Set.mem_setOf_eq] using hu_grade
  have hu_self : t45gamma_yrep (structMap (t45gamma_rips_filtrationLaw
      (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC) ∈
      (fun i => {j : ↥L | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ β i j})
        (t45gamma_yrep (structMap (t45gamma_rips_filtrationLaw
          (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC)) :=
    (t45gamma_rips_filtrationLaw _ _ _).refl hu_memb
  rw [hspec', hclass_eq] at hu_self
  exact hu_self

/-- F3: the 𝔽-representative of `ψ_{β'} y` is `𝔽^{β'−cδ}`-joined to `(yrep y : X)`. -/
theorem t45gamma_F3 {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ} {c δ : ℝ} {β' : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (yC : comps (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β') :
    JoinedIn (superlevel f (β' - c * δ)) (t45gamma_yrep yC : X)
      (t45gamma_xrep (t45gamma_psiConc hc hδ yC) : X) := by
  classical
  have hz_memb : t45gamma_xrep (t45gamma_psiConc hc hδ yC) ∈ superlevel f (β' - c * δ) := by
    simpa only [t45gamma_xrep, superlevel, Set.mem_setOf_eq] using
      t45gamma_xrep_grade (t45gamma_psiConc hc hδ yC)
  have hz_class := (compRep_spec (superlevel f) (fun t => JoinedIn (superlevel f t))
    (β' - c * δ) (t45gamma_psiConc hc hδ yC)).2
  have hz_class' : (fun zz => {y1 : X | JoinedIn (superlevel f (β' - c * δ)) zz y1})
      (t45gamma_xrep (t45gamma_psiConc hc hδ yC) : X) =
      (t45gamma_psiConc hc hδ yC).val := hz_class
  have hz_self : t45gamma_xrep (t45gamma_psiConc hc hδ yC) ∈
      (fun zz => {y1 : X | JoinedIn (superlevel f (β' - c * δ)) zz y1})
        (t45gamma_xrep (t45gamma_psiConc hc hδ yC) : X) :=
    (t45gamma_super_filtrationLaw f).refl hz_memb
  have hval_psiY : (t45gamma_psiConc hc hδ yC).val =
      (fun zz => {y1 : X | JoinedIn (superlevel f (β' - c * δ)) zz y1})
        ((t45gamma_yrep yC) : X) := rfl
  rw [hz_class', hval_psiY] at hz_self
  exact hz_self

/-- X-side class equality: two points joined in `𝔽^t` have equal classes. -/
theorem t45gamma_xrclass {X : Type*} [MetricSpace X] {f : X → ℝ} {t : ℝ} {x1 x2 : X}
    (hx1 : x1 ∈ superlevel f t) (hx2 : x2 ∈ superlevel f t)
    (hjoin : JoinedIn (superlevel f t) x1 x2) :
    (fun z => {y1 : X | JoinedIn (superlevel f t) z y1}) x1
      = (fun z => {y1 : X | JoinedIn (superlevel f t) z y1}) x2 := by
  ext w
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun h => JoinedIn.trans (JoinedIn.symm hjoin) h,
         fun h => JoinedIn.trans hjoin h⟩

/-- **Square (ii′)** for ψ: `ψ_β ∘ y^{β'}_β = x^{β'−cδ}_{β−cδ} ∘ ψ_{β'}`. -/
theorem t45gamma_sq2_psi {α c δ β β' : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (hLip : ∀ x y : X, |f x - f y| ≤ c * dist x y)
    (vs : X → ↥L) (hvs : ∀ z : X, α ≤ f z → dist z ((vs z : ↥L) : X) ≤ δ / 4)
    (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
    (yC : comps (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β') :
    t45gamma_psiConc hc hδ
        (structMap (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
          (fun x : ↥L => f x) δ) hle yC) =
      structMap (t45gamma_super_filtrationLaw f)
        (show β - c * δ ≤ β' - c * δ by linarith)
        (t45gamma_psiConc hc hδ yC) := by
  classical
  -- (F1) transported: ripsJoined at ((β−cδ)+cδ) from u to v
  have hmemB : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      ((β - c * δ) + c * δ)
      (t45gamma_yrep (structMap (t45gamma_rips_filtrationLaw
        (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC))
      (t45gamma_yrep yC) := by
    rw [show (β - c * δ) + c * δ = β by ring]
    exact (t45gamma_rips_filtrationLaw _ _ _).symm (t45gamma_F1 hle yC)
  have huX_join : JoinedIn (superlevel f (β - c * δ))
      (t45gamma_yrep (structMap (t45gamma_rips_filtrationLaw
        (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC) : X)
      (t45gamma_yrep yC : X) :=
    t45gamma_chain_super (fun w : ↥L => (w : X)) (fun x y : ↥L => dist (x : X) (y : X))
      (fun _ _ => rfl) f c hc hLip δ (β - c * δ) hδ hδρ
      (t45gamma_yrep (structMap (t45gamma_rips_filtrationLaw
        (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC))
      (t45gamma_yrep yC) hmemB
  -- (F3) dropped to (β−cδ)
  have hmem2 : JoinedIn (superlevel f (β - c * δ)) (t45gamma_yrep yC : X)
      (t45gamma_xrep (t45gamma_psiConc hc hδ yC) : X) :=
    (t45gamma_F3 hc hδ yC).mono ((t45gamma_super_filtrationLaw f).antitone
      (show β - c * δ ≤ β' - c * δ by linarith))
  have hjoin2 := huX_join.trans hmem2
  -- (C) the two 𝔽^{β−cδ}-classes coincide
  have hclassX := t45gamma_xrclass
    (show (t45gamma_yrep (structMap (t45gamma_rips_filtrationLaw
      (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC) : X) ∈
      superlevel f (β - c * δ) from
      le_trans (show β - c * δ ≤ β by linarith [mul_nonneg hc hδ.le])
        (t45gamma_yrep_grade (structMap (t45gamma_rips_filtrationLaw
          (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC)))
    (show t45gamma_xrep (t45gamma_psiConc hc hδ yC) ∈ superlevel f (β - c * δ) from
      le_trans (show β - c * δ ≤ β' - c * δ by linarith)
        (t45gamma_xrep_grade (t45gamma_psiConc hc hδ yC))) hjoin2
  have hvalL : (t45gamma_psiConc hc hδ
      (structMap (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ) hle yC)).val =
      (fun zz => {y1 : X | JoinedIn (superlevel f (β - c * δ)) zz y1})
        (t45gamma_yrep (structMap (t45gamma_rips_filtrationLaw
          (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hle yC) : X) := rfl
  have hvalR : (structMap (t45gamma_super_filtrationLaw f)
      (show β - c * δ ≤ β' - c * δ by linarith) (t45gamma_psiConc hc hδ yC)).val =
      (fun zz => {y1 : X | JoinedIn (superlevel f (β - c * δ)) zz y1})
        (t45gamma_xrep (t45gamma_psiConc hc hδ yC) : X) := by
    rw [structMap_val]; rfl
  refine Subtype.ext ?_
  rw [hvalL, hvalR]
  exact hclassX

end

/-! ## Stage B part 5 (GREEN): square (iii') for the concrete pair — `φ_{β-ε} ∘ ψ_β = y^β_{(β-ε)-ε}`.
The ripsJoined coordinates are the SAMPLE vertices (`vs (vY : X)`, `vs (uX : X)`); chain_rips_gen at `(β-cδ)` outputs level `(β-cδ)-cδ/4`, compat-lowered to `(β-cδ)-cδ`; then the sample edge + `t45gamma_rclass`; closed by `Subtype.ext`. All call sites carry the pinned implicit args from the #20 header edit. -/

/-- **Square (iii′)** for the concrete pair: `φ_{β−ε} ∘ ψ_β = y^β_{(β−ε)−ε}`. -/
theorem t45gamma_sq3_phi_psi {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ}
    {α c δ β : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hLip : ∀ x y : X, |f x - f y| ≤ c * dist x y)
    (vs : X → ↥L) (hvs : ∀ z : X, α ≤ f z → dist z ((vs z : ↥L) : X) ≤ δ / 4)
    (hβ : α ≤ β) (hβε : α ≤ β - c * δ) (hβee : (β - c * δ) - c * δ ≤ β)
    (yC : comps (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β) :
    t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c) (δ := δ)
        (β := β - c * δ) hc hδ hLip vs hvs hβε
        (t45gamma_psiConc (X := X) (L := L) (f := f) (c := c) (δ := δ) (β := β) hc hδ yC) =
      structMap (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ) hβee yC := by
  classical
  have hε : 0 ≤ c * δ := mul_nonneg hc hδ.le
  have hcd4 : c * (δ / 4) ≤ c * δ :=
    mul_le_mul_of_nonneg_left (show (δ : ℝ) / 4 ≤ δ by linarith) hc
  -- native-typed witnesses
  let vY : ↥L := t45gamma_yrep (X := X) (L := L) (f := f) (δ := δ) (β := β) yC
  let uX : X := t45gamma_xrep (X := X) (f := f)
    (t45gamma_psiConc (X := X) (L := L) (f := f) (c := c) (δ := δ) (β := β) hc hδ yC)
  have hvY_gradeβ : β ≤ f (vY : X) := by
    show β ≤ f ((t45gamma_yrep (X := X) (L := L) (f := f) (δ := δ) (β := β) yC) : X)
    exact t45gamma_yrep_grade (X := X) (L := L) (f := f) (δ := δ) (β := β) yC
  have huX_grade : β - c * δ ≤ f uX := by
    show β - c * δ ≤ f (t45gamma_xrep (X := X) (f := f)
      (t45gamma_psiConc (X := X) (L := L) (f := f) (c := c) (δ := δ) (β := β) hc hδ yC))
    exact t45gamma_xrep_grade (X := X) (f := f)
      (t45gamma_psiConc (X := X) (L := L) (f := f) (c := c) (δ := δ) (β := β) hc hδ yC)
  -- F3: vY ~ uX in 𝔽^{β−cδ}
  have hjoin_vz : JoinedIn (superlevel f (β - c * δ)) (vY : X) uX := by
    show JoinedIn (superlevel f (β - c * δ))
      ((t45gamma_yrep (X := X) (L := L) (f := f) (δ := δ) (β := β) yC) : X)
      (t45gamma_xrep (X := X) (f := f)
        (t45gamma_psiConc (X := X) (L := L) (f := f) (c := c) (δ := δ) (β := β) hc hδ yC) : X)
    exact t45gamma_F3 (X := X) (L := L) (f := f) (c := c) (δ := δ) (β' := β) hc hδ yC
  -- chain_rips_gen at (β−cδ)
  have hvu_join : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      ((β - c * δ) - c * (δ / 4)) (vs (vY : X)) (vs (uX : X)) :=
    t45gamma_chain_rips_gen (ι := ↥L) (coe := fun w : ↥L => (w : X))
      (Dm := fun x y : ↥L => dist (x : X) (y : X)) (hDm := fun _ _ => rfl)
      (g := fun w : ↥L => f w) (f := f) (hgf := fun _ => rfl)
      (c := c) (hc := hc) (hLip := hLip) (δ := δ) (hδ := hδ) (t' := β - c * δ)
      (vsamp := vs) (hvsamp := fun w hw => hvs w (le_trans hβε hw))
      (x := (vY : X)) (y := uX) (hjoined := hjoin_vz)
  have hvu_low : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      ((β - c * δ) - c * δ) (vs (vY : X)) (vs (uX : X)) :=
    (t45gamma_rips_filtrationLaw _ _ _).compat
      (show (β - c * δ) - c * δ ≤ β - c * δ - c * (δ / 4) by linarith [hcd4]) hvu_join
  -- grades at the target level
  have hvY' : (β - c * δ) - c * δ ≤ f (vY : X) := by linarith [hvY_gradeβ, hε]
  have hvs_vY : (β - c * δ) - c * δ ≤ f (vs (vY : X) : X) := by
    have hb2 := (abs_le.mp (hLip (vY : X) (vs (vY : X) : X))).2
    have hvsd : dist (vY : X) (vs (vY : X) : X) ≤ δ / 4 :=
      hvs (vY : X) (le_trans (le_trans hβε (by linarith [hε])) hvY_gradeβ)
    have hcm : c * dist (vY : X) (vs (vY : X) : X) ≤ c * (δ / 4) :=
      mul_le_mul_of_nonneg_left hvsd hc
    linarith [hvY_gradeβ, hb2, hcm, hcd4, hε]
  have hvs_uX : (β - c * δ) - c * δ ≤ f (vs (uX : X) : X) := by
    show (β - c * δ) - c * δ ≤ f (vs (t45gamma_xrep (X := X) (f := f)
      (t45gamma_psiConc (X := X) (L := L) (f := f) (c := c) (δ := δ) (β := β) hc hδ yC) : X) : X)
    exact t45gamma_grade_sample' (X := X) (L := L) (f := f) (α := α) (c := c) (δ := δ)
      (s₁ := β - c * δ) hc hδ hLip vs hvs (le_trans hβε huX_grade) huX_grade
  -- sample edge vY ~ vs vY
  have hedge : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      ((β - c * δ) - c * δ) vY (vs (vY : X)) := by
    by_cases heq : vs (vY : X) = vY
    · rw [heq]; exact ⟨hvY', Relation.ReflTransGen.refl⟩
    · refine ⟨hvY', Relation.ReflTransGen.single ⟨hvY', hvs_vY, ?_⟩⟩
      refine (SimpleGraph.fromRel_adj (fun a b =>
        (fun x y : ↥L => dist (x : X) (y : X)) a b ≤ δ) _ _).mpr
        ⟨fun h => heq h.symm, Or.inl ?_⟩
      exact le_trans (hvs (vY : X) (le_trans (le_trans hβε (by linarith [hε])) hvY_gradeβ))
        (show (δ : ℝ) / 4 ≤ δ by linarith)
  -- ripsJoined ((β−cδ)−cδ) (vs uX) vY
  have hvsU_v : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      ((β - c * δ) - c * δ) (vs (uX : X)) vY :=
    ⟨hvs_uX, ((t45gamma_rips_filtrationLaw _ _ _).symm hvu_low).2.trans
      ((t45gamma_rips_filtrationLaw _ _ _).symm hedge).2⟩
  have hrc := t45gamma_rclass (X := X) (L := L) (f := f) (δ := δ)
    (t' := (β - c * δ) - c * δ) hvs_uX hvY' hvsU_v
  -- both values as class-sets
  have hvalL : (t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c) (δ := δ)
      (β := β - c * δ) hc hδ hLip vs hvs hβε
      (t45gamma_psiConc (X := X) (L := L) (f := f) (c := c) (δ := δ) (β := β) hc hδ yC)).val =
      (fun i => {j : ↥L | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ ((β - c * δ) - c * δ) i j})
        (vs (t45gamma_xrep (X := X) (f := f) (t45gamma_psiConc (X := X) (L := L) (f := f)
          (c := c) (δ := δ) (β := β) hc hδ yC) : X)) := rfl
  have hvalR : (structMap (t45gamma_rips_filtrationLaw
      (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) hβee yC).val =
      (fun i => {j : ↥L | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ ((β - c * δ) - c * δ) i j}) vY := by
    rw [structMap_val]; rfl
  refine Subtype.ext ?_
  rw [hvalL, hvalR]
  exact hrc


/-! ## Stage B part 6 (GREEN): square (iv') for the concrete pair — `ψ_{β-ε} ∘ φ_β = x^β_{(β-ε)-ε}`.
Witnesses `zX := xrep xC`, `wY := yrep(φ_β xC)`; FACT1 class-membership `wY ∈ φ_β(xC).val`;
FACT2 `chain_super` with the level transport `((β−cδ)−cδ)+cδ = β−cδ`; FACT3 `t45gamma_sample_joined`
at `β' := β` + antitone drop; composition + `t45gamma_xrclass`, closed by `Subtype.ext`. -/

/-- **Square (iv′)** for the concrete pair: `ψ_{β−ε} ∘ φ_β = x^β_{(β−ε)−ε}`. -/
theorem t45gamma_sq4_psi_phi {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ}
    {α c δ β : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (hLip : ∀ x y : X, |f x - f y| ≤ c * dist x y)
    (vs : X → ↥L) (hvs : ∀ z : X, α ≤ f z → dist z ((vs z : ↥L) : X) ≤ δ / 4)
    (hβ : α ≤ β) (hβee : (β - c * δ) - c * δ ≤ β)
    (xC : comps (superlevel f) (fun t => JoinedIn (superlevel f t)) β) :
    t45gamma_psiConc (X := X) (L := L) (f := f) (c := c) (δ := δ) (β := β - c * δ) hc hδ
        (t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c) (δ := δ)
          (β := β) hc hδ hLip vs hvs hβ xC) =
      structMap (t45gamma_super_filtrationLaw f) hβee xC := by
  classical
  have hε : 0 ≤ c * δ := mul_nonneg hc hδ.le
  have hcd4 : c * (δ / 4) ≤ c * δ :=
    mul_le_mul_of_nonneg_left (show (δ : ℝ) / 4 ≤ δ by linarith) hc
  -- native-typed witnesses
  let zX : X := t45gamma_xrep (X := X) (f := f) xC
  let wY : ↥L := t45gamma_yrep (X := X) (L := L) (f := f) (δ := δ) (β := β - c * δ)
    (t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c) (δ := δ)
      (β := β) hc hδ hLip vs hvs hβ xC)
  have hzX_grade : β ≤ f zX := by
    show β ≤ f (t45gamma_xrep (X := X) (f := f) xC)
    exact t45gamma_xrep_grade (X := X) (f := f) xC
  have hwY_grade : β - c * δ ≤ f (wY : X) := by
    show β - c * δ ≤ f (t45gamma_yrep (X := X) (L := L) (f := f) (δ := δ) (β := β - c * δ)
      (t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c) (δ := δ)
        (β := β) hc hδ hLip vs hvs hβ xC))
    exact t45gamma_yrep_grade (X := X) (L := L) (f := f) (δ := δ) (β := β - c * δ)
      (t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c) (δ := δ)
        (β := β) hc hδ hLip vs hvs hβ xC)
  -- FACT 1: wY ∈ φ_β(x)'s val = the ripsJoined-class of vs zX at (β−cδ)
  have hwY_val : wY ∈ (t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c)
      (δ := δ) (β := β) hc hδ hLip vs hvs hβ xC).val := by
    have hspec := (compRep_spec (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ)
      (β - c * δ) (t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c) (δ := δ)
        (β := β) hc hδ hLip vs hvs hβ xC)).2
    have hspec' : (fun i => {j : ↥L | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ (β - c * δ) i j}) wY =
      (t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c) (δ := δ)
        (β := β) hc hδ hLip vs hvs hβ xC).val := hspec
    have hw_self : wY ∈ (fun i => {j : ↥L | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ (β - c * δ) i j}) wY :=
      ⟨hwY_grade, Relation.ReflTransGen.refl⟩
    rw [hspec'] at hw_self
    exact hw_self
  have hvalphi : (t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c) (δ := δ)
      (β := β) hc hδ hLip vs hvs hβ xC).val =
      (fun i => {j : ↥L | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ (β - c * δ) i j}) (vs (zX : X)) := rfl
  -- FACT 1 (composed): ripsJoined (β−cδ) (vs zX) wY
  have hvw : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      (β - c * δ) (vs (zX : X)) wY := by
    rw [hvalphi] at hwY_val
    exact hwY_val
  -- FACT 2: chain_super at ((β−cδ)−cδ)
  have hsol : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
      (((β - c * δ) - c * δ) + c * δ) wY (vs (zX : X)) := by
    rw [show ((β - c * δ) - c * δ) + c * δ = β - c * δ by ring]
    exact (t45gamma_rips_filtrationLaw _ _ _).symm hvw
  have hjoinWz : JoinedIn (superlevel f ((β - c * δ) - c * δ)) (wY : X) (vs (zX : X)) :=
    t45gamma_chain_super (ι := ↥L) (coe := fun w : ↥L => (w : X))
      (Dm := fun x y : ↥L => dist (x : X) (y : X)) (hDm := fun _ _ => rfl)
      (f := f) (c := c) (hc := hc) (hLip := hLip) (δ := δ)
      (t := ((β - c * δ) - c * δ)) (hδ := hδ) (hconvρ := hδρ)
      (i := wY) (j := vs (zX : X)) (h := hsol)
  -- FACT 3: zX ~ vs zX in 𝔽^{β−cδ}, dropped to ((β−cδ)−cδ)
  have hdist : dist zX (vs (zX : X) : X) ≤ δ / 4 :=
    hvs zX (le_trans (by linarith [hε]) hzX_grade)
  have hjoinZvs : JoinedIn (superlevel f (β - c * δ)) zX (vs (zX : X) : X) :=
    t45gamma_sample_joined (ι := ↥L) (coe := fun w : ↥L => (w : X)) (f := f) (c := c) (δ := δ)
      (β := β) hc hδ hδρ hLip (v := vs (zX : X)) (z := zX) hdist hzX_grade
  have hjoinZvs' : JoinedIn (superlevel f ((β - c * δ) - c * δ)) zX (vs (zX : X) : X) :=
    hjoinZvs.mono ((t45gamma_super_filtrationLaw f).antitone
      (show (β - c * δ) - c * δ ≤ β - c * δ by linarith))
  -- composition: wY ~ vs zX ~ zX in 𝔽^{(β−cδ)−cδ}
  have hjoin2 : JoinedIn (superlevel f ((β - c * δ) - c * δ)) (wY : X) zX :=
    hjoinWz.trans hjoinZvs'.symm
  -- classes coincide
  have hclassX := t45gamma_xrclass (X := X) (f := f) (t := ((β - c * δ) - c * δ))
    (show (wY : X) ∈ superlevel f ((β - c * δ) - c * δ) from
      le_trans (sub_le_self (β - c * δ) hε) hwY_grade)
    (show zX ∈ superlevel f ((β - c * δ) - c * δ) from
      le_trans (sub_le_self (β - c * δ) hε) (le_trans (sub_le_self β hε) hzX_grade))
    hjoin2
  -- both values as class-sets
  have hvalL : (t45gamma_psiConc (X := X) (L := L) (f := f) (c := c) (δ := δ)
      (β := β - c * δ) hc hδ
      (t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c) (δ := δ)
        (β := β) hc hδ hLip vs hvs hβ xC)).val =
      (fun zz => {y1 : X | JoinedIn (superlevel f ((β - c * δ) - c * δ)) zz y1}) (wY : X) := rfl
  have hvalR : (structMap (t45gamma_super_filtrationLaw f) hβee xC).val =
      (fun zz => {y1 : X | JoinedIn (superlevel f ((β - c * δ) - c * δ)) zz y1}) zX := by
    rw [structMap_val]; rfl
  refine Subtype.ext ?_
  rw [hvalL, hvalR]
  exact hclassX


/-- **The concrete strong-interleaving instance** for the two modules of Theorem 4.5. -/
theorem t45gamma_instance {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ}
    {α c : ℝ} {δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (hLip : ∀ x y : X, |f x - f y| ≤ c * dist x y)
    (hL : IsGeodesicSample (L : Set X) (superlevel f α) (δ / 4))
    (hNonempty : ∃ x : X, α ≤ f x) :
    StrongInterleavingAbove (superlevel f) (fun t => JoinedIn (superlevel f t))
      (fun t => {i : ↥L | t ≤ f (i : X)}) (ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ) (t45gamma_super_filtrationLaw f)
      (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ) (α := α) (ε := c * δ) (hε := mul_nonneg hc hδ.le) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hNonempty
  haveI : Nonempty ↥L := by
    obtain ⟨v, hvL, -⟩ := hL x₀ hx₀
    exact ⟨⟨v, hvL⟩⟩
  obtain ⟨vs, hvs⟩ := t45gamma_sample_choice (L := L) (f := f) (α := α) (δ := δ) hL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun β hβ xC => t45gamma_phiConc2 (X := X) (L := L) (f := f) (α := α) (c := c)
      (δ := δ) (β := β) hc hδ hLip vs hvs hβ xC
  · exact fun β hβ yC => t45gamma_psiConc (X := X) (L := L) (f := f) (c := c) (δ := δ)
      (β := β) hc hδ yC
  · exact fun β β' hβ hβ' hle x => t45gamma_sq1_phi (α := α) (c := c) (δ := δ) (β := β)
      (β' := β') hc hδ hδρ hLip vs hvs hβ hβ' hle x
  · exact fun β β' hβ hβ' hle y => t45gamma_sq2_psi (α := α) (c := c) (δ := δ) (β := β)
      (β' := β') hc hδ hδρ hLip vs hvs hβ hβ' hle y
  · exact fun β hβ hβε y => t45gamma_sq3_phi_psi (X := X) (L := L) (f := f) (α := α) (c := c)
      (δ := δ) (β := β) hc hδ hLip vs hvs hβ hβε
      (by have : (0:ℝ) ≤ c * δ := mul_nonneg hc hδ.le; linarith) y
  · exact fun β hβ hβε x => t45gamma_sq4_psi_phi (X := X) (L := L) (f := f) (α := α) (c := c)
      (δ := δ) (β := β) hc hδ hδρ hLip vs hvs hβ
      (by have : (0:ℝ) ≤ c * δ := mul_nonneg hc hδ.le; linarith) x

/-- Deliverable 1: the superlevel-set module is `IsTameModule`.
`IsTame0`'s conj.2 is *already* stated via `JoinedIn` (the paper's path-component relation, and
`pathComponentIn F x = {y | JoinedIn F x y}` definitionally), so conj.2/3 are `htame.2.1`/`.2.2`
verbatim; conj.1 reuses the `t45gamma_super_qtame` containment (image over `𝔽^t` sits inside the
finite set of `pathComponentIn (𝔽^t)` classes, plus possibly `∅`). -/
theorem t45gamma_super_isTameModule {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (htame : IsTame0 f) :
    IsTameModule (superlevel f) (fun t => JoinedIn (superlevel f t)) := by
  refine ⟨fun t => ?_, htame.2.1, htame.2.2⟩
  -- the class image over `𝔽^t` is contained in `{∅} ∪ {pathComponentIn (𝔽^t) x | x ∈ 𝔽^t}`,
  -- the latter finite by `IsTame0` condition 1.
  have hsub : ((fun x => {y | JoinedIn (superlevel f t) x y}) '' superlevel f t) ⊆
      insert (∅ : Set X) {C | ∃ x ∈ superlevel f t, C = pathComponentIn (superlevel f t) x} := by
    rintro S ⟨x, hx, rfl⟩
    -- `x ∈ 𝔽^t`, so its class is nonempty and equals `pathComponentIn (𝔽^t) x`.
    exact Or.inr ⟨x, hx, rfl⟩
  exact Set.Finite.subset (Set.Finite.insert (∅ : Set X) (htame.1 t)) hsub


/-- Deliverable 2: the Rips module on the finite sample `↥L` is `IsTameModule`.
conj.1: image of a subset of the finite type `↥L`.
conj.3: `t45gamma_rips_module_tame` (banked).
conj.2: `T := {f i | i ∈ ↥L}`; on a `T`-free window `[t,s]` no `f`-value lies in `[t,s]`, hence
`t ≤ f a ↔ s ≤ f a` for every vertex `a`, so `rel_t ≤ rel_s` pointwise and `ReflTransGen.mono`
lifts the `R_δ(L^t)`-chain to an `R_δ(L^s)`-chain. -/
theorem t45gamma_rips_isTameModule {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ}
    {δ : ℝ} :
    IsTameModule (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) := by
  classical
  refine ⟨fun t => ?_, ?_, ?_⟩
  -- conj.1: the image is a set of subsets of the finite vertex type `↥L`.
  · exact Set.Finite.image (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ t i j})
      (Set.toFinite ((fun t => {i : ↥L | t ≤ f (i : X)}) t))
  -- conj.2: finite critical set = image of the `f`-values on `↥L`.
  · refine ⟨(Finset.univ : Finset ↥L).image (fun i : ↥L => f (i : X)), ?_⟩
    intro t s hst hT
    refine ⟨?_, ?_⟩
    -- (a) ∀ x ∈ L^t, ∃ y ∈ L^s, ripsJoined (level t) x y : take y = x (reflexive).
    · rintro (x : ↥L) (hx : x ∈ (fun t => {i : ↥L | t ≤ f (i : X)}) t)
      have hxt : t ≤ f (x : X) := by show t ≤ f (x : X); exact hx
      -- T-freeness at `f x ∈ T` upgrades `t ≤ f x` to `s ≤ f x`.
      have hfxT : f (x : X) ∈ (Finset.univ : Finset ↥L).image (fun i : ↥L => f (i : X)) :=
        Finset.mem_image_of_mem _ (Finset.mem_univ x)
      have hsx : s ≤ f (x : X) := by
        rcases hT _ hfxT with hlt | hgt
        · linarith
        · linarith
      refine ⟨x, ?_, ?_⟩
      · show s ≤ f (x : X); exact hsx
      · refine ⟨hxt, Relation.ReflTransGen.refl⟩
    -- (b) ∀ y,y' ∈ L^s, ripsJoined (level t) y y' → ripsJoined (level s) y y'.
    · rintro (y : ↥L) (hy : y ∈ (fun t => {i : ↥L | t ≤ f (i : X)}) s) (y' : ↥L)
        (hy' : y' ∈ (fun t => {i : ↥L | t ≤ f (i : X)}) s)
        (hJ : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ t y y')
      have hys : s ≤ f (y : X) := by show s ≤ f (y : X); exact hy
      obtain ⟨hJt, hJchain⟩ := hJ
      refine ⟨hys, ?_⟩
      -- every `rel_t`-step is a `rel_s`-step (T-free ⇒ `t ≤ f a ⇒ s ≤ f a`), so lift the chain.
      have hmono :
          (fun a b : ↥L =>
              t ≤ f (a : X) ∧ t ≤ f (b : X) ∧ (ripsGraph (fun x y : ↥L => dist (x : X) (y : X)) δ).Adj a b)
            ≤ (fun a b : ↥L =>
              s ≤ f (a : X) ∧ s ≤ f (b : X) ∧ (ripsGraph (fun x y : ↥L => dist (x : X) (y : X)) δ).Adj a b) := by
        intro a b hab
        have ha1 : t ≤ f (a : X) := hab.1
        have hb1 : t ≤ f (b : X) := hab.2.1
        have hfaT : f (a : X) ∈ (Finset.univ : Finset ↥L).image (fun i : ↥L => f (i : X)) :=
          Finset.mem_image_of_mem _ (Finset.mem_univ a)
        have hfbT : f (b : X) ∈ (Finset.univ : Finset ↥L).image (fun i : ↥L => f (i : X)) :=
          Finset.mem_image_of_mem _ (Finset.mem_univ b)
        have hsa : s ≤ f (a : X) := by
          rcases hT _ hfaT with hlt | hgt
          · linarith
          · linarith
        have hsb : s ≤ f (b : X) := by
          rcases hT _ hfbT with hlt | hgt
          · linarith
          · linarith
        refine ⟨?_, ?_, hab.2.2⟩
        · show s ≤ f (a : X); exact hsa
        · show s ≤ f (b : X); exact hsb
      exact Relation.ReflTransGen.mono hmono y y' hJchain
  -- conj.3: banked `t45gamma_rips_module_tame` (eventual emptiness of the upper-star Rips stage).
  · exact t45gamma_rips_module_tame (fun x : ↥L => f (x : X))



/-! ## The degenerate case `𝔽^α = ∅`: the interleaving is vacuous

When no point of `X` has grade `≥ α`, every stage of BOTH filtrations at every level `β ≥ α`
is empty, so all component-class types at those levels are empty. The interleaving maps are
then the empty maps and the four commuting squares hold vacuously. Together with the
(concrete, banked) `t45gamma_instance` for the non-degenerate case, this discharges the
`StrongInterleavingAbove` hypothesis of `theorem_4_5_gate_matching` unconditionally. -/

/-- If the stage at level `t` is empty, there are no component classes at level `t`. -/
theorem t45w_compsEmpty {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop) (t : ℝ)
    (h : stage t = ∅) : ∀ C : comps stage J t, False := by
  intro C
  obtain ⟨S, hS⟩ := C
  rw [h, Set.image_empty] at hS
  exact absurd hS (by simp)

/-- In the degenerate case (every `f x < α`) the two concrete modules of Theorem 4.5 are
trivially strongly `(cδ)`-interleaved above `α`: all class types at levels `≥ α` are empty. -/
theorem t45w_degenerate_IL {X : Type*} [MetricSpace X] (L : Finset X) (f : X → ℝ)
    (c δ α : ℝ) (hc : 0 ≤ c) (hδ : 0 < δ)
    (hdeg : ∀ x : X, f x < α) :
    StrongInterleavingAbove (superlevel f) (fun t => JoinedIn (superlevel f t))
      (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ)
      (t45gamma_super_filtrationLaw f)
      (t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X))
        (fun x : ↥L => f x) δ)
      α (c * δ) (mul_nonneg hc hδ.le) := by
  have hX : ∀ β : ℝ, α ≤ β → superlevel f β = ∅ := fun β hβ =>
    Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
      absurd (le_trans hβ hx) (not_le.mpr (hdeg x))
  have hY : ∀ β : ℝ, α ≤ β → (fun t => {i : ↥L | t ≤ f (i : X)}) β = ∅ := fun β hβ =>
    Set.eq_empty_iff_forall_notMem.mpr fun i hi =>
      absurd (le_trans hβ hi) (not_le.mpr (hdeg (i : X)))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun β hβ xC =>
      (t45w_compsEmpty (superlevel f) (fun t => JoinedIn (superlevel f t)) β (hX β hβ) xC).elim
  · exact fun β hβ yC =>
      (t45w_compsEmpty (fun t => {i : ↥L | t ≤ f (i : X)})
        (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β
        (hY β hβ) yC).elim
  · exact fun β β' hβ hβ' _hle x =>
      (t45w_compsEmpty (superlevel f) (fun t => JoinedIn (superlevel f t)) β' (hX β' hβ') x).elim
  · exact fun β β' hβ hβ' _hle y =>
      (t45w_compsEmpty (fun t => {i : ↥L | t ≤ f (i : X)})
        (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β'
        (hY β' hβ') y).elim
  · exact fun β hβ _hβε y =>
      (t45w_compsEmpty (fun t => {i : ↥L | t ≤ f (i : X)})
        (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) β
        (hY β hβ) y).elim
  · exact fun β hβ _hβε x =>
      (t45w_compsEmpty (superlevel f) (fun t => JoinedIn (superlevel f t)) β (hX β hβ) x).elim

/-! ## The reduction of `theorem_4_5` to the gate

Both diagrams are definitionally the `mult` of a `rankFn` of the concrete filtrations:
`diagram0 f = mult (superRank f)` with `superRank f = rankFn (superlevel f) (JoinedIn ·)`, and
`ripsDiagram Dm g δ = mult (ripsRank Dm g δ)` with `ripsRank Dm g δ =
rankFn (fun t => {i | t ≤ g i}) (ripsJoined Dm g δ)`. Hence the gate's conclusion transports
to the published statement of Theorem 4.5 by definitional unfolding alone. -/

end PersistClust.Count

open PersistClust.Count

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X]
    (hconv : 0 < convexityRadius X)
    (L : Finset X) (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (htame : IsTame0 f)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (α : ℝ) (hL : IsGeodesicSample (L : Set X) (superlevel f α) (δ / 4)) :
    ∃ γ : Copies (diagram0 f) ≃
        Copies (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ),
      SatisfiesIIV γ α (c * δ) := by
  have hε : (0 : ℝ) ≤ c * δ := mul_nonneg hc hδ.le
  have hLawX : FiltrationLaw (superlevel f) (fun t => JoinedIn (superlevel f t)) :=
    t45gamma_super_filtrationLaw f
  have hLawY : FiltrationLaw (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) :=
    t45gamma_rips_filtrationLaw (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
  have hTameX : IsTameModule (superlevel f) (fun t => JoinedIn (superlevel f t)) :=
    t45gamma_super_isTameModule htame
  have hTameY : IsTameModule (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ) :=
    t45gamma_rips_isTameModule
  have hIL : StrongInterleavingAbove (superlevel f) (fun t => JoinedIn (superlevel f t))
      (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ)
      hLawX hLawY α (c * δ) hε := by
    by_cases hNE : ∃ x : X, α ≤ f x
    · exact t45gamma_instance hc hδ hδρ hLip hL hNE
    · have hdeg : ∀ x : X, f x < α := by
        intro x
        by_cases hx : α ≤ f x
        · exact absurd ⟨x, hx⟩ hNE
        · exact lt_of_not_ge hx
      exact t45w_degenerate_IL L f c δ α hc hδ hdeg
  obtain ⟨γ, hγ⟩ := theorem_4_5_gate_matching (superlevel f)
      (fun t => JoinedIn (superlevel f t))
      (fun t => {i : ↥L | t ≤ f (i : X)})
      (ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ)
      α (c * δ) hε hLawX hLawY hTameX hTameY hIL
  exact ⟨γ, hγ⟩
