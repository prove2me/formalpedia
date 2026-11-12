-- Prove2me | solution 1 for StabilityDichotomies.Solvability.stable_solvability_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:06:29.816326+00:00
-- url     : https://prove2.me/submissions/8f55318f-aa1d-4834-806f-b84cb8e61f0a

import Mathlib
import Definitions.Def_StabilityDichotomies_Solvability_Model
import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality
import Definitions.Def_StabilityDichotomies_Solvability_Stability
import Definitions.Def_StabilityDichotomies_Solvability_Incidence
import Theorems.Thm_StabilityDichotomies_Solvability_sparse_large_diameter_obstruction
import Theorems.Thm_StabilityDichotomies_Solvability_hamming_incidence_separation
import Theorems.Thm_StabilityDichotomies_Solvability_boolean_finite_duality_criterion

section
set_option autoImplicit false

namespace StabilityDichotomies.Dev.UpperBound

open StabilityDichotomies.Solvability
open scoped Classical

lemma pure_toReal {V : Type} [Fintype V] (x z : V → Bool) :
    ((PMF.pure x) z).toReal = if z = x then 1 else 0 := by
  rw [PMF.pure_apply]; split_ifs <;> simp

lemma wasserstein_pure {V : Type} [Fintype V] (x y : V → Bool) :
    wasserstein (PMF.pure x) (PMF.pure y) = hammingDist x y := by
  unfold wasserstein
  have hS : {t : ℝ | ∃ π ∈ FairProxy.ClosedFormDD.couplingSet
      (fun z => ((PMF.pure x) z).toReal) (fun z => ((PMF.pure y) z).toReal),
      t = ∑ a, ∑ b, π a b * hammingCost a b} = {(hammingDist x y : ℝ)} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨π, ⟨h1, h2, h3⟩, rfl⟩
      simp only [pure_toReal] at h1 h2
      have hr : ∀ s u, s ≠ x → π s u = 0 := by
        intro s u hs
        have := h1 s
        rw [if_neg hs] at this
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => (h3 s u).1)).1 this u
          (Finset.mem_univ _)
      have hc : ∀ s u, u ≠ y → π s u = 0 := by
        intro s u hu
        have := h2 u
        rw [if_neg hu] at this
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => (h3 s u).1)).1 this s
          (Finset.mem_univ _)
      have hxy : π x y = 1 := by
        have := h1 x
        rw [if_pos rfl, Finset.sum_eq_single y (fun u _ hu => hc x u hu)] at this
        · exact this
        · simp
      rw [Finset.sum_eq_single x]
      · rw [Finset.sum_eq_single y]
        · rw [hxy]; simp [hammingCost]
        · intro u _ hu; rw [hc x u hu]; simp
        · simp
      · intro s _ hs
        apply Finset.sum_eq_zero
        intro u _; rw [hr s u hs]; simp
      · simp
    · rintro rfl
      refine ⟨fun a b => if a = x ∧ b = y then 1 else 0, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro s
        simp only [pure_toReal]
        by_cases hs : s = x
        · subst hs; simp
        · simp [hs]
      · intro u
        simp only [pure_toReal]
        by_cases hu : u = y
        · subst hu; simp
        · simp [hu]
      · intro s u; show 0 ≤ (if s = x ∧ u = y then (1:ℝ) else 0) ∧ _ ≤ 1
        by_cases hh : s = x ∧ u = y <;> simp [hh]
      · rw [Finset.sum_eq_single x]
        · rw [Finset.sum_eq_single y]
          · simp [hammingCost]
          · intro u _ hu; simp [hu]
          · simp
        · intro s _ hs
          apply Finset.sum_eq_zero
          intro u _; simp [hs]
        · simp
  rw [hS, csInf_singleton]

lemma sens_bound {Γ : Language} (D : DeterministicSolver Γ)
    (hD : ∀ (V : Type) [Fintype V] (I : Instance Γ V) (c : Constraint Γ V),
      c ∈ I.constraints → hammingDist (D V I) (D V (I.delete c)) ≤ maxArity Γ)
    (V : Type) [Fintype V] (I : Instance Γ V) :
    averageSensitivity (deterministicLaw D) I ≤ (maxArity Γ : ℝ) := by
  unfold averageSensitivity
  split_ifs with h0
  · exact Nat.cast_nonneg _
  · have hpos : (0 : ℝ) < (I.constraints.card : ℝ) := by
      have : 0 < Multiset.card I.constraints :=
        Multiset.card_pos.2 h0
      exact_mod_cast this
    rw [div_le_iff₀ hpos]
    have := Multiset.sum_le_card_nsmul
      (I.constraints.map fun c => wasserstein (deterministicLaw D V I)
        (deterministicLaw D V (I.delete c))) (maxArity Γ : ℝ) (by
      intro t ht
      obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 ht
      show wasserstein (PMF.pure (D V I)) (PMF.pure (D V (I.delete c))) ≤ _
      rw [wasserstein_pure]
      exact_mod_cast hD V I c hc)
    simpa [mul_comm] using this

lemma main {Γ : Language} (D : DeterministicSolver Γ)
    (hsol : ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I → Solution I (D V I))
    (hD : ∀ (V : Type) [Fintype V] (I : Instance Γ V) (c : Constraint Γ V),
      c ∈ I.constraints → hammingDist (D V I) (D V (I.delete c)) ≤ maxArity Γ) :
    Solves (deterministicLaw D) ∧
      ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
        averageSensitivity (deterministicLaw D) I ≤ (maxArity Γ : ℝ) := by
  refine ⟨?_, fun V _ I _ => sens_bound D hD V I⟩
  intro V _ I hI x hx
  show (PMF.pure (D V I)) x = 0
  rw [PMF.pure_apply, if_neg]
  rintro rfl
  exact hx (hsol V I hI)

lemma arity_le {Γ : Language} {V : Type} (c : Constraint Γ V) :
    c.rel.val.arity ≤ maxArity Γ :=
  Finset.le_sup (f := Relation.arity) c.rel.property

lemma ham_le_range {V : Type} [Fintype V] {r : ℕ} (x y : V → Bool) (s : Fin r → V)
    (h : ∀ v, x v ≠ y v → v ∈ Finset.univ.image s) : hammingDist x y ≤ r := by
  unfold hammingDist
  calc _ ≤ (Finset.univ.image s).card :=
        Finset.card_le_card (fun v hv => h v (by simpa using hv))
    _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
    _ = r := by simp

lemma valid_case (Γ : Language) (b : Bool) (h : Valid Γ b) :
    ∃ D : DeterministicSolver Γ,
      Solves (deterministicLaw D) ∧
      ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
        averageSensitivity (deterministicLaw D) I ≤ (maxArity Γ : ℝ) := by
  refine ⟨fun V _ I => fun _ => b, main _ ?_ ?_⟩
  · intro V _ I _ c _
    exact h c.rel.val c.rel.property
  · intro V _ I c _
    simp

/-- the chosen CNF -/
noncomputable def cnf (pos : Bool) (R : Relation) : CNF R.arity :=
  if h : StrictEssential pos R then Classical.choose h else []

lemma cnf_spec (pos : Bool) (R : Relation) (h : StrictEssential pos R) :
    (∀ c ∈ cnf pos R, c.length = 1 ∨ ∀ l ∈ c, l.2 = pos) ∧
    ∀ x, x ∈ R.tuples ↔ CNFHolds (cnf pos R) x := by
  unfold cnf; rw [dif_pos h]; exact Classical.choose_spec h

def Z {Γ : Language} {V : Type} (pos : Bool) (I : Instance Γ V) (v : V) : Prop :=
  ∃ c ∈ I.constraints, ∃ i, c.scope i = v ∧ [(i, !pos)] ∈ cnf pos c.rel.val

noncomputable def alg {Γ : Language} (pos : Bool) : DeterministicSolver Γ :=
  fun V _ I v => if Z pos I v then !pos else pos

lemma Z_mono {Γ : Language} {V : Type} (pos : Bool) (I : Instance Γ V) (c : Constraint Γ V)
    (v : V) (h : Z pos (I.delete c) v) : Z pos I v := by
  obtain ⟨c', hc', i, hi, hu⟩ := h
  exact ⟨c', Multiset.mem_of_mem_erase hc', i, hi, hu⟩

lemma Z_solution {Γ : Language} {V : Type} (pos : Bool) (I : Instance Γ V) (y : V → Bool)
    (hy : Solution I y) (v : V) (h : Z pos I v) (hs : ∀ R ∈ Γ.relations, StrictEssential pos R) :
    y v = !pos := by
  obtain ⟨c, hc, i, hi, hu⟩ := h
  have := ((cnf_spec pos _ (hs _ c.rel.property)).2 _).1 (hy c hc) _ hu
  obtain ⟨l, hl, hl2⟩ := this
  simp at hl; subst hl
  simpa [hi] using hl2

lemma strict_case (Γ : Language) (pos : Bool)
    (hs : ∀ R ∈ Γ.relations, StrictEssential pos R) :
    ∃ D : DeterministicSolver Γ,
      Solves (deterministicLaw D) ∧
      ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
        averageSensitivity (deterministicLaw D) I ≤ (maxArity Γ : ℝ) := by
  refine ⟨alg pos, main _ ?_ ?_⟩
  · intro V _ I ⟨y, hy⟩ c hc
    have hsp := cnf_spec pos _ (hs _ c.rel.property)
    show (fun i => alg pos V I (c.scope i)) ∈ c.rel.val.tuples
    rw [hsp.2]
    intro cl hcl
    obtain ⟨l, hl, hyl⟩ := (hsp.2 _).1 (hy c hc) cl hcl
    by_cases hlp : l.2 = pos
    · refine ⟨l, hl, ?_⟩
      show alg pos V I (c.scope l.1) = l.2
      unfold alg
      by_cases hz : Z pos I (c.scope l.1)
      · exfalso
        have := Z_solution pos I y hy _ hz hs
        have hyl' : y (c.scope l.1) = l.2 := hyl
        rw [hyl', hlp] at this
        cases pos <;> simp at this
      · simp [hz, hlp]
    · have hcl1 : cl = [l] := by
        rcases hsp.1 cl hcl with hlen | hall
        · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hlen
          simp at hl; simp [hl]
        · exact absurd (hall l hl) hlp
      have hn : l.2 = !pos := by cases hb : l.2 <;> cases pos <;> simp_all
      refine ⟨l, hl, ?_⟩
      show alg pos V I (c.scope l.1) = l.2
      unfold alg
      have hz : Z pos I (c.scope l.1) := ⟨c, hc, l.1, rfl, by rw [← hn, ← hcl1]; exact hcl⟩
      simp [hz, hn]
  · intro V _ I c hc
    refine le_trans (ham_le_range (r := c.rel.val.arity) _ _ c.scope ?_) (arity_le c)
    intro v hv
    simp only [alg] at hv
    by_cases h1 : Z pos I v
    · obtain ⟨c', hc', i, hi, hu⟩ := h1
      by_cases hcc : c' = c
      · subst hcc; exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
      · exfalso; apply hv
        have : Z pos (I.delete c) v :=
          ⟨c', (Multiset.mem_erase_of_ne hcc).2 hc', i, hi, hu⟩
        have h1' : Z pos I v := ⟨c', hc', i, hi, hu⟩
        simp [h1', this]
    · exfalso; apply hv
      have : ¬ Z pos (I.delete c) v := fun h => h1 (Z_mono pos I c v h)
      simp [h1, this]

theorem upper_bound (Γ : Language)
    (h : Valid Γ false ∨ Valid Γ true ∨ StrictEssentialLanguage Γ true ∨ StrictEssentialLanguage Γ false) :
    ∃ D : DeterministicSolver Γ,
      Solves (deterministicLaw D) ∧
      ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
        averageSensitivity (deterministicLaw D) I ≤ (maxArity Γ : ℝ) := by
  rcases h with h | h | h | h
  · exact valid_case Γ false h
  · exact valid_case Γ true h
  · exact strict_case Γ true h
  · exact strict_case Γ false h

end StabilityDichotomies.Dev.UpperBound
end

section
set_option autoImplicit false

namespace StabilityDichotomies.Dev.LowerBound

open StabilityDichotomies.Solvability

section Graph

variable {V : Type} {G : SimpleGraph V}

lemma edist_start_getVert : ∀ {u v : V} (p : G.Walk u v) (i : ℕ), i ≤ p.length →
    G.edist u (p.getVert i) ≤ i
  | u, _, .nil, i, h => by
      have : i = 0 := by simpa using h
      subst this; simp
  | u, _, .cons h p, 0, _ => by simp
  | u, _, .cons (v := w) h p, i + 1, hi => by
      have hi' : i ≤ p.length := by simpa using hi
      have ih := edist_start_getVert p i hi'
      have h1 : G.edist u w ≤ 1 := by
        simpa using SimpleGraph.edist_le (G := G) (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)
      have := SimpleGraph.edist_triangle (G := G) (u := u) (v := w) (w := p.getVert i)
      simp only [SimpleGraph.Walk.getVert_cons_succ]
      calc G.edist u (p.getVert i) ≤ G.edist u w + G.edist w (p.getVert i) := this
        _ ≤ 1 + i := add_le_add h1 ih
        _ = ((i + 1 : ℕ) : ℕ∞) := by push_cast; ring

lemma edist_getVert_end : ∀ {u v : V} (p : G.Walk u v) (j : ℕ), j ≤ p.length →
    G.edist (p.getVert j) v ≤ ((p.length - j : ℕ) : ℕ∞)
  | u, _, .nil, j, h => by
      have : j = 0 := by simpa using h
      subst this; simp
  | u, _, .cons (v := w) h p, 0, _ => by
      simpa using SimpleGraph.edist_le (G := G) (SimpleGraph.Walk.cons h p)
  | u, _, .cons (v := w) h p, j + 1, hj => by
      have hj' : j ≤ p.length := by simpa using hj
      have ih := edist_getVert_end p j hj'
      simpa using ih

lemma edist_getVert_ge {u v : V} (p : G.Walk u v) (hp : (p.length : ℕ∞) = G.edist u v)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    ((j - i : ℕ) : ℕ∞) ≤ G.edist (p.getVert i) (p.getVert j) := by
  have h1 := edist_start_getVert p i (hij.trans hj)
  have h2 := edist_getVert_end p j hj
  have h3 : G.edist u v ≤ G.edist u (p.getVert i) + (G.edist (p.getVert i) (p.getVert j)
      + G.edist (p.getVert j) v) :=
    (SimpleGraph.edist_triangle (v := p.getVert i)).trans
      (add_le_add_right (SimpleGraph.edist_triangle (v := p.getVert j)) _)
  rw [← hp] at h3
  generalize G.edist (p.getVert i) (p.getVert j) = e at *
  induction e using ENat.recTopCoe with
  | top => simp
  | coe k =>
    have h4 : (p.length : ℕ∞) ≤ (i : ℕ∞) + (k + ((p.length - j : ℕ) : ℕ∞)) :=
      h3.trans (add_le_add h1 (add_le_add_right h2 _))
    have h5 : p.length ≤ i + (k + (p.length - j)) := by exact_mod_cast h4
    exact_mod_cast (by omega : j - i ≤ k)

lemma getVert_side {W : Type} {G : SimpleGraph (V ⊕ W)}
    (hbip : ∀ a b, G.Adj a b → a.isRight ≠ b.isRight) {u v : V ⊕ W} (p : G.Walk u v) :
    ∀ i, i ≤ p.length → (p.getVert i).isRight = Bool.xor u.isRight (decide (i % 2 = 1))
  | 0, _ => by simp
  | i + 1, hi => by
      have ih := getVert_side hbip p i (by omega)
      have hadj := hbip _ _ (p.adj_getVert_succ (by omega : i < p.length))
      have : (p.getVert (i + 1)).isRight = !(p.getVert i).isRight := by
        revert hadj; cases (p.getVert i).isRight <;> cases (p.getVert (i+1)).isRight <;> simp
      rw [this, ih]
      have : (i + 1) % 2 = 1 ↔ ¬ (i % 2 = 1) := by omega
      simp only [decide_eq_decide.mpr this, decide_not]
      cases u.isRight <;> cases decide (i % 2 = 1) <;> simp

lemma spread {V W : Type} [Finite V] [Finite W] (G : SimpleGraph (V ⊕ W))
    (hbip : ∀ a b, G.Adj a b → a.isRight ≠ b.isRight) (hconn : G.Connected)
    (N : ℕ) (hd : ((2 * N : ℕ) : ℕ∞) ≤ G.ediam) :
    ∃ c : Fin N → W, ∀ a b : Fin N, a.val ≤ b.val →
      ((2 * (b.val - a.val) : ℕ) : ℕ∞) ≤ G.edist (.inr (c a)) (.inr (c b)) := by
  have : Nonempty (V ⊕ W) := hconn.nonempty
  have : Finite (V ⊕ W) := inferInstance
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_edist u v
  have hD : 2 * N ≤ p.length := by
    have : ((2 * N : ℕ) : ℕ∞) ≤ (p.length : ℕ∞) := by rw [hp, huv]; exact hd
    exact_mod_cast this
  set s : ℕ := if u.isRight then 0 else 1 with hs
  have hside : ∀ a : Fin N, (p.getVert (2 * a.val + s)).isRight = true := by
    intro a
    have h := getVert_side hbip p (2 * a.val + s) (by
      have := a.2; simp only [hs]; split_ifs <;> omega)
    rw [h]
    simp only [hs]
    split_ifs with hu
    · simp [hu]
    · have : u.isRight = false := by simpa using hu
      simp [this]
  have hex : ∀ a : Fin N, ∃ w : W, p.getVert (2 * a.val + s) = .inr w := by
    intro a
    have := hside a
    rcases hx : p.getVert (2 * a.val + s) with x | w
    · rw [hx] at this; simp at this
    · exact ⟨w, rfl⟩
  choose c hc using hex
  refine ⟨c, fun a b hab => ?_⟩
  have := edist_getVert_ge p hp (i := 2 * a.val + s) (j := 2 * b.val + s) (by omega)
    (by have := b.2; simp only [hs]; split_ifs <;> omega)
  rw [hc a, hc b] at this
  have e : 2 * b.val + s - (2 * a.val + s) = 2 * (b.val - a.val) := by omega
  rwa [e] at this

end Graph

section Wass

open scoped Classical

variable {V : Type} [Fintype V]

lemma pmf_sum_toReal {α : Type} [Fintype α] (μ : PMF α) : ∑ x, (μ x).toReal = 1 := by
  have h : ∑ x, μ x = 1 := by simpa [tsum_fintype] using μ.tsum_coe
  have := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top μ x), ENNReal.toReal_one] at this

lemma pmf_toReal_le_one {α : Type} (μ : PMF α) (x : α) : (μ x).toReal ≤ 1 := by
  have := ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ x)
  simpa using this

lemma wasserstein_nonneg (μ ν : PMF (V → Bool)) : 0 ≤ wasserstein μ ν := by
  apply Real.sInf_nonneg
  rintro t ⟨π, ⟨_, _, hπ⟩, rfl⟩
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (hπ x y).1 (by unfold hammingCost; positivity)

lemma wasserstein_lipschitz (μ ν : PMF (V → Bool)) (f : (V → Bool) → ℝ)
    (hf : ∀ x y, |f x - f y| ≤ (hammingDist x y : ℝ)) :
    |∑ x, (μ x).toReal * f x - ∑ y, (ν y).toReal * f y| ≤ wasserstein μ ν := by
  have hne : {t : ℝ | ∃ π ∈ FairProxy.ClosedFormDD.couplingSet
      (fun x => (μ x).toReal) (fun y => (ν y).toReal),
      t = ∑ x, ∑ y, π x y * hammingCost x y}.Nonempty := by
    refine ⟨_, fun x y => (μ x).toReal * (ν y).toReal, ⟨?_, ?_, ?_⟩, rfl⟩
    · intro x
      rw [← Finset.mul_sum, pmf_sum_toReal, mul_one]
    · intro y
      rw [← Finset.sum_mul, pmf_sum_toReal, one_mul]
    · intro x y
      refine ⟨mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ?_⟩
      calc (μ x).toReal * (ν y).toReal ≤ 1 * 1 :=
            mul_le_mul (pmf_toReal_le_one _ _) (pmf_toReal_le_one _ _)
              ENNReal.toReal_nonneg zero_le_one
        _ = 1 := one_mul 1
  apply le_csInf hne
  rintro t ⟨π, ⟨h1, h2, h3⟩, rfl⟩
  have e1 : ∑ x, (μ x).toReal * f x = ∑ x, ∑ y, π x y * f x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, h1]
  have e2 : ∑ y, (ν y).toReal * f y = ∑ x, ∑ y, π x y * f y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, h2]
  rw [e1, e2, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  calc |∑ x, ∑ y, π x y * (f x - f y)|
      ≤ ∑ x, |∑ y, π x y * (f x - f y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, |π x y * (f x - f y)| :=
        Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, π x y * hammingCost x y := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (h3 x y).1]
        exact mul_le_mul_of_nonneg_left (hf x y) (h3 x y).1

lemma wass_pair (μi μj ν : PMF (V → Bool)) (f : (V → Bool) → ℝ)
    (hf : ∀ x y, |f x - f y| ≤ (hammingDist x y : ℝ)) (t : ℝ)
    (hi : ∀ x, μi x ≠ 0 → f x = 0) (hj : ∀ x, μj x ≠ 0 → t ≤ f x) :
    t ≤ wasserstein μi ν + wasserstein μj ν := by
  have hEi : ∑ x, (μi x).toReal * f x = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h : μi x = 0
    · simp [h]
    · rw [hi x h, mul_zero]
  have hEj : t ≤ ∑ x, (μj x).toReal * f x := by
    calc t = ∑ x, (μj x).toReal * t := by rw [← Finset.sum_mul, pmf_sum_toReal, one_mul]
      _ ≤ _ := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases h : μj x = 0
        · simp [h]
        · exact mul_le_mul_of_nonneg_left (hj x h) ENNReal.toReal_nonneg
  have h1 := wasserstein_lipschitz μi ν f hf
  have h2 := wasserstein_lipschitz μj ν f hf
  rw [hEi] at h1
  have := (abs_le.mp h1).1
  have := (abs_le.mp h2).1
  have := (abs_le.mp h2).2
  linarith

end Wass

section Pad

open scoped Classical

variable {Γ : Language} {m n : ℕ}

def padC (hmn : m ≤ n) (c : Constraint Γ (Fin m)) : Constraint Γ (Fin n) :=
  ⟨c.rel, Fin.castLE hmn ∘ c.scope⟩

def pad (hmn : m ≤ n) (I : Instance Γ (Fin m)) : Instance Γ (Fin n) :=
  ⟨I.constraints.map (padC hmn)⟩

lemma padC_injective (hmn : m ≤ n) : Function.Injective (padC (Γ := Γ) hmn) := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ h
  simp only [padC, Constraint.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have h3 : s = s' := by
    funext i
    have := congrFun (eq_of_heq h2) i
    exact Fin.castLE_injective hmn this
  rw [h3]

lemma pad_delete (hmn : m ≤ n) (I : Instance Γ (Fin m)) (c : Constraint Γ (Fin m)) :
    (pad hmn I).delete (padC hmn c) = pad hmn (I.delete c) := by
  simp only [pad, Instance.delete, Instance.mk.injEq]
  exact (Multiset.map_erase _ (padC_injective hmn) _ _).symm

lemma solution_pad {hmn : m ≤ n} {I : Instance Γ (Fin m)} {x : Fin n → Bool}
    (h : Solution (pad hmn I) x) : Solution I (x ∘ Fin.castLE hmn) := by
  intro c hc
  exact h (padC hmn c) (Multiset.mem_map_of_mem _ hc)

lemma satisfiable_pad (hmn : m ≤ n) {I : Instance Γ (Fin m)} (h : Satisfiable I) :
    Satisfiable (pad hmn I) := by
  obtain ⟨x, hx⟩ := h
  have hext : ∀ k : Fin m, (fun j : Fin n => if hj : j.val < m then x ⟨j.val, hj⟩ else false)
      (Fin.castLE hmn k) = x k := by
    intro k
    simp [Fin.castLE]
  refine ⟨fun j => if hj : j.val < m then x ⟨j.val, hj⟩ else false, ?_⟩
  intro c hc
  obtain ⟨c0, hc0, rfl⟩ := Multiset.mem_map.mp hc
  have := hx c0 hc0
  unfold Constraint.Satisfied at this ⊢
  have e : (fun i : Fin c0.rel.val.arity =>
      (fun j : Fin n => if hj : j.val < m then x ⟨j.val, hj⟩ else false)
      (Fin.castLE hmn (c0.scope i))) = fun i => x (c0.scope i) := by
    funext i
    exact hext _
  exact e ▸ this

lemma hammingDist_comp_castLE (hmn : m ≤ n) (x y : Fin n → Bool) :
    hammingDist (x ∘ Fin.castLE hmn) (y ∘ Fin.castLE hmn) ≤ hammingDist x y := by
  unfold hammingDist
  refine Finset.card_le_card_of_injOn (Fin.castLE hmn) ?_ (Fin.castLE_injective hmn).injOn
  intro i hi
  simpa using hi

def distTo (hmn : m ≤ n) (S : Finset (Fin m → Bool)) (hS : S.Nonempty)
    (x : Fin n → Bool) : ℕ :=
  S.inf' hS fun y => hammingDist (x ∘ Fin.castLE hmn) y

lemma distTo_lip (hmn : m ≤ n) (S : Finset (Fin m → Bool)) (hS : S.Nonempty)
    (x x' : Fin n → Bool) :
    distTo hmn S hS x ≤ distTo hmn S hS x' + hammingDist x x' := by
  obtain ⟨y, hy, hmin⟩ := Finset.exists_mem_eq_inf' hS (fun y => hammingDist (x' ∘ Fin.castLE hmn) y)
  unfold distTo
  rw [hmin]
  calc S.inf' hS (fun y => hammingDist (x ∘ Fin.castLE hmn) y)
      ≤ hammingDist (x ∘ Fin.castLE hmn) y := Finset.inf'_le _ hy
    _ ≤ hammingDist (x ∘ Fin.castLE hmn) (x' ∘ Fin.castLE hmn) + hammingDist (x' ∘ Fin.castLE hmn) y :=
        hammingDist_triangle _ _ _
    _ ≤ _ := by
        have := hammingDist_comp_castLE hmn x x'
        omega

lemma distTo_zero (hmn : m ≤ n) (S : Finset (Fin m → Bool)) (hS : S.Nonempty)
    (x : Fin n → Bool) (h : x ∘ Fin.castLE hmn ∈ S) : distTo hmn S hS x = 0 := by
  have := Finset.inf'_le (fun y => hammingDist (x ∘ Fin.castLE hmn) y) h
  simp only [hammingDist_self] at this
  unfold distTo
  omega

lemma le_distTo (hmn : m ≤ n) (S : Finset (Fin m → Bool)) (hS : S.Nonempty)
    (x : Fin n → Bool) (t : ℕ) (h : ∀ y ∈ S, t ≤ hammingDist y (x ∘ Fin.castLE hmn)) :
    t ≤ distTo hmn S hS x := by
  unfold distTo
  apply (Finset.le_inf'_iff hS _).mpr
  intro y hy
  rw [hammingDist_comm]
  exact h y hy

end Pad

section Pair

open scoped Classical

variable {Γ : Language} {m n : ℕ}

lemma occ_mem {I : Instance Γ (Fin m)} (o : Occurrence I) :
    occurrenceConstraint I o ∈ I.constraints := by
  have : occurrenceConstraint I o ∈ I.constraints.toList := List.get_mem _ _
  exact Multiset.mem_toList.mp this

lemma delete_comm (I : Instance Γ (Fin m)) (c c' : Constraint Γ (Fin m)) :
    (I.delete c).delete c' = (I.delete c').delete c := by
  simp only [Instance.delete, Instance.mk.injEq]
  exact Multiset.erase_comm _ _ _

lemma pair_bound (hmn : m ≤ n) (F : Instance Γ (Fin m)) (hF : MinimallyUnsatisfiable F)
    (A : Solver Γ) (hA : Solves A) (o o' : Occurrence F) (hne : o ≠ o') (t : ℕ)
    (ht : ((2 * t : ℕ) : ℕ∞) ≤ (incidenceGraph F).edist (.inr o) (.inr o')) :
    (t : ℝ) ≤
      wasserstein (A (Fin n) (pad hmn (F.delete (occurrenceConstraint F o))))
        (A (Fin n) ((pad hmn (F.delete (occurrenceConstraint F o))).delete
          (padC hmn (occurrenceConstraint F o')))) +
      wasserstein (A (Fin n) (pad hmn (F.delete (occurrenceConstraint F o'))))
        (A (Fin n) ((pad hmn (F.delete (occurrenceConstraint F o'))).delete
          (padC hmn (occurrenceConstraint F o)))) := by
  set c := occurrenceConstraint F o with hc
  set c' := occurrenceConstraint F o' with hc'
  have hsat : Satisfiable (F.delete c) := hF.2 c (occ_mem o)
  have hsat' : Satisfiable (F.delete c') := hF.2 c' (occ_mem o')
  rw [pad_delete, pad_delete, delete_comm F c c']
  set ν := A (Fin n) (pad hmn ((F.delete c').delete c)) with hν
  set S : Finset (Fin m → Bool) := Finset.univ.filter (fun y => Solution (F.delete c) y) with hS
  have hSne : S.Nonempty := by
    obtain ⟨y, hy⟩ := hsat
    exact ⟨y, by simp [hS, hy]⟩
  have hlip : ∀ x y : Fin n → Bool,
      |((distTo hmn S hSne x : ℕ) : ℝ) - (distTo hmn S hSne y : ℕ)| ≤ (hammingDist x y : ℝ) := by
    intro x y
    have h1 := distTo_lip hmn S hSne x y
    have h2 := distTo_lip hmn S hSne y x
    rw [hammingDist_comm y x] at h2
    rw [abs_le]
    constructor
    · have : ((distTo hmn S hSne y : ℕ) : ℝ) ≤ (distTo hmn S hSne x : ℕ) + (hammingDist x y : ℝ) := by
        exact_mod_cast h2
      linarith
    · have : ((distTo hmn S hSne x : ℕ) : ℝ) ≤ (distTo hmn S hSne y : ℕ) + (hammingDist x y : ℝ) := by
        exact_mod_cast h1
      linarith
  refine wass_pair _ _ ν (fun x => (distTo hmn S hSne x : ℝ)) hlip t ?_ ?_
  · intro x hx
    have hsolve : Solution (pad hmn (F.delete c)) x := by
      by_contra hcon
      exact hx (hA (Fin n) _ (satisfiable_pad hmn hsat) x hcon)
    have := distTo_zero hmn S hSne x (by simpa [hS] using solution_pad hsolve)
    simp [this]
  · intro x hx
    have hsolve : Solution (pad hmn (F.delete c')) x := by
      by_contra hcon
      exact hx (hA (Fin n) _ (satisfiable_pad hmn hsat') x hcon)
    have hy := solution_pad hsolve
    have : t ≤ distTo hmn S hSne x := by
      apply le_distTo
      intro y hyS
      have hyS' : Solution (F.delete c) y := by simpa [hS] using hyS
      have := hamming_incidence_separation Γ (Fin m) F hF o o' hne y _ hyS' hy
      have h2 := ht.trans this
      have : 2 * t ≤ 2 * hammingDist y (x ∘ Fin.castLE hmn) := by exact_mod_cast h2
      omega
    exact_mod_cast this

end Pair

section Count

lemma sum_range_sub (M : ℕ) : ∑ a ∈ Finset.range M, ((M : ℝ) - a) = M * (M + 1) / 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have h : ∀ a : ℕ, (((M + 1 : ℕ) : ℝ) - a) = ((M : ℝ) - a) + 1 := by
      intro a; push_cast; ring
    simp_rw [h, Finset.sum_add_distrib]
    rw [ih]
    simp
    ring

lemma double_sum_lower (D : ℕ → ℕ → ℝ) (hD0 : ∀ a b, 0 ≤ D a b) (K : ℕ)
    (hD : ∀ a b, a < b → b < K → (b : ℝ) - a ≤ D a b + D b a) :
    ∀ M, M ≤ K → ((M : ℝ) ^ 3 - M) / 6 ≤ ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M, D a b := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro hM
    have ih' := ih (by omega)
    have h1 : ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1), D a b
        = ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M, D a b
          + ∑ a ∈ Finset.range M, (D a M + D M a) + D M M := by
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
      ring
    have h2 : ∑ a ∈ Finset.range M, ((M : ℝ) - a) ≤ ∑ a ∈ Finset.range M, (D a M + D M a) :=
      Finset.sum_le_sum fun a ha => hD a M (Finset.mem_range.mp ha) (by omega)
    rw [sum_range_sub] at h2
    have := hD0 M M
    rw [h1]
    push_cast
    nlinarith

end Count

section Sens

open scoped Classical

variable {Γ : Language} {m n : ℕ}

lemma finsum_list_get {α : Type} (L : List α) (h : α → ℝ) :
    ∑ j : Fin L.length, h (L.get j) = (L.map h).sum := by
  rw [← List.sum_ofFn]
  have e : (fun j : Fin L.length => h (L.get j)) = h ∘ L.get := rfl
  rw [e, ← List.map_ofFn, List.ofFn_get]

lemma asens_ge (hmn : m ≤ n) (F : Instance Γ (Fin m)) (A : Solver Γ) (o : Occurrence F)
    (hne : (pad hmn (F.delete (occurrenceConstraint F o))).constraints ≠ 0) :
    (∑ o' ∈ Finset.univ.erase o,
        wasserstein (A (Fin n) (pad hmn (F.delete (occurrenceConstraint F o))))
          (A (Fin n) ((pad hmn (F.delete (occurrenceConstraint F o))).delete
            (padC hmn (occurrenceConstraint F o'))))) /
      ((pad hmn (F.delete (occurrenceConstraint F o))).constraints.card : ℝ)
    ≤ averageSensitivity A (pad hmn (F.delete (occurrenceConstraint F o))) := by
  set G := pad hmn (F.delete (occurrenceConstraint F o)) with hG
  set g : Constraint Γ (Fin n) → ℝ := fun c => wasserstein (A (Fin n) G) (A (Fin n) (G.delete c))
    with hg
  set L := F.constraints.toList with hLdef
  have hk : o.val < L.length := o.2
  have hperm : (L[o.val] :: L.eraseIdx o.val).Perm L := List.getElem_cons_eraseIdx_perm hk
  have hFc : F.constraints = (L : Multiset (Constraint Γ (Fin m))) := (Multiset.coe_toList _).symm
  have hocc : occurrenceConstraint F o = L[o.val] := rfl
  have herase : F.constraints.erase (occurrenceConstraint F o) =
      ((L.eraseIdx o.val : List (Constraint Γ (Fin m))) : Multiset _) := by
    rw [hocc]
    refine (congrArg (fun M : Multiset (Constraint Γ (Fin m)) => M.erase L[o.val]) hFc).trans ?_
    have : (L : Multiset (Constraint Γ (Fin m))) =
        L[o.val] ::ₘ ((L.eraseIdx o.val : List (Constraint Γ (Fin m))) : Multiset _) := by
      rw [Multiset.cons_coe]
      exact (Multiset.coe_eq_coe.mpr hperm.symm)
    rw [this, Multiset.erase_cons_head]
  have hGc : G.constraints = ((L.eraseIdx o.val).map (padC hmn) : List _) := by
    simp only [hG, pad, Instance.delete]
    rw [herase]
    rfl
  have hsum1 : (G.constraints.map g).sum = ((L.eraseIdx o.val).map (g ∘ padC hmn)).sum := by
    rw [hGc, Multiset.map_coe, Multiset.sum_coe, List.map_map]
  have hsum2 : (L.map (g ∘ padC hmn)).sum
      = (g ∘ padC hmn) L[o.val] + ((L.eraseIdx o.val).map (g ∘ padC hmn)).sum := by
    rw [← (hperm.map (g ∘ padC hmn)).sum_eq]
    simp
  have hsum3 : ∑ j : Fin L.length, (g ∘ padC hmn) (L.get j) = (L.map (g ∘ padC hmn)).sum :=
    finsum_list_get L _
  have hsum4 := Finset.add_sum_erase (Finset.univ : Finset (Fin L.length))
    (fun j => (g ∘ padC hmn) (L.get j)) (Finset.mem_univ o)
  have hfinal : ∑ o' ∈ Finset.univ.erase o, g (padC hmn (occurrenceConstraint F o'))
      = (G.constraints.map g).sum := by
    rw [hsum1]
    have : ∑ o' ∈ Finset.univ.erase o, g (padC hmn (occurrenceConstraint F o'))
        = ∑ o' ∈ Finset.univ.erase o, (g ∘ padC hmn) (L.get o') := rfl
    rw [this]
    have h5 : (g ∘ padC hmn) (L.get o) = (g ∘ padC hmn) L[o.val] := rfl
    simp only [h5] at hsum4
    linarith
  unfold averageSensitivity
  rw [if_neg hne]
  exact le_of_eq (by rw [hfinal])

end Sens

open scoped Classical in
theorem lower_bound (Γ : Language) (hΓ : ¬ FiniteDuality Γ) :
    ∀ A : Solver Γ, Solves A →
      ∀ n : ℕ, 8 ≤ n → ∃ I : Instance Γ (Fin n),
        Satisfiable I ∧
        (n : ℝ) / (96 * (kappa Γ : ℝ)) ≤ averageSensitivity A I := by
  intro A hA n hn
  obtain ⟨m, F, hmin, hconn, hm, hcard, hdiam⟩ :=
    sparse_large_diameter_obstruction Γ hΓ (n / 4) (by omega)
  have hN2 : 2 ≤ n / 4 := by omega
  have hmn : m ≤ n := by omega
  set N := n / 4 with hNdef
  have hbip : ∀ a b, (incidenceGraph F).Adj a b → a.isRight ≠ b.isRight := by
    intro a b hab
    cases a <;> cases b <;> simp_all [incidenceGraph, IncAdjacent]
  obtain ⟨c, hc⟩ := spread (incidenceGraph F) hbip hconn N hdiam
  have hcne : ∀ a b : Fin N, a ≠ b → c a ≠ c b := by
    intro a b hab heq
    have key : ∀ a b : Fin N, a < b → c a = c b → False := by
      intro a b hlt h
      have := hc a b hlt.le
      rw [h] at this
      simp only [SimpleGraph.edist_self, nonpos_iff_eq_zero, Nat.cast_eq_zero] at this
      have := a.2; have := b.2
      have : (a : ℕ) < b := hlt
      omega
    rcases lt_or_gt_of_ne hab with h | h
    · exact key a b h heq
    · exact key b a h heq.symm
  have hcinj : Function.Injective c := by
    intro a b h
    by_contra hab
    exact hcne a b hab h
  obtain ⟨G, hG⟩ : ∃ G : Fin N → Instance Γ (Fin n),
      ∀ a, G a = pad hmn (F.delete (occurrenceConstraint F (c a))) := ⟨_, fun _ => rfl⟩
  obtain ⟨Wf, hWf⟩ : ∃ Wf : Fin N → Occurrence F → ℝ, ∀ a o,
      Wf a o = wasserstein (A (Fin n) (G a))
        (A (Fin n) ((G a).delete (padC hmn (occurrenceConstraint F o)))) := ⟨_, fun _ _ => rfl⟩
  have hW0 : ∀ a o, 0 ≤ Wf a o := fun a o => by rw [hWf]; exact wasserstein_nonneg _ _
  have hpair : ∀ a b : Fin N, a < b → ((b : ℕ) : ℝ) - (a : ℕ) ≤ Wf a (c b) + Wf b (c a) := by
    intro a b hab
    have h := pair_bound (n := n) hmn F hmin A hA (c a) (c b) (hcne a b hab.ne) (b.val - a.val)
      (hc a b hab.le)
    rw [hWf, hWf, hG, hG]
    have e : (((b.val - a.val : ℕ)) : ℝ) = (b : ℕ) - (a : ℕ) := by
      rw [Nat.cast_sub (le_of_lt hab)]
    rw [e] at h
    exact h
  -- the double sum
  obtain ⟨D, hD, hD0⟩ : ∃ D : ℕ → ℕ → ℝ, (∀ a b : Fin N, D a b = if a = b then 0 else Wf a (c b))
      ∧ ∀ a b, 0 ≤ D a b :=
    ⟨fun a b => if h : a < N ∧ b < N then
      (if (⟨a, h.1⟩ : Fin N) = ⟨b, h.2⟩ then 0 else Wf ⟨a, h.1⟩ (c ⟨b, h.2⟩)) else 0,
      fun a b => by simp [a.2, b.2],
      fun a b => by
        dsimp only
        split_ifs <;> first | exact le_refl _ | exact hW0 _ _⟩
  have hDpair : ∀ a b, a < b → b < N → (b : ℝ) - a ≤ D a b + D b a := by
    intro a b hab hb
    have h := hpair ⟨a, by omega⟩ ⟨b, hb⟩ hab
    have h1 := hD ⟨a, by omega⟩ ⟨b, hb⟩
    have h2 := hD ⟨b, hb⟩ ⟨a, by omega⟩
    simp only [Fin.mk.injEq] at h1 h2
    rw [if_neg hab.ne] at h1
    rw [if_neg hab.ne'] at h2
    simp only at h h1 h2
    rw [h1, h2]
    exact h
  have hlow := double_sum_lower D hD0 N hDpair N le_rfl
  have hconv : ∑ a : Fin N, ∑ b : Fin N, D a b =
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, D a b := by
    rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range N, D a b)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun b => D a b)]
  rw [← hconv] at hlow
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨a, -, ha⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin N)))
    (f := fun _ => ((N : ℝ) ^ 2 - 1) / 6) (g := fun a : Fin N => ∑ b : Fin N, D (a : ℕ) (b : ℕ))
    ⟨(⟨0, by omega⟩ : Fin N), Finset.mem_univ _⟩ (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc (N : ℝ) * (((N : ℝ) ^ 2 - 1) / 6) = ((N : ℝ) ^ 3 - N) / 6 := by ring
        _ ≤ _ := hlow)
  have hDa : ∑ b : Fin N, D (a : ℕ) (b : ℕ) = ∑ b ∈ Finset.univ.erase a, Wf a (c b) := by
    have h0 : D (a : ℕ) (a : ℕ) = 0 := by rw [hD, if_pos rfl]
    rw [← Finset.sum_erase Finset.univ (f := fun b : Fin N => D (a : ℕ) (b : ℕ)) h0]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hD, if_neg (Finset.ne_of_mem_erase hb).symm]
  have hsub : ∑ b ∈ Finset.univ.erase a, Wf a (c b) ≤ ∑ o ∈ Finset.univ.erase (c a), Wf a o := by
    rw [← Finset.sum_image (f := fun o => Wf a o) (s := Finset.univ.erase a) (g := c)
      (fun x _ y _ h => hcinj h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun o _ _ => hW0 a o)
    intro o ho
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ho
    exact Finset.mem_erase.mpr ⟨fun h => (Finset.ne_of_mem_erase hb) (hcinj h), Finset.mem_univ _⟩
  have hS : (((N : ℝ) ^ 2 - 1) / 6) ≤ ∑ o ∈ Finset.univ.erase (c a), Wf a o :=
    ha.trans (hDa.le.trans hsub)
  -- cardinalities
  have hFcard : 2 ≤ F.constraints.card := by
    have h1 := Fintype.card_le_of_injective c hcinj
    rw [Fintype.card_fin] at h1
    have h2 : Fintype.card (Occurrence F) = F.constraints.card := by
      rw [Fintype.card_fin, Multiset.length_toList]
    omega
  have hGcard : (pad hmn (F.delete (occurrenceConstraint F (c a)))).constraints.card
      = F.constraints.card - 1 := by
    simp only [pad, Instance.delete, Multiset.card_map]
    exact Multiset.card_erase_of_mem (occ_mem _)
  have hne : (pad hmn (F.delete (occurrenceConstraint F (c a)))).constraints ≠ 0 := by
    intro h
    rw [h] at hGcard
    simp at hGcard
    omega
  have hκ : 1 ≤ kappa Γ := by
    unfold kappa
    obtain ⟨R0, hR0⟩ := Γ.relations_nonempty
    have : 0 < ∑ R ∈ Γ.relations, 2 ^ R.arity * R.tuples.card ^ 2 := by
      apply Finset.sum_pos _ ⟨R0, hR0⟩
      intro R _
      have := Finset.card_pos.mpr R.tuples_nonempty
      positivity
    omega
  have hκr : (1 : ℝ) ≤ (kappa Γ : ℝ) := by exact_mod_cast hκ
  have hcardG : ((pad hmn (F.delete (occurrenceConstraint F (c a)))).constraints.card : ℝ)
      ≤ (kappa Γ : ℝ) * N := by
    have : (pad hmn (F.delete (occurrenceConstraint F (c a)))).constraints.card ≤ kappa Γ * N := by
      omega
    exact_mod_cast this
  have hcardpos : (0 : ℝ) < ((pad hmn (F.delete (occurrenceConstraint F (c a)))).constraints.card : ℝ) := by
    have : 0 < (pad hmn (F.delete (occurrenceConstraint F (c a)))).constraints.card := by omega
    exact_mod_cast this
  refine ⟨pad hmn (F.delete (occurrenceConstraint F (c a))),
    satisfiable_pad hmn (hmin.2 _ (occ_mem _)), ?_⟩
  refine le_trans ?_ (asens_ge hmn F A (c a) hne)
  have hSeq : ∑ o ∈ Finset.univ.erase (c a),
      wasserstein (A (Fin n) (pad hmn (F.delete (occurrenceConstraint F (c a)))))
        (A (Fin n) ((pad hmn (F.delete (occurrenceConstraint F (c a)))).delete
          (padC hmn (occurrenceConstraint F o)))) = ∑ o ∈ Finset.univ.erase (c a), Wf a o :=
    Finset.sum_congr rfl fun o _ => by rw [hWf, hG]
  rw [hSeq]
  set cG := ((pad hmn (F.delete (occurrenceConstraint F (c a)))).constraints.card : ℝ)
  set Ssum := ∑ o ∈ Finset.univ.erase (c a), Wf a o
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hn8 : (n : ℝ) ≤ 8 * N := by
    have : n ≤ 8 * N := by omega
    exact_mod_cast this
  have hkN : 0 < (kappa Γ : ℝ) * N := by positivity
  have hSnn : 0 ≤ Ssum := le_trans (by nlinarith) hS
  calc (n : ℝ) / (96 * kappa Γ) ≤ (((N : ℝ) ^ 2 - 1) / 6) / ((kappa Γ : ℝ) * N) := by
        rw [div_le_div_iff₀ (by positivity) hkN]
        have h1 : (n : ℝ) * N ≤ 8 * N * N := mul_le_mul_of_nonneg_right hn8 hNpos.le
        have h2 : 0 ≤ (kappa Γ : ℝ) * ((N : ℝ) ^ 2 - 2) :=
          mul_nonneg (by linarith) (by nlinarith)
        nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ kappa Γ)]
    _ ≤ Ssum / ((kappa Γ : ℝ) * N) := by gcongr
    _ ≤ Ssum / cG := div_le_div_of_nonneg_left hSnn hcardpos hcardG

end StabilityDichotomies.Dev.LowerBound
end

section
set_option autoImplicit false

namespace StabilityDichotomies.Solvability

theorem chk_stable_solvability_dichotomy (Γ : Language) :
    Xor
      (FiniteDuality Γ ∧
        ∃ D : DeterministicSolver Γ,
          Solves (deterministicLaw D) ∧
          ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
            averageSensitivity (deterministicLaw D) I ≤ (maxArity Γ : ℝ))
      (¬ FiniteDuality Γ ∧
        ∀ A : Solver Γ, Solves A →
          ∀ n : ℕ, 8 ≤ n → ∃ I : Instance Γ (Fin n),
            Satisfiable I ∧
            (n : ℝ) / (96 * (kappa Γ : ℝ)) ≤ averageSensitivity A I) := by
  by_cases hFD : FiniteDuality Γ
  · exact Or.inl ⟨⟨hFD, StabilityDichotomies.Dev.UpperBound.upper_bound Γ
      ((boolean_finite_duality_criterion Γ).mp hFD)⟩, fun h => h.1 hFD⟩
  · exact Or.inr ⟨⟨hFD, StabilityDichotomies.Dev.LowerBound.lower_bound Γ hFD⟩,
      fun h => hFD h.1⟩

end StabilityDichotomies.Solvability
end

theorem solution : type_of% @StabilityDichotomies.Solvability.chk_stable_solvability_dichotomy := @StabilityDichotomies.Solvability.chk_stable_solvability_dichotomy
