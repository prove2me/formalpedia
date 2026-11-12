-- Prove2me | solution 1 for OuterplanarL1Tan.Linear.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:03:11.94141+00:00
-- url     : https://prove2.me/submissions/50ca66ef-2c8d-48ce-8224-7dcfbf39616c

import Mathlib
import Definitions.Def_OuterplanarL1Tan_Linear_BoundaryPattern
import Theorems.Thm_OuterplanarL1Tan_Linear_claim_3

section
set_option autoImplicit false

namespace OuterplanarL1Tan.Dev.Dist

open OuterplanarL1Tan.Linear

theorem walkLength_append {V : Type} {G : SimpleGraph V} (length : V → V → ℝ)
    {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    OAI.PlanarL1.walkLength length (p.append q) =
      OAI.PlanarL1.walkLength length p + OAI.PlanarL1.walkLength length q := by
  induction p with
  | nil => simp [OAI.PlanarL1.walkLength]
  | cons h p ih =>
    simp only [SimpleGraph.Walk.cons_append, OAI.PlanarL1.walkLength, ih]
    ring

theorem walkLength_nonneg {V : Type} (W : WeightedGraph V) {u v : V}
    (p : W.graph.Walk u v) : 0 ≤ OAI.PlanarL1.walkLength W.length p := by
  induction p with
  | nil => simp [OAI.PlanarL1.walkLength]
  | cons h p ih =>
    simp only [OAI.PlanarL1.walkLength]
    exact add_nonneg (W.nonnegative _ _ h) ih

theorem walkLength_reverse {V : Type} (W : WeightedGraph V) {u v : V}
    (p : W.graph.Walk u v) :
    OAI.PlanarL1.walkLength W.length p.reverse = OAI.PlanarL1.walkLength W.length p := by
  induction p with
  | nil => simp [OAI.PlanarL1.walkLength]
  | cons h p ih =>
    rename_i a b c
    rw [SimpleGraph.Walk.reverse_cons, walkLength_append]
    simp only [OAI.PlanarL1.walkLength, ih]
    rw [W.symmetric b a]
    ring

theorem dist_nonneg {V : Type} (W : WeightedGraph V) (u v : V) : 0 ≤ W.distance u v := by
  unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
  apply Real.sInf_nonneg
  rintro _ ⟨p, rfl⟩
  exact walkLength_nonneg W p

theorem dist_le_walk {V : Type} (W : WeightedGraph V) {u v : V} (p : W.graph.Walk u v) :
    W.distance u v ≤ OAI.PlanarL1.walkLength W.length p := by
  unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact walkLength_nonneg W q
  · exact ⟨p, rfl⟩

theorem dist_self {V : Type} (W : WeightedGraph V) (u : V) : W.distance u u = 0 := by
  apply le_antisymm
  · have := dist_le_walk W (SimpleGraph.Walk.nil : W.graph.Walk u u)
    simpa [OAI.PlanarL1.walkLength] using this
  · exact dist_nonneg W u u

theorem dist_comm {V : Type} (W : WeightedGraph V) (u v : V) :
    W.distance u v = W.distance v u := by
  have h : ∀ a b : V, W.distance a b ≤ W.distance b a := by
    intro a b
    by_cases hne : Nonempty (W.graph.Walk a b)
    · obtain ⟨q⟩ := hne
      unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
      have hne2 : (Set.range fun p : W.graph.Walk b a => OAI.PlanarL1.walkLength W.length p).Nonempty := ⟨_, Set.mem_range_self q.reverse⟩
      apply le_csInf hne2
      rintro _ ⟨p, rfl⟩
      have := dist_le_walk W p.reverse
      rw [walkLength_reverse] at this
      exact this
    · have : IsEmpty (W.graph.Walk a b) := not_nonempty_iff.mp hne
      have h0 : W.distance a b = 0 := by
        unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
        rw [Set.range_eq_empty]; exact Real.sInf_empty
      rw [h0]; exact dist_nonneg W b a
  exact le_antisymm (h u v) (h v u)

theorem dist_triangle {V : Type} (W : WeightedGraph V) (hr : W.FiniteDistances)
    (u v w : V) : W.distance u w ≤ W.distance u v + W.distance v w := by
  obtain ⟨p0⟩ := hr u v
  obtain ⟨q0⟩ := hr v w
  haveI : Nonempty (W.graph.Walk u v) := ⟨p0⟩
  haveI : Nonempty (W.graph.Walk v w) := ⟨q0⟩
  have key : ∀ p : W.graph.Walk u v, ∀ q : W.graph.Walk v w,
      W.distance u w ≤ OAI.PlanarL1.walkLength W.length p +
        OAI.PlanarL1.walkLength W.length q := by
    intro p q
    have := dist_le_walk W (p.append q)
    rwa [walkLength_append] at this
  have h1 : ∀ p : W.graph.Walk u v, W.distance u w - OAI.PlanarL1.walkLength W.length p
      ≤ W.distance v w := by
    intro p
    unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨q, rfl⟩
    have := key p q
    unfold WeightedGraph.distance OAI.PlanarL1.graphDistance at this
    linarith
  have h2 : W.distance u w - W.distance v w ≤ W.distance u v := by
    unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨p, rfl⟩
    have := h1 p
    unfold WeightedGraph.distance OAI.PlanarL1.graphDistance at this
    linarith
  linarith

end OuterplanarL1Tan.Dev.Dist
end

section
set_option autoImplicit false

namespace OuterplanarL1Tan.Dev.TV

open OuterplanarL1Tan.Linear MeasureTheory

theorem arc_le (a : ℕ → ℝ) (p r : ℕ) (h : p ≤ r) :
    |a r - a p| ≤ ∑ k ∈ Finset.Ico p r, |a (k + 1) - a k| := by
  induction r, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have := abs_sub_le (a (n + 1)) (a n) (a p)
    linarith

theorem cyc_ge_aux {m : ℕ} (hm : 0 < m) (q : Fin m → ℝ) (i j : Fin m) (hij : i ≤ j) :
    2 * |q i - q j| ≤ ∑ k : Fin m, |q k - q (cyclicNext hm k)| := by
  set a : ℕ → ℝ := fun n => q ⟨n % m, Nat.mod_lt _ hm⟩ with ha
  have hsum : ∑ k : Fin m, |q k - q (cyclicNext hm k)| =
      ∑ k ∈ Finset.range m, |a (k + 1) - a k| := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => |a (k + 1) - a k|)]
    apply Finset.sum_congr rfl
    intro k _
    rw [abs_sub_comm]
    have h1 : a k = q k := by
      simp only [ha]; congr 1; ext; simp [Nat.mod_eq_of_lt k.2]
    have h2 : a (k + 1) = q (cyclicNext hm k) := by
      simp only [ha, cyclicNext]
    rw [h1, h2]
  have ai : a i = q i := by simp only [ha]; congr 1; ext; simp [Nat.mod_eq_of_lt i.2]
  have aj : a j = q j := by simp only [ha]; congr 1; ext; simp [Nat.mod_eq_of_lt j.2]
  have a0 : a m = a 0 := by simp [ha]
  have hjm : (j : ℕ) ≤ m := j.2.le
  have hi : (i : ℕ) ≤ j := hij
  have e1 := arc_le a 0 i (Nat.zero_le _)
  have e2 := arc_le a i j hi
  have e3 := arc_le a j m hjm
  have split : ∑ k ∈ Finset.range m, |a (k + 1) - a k| =
      ∑ k ∈ Finset.Ico 0 (i : ℕ), |a (k + 1) - a k| + ∑ k ∈ Finset.Ico (i : ℕ) j, |a (k + 1) - a k|
        + ∑ k ∈ Finset.Ico (j : ℕ) m, |a (k + 1) - a k| := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le _) hi,
      Finset.sum_Ico_consecutive _ (le_trans (Nat.zero_le _) hi) hjm]
  rw [hsum, split]
  rw [a0] at e3
  have t := abs_sub_le (a i) (a 0) (a j)
  have s1 : |a i - a 0| = |a i - a 0| := rfl
  rw [← ai, ← aj]
  have : |a i - a j| ≤ |a i - a 0| + |a 0 - a j| := t
  rw [abs_sub_comm (a j) (a i)] at e2
  rw [abs_sub_comm (a 0) (a j)] at this
  linarith [abs_sub_comm (a 0) (a i), abs_sub_comm (a j) (a 0)]

theorem cyc_ge {m : ℕ} (hm : 0 < m) (q : Fin m → ℝ) (i j : Fin m) :
    2 * |q i - q j| ≤ ∑ k : Fin m, |q k - q (cyclicNext hm k)| := by
  rcases le_total i j with h | h
  · exact cyc_ge_aux hm q i j h
  · rw [abs_sub_comm]; exact cyc_ge_aux hm q j i h

theorem tv_le {ι : Type} [Fintype ι] (u v : ι → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hu : ∀ i, |u i| ≤ d) (hv : ∀ i, |v i| ≤ d)
    (h : ∀ t : ℝ, -d < t → t < d →
      (Finset.univ.filter (fun i => ¬ (u i ≤ t ↔ v i ≤ t))).card ≤ 2) :
    ∑ i, |u i - v i| ≤ 4 * d := by
  classical
  set S : ι → Set ℝ := fun i => Set.Ioo (min (u i) (v i)) (max (u i) (v i)) with hS
  have hSm : ∀ i, MeasurableSet (S i) := fun i => measurableSet_Ioo
  have hvol : ∀ i, volume (S i) = ENNReal.ofReal |u i - v i| := by
    intro i
    simp only [hS, Real.volume_Ioo]
    rw [max_sub_min_eq_abs, abs_sub_comm]
  have hsub : ∀ i, S i ⊆ Set.Ioo (-d) d := by
    intro i t ht
    have h1 := abs_le.mp (hu i)
    have h2 := abs_le.mp (hv i)
    simp only [hS, Set.mem_Ioo] at ht ⊢
    constructor
    · have := ht.1
      rcases le_total (u i) (v i) with c | c
      · rw [min_eq_left c] at this; linarith
      · rw [min_eq_right c] at this; linarith
    · have := ht.2
      rcases le_total (u i) (v i) with c | c
      · rw [max_eq_right c] at this; linarith
      · rw [max_eq_left c] at this; linarith
  have hf : ∀ t : ℝ, ∑ i, (S i).indicator (1 : ℝ → ENNReal) t ≤
      (Set.Ioo (-d) d).indicator (fun _ => (2 : ENNReal)) t := by
    intro t
    by_cases ht : t ∈ Set.Ioo (-d) d
    · rw [Set.indicator_of_mem ht]
      have : ∑ i, (S i).indicator (1 : ℝ → ENNReal) t =
          ((Finset.univ.filter (fun i => t ∈ S i)).card : ENNReal) := by
        simp only [Set.indicator_apply, Pi.one_apply]
        rw [Finset.sum_boole]
      rw [this]
      have hc : (Finset.univ.filter (fun i => t ∈ S i)).card ≤ 2 := by
        refine le_trans (Finset.card_le_card ?_) (h t ht.1 ht.2)
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS, Set.mem_Ioo] at hi ⊢
        rcases le_total (u i) (v i) with c | c
        · rw [min_eq_left c, max_eq_right c] at hi
          intro hiff
          have := hiff.mp hi.1.le
          linarith [hi.2]
        · rw [min_eq_right c, max_eq_left c] at hi
          intro hiff
          have := hiff.mpr hi.1.le
          linarith [hi.2]
      exact_mod_cast hc
    · rw [Set.indicator_of_notMem ht]
      have : ∑ i, (S i).indicator (1 : ℝ → ENNReal) t = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        apply Set.indicator_of_notMem
        exact fun hh => ht (hsub i hh)
      rw [this]
  have hint : ∑ i, volume (S i) ≤ 2 * ENNReal.ofReal (2 * d) := by
    have e1 : ∑ i, volume (S i) = ∫⁻ t, ∑ i, (S i).indicator (1 : ℝ → ENNReal) t := by
      rw [lintegral_finset_sum _ (fun i _ => (measurable_one.indicator (hSm i)))]
      apply Finset.sum_congr rfl
      intro i _
      rw [lintegral_indicator_one (hSm i)]
    rw [e1]
    calc ∫⁻ t, ∑ i, (S i).indicator (1 : ℝ → ENNReal) t
        ≤ ∫⁻ t, (Set.Ioo (-d) d).indicator (fun _ => (2 : ENNReal)) t := lintegral_mono hf
      _ = 2 * volume (Set.Ioo (-d) d) := lintegral_indicator_const measurableSet_Ioo _
      _ = 2 * ENNReal.ofReal (2 * d) := by
        rw [Real.volume_Ioo]; congr 2; ring
  have h2 : ENNReal.ofReal (∑ i, |u i - v i|) ≤ ENNReal.ofReal (4 * d) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    calc ∑ i, ENNReal.ofReal |u i - v i| = ∑ i, volume (S i) := by simp [hvol]
      _ ≤ 2 * ENNReal.ofReal (2 * d) := hint
      _ = ENNReal.ofReal (4 * d) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h2

end OuterplanarL1Tan.Dev.TV
end

section
set_option autoImplicit false

namespace OuterplanarL1Tan.Dev.L2

open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.Dist OuterplanarL1Tan.Dev.TV

theorem l1norm {ι : Type} [Fintype ι] (f g : ι → ℝ) :
    ‖WithLp.toLp 1 f - WithLp.toLp 1 g‖ = ∑ i, |f i - g i| := by
  rw [← WithLp.toLp_sub, PiLp.norm_eq_of_nat 1 (by norm_num)]
  simp

noncomputable def qq {V : Type} (W : WeightedGraph V) (x y z : V) : ℝ :=
  W.distance x z - W.distance y z

theorem pat_norm_eq {V : Type} [Fintype V] (W : WeightedGraph V) (D : PlaneDrawing W.graph)
    (B : OuterFacialWalk D) (x y : V) :
    ‖pattern W D B x - pattern W D B y‖ =
      ∑ j, |qq W x y (B.vertex j) - qq W x y (B.vertex (cyclicNext B.positive j))| := by
  unfold pattern
  rw [l1norm]
  apply Finset.sum_congr rfl
  intro j _
  unfold qq
  congr 1
  ring

theorem qq_abs_le {V : Type} (W : WeightedGraph V) (hr : W.FiniteDistances) (x y z : V) :
    |qq W x y z| ≤ W.distance x y := by
  unfold qq
  rw [abs_le]
  have t1 := dist_triangle W hr x y z
  have t2 := dist_triangle W hr y x z
  have c := dist_comm W x y
  constructor <;> linarith

theorem tv_bound {V : Type} [Fintype V] (W : WeightedGraph V) (hr : W.FiniteDistances)
    (D : PlaneDrawing W.graph) (B : OuterFacialWalk D) (x y : V) :
    ‖pattern W D B x - pattern W D B y‖ ≤ 4 * W.distance x y := by
  rw [pat_norm_eq]
  apply tv_le (fun j => qq W x y (B.vertex j)) (fun j => qq W x y (B.vertex (cyclicNext B.positive j)))
    _ (dist_nonneg W x y) (fun j => qq_abs_le W hr x y _) (fun j => qq_abs_le W hr x y _)
  intro t h1 h2
  have := claim_3 W hr D B x y t h1 h2
  unfold transitionCount at this
  convert this using 2
  ext j
  simp [sublevel, differencePotential, qq]

theorem tv_equal {V : Type} [Fintype V] (W : WeightedGraph V) (hr : W.FiniteDistances)
    (D : PlaneDrawing W.graph) (B : OuterFacialWalk D) (x y : V)
    (hx : x ∈ D.boundary Set.univ) (hy : y ∈ D.boundary Set.univ) :
    4 * W.distance x y ≤ ‖pattern W D B x - pattern W D B y‖ := by
  rw [← B.covers_boundary] at hx hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  rw [pat_norm_eq]
  have := cyc_ge B.positive (fun k => qq W (B.vertex i) (B.vertex j) (B.vertex k)) i j
  simp only [qq, dist_self, dist_comm W (B.vertex j) (B.vertex i)] at this ⊢
  have e : |(0 - W.distance (B.vertex i) (B.vertex j)) -
      (W.distance (B.vertex i) (B.vertex j) - 0)| = 2 * W.distance (B.vertex i) (B.vertex j) := by
    have := dist_nonneg W (B.vertex i) (B.vertex j)
    rw [show (0 - W.distance (B.vertex i) (B.vertex j)) -
      (W.distance (B.vertex i) (B.vertex j) - 0) = -(2 * W.distance (B.vertex i) (B.vertex j)) by ring,
      abs_neg, abs_of_nonneg (by linarith)]
  rw [e] at this
  linarith

end OuterplanarL1Tan.Dev.L2

namespace OuterplanarL1Tan.Linear

theorem chk_lemma_2 {V : Type} [Fintype V] (W : WeightedGraph V)
    (reachable : W.FiniteDistances) (D : PlaneDrawing W.graph)
    (B : OuterFacialWalk D) :
    (∀ x y : V, ‖pattern W D B x - pattern W D B y‖ ≤ 4 * W.distance x y) ∧
    (∀ x y : V, x ∈ D.boundary Set.univ → y ∈ D.boundary Set.univ →
      ‖pattern W D B x - pattern W D B y‖ = 4 * W.distance x y) := by
  refine ⟨fun x y => OuterplanarL1Tan.Dev.L2.tv_bound W reachable D B x y, ?_⟩
  intro x y hx hy
  exact le_antisymm (OuterplanarL1Tan.Dev.L2.tv_bound W reachable D B x y)
    (OuterplanarL1Tan.Dev.L2.tv_equal W reachable D B x y hx hy)

end OuterplanarL1Tan.Linear
end

theorem solution : type_of% @OuterplanarL1Tan.Linear.chk_lemma_2 := @OuterplanarL1Tan.Linear.chk_lemma_2
