-- Prove2me | solution 1 for TalagrandConc.ConvexHull.lemma_4_1_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:48:42.125975+00:00
-- url     : https://prove2.me/submissions/a8611ff7-6690-4649-940e-e6c045d4b682

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic



namespace TalagrandConc.ConvexHull

open scoped ENNReal

/-- Squared Euclidean norm on `Fin N → ℝ`. -/
def sqn {N : ℕ} (s : Fin N → ℝ) : ℝ := ∑ i, s i ^ 2

lemma sqn_nonneg {N : ℕ} (s : Fin N → ℝ) : 0 ≤ sqn s :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

lemma sqn_continuous {N : ℕ} : Continuous (sqn (N := N)) := by
  unfold sqn
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2

lemma U_finite {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) : (U A x).Finite := by
  classical
  apply (Set.finite_range (fun b : Fin N → Bool => fun i => if b i then (1 : ℝ) else 0)).subset
  intro s hs
  refine ⟨fun i => decide (s i = 1), ?_⟩
  funext i
  rcases hs.1 i with h | h <;> simp [h]

lemma V_compact {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) :
    IsCompact (V A x) :=
  (U_finite A x).isCompact_convexHull ℝ

/-- The indicator of `{i | x i ≠ y i}`. -/
def ind {Ω : Type*} [DecidableEq Ω] {N : ℕ} (x y : Fin N → Ω) : Fin N → ℝ :=
  fun i => if x i = y i then 0 else 1

lemma ind_mem_U {Ω : Type*} [DecidableEq Ω] {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω)
    {y : Fin N → Ω} (hy : y ∈ A) : ind x y ∈ U A x := by
  refine ⟨fun i => ?_, y, hy, fun i hi => ?_⟩
  · unfold ind; split_ifs <;> simp
  · unfold ind at hi
    by_contra h
    simp [h] at hi

lemma sum_filter_eq_sum_mul_ind {Ω : Type*} [DecidableEq Ω] {N : ℕ} (x y : Fin N → Ω)
    (c : Fin N → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), c i) = ∑ i, c i * ind x y i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  unfold ind
  by_cases h : x i = y i <;> simp [h]

/-- A linear functional attains on `U` a value at most its value at any point of the hull. -/
lemma exists_U_le {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω)
    (c : Fin N → ℝ) {s : Fin N → ℝ} (hs : s ∈ V A x) :
    ∃ u ∈ U A x, ∑ i, c i * u i ≤ ∑ i, c i * s i := by
  by_contra h
  push_neg at h
  have hlin : IsLinearMap ℝ (fun w : Fin N → ℝ => ∑ i, c i * w i) := by
    refine ⟨fun a b => ?_, fun r a => ?_⟩
    · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  have hsub : U A x ⊆ {w | (∑ i, c i * s i) < ∑ i, c i * w i} := fun u hu => h u hu
  have := convexHull_min hsub (convex_halfSpace_gt hlin _) hs
  rw [Set.mem_setOf_eq] at this
  exact lt_irrefl _ this

/-- Variational inequality for the minimizer of the squared norm on the convex set `V`. -/
lemma var_ineq {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω)
    {v w : Fin N → ℝ} (hv : v ∈ V A x) (hw : w ∈ V A x) (hmin : IsMinOn sqn (V A x) v) :
    sqn v ≤ ∑ i, v i * w i := by
  by_contra h
  push_neg at h
  have hS0 : 0 ≤ sqn (w - v) := sqn_nonneg _
  have hc : ∑ i, v i * w i - sqn v < 0 := by linarith
  set c : ℝ := ∑ i, v i * w i - sqn v with hcdef
  set S : ℝ := sqn (w - v) with hSdef
  set θ : ℝ := min 1 (-c / (S + 1)) with hθ
  have hθpos : 0 < θ := by
    apply lt_min one_pos
    apply div_pos (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθc : θ * (S + 1) ≤ -c := by
    have : θ ≤ -c / (S + 1) := min_le_right _ _
    rwa [le_div_iff₀ (by linarith)] at this
  have hmem := (convex_convexHull ℝ (U A x)).add_smul_sub_mem hv hw ⟨hθpos.le, hθ1⟩
  have h1 : sqn v ≤ sqn (v + θ • (w - v)) := (isMinOn_iff.mp hmin) _ hmem
  have expand : sqn (v + θ • (w - v)) = sqn v + 2 * θ * c + θ ^ 2 * S := by
    have e : ∀ i, (v i + θ * (w i - v i)) ^ 2 =
        v i ^ 2 + 2 * θ * (v i * w i - v i ^ 2) + θ ^ 2 * (w i - v i) ^ 2 := fun i => by ring
    simp only [sqn, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, e,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hcdef, hSdef]
  have h2 : 0 ≤ θ * (2 * c + θ * S) := by nlinarith [h1, expand]
  have h3 : 0 ≤ 2 * c + θ * S := (mul_nonneg_iff_of_pos_left hθpos).mp h2
  nlinarith

/-- Cauchy–Schwarz in the form we need. -/
lemma cs_sqrt {N : ℕ} (a v : Fin N → ℝ) :
    ∑ i, a i * v i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, v i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a v
  have h2 : |∑ i, a i * v i| ≤ Real.sqrt ((∑ i, a i ^ 2) * ∑ i, v i ^ 2) :=
    Real.abs_le_sqrt h
  rw [Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h2
  exact (le_abs_self _).trans h2

lemma fc_eq_top_of_empty {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω)
    (hV : V A x = ∅) : fc A x = ⊤ := by
  simp [fc, hV]

lemma lemma_4_1_2_core {Ω : Type*} [DecidableEq Ω] {N : ℕ} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) (t : ℝ) (ht : 0 ≤ t) :
    x ∈ enlarge A t ↔
      ∀ a : Fin N → ℝ, ∃ y ∈ A,
        (∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), a i) ≤ t * Real.sqrt (∑ i, a i ^ 2) := by
  have ht' : ((t : ℝ) : EReal) = ((ENNReal.ofReal t : ℝ≥0∞) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left ht]
  have hmem : x ∈ enlarge A t ↔ fc A x ≤ ENNReal.ofReal t := by
    simp only [enlarge, Set.mem_setOf_eq]
    rw [ht', EReal.coe_ennreal_le_coe_ennreal_iff]
  rw [hmem]
  have hcont : ContinuousOn (sqn (N := N)) (V A x) := sqn_continuous.continuousOn
  constructor
  · -- (⇒)
    intro hfc a
    rcases (V A x).eq_empty_or_nonempty with hV | hV
    · rw [fc_eq_top_of_empty A x hV] at hfc
      exact absurd (top_le_iff.mp hfc) ENNReal.ofReal_ne_top
    obtain ⟨v, hv, hmin⟩ := (V_compact A x).exists_isMinOn hV hcont
    have hfc_ge : ENNReal.ofReal (Real.sqrt (sqn v)) ≤ fc A x := by
      refine le_iInf₂ fun s hs => ?_
      apply ENNReal.ofReal_le_ofReal
      exact Real.sqrt_le_sqrt ((isMinOn_iff.mp hmin) s hs)
    have hm : Real.sqrt (sqn v) ≤ t :=
      (ENNReal.ofReal_le_ofReal_iff ht).mp (hfc_ge.trans hfc)
    -- positive part of `a`
    set ap : Fin N → ℝ := fun i => max (a i) 0 with hap
    have hap0 : ∀ i, 0 ≤ ap i := fun i => le_max_right _ _
    have hap_le : Real.sqrt (∑ i, ap i ^ 2) ≤ Real.sqrt (∑ i, a i ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      simp only [hap]
      rcases le_or_gt (a i) 0 with h | h
      · rw [max_eq_right h, zero_pow two_ne_zero]; exact sq_nonneg _
      · rw [max_eq_left h.le]
    have hcs : ∑ i, ap i * v i ≤ t * Real.sqrt (∑ i, a i ^ 2) := by
      calc ∑ i, ap i * v i ≤ Real.sqrt (∑ i, ap i ^ 2) * Real.sqrt (∑ i, v i ^ 2) := cs_sqrt ap v
        _ = Real.sqrt (∑ i, ap i ^ 2) * Real.sqrt (sqn v) := rfl
        _ ≤ Real.sqrt (∑ i, a i ^ 2) * t :=
          mul_le_mul hap_le hm (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = t * Real.sqrt (∑ i, a i ^ 2) := mul_comm _ _
    obtain ⟨u, ⟨hu01, y, hy, hyu⟩, hule⟩ := exists_U_le A x ap hv
    refine ⟨y, hy, ?_⟩
    have hu_one : ∀ i, x i ≠ y i → u i = 1 := by
      intro i hi
      rcases hu01 i with h | h
      · exact absurd (hyu i h) hi
      · exact h
    have hu_nonneg : ∀ i, 0 ≤ u i := by
      intro i
      rcases hu01 i with h | h <;> rw [h] <;> norm_num
    calc (∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), a i)
        ≤ ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), ap i :=
          Finset.sum_le_sum fun i _ => le_max_left _ _
      _ = ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), ap i * u i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mem_filter] at hi
          rw [hu_one i hi.2, mul_one]
      _ ≤ ∑ i, ap i * u i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro i _ _
          exact mul_nonneg (hap0 i) (hu_nonneg i)
      _ ≤ ∑ i, ap i * v i := hule
      _ ≤ t * Real.sqrt (∑ i, a i ^ 2) := hcs
  · -- (⇐)
    intro h
    obtain ⟨y0, hy0, -⟩ := h 0
    have hV : (V A x).Nonempty := ⟨ind x y0, subset_convexHull ℝ _ (ind_mem_U A x hy0)⟩
    obtain ⟨v, hv, hmin⟩ := (V_compact A x).exists_isMinOn hV hcont
    obtain ⟨y, hy, hyv⟩ := h v
    rw [sum_filter_eq_sum_mul_ind] at hyv
    have hvar := var_ineq A x hv (subset_convexHull ℝ _ (ind_mem_U A x hy)) hmin
    have hm2 : sqn v ≤ t * Real.sqrt (sqn v) := hvar.trans hyv
    have hm : Real.sqrt (sqn v) ≤ t := by
      have hs := Real.sq_sqrt (sqn_nonneg v)
      have h0 := Real.sqrt_nonneg (sqn v)
      nlinarith
    calc fc A x ≤ ENNReal.ofReal (Real.sqrt (∑ i, v i ^ 2)) := iInf₂_le v hv
      _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal hm

end TalagrandConc.ConvexHull

open TalagrandConc.ConvexHull


theorem solution {Ω : Type*} [DecidableEq Ω] {N : ℕ} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) (t : ℝ) (ht : 0 ≤ t) :
    x ∈ enlarge A t ↔
      ∀ a : Fin N → ℝ, ∃ y ∈ A,
        (∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), a i) ≤ t * Real.sqrt (∑ i, a i ^ 2) := by
  exact lemma_4_1_2_core A x t ht
