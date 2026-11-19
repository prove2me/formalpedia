-- Prove2me | solution 1 for StrictCompatLB.FullInhomogeneous.random_graph_eventually_connected_ae
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T21:41:47.593775+00:00
-- url     : https://prove2.me/submissions/019930f1-9850-4b2f-b79e-1d01042d1132

import Mathlib
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph
import Definitions.Def_StrictCompatLB_MeanField_GraphConditions

set_option autoImplicit false

open MeasureTheory Filter Topology
open StrictCompatLB.MeanField StrictCompatLB.Inhomogeneous
open scoped ENNReal NNReal

namespace SC9aK2

/-! ## Deterministic part: two-step connectivity criterion. -/

theorem conn_of (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (hN : 0 < N)
    (hA : ∀ v v' : Fin N, ∃ w, (v, w) ∈ G N ∧ (v', w) ∈ G N)
    (hB : ∀ w : Fin (M N), ∃ v, (v, w) ∈ G N) : (compatGraph M G N).Connected := by
  have adj : ∀ v w, (v, w) ∈ G N → (compatGraph M G N).Adj (Sum.inl v) (Sum.inr w) := by
    intro v w h
    simp only [compatGraph, SimpleGraph.fromRel_adj]
    exact ⟨Sum.inl_ne_inr, Or.inl ⟨v, w, rfl, rfl, h⟩⟩
  let v0 : Fin N := ⟨0, hN⟩
  have rl : ∀ v, (compatGraph M G N).Reachable (Sum.inl v) (Sum.inl v0) := by
    intro v
    obtain ⟨w, h1, h2⟩ := hA v v0
    exact (adj v w h1).reachable.trans (adj v0 w h2).reachable.symm
  have r : ∀ a, (compatGraph M G N).Reachable a (Sum.inl v0) := by
    rintro (v | w)
    · exact rl v
    · obtain ⟨v, hv⟩ := hB w
      exact (adj v w hv).reachable.symm.trans (rl v)
  rw [SimpleGraph.connected_iff]
  exact ⟨fun a b => (r a).trans (r b).symm, ⟨Sum.inl v0⟩⟩

/-! ## Bernoulli facts. -/

local instance bernProb (q : ℝ) : IsProbabilityMeasure (bernoulliEdge q) := by
  unfold bernoulliEdge; infer_instance

theorem bern_true (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    bernoulliEdge q {true} = ENNReal.ofReal q := by
  have hc : ((unitInterval.toNNReal ⟨q, h0, h1⟩ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal q := by
    rw [ENNReal.ofReal_eq_coe_nnreal h0]; rfl
  rw [bernoulliEdge, Set.projIcc_of_mem _ ⟨h0, h1⟩, ProbabilityTheory.bernoulliMeasure_def]
  simp [hc]

theorem bern_false (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    bernoulliEdge q {false} = ENNReal.ofReal (1 - q) := by
  have hc : ((unitInterval.toNNReal (unitInterval.symm ⟨q, h0, h1⟩) : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal (1 - q) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.2 h1)]; rfl
  rw [bernoulliEdge, Set.projIcc_of_mem _ ⟨h0, h1⟩, ProbabilityTheory.bernoulliMeasure_def]
  simp [hc]

/-! ## Product structure of the edge law (columns indexed by dispatchers). -/

noncomputable def Q (m N : ℕ) (q : Fin m → ℝ) : Measure (Fin m → Fin N → Bool) :=
  Measure.pi fun w => Measure.pi fun _ : Fin N => bernoulliEdge (q w)

def Ψ {N m : ℕ} (y : Fin m → Fin N → Bool) : Fin N × Fin m → Bool := fun e => y e.2 e.1

theorem measurable_Ψ (N m : ℕ) : Measurable (Ψ : (Fin m → Fin N → Bool) → _) :=
  measurable_pi_lambda _ fun e => (measurable_pi_apply e.1).comp (measurable_pi_apply e.2)

theorem edgeLaw_eq (M : ℕ → ℕ) (p : (N : ℕ) → Fin (M N) → ℝ) (N : ℕ) :
    edgeLaw M p N = (Q (M N) N (p N)).map Ψ := by
  unfold edgeLaw
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_Ψ _ _) (MeasurableSet.univ_pi hs)]
  have : (Ψ : (Fin (M N) → Fin N → Bool) → _) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun w => Set.univ.pi fun v => s (v, w)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_univ_pi, Ψ, Prod.forall]
    exact forall_comm
  rw [this, Q, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type, Finset.prod_comm]

/-- Measure of `{z | ∀ u ∈ T, z u = true}` under the column law. -/
theorem box_true (N : ℕ) (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (T : Finset (Fin N)) :
    (Measure.pi fun _ : Fin N => bernoulliEdge q) {z | ∀ u ∈ T, z u = true}
      = ENNReal.ofReal (q ^ T.card) := by
  have : {z : Fin N → Bool | ∀ u ∈ T, z u = true}
      = Set.univ.pi (fun u => if u ∈ T then ({true} : Set Bool) else Set.univ) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
    constructor
    · intro h u
      by_cases hu : u ∈ T
      · simp [hu, h u hu]
      · simp [hu]
    · intro h u hu
      have := h u
      simpa [hu] using this
  rw [this, Measure.pi_pi]
  simp_rw [apply_ite (bernoulliEdge q), measure_univ, bern_true q h0 h1]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, ENNReal.ofReal_pow h0]

/-! ## The two bad events. -/

def badA {N m : ℕ} (v v' : Fin N) : Set (Fin N × Fin m → Bool) :=
  {x | ∀ w, ¬ (x (v, w) = true ∧ x (v', w) = true)}

def badB {N m : ℕ} (w : Fin m) : Set (Fin N × Fin m → Bool) :=
  {x | ∀ v, x (v, w) = false}

theorem badA_le (M : ℕ → ℕ) (p : (N : ℕ) → Fin (M N) → ℝ) (N : ℕ)
    (h0 : ∀ w, 0 ≤ p N w) (h1 : ∀ w, p N w ≤ 1) (v v' : Fin N) :
    edgeLaw M p N (badA v v') ≤ ENNReal.ofReal (Real.exp (-∑ w, p N w ^ 2)) := by
  rw [edgeLaw_eq, Measure.map_apply (measurable_Ψ _ _) (Set.toFinite _).measurableSet]
  have hpre : (Ψ : (Fin (M N) → Fin N → Bool) → _) ⁻¹' (badA v v')
      = Set.univ.pi (fun _ => {z : Fin N → Bool | ∀ u ∈ ({v, v'} : Finset (Fin N)), z u = true}ᶜ) := by
    ext y
    simp [badA, Ψ, Set.mem_univ_pi]
  rw [hpre, Q, Measure.pi_pi]
  have hfac : ∀ w, (Measure.pi fun _ : Fin N => bernoulliEdge (p N w))
      {z : Fin N → Bool | ∀ u ∈ ({v, v'} : Finset (Fin N)), z u = true}ᶜ
        ≤ ENNReal.ofReal (1 - p N w ^ 2) := by
    intro w
    rw [prob_compl_eq_one_sub (Set.toFinite _).measurableSet, box_true N _ (h0 w) (h1 w)]
    rw [ENNReal.ofReal_sub _ (sq_nonneg _), ENNReal.ofReal_one]
    apply tsub_le_tsub_left
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_of_le_one (h0 w) (h1 w) (Finset.card_le_two)
  calc ∏ w, (Measure.pi fun _ : Fin N => bernoulliEdge (p N w))
        {z : Fin N → Bool | ∀ u ∈ ({v, v'} : Finset (Fin N)), z u = true}ᶜ
      ≤ ∏ w, ENNReal.ofReal (1 - p N w ^ 2) := Finset.prod_le_prod' fun w _ => hfac w
    _ = ENNReal.ofReal (∏ w, (1 - p N w ^ 2)) := by
        rw [ENNReal.ofReal_prod_of_nonneg]
        intro w _
        nlinarith [h0 w, h1 w]
    _ ≤ ENNReal.ofReal (Real.exp (-∑ w, p N w ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Finset.sum_neg_distrib, Real.exp_sum]
        apply Finset.prod_le_prod
        · intro w _; nlinarith [h0 w, h1 w]
        · intro w _; exact Real.one_sub_le_exp_neg _

theorem badB_le (M : ℕ → ℕ) (p : (N : ℕ) → Fin (M N) → ℝ) (N : ℕ)
    (h0 : ∀ w, 0 ≤ p N w) (h1 : ∀ w, p N w ≤ 1) (w : Fin (M N)) :
    edgeLaw M p N (badB w) ≤ ENNReal.ofReal (Real.exp (-(N * p N w))) := by
  have hset : (badB w : Set (Fin N × Fin (M N) → Bool))
      = Set.univ.pi (fun e => if e.2 = w then ({false} : Set Bool) else Set.univ) := by
    ext x
    simp only [badB, Set.mem_setOf_eq, Set.mem_univ_pi]
    constructor
    · intro h e
      obtain ⟨v, w'⟩ := e
      by_cases he : w' = w
      · subst he; simp [h v]
      · simp [he]
    · intro h v
      have := h (v, w)
      simpa using this
  rw [hset, edgeLaw, Measure.pi_pi]
  simp_rw [apply_ite (bernoulliEdge _), measure_univ]
  rw [Fintype.prod_prod_type]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [bern_false _ (h0 w) (h1 w), Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (sub_nonneg.2 (h1 w))]
  apply ENNReal.ofReal_le_ofReal
  calc (1 - p N w) ^ N ≤ (Real.exp (-p N w)) ^ N :=
        pow_le_pow_left₀ (sub_nonneg.2 (h1 w)) (Real.one_sub_le_exp_neg _) N
    _ = Real.exp (-(N * p N w)) := by
        rw [← Real.exp_nat_mul]; ring_nf

def good {N m : ℕ} (x : Fin N × Fin m → Bool) : Prop :=
  (∀ v v' : Fin N, ∃ w, x (v, w) = true ∧ x (v', w) = true) ∧ ∀ w : Fin m, ∃ v, x (v, w) = true

theorem bad_le (M : ℕ → ℕ) (p : (N : ℕ) → Fin (M N) → ℝ) (N : ℕ)
    (h0 : ∀ w, 0 ≤ p N w) (h1 : ∀ w, p N w ≤ 1) :
    edgeLaw M p N {x | ¬ good x} ≤ ENNReal.ofReal ((N : ℝ) * N * Real.exp (-∑ w, p N w ^ 2)
      + (M N : ℝ) * Real.exp (-(N * minEdgeProb M p N))) := by
  have hsub : {x : Fin N × Fin (M N) → Bool | ¬ good x}
      ⊆ (⋃ v, ⋃ v', badA v v') ∪ ⋃ w, badB w := by
    intro x hx
    simp only [good, not_and_or, not_forall, not_exists] at hx
    rcases hx with ⟨v, v', h⟩ | ⟨w, h⟩
    · left; simp only [Set.mem_iUnion]; exact ⟨v, v', fun w hw => (h w).elim (fun h' => h' hw.1) (fun h' => h' hw.2)⟩
    · right; simp only [Set.mem_iUnion]
      exact ⟨w, fun v => by simpa using h v⟩
  have hmin : ∀ w, minEdgeProb M p N ≤ p N w := fun w => ciInf_le (Finite.bddBelow_range _) w
  have hB : ∀ w, edgeLaw M p N (badB w) ≤ ENNReal.ofReal (Real.exp (-(N * minEdgeProb M p N))) :=
    fun w => (badB_le M p N h0 h1 w).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
      have := hmin w
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith)))
  calc edgeLaw M p N {x | ¬ good x}
      ≤ edgeLaw M p N ((⋃ v, ⋃ v', badA v v') ∪ ⋃ w, badB w) := measure_mono hsub
    _ ≤ edgeLaw M p N (⋃ v, ⋃ v', badA v v') + edgeLaw M p N (⋃ w, badB w) := measure_union_le _ _
    _ ≤ (∑ v : Fin N, ∑ v' : Fin N, ENNReal.ofReal (Real.exp (-∑ w, p N w ^ 2)))
        + ∑ w : Fin (M N), ENNReal.ofReal (Real.exp (-(N * minEdgeProb M p N))) := by
        gcongr
        · refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
          refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun v' _ => ?_)
          exact badA_le M p N h0 h1 v v'
        · exact (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun w _ => hB w)
    _ = ENNReal.ofReal ((N : ℝ) * N * Real.exp (-∑ w, p N w ^ 2)
          + (M N : ℝ) * Real.exp (-(N * minEdgeProb M p N))) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_natCast, mul_assoc]

/-! ## Asymptotics from (H1), (H3). -/

theorem exp_two_log (N : ℕ) (hN : 0 < N) :
    Real.exp (-(2 * Real.log N)) = 1 / (N : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [Real.exp_neg, show (2 : ℝ) * Real.log N = Real.log ((N : ℝ) ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
  ring

theorem eventually_good (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (p : (N : ℕ) → Fin (M N) → ℝ)
    (hp_pos : ∀ N w, 0 < p N w)
    (h1 : Tendsto (fun N : ℕ =>
      (N : ℝ) / (Real.log (M N) + Real.log N) * minEdgeProb M p N) atTop atTop)
    (h3 : Tendsto (fun N : ℕ =>
      Real.log N / (M N : ℝ) ^ 2 * ∑ w : Fin (M N), 1 / (p N w) ^ 2) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) * N * Real.exp (-∑ w, p N w ^ 2)
      + (M N : ℝ) * Real.exp (-(N * minEdgeProb M p N)) ≤ 2 * (1 / (N : ℝ) ^ 2) := by
  filter_upwards [h1.eventually (eventually_ge_atTop 4),
    h3.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)), eventually_ge_atTop 2]
    with N hN1 hN3 hN2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hMpos : (0 : ℝ) < M N := by exact_mod_cast hM N
  have hlogM : 0 ≤ Real.log (M N) :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.2 (hM N).ne'))
  set L := Real.log N with hLdef
  set S := ∑ w : Fin (M N), 1 / (p N w) ^ 2 with hSdef
  set S2 := ∑ w, p N w ^ 2 with hS2def
  -- Cauchy-Schwarz: M^2 ≤ S2 * S
  have hCS : (M N : ℝ) ^ 2 ≤ S2 * S := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun w => p N w) (fun w => 1 / p N w)
    have e1 : ∑ w : Fin (M N), p N w * (1 / p N w) = M N := by
      simp [fun w => (hp_pos N w).ne']
    have e2 : ∑ w : Fin (M N), (1 / p N w) ^ 2 = S := by
      simp [hSdef]
    rw [e1, e2] at h
    exact h
  have hSpos : 0 < S := Finset.sum_pos (fun w _ => by have := hp_pos N w; positivity)
    ⟨⟨0, hM N⟩, Finset.mem_univ _⟩
  have h3' : L * S * 4 < (M N : ℝ) ^ 2 := by
    have : L / (M N : ℝ) ^ 2 * S < 1 / 4 := hN3
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)] at this
    linarith
  have hS2 : 4 * L < S2 := by
    by_contra hc
    push_neg at hc
    have : S2 * S ≤ 4 * L * S := mul_le_mul_of_nonneg_right hc hSpos.le
    nlinarith
  have hD : 0 < Real.log (M N) + L := by linarith
  have hNp : 4 * (Real.log (M N) + L) ≤ N * minEdgeProb M p N := by
    have : (4 : ℝ) ≤ N / (Real.log (M N) + L) * minEdgeProb M p N := hN1
    rw [div_mul_eq_mul_div, le_div_iff₀ hD] at this
    linarith
  have t1 : (N : ℝ) * N * Real.exp (-S2) ≤ 1 / (N : ℝ) ^ 2 := by
    have : Real.exp (-S2) ≤ Real.exp (-(2 * L)) * Real.exp (-(2 * L)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    rw [exp_two_log N (by omega)] at this
    calc (N : ℝ) * N * Real.exp (-S2) ≤ N * N * (1 / (N : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2)) := by
          gcongr
      _ = 1 / (N : ℝ) ^ 2 := by field_simp
  have t2 : (M N : ℝ) * Real.exp (-(N * minEdgeProb M p N)) ≤ 1 / (N : ℝ) ^ 2 := by
    have : Real.exp (-(N * minEdgeProb M p N))
        ≤ Real.exp (-Real.log (M N)) * Real.exp (-(2 * L)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    rw [exp_two_log N (by omega), Real.exp_neg (Real.log (M N : ℝ)), Real.exp_log hMpos] at this
    calc (M N : ℝ) * Real.exp (-(N * minEdgeProb M p N))
        ≤ M N * ((M N : ℝ)⁻¹ * (1 / (N : ℝ) ^ 2)) := by gcongr
      _ = 1 / (N : ℝ) ^ 2 := by field_simp
  linarith

end SC9aK2

/-- K2: the inhomogeneous random bipartite graph is almost surely eventually connected. -/
theorem solution (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ)
    (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (h1 : Tendsto (fun N : ℕ =>
      (N : ℝ) / (Real.log (M N) + Real.log N) * minEdgeProb M p N) atTop atTop)
    (h3 : Tendsto (fun N : ℕ =>
      Real.log N / (M N : ℝ) ^ 2 * ∑ w : Fin (M N), 1 / (p N w) ^ 2) atTop (𝓝 0))
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω) [IsProbabilityMeasure P₀]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N))
    (hX_law : ∀ N, P₀.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (compatGraph M (fun N => graphOf (X N ω)) N).Connected := by
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (SC9aK2.eventually_good M hM p hp_pos h1 h3)
  have h0 : ∀ N w, 0 ≤ p N w := fun N w => (hp_pos N w).le
  set N2 := max N1 1 with hN2
  let s : ℕ → Set Ω := fun N =>
    if N2 ≤ N then X N ⁻¹' {x | ¬ SC9aK2.good x} else ∅
  have hbound : ∀ N, P₀ (s N) ≤ ENNReal.ofReal (2 * (1 / (N : ℝ) ^ 2)) := by
    intro N
    by_cases hN : N2 ≤ N
    · simp only [s, hN, if_true]
      rw [← Measure.map_apply (hX_meas N) (Set.toFinite _).measurableSet, hX_law N]
      exact (SC9aK2.bad_le M p N (h0 N) (hp_le N)).trans
        (ENNReal.ofReal_le_ofReal (hN1 N (le_trans (le_max_left _ _) hN)))
    · simp [s, hN]
  have hsum : Summable (fun N : ℕ => 2 * (1 / (N : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 2
  have hs : ∑' N, P₀ (s N) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hs] with ω hω
  obtain ⟨N3, hN3⟩ := eventually_atTop.1 hω
  refine ⟨max N2 N3, fun N hN => ?_⟩
  have hN2N : N2 ≤ N := le_trans (le_max_left _ _) hN
  have hgood : SC9aK2.good (X N ω) := by
    have := hN3 N (le_trans (le_max_right _ _) hN)
    simpa [s, hN2N] using this
  apply SC9aK2.conn_of M (fun N => graphOf (X N ω)) N
    (by have := le_trans (le_max_right N1 1) hN2N; omega)
  · intro v v'
    obtain ⟨w, hw1, hw2⟩ := hgood.1 v v'
    exact ⟨w, by simp [graphOf, hw1], by simp [graphOf, hw2]⟩
  · intro w
    obtain ⟨v, hv⟩ := hgood.2 w
    exact ⟨v, by simp [graphOf, hv]⟩
