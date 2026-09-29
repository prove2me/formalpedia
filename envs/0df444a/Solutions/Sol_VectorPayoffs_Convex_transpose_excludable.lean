-- Prove2me | solution 1 for VectorPayoffs.Convex.transpose_excludable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:17:32.962616+00:00
-- url     : https://prove2.me/submissions/768b0fe5-d435-4c80-a7cf-dfb26e93bf5e

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- A play of `(f', f)` in `M` is a play of `(f, f')` in the transpose `M'`. -/
theorem aux_tpe_transpose_play {N r s : ℕ} (G : Game N r s) (f' : Strategy N r)
    (f : Strategy N s) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (x : ℕ → Ω → E N)
    (hx : G.IsPlay f' f μ x) : G.transpose.IsPlay f f' μ x := by
  refine ⟨hx.1, fun n B hB => (hx.2 n B hB).trans (Filter.EventuallyEq.of_eq ?_)⟩
  funext ω
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  simp only [Game.transpose]
  ring

/-- Every outcome of a play lies in `X` almost surely. -/
theorem aux_tpe_outcome_null {N r s : ℕ} (G : Game N r s) (f' : Strategy N r)
    (f : Strategy N s) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → Ω → E N) (hx : G.IsPlay f' f μ x) (k : ℕ) :
    μ (x (k + 1) ⁻¹' G.Xᶜ) = 0 := by
  have hB : MeasurableSet (G.Xᶜ) := G.isClosed_X.isOpen_compl.measurableSet
  have hmeas : Measurable (hist x k) := by
    unfold hist
    exact measurable_pi_lambda _ (fun i => hx.1 i.val)
  have hm : MeasurableSpace.comap (hist x k) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    hmeas.comap_le
  have hce := hx.2 k (G.Xᶜ) hB
  have hzero : (fun ω => ∑ i, ∑ j, f'.toFun k (hist x k ω) i * f.toFun k (hist x k ω) j *
      (G.m i j G.Xᶜ).toReal) = fun _ => (0 : ℝ) := by
    funext ω
    simp [G.m_compl_X]
  rw [hzero] at hce
  have hpre : MeasurableSet (x (k + 1) ⁻¹' G.Xᶜ) := (hx.1 k) hB
  have h1 := integral_condExp (μ := μ)
    (f := (x (k + 1) ⁻¹' G.Xᶜ).indicator (fun _ => (1 : ℝ))) hm
  rw [integral_congr_ae hce] at h1
  simp only [integral_zero] at h1
  have h2 : ∫ ω, (x (k + 1) ⁻¹' G.Xᶜ).indicator (fun _ => (1 : ℝ)) ω ∂μ
      = μ.real (x (k + 1) ⁻¹' G.Xᶜ) := by
    rw [integral_indicator_const _ hpre]
    simp
  rw [h2] at h1
  have h3 : μ.real (x (k + 1) ⁻¹' G.Xᶜ) = 0 := h1.symm
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at h3
  rcases h3 with h3 | h3
  · exact h3
  · exact absurd h3 (measure_ne_top _ _)

/-- The average of a history in `X` lies in `X`. -/
theorem aux_tpe_avg_mem {N : ℕ} (X : Set (E N)) (hX : Convex ℝ X) {Ω : Type}
    (x : ℕ → Ω → E N) (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (hω : ∀ k, x (k + 1) ω ∈ X) :
    avg x n ω ∈ X := by
  unfold avg avgHist hist
  rw [Finset.smul_sum]
  refine hX.sum_mem (fun _ _ => by positivity) ?_ (fun i _ => hω i.val)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

end VectorPayoffs.Convex

open VectorPayoffs.Convex
open MeasureTheory

theorem solution {N r s : ℕ} (G : Game N r s) (S T : Set (E N))
    (hS : IsClosed S) (hT : IsClosed T) (hST : Disjoint S T) (f : Strategy N s)
    (hf : G.transpose.ApproachableWith S f) : G.ExcludableWith T f := by
  set K := S ∩ Metric.cthickening 1 G.X with hKdef
  have hK : IsCompact K := by
    have hc : IsCompact (Metric.cthickening 1 G.X) :=
      Metric.isCompact_of_isClosed_isBounded Metric.isClosed_cthickening
        G.isBounded_X.cthickening
    exact hc.inter_left hS
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hT.isOpen_compl
    (fun y hy => Set.disjoint_left.mp hST hy.1)
  refine ⟨δ / 2, half_pos hδ, fun ε hε => ?_⟩
  set ε' := min (min (δ / 2) 1) ε with hε'def
  have hε'pos : 0 < ε' := by positivity
  have hε'1 : ε' ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε'2 : ε' ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε'3 : ε' ≤ ε := min_le_right _ _
  -- pointwise geometric lemma
  have key : ∀ a ∈ G.X, Metric.infEDist a S < ENNReal.ofReal ε' →
      ENNReal.ofReal (δ / 2) ≤ Metric.infEDist a T := by
    intro a ha has
    rw [Metric.le_infEDist]
    intro z hz
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hyS, hy⟩ := Metric.infEDist_lt_iff.mp has
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε'pos] at hy
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (half_pos hδ)] at hlt
    have hyK : y ∈ K := by
      refine ⟨hyS, Metric.mem_cthickening_of_dist_le y a 1 G.X ha ?_⟩
      rw [dist_comm]; linarith
    have hzth : z ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]
      refine ⟨y, hyK, ?_⟩
      calc dist z y ≤ dist z a + dist a y := dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := by rw [dist_comm z a]; linarith
        _ = δ := by ring
    exact hsub hzth hz
  obtain ⟨N₀, hN₀⟩ := hf ε' hε'pos
  refine ⟨N₀, fun f' Ω _ μ _ x hx => ?_⟩
  have hx' := aux_tpe_transpose_play G f' f μ x hx
  have hbad := hN₀ f' Ω μ x hx'
  set bad := {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧
        ENNReal.ofReal ε' ≤ Metric.infEDist (avg x n ω) S} with hbaddef
  set good := {ω | ∀ n, N₀ ≤ n → 1 ≤ n →
          ENNReal.ofReal (δ / 2) ≤ Metric.infEDist (avg x n ω) T} with hgooddef
  set null := ⋃ k, x (k + 1) ⁻¹' G.Xᶜ with hnulldef
  have hnull : μ null = 0 :=
    measure_iUnion_null (fun k => aux_tpe_outcome_null G f' f μ x hx k)
  have hcover : (Set.univ : Set Ω) ⊆ good ∪ bad ∪ null := by
    intro ω _
    by_cases hb : ω ∈ bad
    · exact Or.inl (Or.inr hb)
    by_cases hn : ω ∈ null
    · exact Or.inr hn
    left; left
    have hω : ∀ k, x (k + 1) ω ∈ G.X := by
      intro k
      by_contra hk
      exact hn (Set.mem_iUnion.mpr ⟨k, hk⟩)
    intro n hn0 hn1
    apply key _ (aux_tpe_avg_mem G.X G.convex_X x n hn1 ω hω)
    by_contra hge
    push Not at hge
    exact hb ⟨n, hn0, hn1, hge⟩
  have hle : (1 : ENNReal) ≤ μ good + μ bad := by
    calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
      _ ≤ μ (good ∪ bad ∪ null) := measure_mono hcover
      _ ≤ μ (good ∪ bad) + μ null := measure_union_le _ _
      _ = μ (good ∪ bad) := by rw [hnull, add_zero]
      _ ≤ μ good + μ bad := measure_union_le _ _
  have hreal : (1 : ℝ) ≤ (μ good).toReal + (μ bad).toReal := by
    have := ENNReal.toReal_mono (by finiteness) hle
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    simpa using this
  linarith
