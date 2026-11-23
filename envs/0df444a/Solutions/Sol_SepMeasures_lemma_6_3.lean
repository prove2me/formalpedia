-- Prove2me | solution 1 for SepMeasures.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:39:02.140046+00:00
-- url     : https://prove2.me/submissions/85bb05f0-ef12-48a4-a99b-afdcedd1f561

import Mathlib
import Definitions.Def_SepMeasures_Families

open MeasureTheory SepMeasures Filter Topology

namespace Aux63

lemma cube_norm_le {d : ℕ} {x : E d}
    (hx : x ∈ {z : E d | ∀ i, z i ∈ Set.Icc (-1 : ℝ) 1}) : ‖x‖ ≤ d := by
  have hx_sum : x = ∑ i : Fin d, (x i) • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc ‖x‖ = ‖∑ i : Fin d, (x i) • EuclideanSpace.single i (1 : ℝ)‖ := by rw [← hx_sum]
    _ ≤ ∑ i : Fin d, ‖(x i) • EuclideanSpace.single i (1 : ℝ)‖ := norm_sum_le _ _
    _ = ∑ i : Fin d, |x i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single, Real.norm_eq_abs,
          abs_one, mul_one]
    _ ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact abs_le.mpr (hx i)
    _ = d := by simp

lemma infDist_hyp_eq {d : ℕ} (H : Hyp d) (x : E d) :
    Metric.infDist x H.set = |inner ℝ (‖H.u‖⁻¹ • H.u) x - ‖H.u‖⁻¹ * H.c| := by
  set u := ‖H.u‖⁻¹ • H.u
  set c := ‖H.u‖⁻¹ * H.c
  have hn_pos : 0 < ‖H.u‖ := norm_pos_iff.mpr H.hu
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn_pos), inv_mul_cancel₀ hn_pos.ne']
  have hset_eq : H.set = {z : E d | inner ℝ u z = c} := by
    ext z
    simp only [Hyp.set, u, c, inner_smul_left, starRingEnd_apply, star_trivial]
    change inner ℝ H.u z = H.c ↔ ‖H.u‖⁻¹ * inner ℝ H.u z = ‖H.u‖⁻¹ * H.c
    constructor
    · intro h; rw [h]
    · exact mul_left_cancel₀ (inv_ne_zero hn_pos.ne')
  let z₀ : E d := x - (inner ℝ u x - c) • u
  have hz₀ : z₀ ∈ H.set := by
    rw [hset_eq]
    change inner ℝ u z₀ = c
    dsimp [z₀]
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hu_norm, one_pow, mul_one]
    ring
  have hdist_z₀ : dist x z₀ = |inner ℝ u x - c| := by
    dsimp [z₀]
    rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs, hu_norm, mul_one]
  refine le_antisymm ?_ ?_
  · exact (Metric.infDist_le_dist_of_mem hz₀).trans_eq hdist_z₀
  · refine (Metric.le_infDist ⟨z₀, hz₀⟩).mpr fun z hz => ?_
    rw [hset_eq] at hz
    have hz' : inner ℝ u z = c := hz
    have h1 : |inner ℝ u x - c| = |inner ℝ u (x - z)| := by
      rw [inner_sub_right, hz']
    rw [h1, dist_eq_norm]
    exact (abs_real_inner_le_norm u (x - z)).trans_eq (by rw [hu_norm, one_mul])

lemma strip_unit_eq {d : ℕ} (H₀ : Hyp d) (hu₀ : ‖H₀.u‖ = 1) (ρ : ℝ) :
    strip H₀ ρ = {x : E d | |inner ℝ H₀.u x - H₀.c| ≤ ρ} := by
  ext x
  simp [strip, infDist_hyp_eq H₀ x, hu₀]

lemma tendsto_strip_zero {d : ℕ} (ν₀ : Measure (E d)) [IsFiniteMeasure ν₀]
    (H₀ : Hyp d) (hu₀ : ‖H₀.u‖ = 1) (hna : ν₀ H₀.set = 0) :
    Tendsto (fun j : ℕ => ν₀ (strip H₀ (1 / ((j : ℝ) + 1)))) atTop (𝓝 0) := by
  let S (j : ℕ) : Set (E d) := strip H₀ (1 / ((j : ℝ) + 1))
  have hS_meas : ∀ j, NullMeasurableSet (S j) ν₀ := by
    intro j
    dsimp [S]
    rw [strip_unit_eq H₀ hu₀]
    exact (isClosed_le (continuous_abs.comp ((continuous_const.inner continuous_id).sub
      continuous_const)) continuous_const).measurableSet.nullMeasurableSet
  have hS_anti : Antitone S := by
    intro i j hij x hx
    dsimp [S] at hx ⊢
    rw [strip_unit_eq H₀ hu₀] at hx ⊢
    have hx' : |inner ℝ H₀.u x - H₀.c| ≤ 1 / ((j : ℝ) + 1) := hx
    have hdiv : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    exact hx'.trans hdiv
  have hS_inter : (⋂ j : ℕ, S j) = H₀.set := by
    ext x
    simp only [Set.mem_iInter, S, strip_unit_eq H₀ hu₀, Hyp.set]
    change (∀ j : ℕ, |inner ℝ H₀.u x - H₀.c| ≤ 1 / ((j : ℝ) + 1)) ↔ inner ℝ H₀.u x = H₀.c
    constructor
    · intro h
      have hle : |inner ℝ H₀.u x - H₀.c| ≤ 0 :=
        le_of_tendsto_of_tendsto' tendsto_const_nhds
          tendsto_one_div_add_atTop_nhds_zero_nat h
      have heq : |inner ℝ H₀.u x - H₀.c| = 0 := le_antisymm hle (abs_nonneg _)
      linarith [abs_eq_zero.mp heq]
    · intro h j
      rw [h, sub_self, abs_zero]
      positivity
  have htend := tendsto_measure_iInter_atTop hS_meas hS_anti ⟨0, measure_ne_top ν₀ _⟩
  rwa [hS_inter, hna] at htend

lemma strip_subset_of_close {d : ℕ} (H : Hyp d) (H₀ : Hyp d) (hu₀ : ‖H₀.u‖ = 1)
    {η ρ : ℝ}
    (h1 : ‖(‖H.u‖⁻¹ • H.u) - H₀.u‖ < ρ / (3 * ((d : ℝ) + 1)))
    (h2 : |‖H.u‖⁻¹ * H.c - H₀.c| < ρ / 3)
    (h3 : η < ρ / 3) :
    strip H η ⊆ strip H₀ ρ ∪ ({x : E d | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1})ᶜ := by
  intro x hx
  by_cases hxQ : x ∈ {z : E d | ∀ i, z i ∈ Set.Icc (-1 : ℝ) 1}
  · left
    rw [strip_unit_eq H₀ hu₀]
    have hx_d : ‖x‖ ≤ d := cube_norm_le hxQ
    have hdist : |inner ℝ (‖H.u‖⁻¹ • H.u) x - ‖H.u‖⁻¹ * H.c| ≤ η := by
      simpa [strip, infDist_hyp_eq H x] using hx
    have hdiff_u : |inner ℝ (H₀.u - ‖H.u‖⁻¹ • H.u) x| < ρ / 3 := by
      calc |inner ℝ (H₀.u - ‖H.u‖⁻¹ • H.u) x|
        _ ≤ ‖H₀.u - ‖H.u‖⁻¹ • H.u‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ = ‖(‖H.u‖⁻¹ • H.u) - H₀.u‖ * ‖x‖ := by rw [norm_sub_rev]
        _ ≤ ‖(‖H.u‖⁻¹ • H.u) - H₀.u‖ * ((d : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ < (ρ / (3 * ((d : ℝ) + 1))) * ((d : ℝ) + 1) :=
            mul_lt_mul_of_pos_right h1 (by positivity)
        _ = ρ / 3 := by field_simp
    have hsplit : inner ℝ H₀.u x - H₀.c =
        inner ℝ (H₀.u - ‖H.u‖⁻¹ • H.u) x +
          (inner ℝ (‖H.u‖⁻¹ • H.u) x - ‖H.u‖⁻¹ * H.c) +
          (‖H.u‖⁻¹ * H.c - H₀.c) := by
      rw [inner_sub_left]; ring
    have habs : |inner ℝ H₀.u x - H₀.c| ≤
        |inner ℝ (H₀.u - ‖H.u‖⁻¹ • H.u) x| +
          |inner ℝ (‖H.u‖⁻¹ • H.u) x - ‖H.u‖⁻¹ * H.c| +
          |‖H.u‖⁻¹ * H.c - H₀.c| := by
      rw [hsplit]
      have a1 := abs_add_le
        (inner ℝ (H₀.u - ‖H.u‖⁻¹ • H.u) x + (inner ℝ (‖H.u‖⁻¹ • H.u) x - ‖H.u‖⁻¹ * H.c))
        (‖H.u‖⁻¹ * H.c - H₀.c)
      have a2 := abs_add_le
        (inner ℝ (H₀.u - ‖H.u‖⁻¹ • H.u) x)
        (inner ℝ (‖H.u‖⁻¹ • H.u) x - ‖H.u‖⁻¹ * H.c)
      linarith
    change |inner ℝ H₀.u x - H₀.c| ≤ ρ
    linarith
  · exact Or.inr hxQ

end Aux63

theorem solution (d : ℕ) (hd : 1 ≤ d) (μ : Measure (E d)) [IsFiniteMeasure μ]
    (hsupp : μ {x : E d | ∃ i, x i ∉ Set.Icc (-1 : ℝ) 1} = 0)
    (hna : ∀ H : Hyp d, nonatomic μ H.set = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ H : Hyp d, nonatomic μ (strip H η) < ENNReal.ofReal ε := by
  have _ := hd
  intro ε hε
  by_contra hbad
  push Not at hbad
  let ν₀ : Measure (E d) := nonatomic μ
  let Q : Set (E d) := {x : E d | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}
  have hQcompl : ν₀ Qᶜ = 0 := by
    have hceq : Qᶜ = {x : E d | ∃ i, x i ∉ Set.Icc (-1 : ℝ) 1} := by ext x; simp [Q]
    refine le_antisymm ?_ zero_le
    calc ν₀ Qᶜ ≤ μ Qᶜ := Measure.restrict_apply_le _ _
      _ = 0 := by rw [hceq, hsupp]
  have hex : ∀ k : ℕ, ∃ H : Hyp d, ENNReal.ofReal ε ≤ ν₀ (strip H (1 / ((k : ℝ) + 1))) :=
    fun k => hbad (1 / ((k : ℝ) + 1)) (by positivity)
  choose Hseq hHseq using hex
  let u (k : ℕ) : E d := ‖(Hseq k).u‖⁻¹ • (Hseq k).u
  let c (k : ℕ) : ℝ := ‖(Hseq k).u‖⁻¹ * (Hseq k).c
  have hu_sphere : ∀ k, u k ∈ Metric.sphere (0 : E d) 1 := by
    intro k
    have hn_pos : 0 < ‖(Hseq k).u‖ := norm_pos_iff.mpr (Hseq k).hu
    rw [Metric.mem_sphere, dist_zero_right]
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn_pos), inv_mul_cancel₀ hn_pos.ne']
  have hc_mem : ∀ k, c k ∈ Set.Icc (-(d : ℝ) - 1) ((d : ℝ) + 1) := by
    intro k
    have hne : (strip (Hseq k) (1 / ((k : ℝ) + 1)) ∩ Q).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have hsub : strip (Hseq k) (1 / ((k : ℝ) + 1)) ⊆ Qᶜ := by
        intro x hx
        by_cases hxQ : x ∈ Q
        · exact False.elim (Set.eq_empty_iff_forall_notMem.mp hempty x ⟨hx, hxQ⟩)
        · exact hxQ
      have hzero : ν₀ (strip (Hseq k) (1 / ((k : ℝ) + 1))) = 0 :=
        measure_mono_null hsub hQcompl
      exact ((ENNReal.ofReal_pos.mpr hε).trans_le (hHseq k)).ne' hzero
    obtain ⟨x, hx_strip, hx_Q⟩ := hne
    have hdist : |inner ℝ (u k) x - c k| ≤ 1 / ((k : ℝ) + 1) := by
      simpa [strip, Aux63.infDist_hyp_eq (Hseq k) x, u, c] using hx_strip
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1le : 1 / ((k : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
    have hnorm_u : ‖u k‖ = 1 := by simpa using hu_sphere k
    have hinner_le : |inner ℝ (u k) x| ≤ d := by
      calc |inner ℝ (u k) x| ≤ ‖u k‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ = ‖x‖ := by rw [hnorm_u, one_mul]
        _ ≤ d := Aux63.cube_norm_le hx_Q
    rw [Set.mem_Icc]
    rw [abs_le] at hdist hinner_le
    constructor <;> linarith
  let Kparam : Set (E d × ℝ) :=
    Metric.sphere (0 : E d) 1 ×ˢ Set.Icc (-(d : ℝ) - 1) ((d : ℝ) + 1)
  have hK_compact : IsCompact Kparam := (isCompact_sphere (0 : E d) 1).prod isCompact_Icc
  let uf : Ultrafilter ℕ := Ultrafilter.of atTop
  have huf_le : (uf : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hmem_K : Kparam ∈ uf.map fun k => (u k, c k) :=
    Ultrafilter.mem_map.mpr (Filter.Eventually.of_forall fun k => ⟨hu_sphere k, hc_mem k⟩)
  obtain ⟨⟨u₀, c₀⟩, ⟨hu₀_sph, _⟩, hφ_tend⟩ := hK_compact.ultrafilter_le_nhds' _ hmem_K
  have hu₀_norm : ‖u₀‖ = 1 := by simpa using hu₀_sph
  have hu₀_ne : u₀ ≠ 0 := by intro h; rw [h, norm_zero] at hu₀_norm; norm_num at hu₀_norm
  let H₀ : Hyp d := ⟨u₀, c₀, hu₀_ne⟩
  have hge_ρ : ∀ ρ : ℝ, 0 < ρ → ENNReal.ofReal ε ≤ ν₀ (strip H₀ ρ) := by
    intro ρ hρ
    have hu_tend : Tendsto (fun m => ‖u m - u₀‖) (uf : Filter ℕ) (𝓝 0) := by
      have := (continuous_fst.tendsto (u₀, c₀)).comp hφ_tend
      simpa [dist_eq_norm] using tendsto_iff_dist_tendsto_zero.mp this
    have hc_tend : Tendsto (fun m => |c m - c₀|) (uf : Filter ℕ) (𝓝 0) := by
      have := (continuous_snd.tendsto (u₀, c₀)).comp hφ_tend
      simpa [Real.dist_eq] using tendsto_iff_dist_tendsto_zero.mp this
    have hinv_tend : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) (uf : Filter ℕ) (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mono_left huf_le
    have ev1 : ∀ᶠ m in (uf : Filter ℕ), ‖u m - u₀‖ < ρ / (3 * ((d : ℝ) + 1)) :=
      hu_tend.eventually (gt_mem_nhds (by positivity))
    have ev2 : ∀ᶠ m in (uf : Filter ℕ), |c m - c₀| < ρ / 3 :=
      hc_tend.eventually (gt_mem_nhds (by positivity))
    have ev3 : ∀ᶠ (m : ℕ) in (uf : Filter ℕ), 1 / ((m : ℝ) + 1) < ρ / 3 :=
      hinv_tend.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm1, hm2, hm3⟩ := (ev1.and (ev2.and ev3)).exists
    have hsub := Aux63.strip_subset_of_close (Hseq m) H₀ hu₀_norm hm1 hm2 hm3
    calc ENNReal.ofReal ε ≤ ν₀ (strip (Hseq m) (1 / ((m : ℝ) + 1))) := hHseq m
      _ ≤ ν₀ (strip H₀ ρ ∪ Qᶜ) := measure_mono hsub
      _ ≤ ν₀ (strip H₀ ρ) + ν₀ Qᶜ := measure_union_le _ _
      _ = ν₀ (strip H₀ ρ) := by rw [hQcompl, add_zero]
  haveI : IsFiniteMeasure ν₀ := by dsimp [ν₀, nonatomic]; infer_instance
  have htend_meas := Aux63.tendsto_strip_zero ν₀ H₀ hu₀_norm (hna H₀)
  have hle_zero : ENNReal.ofReal ε ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds htend_meas fun j =>
      hge_ρ (1 / ((j : ℝ) + 1)) (by positivity)
  exact not_le_of_gt (ENNReal.ofReal_pos.mpr hε) hle_zero
