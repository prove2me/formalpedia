-- Prove2me | solution 1 for SepMeasures.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:39:05.175114+00:00
-- url     : https://prove2.me/submissions/1391521e-51ca-434d-8d23-2d6266562a96

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families

open MeasureTheory SepMeasures Filter Topology

namespace Aux61

noncomputable section

lemma coe_nnnorm_eq_ofReal_abs (r : ℝ) : (‖r‖₊ : ENNReal) = ENNReal.ofReal |r| := by
  have h : |r| = (‖r‖₊ : ℝ) := by rw [coe_nnnorm, Real.norm_eq_abs]
  rw [h, ENNReal.ofReal_coe_nnreal]

lemma seminorm_finset_sum_le {d ι : ℕ} (N : Seminorm ℝ (E d)) (s : Finset (Fin ι))
    (f : Fin ι → E d) : N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add N _ _).trans (add_le_add_right ih _)

lemma seminorm_le_const_norm {d : ℕ} (N : Seminorm ℝ (E d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : E d, N z ≤ C * ‖z‖ := by
  let C₀ : ℝ := ∑ i : Fin d, N (EuclideanSpace.single i 1)
  refine ⟨|C₀| + 1, by positivity, fun z => ?_⟩
  have hz : z = ∑ i : Fin d, (z i) • EuclideanSpace.single i (1 : ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have h1 : N z ≤ C₀ * ‖z‖ := by
    calc N z = N (∑ i : Fin d, (z i) • EuclideanSpace.single i (1 : ℝ)) := by rw [← hz]
      _ ≤ ∑ i : Fin d, N ((z i) • EuclideanSpace.single i (1 : ℝ)) :=
          seminorm_finset_sum_le N Finset.univ _
      _ = ∑ i : Fin d, |z i| * N (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul_eq_mul, Real.norm_eq_abs]
      _ ≤ ∑ i : Fin d, ‖z‖ * N (EuclideanSpace.single i 1) := by
          refine Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (PiLp.norm_apply_le z i) (apply_nonneg N _)
      _ = C₀ * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]
  exact h1.trans (mul_le_mul_of_nonneg_right ((le_abs_self C₀).trans (by linarith)) (norm_nonneg _))

lemma continuous_seminorm_Ed {d : ℕ} (N : Seminorm ℝ (E d)) : Continuous N := by
  obtain ⟨C, hC, hbound⟩ := seminorm_le_const_norm N
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε / C, div_pos hε hC, fun y hy => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have hyx : N (y - x) < ε := by
    calc N (y - x) ≤ C * ‖y - x‖ := hbound (y - x)
      _ < C * (ε / C) := mul_lt_mul_of_pos_left (by rwa [dist_eq_norm] at hy) hC
      _ = ε := mul_div_cancel₀ ε hC.ne'
  constructor
  · have := map_add_le_add N (x - y) y
    rw [sub_add_cancel] at this
    have hneg : N (x - y) = N (y - x) := by
      have : x - y = -(y - x) := by abel
      rw [this, map_neg_eq_map]
    linarith
  · have := map_add_le_add N (y - x) x
    rw [sub_add_cancel] at this; linarith

lemma integrable_norm_Ed {d : ℕ} (N : Seminorm ℝ (E d))
    (μ : Measure (E d)) [IsFiniteMeasure μ] (hμ : FiniteFirstMoment N μ) :
    Integrable (fun x : E d => N x) μ := by
  refine ⟨(continuous_seminorm_Ed N).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hle : ∀ x : E d, ‖N x‖ₑ = ENNReal.ofReal (N x) := fun x => by
    change (‖N x‖₊ : ENNReal) = ENNReal.ofReal (N x)
    rw [coe_nnnorm_eq_ofReal_abs, abs_of_nonneg (apply_nonneg N x)]
  calc ∫⁻ x, ‖N x‖ₑ ∂μ = ∫⁻ x, ENNReal.ofReal (N x) ∂μ := lintegral_congr hle
    _ < ⊤ := hμ

lemma integrable_dist_prod {d : ℕ} (N : Seminorm ℝ (E d))
    (μ ν : Measure (E d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : FiniteFirstMoment N μ) (hν : FiniteFirstMoment N ν) :
    Integrable (fun p : E d × E d => N (p.1 - p.2)) (μ.prod ν) := by
  have i1 := (integrable_norm_Ed N μ hμ).mul_prod (integrable_const (1 : ℝ) (μ := ν))
  have i2 := (integrable_const (1 : ℝ) (μ := μ)).mul_prod (integrable_norm_Ed N ν hν)
  have q1 : Integrable (fun p : E d × E d => N p.1) (μ.prod ν) := by simpa using i1
  have q2 : Integrable (fun p : E d × E d => N p.2) (μ.prod ν) := by simpa using i2
  refine (q1.add q2).mono'
    (((continuous_seminorm_Ed N).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (apply_nonneg N _)]
  calc N (p.1 - p.2) = N (p.1 + -p.2) := by rw [sub_eq_add_neg]
    _ ≤ N p.1 + N (-p.2) := map_add_le_add N _ _
    _ = N p.1 + N p.2 := by rw [map_neg_eq_map]

lemma volume_hyp_set_eq_zero {d : ℕ} (H : Hyp d) : (volume : Measure (E d)) H.set = 0 := by
  let Ksub : Submodule ℝ (E d) := LinearMap.ker (innerSL ℝ H.u).toLinearMap
  have hK_ne_top : Ksub ≠ ⊤ := by
    intro htop
    have hu_mem : H.u ∈ Ksub := htop.symm ▸ Submodule.mem_top
    have h0 : inner ℝ H.u H.u = 0 := hu_mem
    rw [real_inner_self_eq_norm_sq] at h0
    exact H.hu (norm_eq_zero.mp (sq_eq_zero_iff.mp h0))
  have hn_pos : 0 < ‖H.u‖ := norm_pos_iff.mpr H.hu
  let z₀ : E d := (H.c / ‖H.u‖ ^ 2) • H.u
  have hz₀ : inner ℝ H.u z₀ = H.c := by
    dsimp [z₀]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hn_pos.ne']
  have hset_eq : H.set = (fun x : E d => x + (-z₀)) ⁻¹' (Ksub : Set (E d)) := by
    ext x
    simp only [Hyp.set, Set.mem_preimage]
    change inner ℝ H.u x = H.c ↔ inner ℝ H.u (x + -z₀) = 0
    rw [inner_add_right, inner_neg_right, hz₀]
    constructor <;> intro h <;> linarith
  rw [hset_eq, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume Ksub hK_ne_top

lemma nontrivial_Ed {d : ℕ} (hd : 1 ≤ d) : Nontrivial (E d) := by
  refine ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), fun h => ?_⟩⟩
  have := congrArg (fun v : E d => v ⟨0, by omega⟩) h
  simp at this

lemma affGenPos_two {d : ℕ} (hd : 1 ≤ d) {S : Set (E d)} (hcardS : ∀ t : Finset (E d),
    (↑t : Set (E d)) ⊆ S → t.card ≤ 2) : AffGenPos d S := by
  have _ := hd
  intro t ht _
  have hle2 := hcardS t ht
  by_cases hsub : Subsingleton (t : Set (E d))
  · exact affineIndependent_of_subsingleton ℝ _
  · rw [subsingleton_iff] at hsub
    push Not at hsub
    obtain ⟨a, _, _⟩ := hsub
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ a]
    have huniq : Subsingleton {x : (t : Set (E d)) // x ≠ a} := by
      refine ⟨fun x y => ?_⟩
      by_contra hxy
      have h1 : x.1.1 ≠ y.1.1 := fun h => hxy (Subtype.ext (Subtype.ext h))
      have h2 : x.1.1 ≠ a.1 := fun h => x.2 (Subtype.ext h)
      have h3 : y.1.1 ≠ a.1 := fun h => y.2 (Subtype.ext h)
      have hcard3 : 3 ≤ ({x.1.1, y.1.1, a.1} : Finset (E d)).card := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [h3]
        · simp [h1, h2]
      have hle : ({x.1.1, y.1.1, a.1} : Finset (E d)).card ≤ t.card := by
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact x.1.2
        · exact y.1.2
        · exact a.2
      omega
    refine Fintype.linearIndependent_iff.mpr (fun g hg i => ?_)
    have hsum : (∑ j, g j • (j.1.1 -ᵥ a.1)) = g i • (i.1.1 -ᵥ a.1) := by
      rw [Finset.sum_eq_single i]
      · intro j _ hji; exact False.elim (hji (Subsingleton.elim j i))
      · intro hi; exact False.elim (hi (Finset.mem_univ i))
    rw [hsum] at hg
    have hne0 : (i.1.1 -ᵥ a.1) ≠ 0 := vsub_ne_zero.mpr (fun h => i.2 (Subtype.ext h))
    exact (smul_eq_zero.mp hg).resolve_right hne0

lemma atoms_dirac {d : ℕ} (z : E d) : atoms (Measure.dirac z) = {z} := by
  ext w
  simp only [atoms, Set.mem_singleton_iff]
  change Measure.dirac z {w} ≠ 0 ↔ w = z
  rw [Measure.dirac_apply' _ (measurableSet_singleton w)]
  by_cases hw : w = z
  · subst hw; simp
  · simp [Set.indicator_of_notMem (Set.mem_singleton_iff.not.mpr (Ne.symm hw)), hw]

lemma nonempty_Pb {d : ℕ} (hd : 1 ≤ d) (N : Seminorm ℝ (E d)) (hN : ∀ x, N x = 0 → x = 0) :
    ∃ p : Measure (E d) × Measure (E d), p ∈ Pb d N ∧ 0 < totalDist N p.1 p.2 := by
  let e₀ : E d := EuclideanSpace.single ⟨0, by omega⟩ 1
  have he₀ : e₀ ≠ 0 := by
    intro h
    have := congrArg (fun v : E d => v ⟨0, by omega⟩) h
    simp [e₀] at this
  refine ⟨(Measure.dirac 0, Measure.dirac e₀), ⟨⟨⟨inferInstance, inferInstance, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · simp [FiniteFirstMoment, lintegral_dirac]
  · simp [FiniteFirstMoment, lintegral_dirac]
  · simp only [atoms_dirac, Set.disjoint_singleton]; exact he₀.symm
  · rw [atoms_dirac, atoms_dirac]
    refine affGenPos_two hd fun t ht => ?_
    have hsub : t ⊆ ({0, e₀} : Finset (E d)) := by
      intro x hx
      have hx' := ht hx
      simp only [Set.mem_union, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton] at hx' ⊢
      exact hx'
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  · intro H
    have hna : ∀ z : E d, nonatomic (Measure.dirac z) H.set = 0 := fun z => by
      have hms : MeasurableSet (H.set ∩ ({z} : Set (E d))ᶜ) :=
        (isClosed_eq (continuous_const.inner continuous_id) continuous_const).measurableSet.inter
          (measurableSet_singleton z).compl
      rw [nonatomic, atoms_dirac, Measure.restrict_apply' (measurableSet_singleton z).compl,
        Measure.dirac_apply' _ hms]
      simp
    exact ⟨hna 0, hna e₀⟩
  · refine ⟨1, ?_, ?_⟩
    · rw [Measure.dirac_apply' _ measurableSet_closedBall.compl]
      have : (0 : E d) ∉ (Metric.closedBall (0 : E d) 1)ᶜ := by simp
      simp [Set.indicator_of_notMem this]
    · rw [Measure.dirac_apply' _ measurableSet_closedBall.compl]
      have he_norm : ‖e₀‖ = 1 := by simp [e₀, PiLp.norm_single]
      have : e₀ ∉ (Metric.closedBall (0 : E d) 1)ᶜ := by simp [he_norm]
      simp [Set.indicator_of_notMem this]
  · simp only [totalDist]
    rw [Measure.dirac_prod_dirac, integral_dirac]
    refine lt_of_le_of_ne (apply_nonneg N _) fun h => ?_
    exact he₀ (sub_eq_zero.mp (hN _ h.symm)).symm

def unitBallMeasure (d : ℕ) : Measure (E d) :=
  ((volume : Measure (E d)) (Metric.closedBall 0 1))⁻¹ •
    (volume : Measure (E d)).restrict (Metric.closedBall 0 1)

lemma unitBallMeasure_isProb {d : ℕ} (hd : 1 ≤ d) : IsProbabilityMeasure (unitBallMeasure d) := by
  have _ := hd
  refine ⟨?_⟩
  unfold unitBallMeasure
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  have hpos : 0 < (volume : Measure (E d)) (Metric.closedBall 0 1) :=
    (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr zero_lt_one)).trans_le
      (measure_mono Metric.ball_subset_closedBall)
  have hlt : (volume : Measure (E d)) (Metric.closedBall 0 1) < ⊤ :=
    (isCompact_closedBall (0 : E d) 1).measure_lt_top
  exact ENNReal.inv_mul_cancel hpos.ne' hlt.ne

lemma unitBallMeasure_singleton {d : ℕ} (hd : 1 ≤ d) (x : E d) : unitBallMeasure d {x} = 0 := by
  haveI := nontrivial_Ed hd
  unfold unitBallMeasure
  rw [Measure.smul_apply, smul_eq_mul]
  have h0 : (volume : Measure (E d)).restrict (Metric.closedBall 0 1) {x} = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans_eq (measure_singleton x)) (zero_le)
  rw [h0, mul_zero]

lemma unitBallMeasure_hyp {d : ℕ} (H : Hyp d) : unitBallMeasure d H.set = 0 := by
  unfold unitBallMeasure
  rw [Measure.smul_apply, smul_eq_mul]
  have h0 : (volume : Measure (E d)).restrict (Metric.closedBall 0 1) H.set = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans_eq (volume_hyp_set_eq_zero H)) (zero_le)
  rw [h0, mul_zero]

lemma unitBallMeasure_compl {d : ℕ} {R : ℝ} (hR : 1 ≤ R) :
    unitBallMeasure d (Metric.closedBall 0 R)ᶜ = 0 := by
  unfold unitBallMeasure
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_closedBall.compl]
  have hdisj : (Metric.closedBall (0 : E d) R)ᶜ ∩ Metric.closedBall 0 1 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hnot hx1
    exact hnot (Metric.closedBall_subset_closedBall hR hx1)
  rw [hdisj, measure_empty, mul_zero]

lemma unitBallMeasure_ffm {d : ℕ} (hd : 1 ≤ d) (N : Seminorm ℝ (E d)) :
    FiniteFirstMoment N (unitBallMeasure d) := by
  haveI := unitBallMeasure_isProb hd
  obtain ⟨C, hC, hbound⟩ := seminorm_le_const_norm N
  unfold FiniteFirstMoment
  have hsupp : unitBallMeasure d (Metric.closedBall 0 1)ᶜ = 0 := unitBallMeasure_compl le_rfl
  have hae : ∀ᵐ x ∂unitBallMeasure d, ENNReal.ofReal (N x) ≤ ENNReal.ofReal C := by
    have hmem : ∀ᵐ x ∂unitBallMeasure d, x ∈ Metric.closedBall (0 : E d) 1 := by
      rw [ae_iff]; exact hsupp
    filter_upwards [hmem] with x hx
    refine ENNReal.ofReal_le_ofReal ?_
    have hnorm : ‖x‖ ≤ 1 := by simpa using hx
    calc N x ≤ C * ‖x‖ := hbound x
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hnorm hC.le
      _ = C := mul_one C
  calc ∫⁻ x, ENNReal.ofReal (N x) ∂unitBallMeasure d
    _ ≤ ∫⁻ _x, ENNReal.ofReal C ∂unitBallMeasure d := lintegral_mono_ae hae
    _ = ENNReal.ofReal C := by simp
    _ < ⊤ := ENNReal.ofReal_lt_top

def truncMeasure {d : ℕ} (μ : Measure (E d)) (R : ℝ) : Measure (E d) :=
  μ.restrict (Metric.closedBall 0 R) + μ (Metric.closedBall 0 R)ᶜ • unitBallMeasure d

lemma truncMeasure_isProb {d : ℕ} (hd : 1 ≤ d) (μ : Measure (E d)) [IsProbabilityMeasure μ] (R : ℝ) :
    IsProbabilityMeasure (truncMeasure μ R) := by
  have := unitBallMeasure_isProb hd
  refine ⟨?_⟩
  unfold truncMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.restrict_apply_univ, measure_univ,
    smul_eq_mul, mul_one, measure_add_measure_compl measurableSet_closedBall, measure_univ]

lemma atoms_truncMeasure {d : ℕ} (hd : 1 ≤ d) (μ : Measure (E d)) (R : ℝ) :
    atoms (truncMeasure μ R) = atoms μ ∩ Metric.closedBall 0 R := by
  ext x
  simp only [atoms, truncMeasure, Set.mem_inter_iff]
  change (μ.restrict (Metric.closedBall 0 R) + μ (Metric.closedBall 0 R)ᶜ • unitBallMeasure d) {x} ≠ 0 ↔
    μ {x} ≠ 0 ∧ x ∈ Metric.closedBall 0 R
  rw [Measure.add_apply, Measure.smul_apply, unitBallMeasure_singleton hd x, smul_zero, add_zero,
    Measure.restrict_apply (measurableSet_singleton x)]
  by_cases hx : x ∈ Metric.closedBall (0 : E d) R
  · have : ({x} : Set (E d)) ∩ Metric.closedBall 0 R = {x} := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hx⟩⟩
    rw [this]; simp [hx]
  · have : ({x} : Set (E d)) ∩ Metric.closedBall 0 R = ∅ := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, hy⟩; exact hx hy
    rw [this, measure_empty]; simp [hx]

lemma truncPair_mem_Pb {d : ℕ} (hd : 1 ≤ d) (N : Seminorm ℝ (E d))
    {μ ν : Measure (E d)} (hP : (μ, ν) ∈ P d N) {R : ℝ} (hR : 1 ≤ R) :
    (truncMeasure μ R, truncMeasure ν R) ∈ Pb d N := by
  rcases hP with ⟨⟨hprobμ, hprobν, hffmμ, hffmν⟩, hdisj, hgen, hna⟩
  have : IsProbabilityMeasure μ := hprobμ
  have : IsProbabilityMeasure ν := hprobν
  have hffm_trunc : ∀ (ρ : Measure (E d)) [IsProbabilityMeasure ρ],
      FiniteFirstMoment N ρ → FiniteFirstMoment N (truncMeasure ρ R) := by
    intro ρ _ hffm
    unfold FiniteFirstMoment truncMeasure
    rw [lintegral_add_measure, lintegral_smul_measure]
    have h1 : (∫⁻ x, ENNReal.ofReal (N x) ∂ρ.restrict (Metric.closedBall 0 R)) ≤
        ∫⁻ x, ENNReal.ofReal (N x) ∂ρ := lintegral_mono' Measure.restrict_le_self le_rfl
    exact ENNReal.add_lt_top.mpr ⟨h1.trans_lt hffm,
      ENNReal.mul_lt_top (measure_lt_top ρ _) (unitBallMeasure_ffm hd N)⟩
  refine ⟨⟨⟨truncMeasure_isProb hd μ R, truncMeasure_isProb hd ν R,
      hffm_trunc μ hffmμ, hffm_trunc ν hffmν⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [atoms_truncMeasure hd μ R, atoms_truncMeasure hd ν R]
    exact hdisj.mono Set.inter_subset_left Set.inter_subset_left
  · rw [atoms_truncMeasure hd μ R, atoms_truncMeasure hd ν R]
    intro t ht hcard
    refine hgen t (ht.trans ?_) hcard
    exact Set.union_subset_union Set.inter_subset_left Set.inter_subset_left
  · intro H
    have hna_trunc : ∀ (ρ : Measure (E d)), nonatomic ρ H.set = 0 →
        nonatomic (truncMeasure ρ R) H.set = 0 := by
      intro ρ hρH
      have hH_meas : MeasurableSet H.set :=
        (isClosed_eq (continuous_const.inner continuous_id) continuous_const).measurableSet
      unfold nonatomic at hρH ⊢
      rw [atoms_truncMeasure hd ρ R]
      have hle1 : (truncMeasure ρ R).restrict (atoms ρ ∩ Metric.closedBall 0 R)ᶜ H.set ≤
          (ρ.restrict (Metric.closedBall 0 R)).restrict (atoms ρ ∩ Metric.closedBall 0 R)ᶜ H.set +
            ρ (Metric.closedBall 0 R)ᶜ * unitBallMeasure d H.set := by
        unfold truncMeasure
        rw [Measure.restrict_add, Measure.add_apply, Measure.restrict_smul, Measure.smul_apply,
          smul_eq_mul]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (Measure.restrict_apply_le _ _) (zero_le))
      rw [unitBallMeasure_hyp H, mul_zero, add_zero] at hle1
      have hle2 : (ρ.restrict (Metric.closedBall 0 R)).restrict
          (atoms ρ ∩ Metric.closedBall 0 R)ᶜ H.set ≤ ρ.restrict (atoms ρ)ᶜ H.set := by
        rw [Measure.restrict_apply hH_meas, Measure.restrict_apply' measurableSet_closedBall,
          Measure.restrict_apply hH_meas]
        refine measure_mono ?_
        rintro x ⟨⟨hxH, hxc⟩, hxB⟩
        exact ⟨hxH, fun hxa => hxc ⟨hxa, hxB⟩⟩
      exact le_antisymm ((hle1.trans hle2).trans_eq hρH) (zero_le)
    exact ⟨hna_trunc μ (hna H).1, hna_trunc ν (hna H).2⟩
  · refine ⟨R, ?_, ?_⟩
    · unfold truncMeasure
      rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply measurableSet_closedBall.compl, Set.compl_inter_self,
        measure_empty, zero_add, unitBallMeasure_compl hR, mul_zero]
    · unfold truncMeasure
      rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply measurableSet_closedBall.compl, Set.compl_inter_self,
        measure_empty, zero_add, unitBallMeasure_compl hR, mul_zero]

lemma prod_restrict_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t) := by
  refine Measure.prod_eq fun A B hA hB => ?_
  rw [Measure.restrict_apply (hA.prod hB), Set.prod_inter_prod, Measure.prod_prod,
    Measure.restrict_apply hA, Measure.restrict_apply hB]

lemma add_prod_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ μ₂ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν] :
    (μ₁ + μ₂).prod ν = μ₁.prod ν + μ₂.prod ν := by
  refine Measure.prod_eq fun A B _ _ => ?_
  rw [Measure.add_apply, Measure.prod_prod, Measure.prod_prod, Measure.add_apply, add_mul]

lemma prod_add_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν₁ ν₂ : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    μ.prod (ν₁ + ν₂) = μ.prod ν₁ + μ.prod ν₂ := by
  refine Measure.prod_eq fun A B _ _ => ?_
  rw [Measure.add_apply, Measure.prod_prod, Measure.prod_prod, Measure.add_apply, mul_add]

lemma smul_prod_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (c : ENNReal) (hc : c ≠ ⊤) (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (c • μ).prod ν = c • (μ.prod ν) := by
  haveI : IsFiniteMeasure (c • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top μ _)⟩
  refine Measure.prod_eq fun A B _ _ => ?_
  rw [Measure.smul_apply, Measure.prod_prod, Measure.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

lemma prod_smul_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (c : ENNReal) (hc : c ≠ ⊤) (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ.prod (c • ν) = c • (μ.prod ν) := by
  have : IsFiniteMeasure (c • ν) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top ν _)⟩
  refine Measure.prod_eq fun A B _ _ => ?_
  rw [Measure.smul_apply, Measure.prod_prod, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

lemma trunc_setIntegral_diff_le {d : ℕ} (hd : 1 ≤ d) (N : Seminorm ℝ (E d))
    (μ ν : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment N μ) (hν : FiniteFirstMoment N ν)
    (R : ℝ) {S : Set (E d × E d)} (hS : MeasurableSet S) :
    |(∫ p in S, N (p.1 - p.2) ∂(μ.prod ν)) -
        ∫ p in S, N (p.1 - p.2) ∂((truncMeasure μ R).prod (truncMeasure ν R))| ≤
      (∫ p in (Metric.closedBall (0 : E d) R ×ˢ Metric.closedBall (0 : E d) R)ᶜ,
        N (p.1 - p.2) ∂(μ.prod ν)) +
      (μ (Metric.closedBall 0 R)ᶜ).toReal *
        (∫ p, N (p.1 - p.2) ∂((unitBallMeasure d).prod ν)) +
      (ν (Metric.closedBall 0 R)ᶜ).toReal *
        (∫ p, N (p.1 - p.2) ∂(μ.prod (unitBallMeasure d))) +
      (μ (Metric.closedBall 0 R)ᶜ * ν (Metric.closedBall 0 R)ᶜ).toReal *
        (∫ p, N (p.1 - p.2) ∂((unitBallMeasure d).prod (unitBallMeasure d))) := by
  haveI := unitBallMeasure_isProb hd
  have hU_ffm := unitBallMeasure_ffm hd N
  let B : Set (E d) := Metric.closedBall 0 R
  let f : E d × E d → ℝ := fun p => N (p.1 - p.2)
  have hf_nn : ∀ p, 0 ≤ f p := fun _ => apply_nonneg N _
  have hcμ : μ Bᶜ ≠ ⊤ := measure_ne_top μ _
  have hcν : ν Bᶜ ≠ ⊤ := measure_ne_top ν _
  haveI : IsFiniteMeasure (μ Bᶜ • unitBallMeasure d) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hcμ.lt_top (measure_lt_top _ _)⟩
  haveI : IsFiniteMeasure (ν Bᶜ • unitBallMeasure d) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hcν.lt_top (measure_lt_top _ _)⟩
  have hprod_eq : (truncMeasure μ R).prod (truncMeasure ν R) =
      (μ.prod ν).restrict (B ×ˢ B) +
        ((μ Bᶜ • ((unitBallMeasure d).prod (ν.restrict B)) +
          ν Bᶜ • ((μ.restrict B).prod (unitBallMeasure d))) +
          (μ Bᶜ * ν Bᶜ) • ((unitBallMeasure d).prod (unitBallMeasure d))) := by
    unfold truncMeasure
    change (μ.restrict B + μ Bᶜ • unitBallMeasure d).prod
        (ν.restrict B + ν Bᶜ • unitBallMeasure d) = _
    rw [add_prod_eq, prod_add_eq, prod_add_eq,
      prod_restrict_eq μ ν measurableSet_closedBall measurableSet_closedBall,
      smul_prod_eq _ hcμ, prod_smul_eq _ hcν, smul_prod_eq _ hcμ, prod_smul_eq _ hcν,
      smul_smul]
    abel
  let m0 := (μ.prod ν).restrict (B ×ˢ B)
  let m1 := μ Bᶜ • ((unitBallMeasure d).prod (ν.restrict B))
  let m2 := ν Bᶜ • ((μ.restrict B).prod (unitBallMeasure d))
  let m3 := (μ Bᶜ * ν Bᶜ) • ((unitBallMeasure d).prod (unitBallMeasure d))
  have i_μν := integrable_dist_prod N μ ν hμ hν
  have i_Uν := integrable_dist_prod N (unitBallMeasure d) ν hU_ffm hν
  have i_μU := integrable_dist_prod N μ (unitBallMeasure d) hμ hU_ffm
  have i_UU := integrable_dist_prod N (unitBallMeasure d) (unitBallMeasure d) hU_ffm hU_ffm
  have hm1_le : m1 ≤ μ Bᶜ • ((unitBallMeasure d).prod ν) := by
    intro T
    dsimp [m1]
    exact mul_le_mul_of_nonneg_left (Measure.prod_mono le_rfl Measure.restrict_le_self T) zero_le
  have hm2_le : m2 ≤ ν Bᶜ • (μ.prod (unitBallMeasure d)) := by
    intro T
    dsimp [m2]
    exact mul_le_mul_of_nonneg_left (Measure.prod_mono Measure.restrict_le_self le_rfl T) zero_le
  have im0 : Integrable f (m0.restrict S) := i_μν.restrict.restrict
  have im1_full : Integrable f m1 :=
    (i_Uν.smul_measure hcμ).mono_measure hm1_le
  have im2_full : Integrable f m2 :=
    (i_μU.smul_measure hcν).mono_measure hm2_le
  have im3_full : Integrable f m3 :=
    i_UU.smul_measure (ENNReal.mul_ne_top hcμ hcν)
  have im1 : Integrable f (m1.restrict S) := im1_full.restrict
  have im2 : Integrable f (m2.restrict S) := im2_full.restrict
  have im3 : Integrable f (m3.restrict S) := im3_full.restrict
  have hsplit_trunc : (∫ p in S, f p ∂((truncMeasure μ R).prod (truncMeasure ν R))) =
      (∫ p in S, f p ∂m0) + ((∫ p in S, f p ∂m1) + (∫ p in S, f p ∂m2) + ∫ p in S, f p ∂m3) := by
    rw [hprod_eq]
    change ∫ p, f p ∂((m0 + ((m1 + m2) + m3)).restrict S) = _
    rw [Measure.restrict_add, Measure.restrict_add, Measure.restrict_add,
      integral_add_measure im0 ((im1.add_measure im2).add_measure im3),
      integral_add_measure (im1.add_measure im2) im3,
      integral_add_measure im1 im2]
  have hm0_eq : (∫ p in S, f p ∂m0) = ∫ p in S ∩ (B ×ˢ B), f p ∂(μ.prod ν) := by
    dsimp [m0]
    rw [Measure.restrict_restrict hS, Set.inter_comm]
  have hBB_meas : MeasurableSet (B ×ˢ B) := measurableSet_closedBall.prod measurableSet_closedBall
  have hsplit_orig : (∫ p in S, f p ∂(μ.prod ν)) =
      (∫ p in S ∩ (B ×ˢ B), f p ∂(μ.prod ν)) + ∫ p in S ∩ (B ×ˢ B)ᶜ, f p ∂(μ.prod ν) := by
    have h := integral_add_compl (μ := (μ.prod ν).restrict S) hBB_meas i_μν.restrict
    rw [Measure.restrict_restrict hBB_meas, Measure.restrict_restrict hBB_meas.compl,
      Set.inter_comm (B ×ˢ B) S, Set.inter_comm (B ×ˢ B)ᶜ S] at h
    exact h.symm
  have htail_le : (∫ p in S ∩ (B ×ˢ B)ᶜ, f p ∂(μ.prod ν)) ≤ ∫ p in (B ×ˢ B)ᶜ, f p ∂(μ.prod ν) :=
    setIntegral_mono_set i_μν.integrableOn (ae_of_all _ hf_nn) (Eventually.of_forall fun _ hx => hx.2)
  have htail_nn : 0 ≤ ∫ p in S ∩ (B ×ˢ B)ᶜ, f p ∂(μ.prod ν) :=
    integral_nonneg hf_nn
  have hm1_bound : 0 ≤ (∫ p in S, f p ∂m1) ∧
      (∫ p in S, f p ∂m1) ≤ (μ Bᶜ).toReal * ∫ p, f p ∂((unitBallMeasure d).prod ν) := by
    refine ⟨integral_nonneg hf_nn, ?_⟩
    calc (∫ p in S, f p ∂m1) ≤ ∫ p, f p ∂m1 :=
          setIntegral_le_integral im1_full (ae_of_all _ hf_nn)
      _ ≤ ∫ p, f p ∂(μ Bᶜ • ((unitBallMeasure d).prod ν)) :=
          integral_mono_measure hm1_le (ae_of_all _ hf_nn) (i_Uν.smul_measure hcμ)
      _ = (μ Bᶜ).toReal * ∫ p, f p ∂((unitBallMeasure d).prod ν) := by
          rw [integral_smul_measure, smul_eq_mul]
  have hm2_bound : 0 ≤ (∫ p in S, f p ∂m2) ∧
      (∫ p in S, f p ∂m2) ≤ (ν Bᶜ).toReal * ∫ p, f p ∂(μ.prod (unitBallMeasure d)) := by
    refine ⟨integral_nonneg hf_nn, ?_⟩
    calc (∫ p in S, f p ∂m2) ≤ ∫ p, f p ∂m2 :=
          setIntegral_le_integral im2_full (ae_of_all _ hf_nn)
      _ ≤ ∫ p, f p ∂(ν Bᶜ • (μ.prod (unitBallMeasure d))) :=
          integral_mono_measure hm2_le (ae_of_all _ hf_nn) (i_μU.smul_measure hcν)
      _ = (ν Bᶜ).toReal * ∫ p, f p ∂(μ.prod (unitBallMeasure d)) := by
          rw [integral_smul_measure, smul_eq_mul]
  have hm3_bound : 0 ≤ (∫ p in S, f p ∂m3) ∧
      (∫ p in S, f p ∂m3) ≤
        (μ Bᶜ * ν Bᶜ).toReal * ∫ p, f p ∂((unitBallMeasure d).prod (unitBallMeasure d)) := by
    refine ⟨integral_nonneg hf_nn, ?_⟩
    calc (∫ p in S, f p ∂m3) ≤ ∫ p, f p ∂m3 :=
          setIntegral_le_integral im3_full (ae_of_all _ hf_nn)
      _ = (μ Bᶜ * ν Bᶜ).toReal * ∫ p, f p ∂((unitBallMeasure d).prod (unitBallMeasure d)) := by
          dsimp [m3]; rw [integral_smul_measure, smul_eq_mul]
  rw [hsplit_orig, hsplit_trunc, hm0_eq]
  have h1nn : 0 ≤ ∫ p in (B ×ˢ B)ᶜ, f p ∂(μ.prod ν) := integral_nonneg hf_nn
  rw [abs_le]
  constructor <;> linarith [hm1_bound.1, hm1_bound.2, hm2_bound.1, hm2_bound.2,
    hm3_bound.1, hm3_bound.2, htail_le, htail_nn, h1nn]

lemma tendsto_compl_closedBall_toReal {d : ℕ} (ρ : Measure (E d)) [IsFiniteMeasure ρ] :
    Tendsto (fun k : ℕ => (ρ (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ).toReal) atTop (𝓝 0) := by
  let S (k : ℕ) : Set (E d) := (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ
  have hmeas : ∀ k, NullMeasurableSet (S k) ρ := fun _ =>
    measurableSet_closedBall.compl.nullMeasurableSet
  have hanti : Antitone S := by
    intro i j hij
    dsimp [S]
    exact Set.compl_subset_compl.mpr
      (Metric.closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right hij 1))
  have hinter : (⋂ k : ℕ, S k) = ∅ := by
    ext x
    simp only [Set.mem_iInter, S, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
      Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    exact ⟨k, hk.le.trans (by linarith)⟩
  have htend := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top ρ _⟩
  rw [hinter, measure_empty] at htend
  have h0 : (0 : ℝ) = (0 : ENNReal).toReal := ENNReal.toReal_zero.symm
  rw [h0]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend

lemma tendsto_prod_tail_zero {d : ℕ} (N : Seminorm ℝ (E d))
    (μ ν : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment N μ) (hν : FiniteFirstMoment N ν) :
    Tendsto (fun k : ℕ =>
      ∫ p in (Metric.closedBall (0 : E d) ((k : ℝ) + 1) ×ˢ
        Metric.closedBall (0 : E d) ((k : ℝ) + 1))ᶜ, N (p.1 - p.2) ∂(μ.prod ν))
      atTop (𝓝 0) := by
  have idist := integrable_dist_prod N μ ν hμ hν
  let T (k : ℕ) : Set (E d × E d) :=
    (Metric.closedBall (0 : E d) ((k : ℝ) + 1) ×ˢ Metric.closedBall (0 : E d) ((k : ℝ) + 1))ᶜ
  have hT_meas : ∀ k, MeasurableSet (T k) := fun _ =>
    (measurableSet_closedBall.prod measurableSet_closedBall).compl
  have hrew : (fun k : ℕ => ∫ p in T k, N (p.1 - p.2) ∂(μ.prod ν)) =
      fun k : ℕ => ∫ p, (T k).indicator (fun q => N (q.1 - q.2)) p ∂(μ.prod ν) :=
    funext fun k => (integral_indicator (hT_meas k)).symm
  change Tendsto (fun k : ℕ => ∫ p in T k, N (p.1 - p.2) ∂(μ.prod ν)) atTop (𝓝 0)
  rw [hrew]
  have hzero : (0 : ℝ) = ∫ _p : E d × E d, (0 : ℝ) ∂(μ.prod ν) := (integral_zero _ _).symm
  rw [hzero]
  refine tendsto_integral_of_dominated_convergence (fun p => N (p.1 - p.2)) ?_ idist ?_ ?_
  · intro k
    exact idist.aestronglyMeasurable.indicator (hT_meas k)
  · intro k
    refine ae_of_all _ fun p => ?_
    by_cases hp : p ∈ T k
    · rw [Set.indicator_of_mem hp, Real.norm_eq_abs, abs_of_nonneg (apply_nonneg N _)]
    · rw [Set.indicator_of_notMem hp, norm_zero]; exact apply_nonneg N _
  · refine ae_of_all _ fun ⟨x, y⟩ => ?_
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨K, hK⟩ := exists_nat_gt (max ‖x‖ ‖y‖)
    refine eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
    dsimp only
    have hk_gt : max ‖x‖ ‖y‖ < (k : ℝ) + 1 :=
      hK.trans_le (by exact_mod_cast Nat.le_succ_of_le hk)
    have hnot : (x, y) ∉ T k := by
      dsimp [T]
      rw [Set.notMem_compl_iff, Set.mem_prod, Metric.mem_closedBall, Metric.mem_closedBall,
        dist_zero_right, dist_zero_right]
      exact ⟨(le_max_left _ _).trans hk_gt.le, (le_max_right _ _).trans hk_gt.le⟩
    rw [Set.indicator_of_notMem hnot]

end

end Aux61

theorem solution (d : ℕ) (hd : 1 ≤ d) (N : Seminorm ℝ (E d)) (hN : ∀ x, N x = 0 → x = 0) :
    cutRatio N (Pb d N) ≤ cutRatio N (P d N) := by
  unfold cutRatio
  obtain ⟨p₀, hp₀Pb, hp₀L⟩ := Aux61.nonempty_Pb hd N hN
  have hne_Pb : Nonempty {p : Measure (E d) × Measure (E d) //
      p ∈ Pb d N ∧ 0 < totalDist N p.1 p.2} := ⟨⟨p₀, hp₀Pb, hp₀L⟩⟩
  have hne_P : Nonempty {p : Measure (E d) × Measure (E d) //
      p ∈ P d N ∧ 0 < totalDist N p.1 p.2} := ⟨⟨p₀, hp₀Pb.1, hp₀L⟩⟩
  have hbdd_Pb : BddBelow (Set.range fun q : {p : Measure (E d) × Measure (E d) //
      p ∈ Pb d N ∧ 0 < totalDist N p.1 p.2} =>
        ⨆ H : Hyp d, cutVal N q.1.1 q.1.2 H / totalDist N q.1.1 q.1.2) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact Real.iSup_nonneg fun H =>
      div_nonneg (integral_nonneg fun _ => apply_nonneg N _) q.2.2.le
  refine le_ciInf fun ⟨⟨μ, ν⟩, hP, hL⟩ => ?_
  rcases hP with ⟨⟨hprobμ, hprobν, hffmμ, hffmν⟩, hdisj, hgen, hna⟩
  have : IsProbabilityMeasure μ := hprobμ
  have : IsProbabilityMeasure ν := hprobν
  set S_μν : ℝ := ⨆ H : Hyp d, cutVal N μ ν H / totalDist N μ ν
  have idist_orig := Aux61.integrable_dist_prod N μ ν hffmμ hffmν
  have hbdd_H_orig : BddAbove (Set.range fun H : Hyp d => cutVal N μ ν H / totalDist N μ ν) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨H, rfl⟩
    exact (div_le_one hL).mpr (setIntegral_le_integral idist_orig (ae_of_all _ fun _ => apply_nonneg N _))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let err (k : ℕ) : ℝ :=
    (∫ p in (Metric.closedBall (0 : E d) ((k : ℝ) + 1) ×ˢ
        Metric.closedBall (0 : E d) ((k : ℝ) + 1))ᶜ, N (p.1 - p.2) ∂(μ.prod ν)) +
      (μ (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ).toReal *
        (∫ p, N (p.1 - p.2) ∂((Aux61.unitBallMeasure d).prod ν)) +
      (ν (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ).toReal *
        (∫ p, N (p.1 - p.2) ∂(μ.prod (Aux61.unitBallMeasure d))) +
      (μ (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ *
        ν (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ).toReal *
        (∫ p, N (p.1 - p.2) ∂((Aux61.unitBallMeasure d).prod (Aux61.unitBallMeasure d)))
  have herr_tend : Tendsto err atTop (𝓝 0) := by
    have t1 := Aux61.tendsto_prod_tail_zero N μ ν hffmμ hffmν
    have t2 := (Aux61.tendsto_compl_closedBall_toReal μ).mul_const
      (∫ p, N (p.1 - p.2) ∂((Aux61.unitBallMeasure d).prod ν))
    have t3 := (Aux61.tendsto_compl_closedBall_toReal ν).mul_const
      (∫ p, N (p.1 - p.2) ∂(μ.prod (Aux61.unitBallMeasure d)))
    have t4 : Tendsto (fun k : ℕ =>
        (μ (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ *
          ν (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ).toReal *
        (∫ p, N (p.1 - p.2) ∂((Aux61.unitBallMeasure d).prod (Aux61.unitBallMeasure d))))
        atTop (𝓝 0) := by
      have hmul : ∀ k : ℕ,
          (μ (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ *
            ν (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ).toReal =
          (μ (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ).toReal *
            (ν (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ).toReal := fun _ => ENNReal.toReal_mul
      simp_rw [hmul]
      simpa using ((Aux61.tendsto_compl_closedBall_toReal μ).mul
        (Aux61.tendsto_compl_closedBall_toReal ν)).mul_const _
    simpa [err] using ((t1.add t2).add t3).add t4
  have hthresh : 0 < min (totalDist N μ ν / 2) (ε * totalDist N μ ν / 2) :=
    lt_min (half_pos hL) (by positivity)
  obtain ⟨k, hk⟩ := (herr_tend.eventually (gt_mem_nhds hthresh)).exists
  set R : ℝ := (k : ℝ) + 1
  have hk_nn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hR1 : 1 ≤ R := by dsimp [R]; linarith
  let μ' := Aux61.truncMeasure μ R
  let ν' := Aux61.truncMeasure ν R
  have hPb' : (μ', ν') ∈ Pb d N :=
    Aux61.truncPair_mem_Pb hd N ⟨⟨hprobμ, hprobν, hffmμ, hffmν⟩, hdisj, hgen, hna⟩ hR1
  have hL_diff : |totalDist N μ ν - totalDist N μ' ν'| ≤ err k := by
    have h := Aux61.trunc_setIntegral_diff_le hd N μ ν hffmμ hffmν R MeasurableSet.univ
    simpa [totalDist, μ', ν', R, err] using h
  have herr_nn : 0 ≤ err k := (abs_nonneg _).trans hL_diff
  have herr_lt1 : err k < totalDist N μ ν / 2 := (lt_min_iff.mp hk).1
  have herr_lt2 : err k < ε * totalDist N μ ν / 2 := (lt_min_iff.mp hk).2
  have hL'_pos : 0 < totalDist N μ' ν' := by
    have := (abs_sub_le_iff.mp hL_diff).1
    linarith
  haveI : Nonempty (Hyp d) := by
    let e₀ : E d := EuclideanSpace.single ⟨0, by omega⟩ 1
    have he₀ : e₀ ≠ 0 := by
      intro h; have := congrArg (fun v : E d => v ⟨0, by omega⟩) h; simp [e₀] at this
    exact ⟨⟨e₀, 0, he₀⟩⟩
  have hsup_le : (⨆ H : Hyp d, cutVal N μ' ν' H / totalDist N μ' ν') ≤ S_μν + ε := by
    refine ciSup_le fun H => ?_
    have hms_sep : MeasurableSet (SepMeasures.Sep H) :=
      ((isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet.prod
        (isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet).union
        ((isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet.prod
        (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet)
    have hC_diff : |cutVal N μ ν H - cutVal N μ' ν' H| ≤ err k := by
      simpa [cutVal, μ', ν', R, err] using
        Aux61.trunc_setIntegral_diff_le hd N μ ν hffmμ hffmν R hms_sep
    have hC'_nn : 0 ≤ cutVal N μ' ν' H := integral_nonneg fun _ => apply_nonneg N _
    have hC'_le_L' : cutVal N μ' ν' H ≤ totalDist N μ' ν' := by
      haveI := hPb'.1.1.1
      haveI := hPb'.1.1.2.1
      exact setIntegral_le_integral
        (Aux61.integrable_dist_prod N μ' ν' hPb'.1.1.2.2.1 hPb'.1.1.2.2.2)
        (ae_of_all _ fun _ => apply_nonneg N _)
    have hratio_C' : cutVal N μ' ν' H / totalDist N μ' ν' ≤ 1 := (div_le_one hL'_pos).mpr hC'_le_L'
    have hratio_nn : 0 ≤ cutVal N μ' ν' H / totalDist N μ' ν' := div_nonneg hC'_nn hL'_pos.le
    have hid : cutVal N μ' ν' H / totalDist N μ' ν' - cutVal N μ ν H / totalDist N μ ν =
        (cutVal N μ' ν' H - cutVal N μ ν H) / totalDist N μ ν +
          (cutVal N μ' ν' H / totalDist N μ' ν') *
            ((totalDist N μ ν - totalDist N μ' ν') / totalDist N μ ν) := by
      field_simp [hL.ne', hL'_pos.ne']
      ring
    have h1 : (cutVal N μ' ν' H - cutVal N μ ν H) / totalDist N μ ν ≤ err k / totalDist N μ ν :=
      div_le_div_of_nonneg_right (abs_sub_le_iff.mp hC_diff).2 hL.le
    have h2 : (cutVal N μ' ν' H / totalDist N μ' ν') *
          ((totalDist N μ ν - totalDist N μ' ν') / totalDist N μ ν) ≤ err k / totalDist N μ ν := by
      have hd1 : (totalDist N μ ν - totalDist N μ' ν') / totalDist N μ ν ≤
          err k / totalDist N μ ν :=
        div_le_div_of_nonneg_right (abs_sub_le_iff.mp hL_diff).1 hL.le
      calc (cutVal N μ' ν' H / totalDist N μ' ν') *
            ((totalDist N μ ν - totalDist N μ' ν') / totalDist N μ ν)
        _ ≤ (cutVal N μ' ν' H / totalDist N μ' ν') * (err k / totalDist N μ ν) :=
            mul_le_mul_of_nonneg_left hd1 hratio_nn
        _ ≤ 1 * (err k / totalDist N μ ν) :=
            mul_le_mul_of_nonneg_right hratio_C' (div_nonneg herr_nn hL.le)
        _ = err k / totalDist N μ ν := one_mul _
    have hsum12 : err k / totalDist N μ ν + err k / totalDist N μ ν =
        2 * err k / totalDist N μ ν := by ring
    have h2e : 2 * err k / totalDist N μ ν < ε :=
      (div_lt_iff₀ hL).mpr (by linarith)
    have hC_le_S : cutVal N μ ν H / totalDist N μ ν ≤ S_μν := le_ciSup hbdd_H_orig H
    linarith
  exact (ciInf_le hbdd_Pb ⟨(μ', ν'), hPb', hL'_pos⟩).trans hsup_le
