-- Prove2me | solution 1 for SepMeasures.theorem_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:57:05.394795+00:00
-- url     : https://prove2.me/submissions/feafafab-c965-4d23-ab5e-d7c3d0cb9b72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families
import Theorems.Thm_SepMeasures_lemma_6_1
import Theorems.Thm_SepMeasures_lemma_6_2
import Theorems.Thm_SepMeasures_eq_8
import Theorems.Thm_SepMeasures_pinelis_planar_norm_representation

open MeasureTheory SepMeasures Filter Topology

namespace Aux33

noncomputable section

def vec (θ : ℝ) : E 2 := !₂[Real.cos θ, Real.sin θ]

lemma continuous_vec : Continuous vec := by
  have heq : vec = fun θ : ℝ =>
      Real.cos θ • EuclideanSpace.single 0 (1 : ℝ) +
        Real.sin θ • EuclideanSpace.single 1 (1 : ℝ) := by
    ext θ i
    fin_cases i <;> simp [vec]
  rw [heq]
  exact (Real.continuous_cos.smul continuous_const).add (Real.continuous_sin.smul continuous_const)

lemma norm_vec (θ : ℝ) : ‖vec θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Fin.isValue, vec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs, sq_abs, Real.cos_sq_add_sin_sq, Real.sqrt_one]

lemma vec_ne_zero (θ : ℝ) : vec θ ≠ 0 := by
  intro h
  have := norm_vec θ
  rw [h, norm_zero] at this
  norm_num at this

lemma vec_add_pi (θ : ℝ) : vec (θ + Real.pi) = -vec θ := by
  ext i
  fin_cases i
  · simp [vec, Real.cos_add_pi]
  · simp [vec, Real.sin_add_pi]

def lineHyp (θ c : ℝ) : Hyp 2 := ⟨vec θ, c, vec_ne_zero θ⟩

lemma lineHyp_add_pi_sign (θ c : ℝ) (x : E 2) :
    (lineHyp (θ + Real.pi) (-c)).sign x = -(lineHyp θ c).sign x := by
  simp only [Hyp.sign, lineHyp, vec_add_pi, inner_neg_left]
  by_cases h1 : -c < -inner ℝ (vec θ) x
  · have h2 : inner ℝ (vec θ) x < c := by linarith
    have h3 : ¬ c < inner ℝ (vec θ) x := by linarith
    simp [h1, h2, h3]
  · by_cases h2 : -inner ℝ (vec θ) x < -c
    · have h3 : c < inner ℝ (vec θ) x := by linarith
      simp [h1, h2, h3]
    · have h3 : ¬ c < inner ℝ (vec θ) x := by linarith
      have h4 : ¬ inner ℝ (vec θ) x < c := by linarith
      simp [h1, h2, h3, h4]

lemma lineHyp_sign_antitone (θ : ℝ) {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) (x : E 2) :
    (lineHyp θ c₂).sign x ≤ (lineHyp θ c₁).sign x := by
  simp only [Hyp.sign, lineHyp]
  by_cases h1 : c₂ < inner ℝ (vec θ) x
  · have h2 : c₁ < inner ℝ (vec θ) x := lt_of_le_of_lt hc h1
    simp [h1, h2]
  · by_cases h2 : inner ℝ (vec θ) x < c₂
    · by_cases h3 : c₁ < inner ℝ (vec θ) x
      · simp [h1, h2, h3]
      · by_cases h4 : inner ℝ (vec θ) x < c₁
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]
    · have h4 : ¬ inner ℝ (vec θ) x < c₁ := by linarith
      by_cases h5 : c₁ < inner ℝ (vec θ) x <;> simp [h1, h2, h4, h5]

lemma abs_sign_le_one {d : ℕ} (K : Hyp d) (x : E d) : |K.sign x| ≤ 1 := by
  unfold Hyp.sign
  split_ifs <;> norm_num

lemma coe_nnnorm_eq_ofReal_abs (r : ℝ) : (‖r‖₊ : ENNReal) = ENNReal.ofReal |r| := by
  have h : |r| = (‖r‖₊ : ℝ) := by rw [coe_nnnorm, Real.norm_eq_abs]
  rw [h, ENNReal.ofReal_coe_nnreal]

lemma seminorm_le_const_norm_E2 (N : Seminorm ℝ (E 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : E 2, N z ≤ C * ‖z‖ := by
  let C : ℝ := N (vec 0) + N (vec (Real.pi / 2)) + 1
  have hC : 0 < C := by
    dsimp [C]; linarith [apply_nonneg N (vec 0), apply_nonneg N (vec (Real.pi / 2))]
  refine ⟨C, hC, fun z => ?_⟩
  have hz : z = (z 0) • vec 0 + (z 1) • vec (Real.pi / 2) := by
    ext i; fin_cases i <;> simp [vec]
  have h0 : |z 0| ≤ ‖z‖ := PiLp.norm_apply_le z 0
  have h1 : |z 1| ≤ ‖z‖ := PiLp.norm_apply_le z 1
  have hle : N z ≤ (N (vec 0) + N (vec (Real.pi / 2))) * ‖z‖ := by
    calc N z = N ((z 0) • vec 0 + (z 1) • vec (Real.pi / 2)) := by rw [← hz]
      _ ≤ N ((z 0) • vec 0) + N ((z 1) • vec (Real.pi / 2)) := map_add_le_add N _ _
      _ = |z 0| * N (vec 0) + |z 1| * N (vec (Real.pi / 2)) := by
          rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖z‖ * N (vec 0) + ‖z‖ * N (vec (Real.pi / 2)) :=
          add_le_add (mul_le_mul_of_nonneg_right h0 (apply_nonneg N _))
            (mul_le_mul_of_nonneg_right h1 (apply_nonneg N _))
      _ = (N (vec 0) + N (vec (Real.pi / 2))) * ‖z‖ := by ring
  exact hle.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg z))

lemma continuous_seminorm_E2 (N : Seminorm ℝ (E 2)) : Continuous N := by
  obtain ⟨C, hC, hbound⟩ := seminorm_le_const_norm_E2 N
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

lemma norm_lower_bound_E2 (N : Seminorm ℝ (E 2)) (hN : ∀ x, N x = 0 → x = 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ z : E 2, c₀ * ‖z‖ ≤ N z := by
  have hne : (Metric.sphere (0 : E 2) 1).Nonempty := ⟨vec 0, by simp [norm_vec]⟩
  obtain ⟨u₀, hu₀_sph, hmin⟩ :=
    (isCompact_sphere (0 : E 2) 1).exists_isMinOn hne (continuous_seminorm_E2 N).continuousOn
  have hu₀_norm : ‖u₀‖ = 1 := by simpa using hu₀_sph
  have hu₀_ne : u₀ ≠ 0 := by intro h; rw [h, norm_zero] at hu₀_norm; norm_num at hu₀_norm
  have hc₀_pos : 0 < N u₀ := lt_of_le_of_ne (apply_nonneg N _) (fun h => hu₀_ne (hN _ h.symm))
  refine ⟨N u₀, hc₀_pos, fun z => ?_⟩
  by_cases hz : z = 0
  · simp [hz]
  · have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hmem : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E 2) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hnz), inv_mul_cancel₀ hnz.ne']
    have hle : N u₀ ≤ N (‖z‖⁻¹ • z) := hmin hmem
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnz)] at hle
    have := (le_inv_mul_iff₀ hnz).mp hle
    nlinarith

lemma integrable_norm_E2 (N : Seminorm ℝ (E 2))
    (μ : Measure (E 2)) [IsFiniteMeasure μ] (hμ : FiniteFirstMoment N μ) :
    Integrable (fun x : E 2 => N x) μ := by
  refine ⟨(continuous_seminorm_E2 N).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hle : ∀ x : E 2, ‖N x‖ₑ = ENNReal.ofReal (N x) := fun x => by
    change (‖N x‖₊ : ENNReal) = ENNReal.ofReal (N x)
    rw [coe_nnnorm_eq_ofReal_abs, abs_of_nonneg (apply_nonneg N x)]
  calc ∫⁻ x, ‖N x‖ₑ ∂μ = ∫⁻ x, ENNReal.ofReal (N x) ∂μ := lintegral_congr hle
    _ < ⊤ := hμ

lemma integrable_dist_prod_E2 (N : Seminorm ℝ (E 2))
    (μ ν : Measure (E 2)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : FiniteFirstMoment N μ) (hν : FiniteFirstMoment N ν) :
    Integrable (fun p : E 2 × E 2 => N (p.1 - p.2)) (μ.prod ν) := by
  have i1 := (integrable_norm_E2 N μ hμ).mul_prod (integrable_const (1 : ℝ) (μ := ν))
  have i2 := (integrable_const (1 : ℝ) (μ := μ)).mul_prod (integrable_norm_E2 N ν hν)
  have q1 : Integrable (fun p : E 2 × E 2 => N p.1) (μ.prod ν) := by simpa using i1
  have q2 : Integrable (fun p : E 2 × E 2 => N p.2) (μ.prod ν) := by simpa using i2
  refine (q1.add q2).mono'
    (((continuous_seminorm_E2 N).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)
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
    dsimp [z₀]; rw [inner_smul_right, real_inner_self_eq_norm_sq]; field_simp [hn_pos.ne']
  have hset_eq : H.set = (fun x : E d => x + (-z₀)) ⁻¹' (Ksub : Set (E d)) := by
    ext x
    simp only [Hyp.set, Set.mem_preimage]
    change inner ℝ H.u x = H.c ↔ inner ℝ H.u (x + -z₀) = 0
    rw [inner_add_right, inner_neg_right, hz₀]
    constructor <;> intro h <;> linarith
  rw [hset_eq, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume Ksub hK_ne_top

lemma measurableSet_hyp_pos {d : ℕ} (K : Hyp d) : MeasurableSet K.pos :=
  isOpen_lt continuous_const (continuous_const.inner continuous_id) |>.measurableSet

lemma measurableSet_hyp_neg {d : ℕ} (K : Hyp d) : MeasurableSet K.neg :=
  isOpen_lt (continuous_const.inner continuous_id) continuous_const |>.measurableSet

lemma measurable_sign {d : ℕ} (K : Hyp d) : Measurable K.sign := by
  unfold Hyp.sign
  exact Measurable.ite (measurableSet_hyp_pos K) measurable_const
    (Measurable.ite (measurableSet_hyp_neg K) measurable_const measurable_const)

lemma measurableSet_sep {d : ℕ} (K : Hyp d) : MeasurableSet (SepMeasures.Sep K) :=
  ((measurableSet_hyp_pos K).prod (measurableSet_hyp_neg K)).union
    ((measurableSet_hyp_neg K).prod (measurableSet_hyp_pos K))

lemma integrable_weighted_sign (μ : Measure (E 2)) [IsProbabilityMeasure μ]
    {w : E 2 → ℝ} (hw_meas : Measurable w) (hw_le : ∀ x, |w x| ≤ 1) (K : Hyp 2) :
    Integrable (fun x => w x * K.sign x) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (hw_meas.mul (measurable_sign K)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |w x| * |K.sign x| ≤ 1 * 1 :=
      mul_le_mul (hw_le x) (abs_sign_le_one K x) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

def unifBall (x₀ : E 2) (r : ℝ) : Measure (E 2) :=
  ((volume : Measure (E 2)) (Metric.closedBall x₀ r))⁻¹ •
    (volume : Measure (E 2)).restrict (Metric.closedBall x₀ r)

lemma unifBall_isProb (x₀ : E 2) {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (unifBall x₀ r) := by
  refine ⟨?_⟩
  unfold unifBall
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  have hpos : 0 < (volume : Measure (E 2)) (Metric.closedBall x₀ r) :=
    (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hr)).trans_le
      (measure_mono Metric.ball_subset_closedBall)
  have hlt : (volume : Measure (E 2)) (Metric.closedBall x₀ r) < ⊤ :=
    (isCompact_closedBall x₀ r).measure_lt_top
  exact ENNReal.inv_mul_cancel hpos.ne' hlt.ne

lemma unifBall_ac (x₀ : E 2) (r : ℝ) : unifBall x₀ r ≪ volume := by
  intro s hs
  unfold unifBall
  rw [Measure.smul_apply, smul_eq_mul]
  have h0 : (volume : Measure (E 2)).restrict (Metric.closedBall x₀ r) s = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans_eq hs) zero_le
  rw [h0, mul_zero]

lemma unifBall_apply_self_compl (x₀ : E 2) (r : ℝ) :
    unifBall x₀ r (Metric.closedBall x₀ r)ᶜ = 0 := by
  unfold unifBall
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_closedBall.compl,
    Set.compl_inter_self, measure_empty, mul_zero]

lemma atoms_eq_empty_of_ac {μ : Measure (E 2)} (hμ : μ ≪ volume) : atoms μ = ∅ := by
  have : Nontrivial (E 2) := ⟨⟨0, vec 0, (vec_ne_zero 0).symm⟩⟩
  ext x
  simp only [atoms, Set.mem_empty_iff_false, iff_false]
  change ¬ μ {x} ≠ 0
  rw [not_not]
  exact hμ (measure_singleton x)

lemma nonempty_Pbc_two (N : Seminorm ℝ (E 2)) (hN : ∀ x, N x = 0 → x = 0) :
    ∃ p : Measure (E 2) × Measure (E 2), p ∈ Pbc 2 N ∧ 0 < totalDist N p.1 p.2 := by
  let μ₀ := unifBall 0 (1 / 4)
  let ν₀ := unifBall (vec 0) (1 / 4)
  have hprobμ : IsProbabilityMeasure μ₀ := unifBall_isProb 0 (by norm_num)
  have hprobν : IsProbabilityMeasure ν₀ := unifBall_isProb (vec 0) (by norm_num)
  have hacμ : μ₀ ≪ volume := unifBall_ac 0 (1 / 4)
  have hacν : ν₀ ≪ volume := unifBall_ac (vec 0) (1 / 4)
  have hsub1 : Metric.closedBall (0 : E 2) (1 / 4) ⊆ Metric.closedBall 0 2 :=
    Metric.closedBall_subset_closedBall (by norm_num)
  have hsub2 : Metric.closedBall (vec 0) (1 / 4) ⊆ Metric.closedBall 0 2 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have hx' : ‖x - vec 0‖ ≤ 1 / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    calc ‖x‖ = ‖(x - vec 0) + vec 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - vec 0‖ + ‖vec 0‖ := norm_add_le _ _
      _ ≤ 1 / 4 + 1 := by rw [norm_vec]; linarith
      _ ≤ 2 := by norm_num
  have hcμ : μ₀ (Metric.closedBall 0 2)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr hsub1) (unifBall_apply_self_compl 0 (1 / 4))
  have hcν : ν₀ (Metric.closedBall 0 2)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr hsub2) (unifBall_apply_self_compl (vec 0) (1 / 4))
  obtain ⟨C, hC, hbound⟩ := seminorm_le_const_norm_E2 N
  have hffm : ∀ (η : Measure (E 2)), IsProbabilityMeasure η →
      η (Metric.closedBall 0 2)ᶜ = 0 → FiniteFirstMoment N η := by
    intro η hprob hc
    have _ := hprob
    unfold FiniteFirstMoment
    have hae : ∀ᵐ x ∂η, ENNReal.ofReal (N x) ≤ ENNReal.ofReal (2 * C) := by
      have hmem : ∀ᵐ x ∂η, x ∈ Metric.closedBall (0 : E 2) 2 := by rw [ae_iff]; exact hc
      filter_upwards [hmem] with x hx
      refine ENNReal.ofReal_le_ofReal ?_
      have hnx : ‖x‖ ≤ 2 := by simpa using hx
      calc N x ≤ C * ‖x‖ := hbound x
        _ ≤ C * 2 := mul_le_mul_of_nonneg_left hnx hC.le
        _ = 2 * C := by ring
    calc ∫⁻ x, ENNReal.ofReal (N x) ∂η
      _ ≤ ∫⁻ _x, ENNReal.ofReal (2 * C) ∂η := lintegral_mono_ae hae
      _ = ENNReal.ofReal (2 * C) := by simp
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hffmμ := hffm μ₀ hprobμ hcμ
  have hffmν := hffm ν₀ hprobν hcν
  refine ⟨(μ₀, ν₀), ⟨⟨⟨⟨hprobμ, hprobν, hffmμ, hffmν⟩, ?_, ?_, ?_⟩, ⟨2, hcμ, hcν⟩⟩, hacμ, hacν⟩, ?_⟩
  · simp [atoms_eq_empty_of_ac hacμ, atoms_eq_empty_of_ac hacν]
  · rw [atoms_eq_empty_of_ac hacμ, atoms_eq_empty_of_ac hacν, Set.union_self]
    intro t ht _
    have ht0 : t = ∅ := Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp ht)
    subst ht0
    have : Subsingleton (↑(∅ : Finset (E 2)) : Set (E 2)) :=
      ⟨fun ⟨x, hx⟩ => False.elim (by simp at hx)⟩
    exact affineIndependent_of_subsingleton ℝ _
  · intro H
    exact ⟨le_antisymm ((Measure.restrict_apply_le _ _).trans_eq (hacμ (volume_hyp_set_eq_zero H))) zero_le,
      le_antisymm ((Measure.restrict_apply_le _ _).trans_eq (hacν (volume_hyp_set_eq_zero H))) zero_le⟩
  · obtain ⟨c₀, hc₀, hlow⟩ := norm_lower_bound_E2 N hN
    let B₁ := Metric.closedBall (0 : E 2) (1 / 4)
    let B₂ := Metric.closedBall (vec 0) (1 / 4)
    have hprod_one : (μ₀.prod ν₀) (B₁ ×ˢ B₂) = 1 := by
      rw [Measure.prod_prod]
      have h1 : μ₀ B₁ = 1 := by
        have := measure_add_measure_compl (μ := μ₀) (s := B₁) measurableSet_closedBall
        rw [unifBall_apply_self_compl 0 (1 / 4), add_zero, measure_univ] at this
        exact this
      have h2 : ν₀ B₂ = 1 := by
        have := measure_add_measure_compl (μ := ν₀) (s := B₂) measurableSet_closedBall
        rw [unifBall_apply_self_compl (vec 0) (1 / 4), add_zero, measure_univ] at this
        exact this
      rw [h1, h2, mul_one]
    have hcompl_zero : (μ₀.prod ν₀) (B₁ ×ˢ B₂)ᶜ = 0 := by
      have := measure_add_measure_compl (μ := μ₀.prod ν₀) (s := B₁ ×ˢ B₂)
        (measurableSet_closedBall.prod measurableSet_closedBall)
      rw [hprod_one, measure_univ] at this
      have hfin : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
      exact (ENNReal.add_right_inj hfin).mp (by rw [add_zero]; exact this)
    have hae : ∀ᵐ p ∂(μ₀.prod ν₀), c₀ / 2 ≤ N (p.1 - p.2) := by
      have hmem : ∀ᵐ p ∂(μ₀.prod ν₀), p ∈ B₁ ×ˢ B₂ := by rw [ae_iff]; exact hcompl_zero
      filter_upwards [hmem] with p hp
      have hp1 : ‖p.1‖ ≤ 1 / 4 := by simpa [B₁] using hp.1
      have hp2 : ‖p.2 - vec 0‖ ≤ 1 / 4 := by simpa [B₂, dist_eq_norm] using hp.2
      have htri : (1 : ℝ) ≤ ‖p.1‖ + ‖p.2 - vec 0‖ + ‖p.1 - p.2‖ := by
        have hv : vec 0 = p.1 - (p.2 - vec 0) - (p.1 - p.2) := by abel
        calc (1 : ℝ) = ‖vec 0‖ := (norm_vec 0).symm
          _ = ‖(p.1 - (p.2 - vec 0)) - (p.1 - p.2)‖ := by rw [← hv]
          _ ≤ ‖p.1 - (p.2 - vec 0)‖ + ‖p.1 - p.2‖ := norm_sub_le _ _
          _ ≤ (‖p.1‖ + ‖p.2 - vec 0‖) + ‖p.1 - p.2‖ := add_le_add (norm_sub_le _ _) le_rfl
      have hd : 1 / 2 ≤ ‖p.1 - p.2‖ := by linarith
      calc c₀ / 2 = c₀ * (1 / 2) := by ring
        _ ≤ c₀ * ‖p.1 - p.2‖ := mul_le_mul_of_nonneg_left hd hc₀.le
        _ ≤ N (p.1 - p.2) := hlow _
    have hint := integrable_dist_prod_E2 N μ₀ ν₀ hffmμ hffmν
    have hle := integral_mono_ae (integrable_const (c₀ / 2)) hint hae
    have hconst : ∫ _p, c₀ / 2 ∂(μ₀.prod ν₀) = c₀ / 2 := by simp
    rw [hconst] at hle
    exact lt_of_lt_of_le (by positivity) hle

lemma continuous_weighted_sign_integral
    (ν : Measure (E 2)) [IsProbabilityMeasure ν] (hν : ν ≪ volume)
    {w : E 2 → ℝ} (hw_meas : Measurable w) (hw_le : ∀ x, |w x| ≤ 1) :
    Continuous (fun p : ℝ × ℝ => ∫ x, w x * (lineHyp p.1 p.2).sign x ∂ν) := by
  rw [continuous_iff_seqContinuous]
  intro u p₀ hu
  have hnull : ν (lineHyp p₀.1 p₀.2).set = 0 := hν (volume_hyp_set_eq_zero _)
  have hae : ∀ᵐ x ∂ν, Tendsto (fun n => w x * (lineHyp (u n).1 (u n).2).sign x)
      atTop (𝓝 (w x * (lineHyp p₀.1 p₀.2).sign x)) := by
    have hnot : ∀ᵐ x ∂ν, x ∉ (lineHyp p₀.1 p₀.2).set := by rw [ae_iff]; simpa using hnull
    filter_upwards [hnot] with x hx
    change inner ℝ (vec p₀.1) x ≠ p₀.2 at hx
    have hcont_f : Continuous (fun q : ℝ × ℝ => inner ℝ (vec q.1) x - q.2) :=
      ((continuous_vec.comp continuous_fst).inner continuous_const).sub continuous_snd
    have htend_f : Tendsto (fun n => inner ℝ (vec (u n).1) x - (u n).2) atTop
        (𝓝 (inner ℝ (vec p₀.1) x - p₀.2)) := (hcont_f.tendsto p₀).comp hu
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · have hev : ∀ᶠ n in atTop, inner ℝ (vec (u n).1) x - (u n).2 < 0 :=
        htend_f.eventually (gt_mem_nhds (by linarith))
      have hnp : ¬ p₀.2 < inner ℝ (vec p₀.1) x := by linarith
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      have hn1 : inner ℝ (vec (u n).1) x < (u n).2 := by linarith
      have hn2 : ¬ (u n).2 < inner ℝ (vec (u n).1) x := by linarith
      simp [Hyp.sign, lineHyp, hn1, hn2, hlt, hnp]
    · have hev : ∀ᶠ n in atTop, 0 < inner ℝ (vec (u n).1) x - (u n).2 :=
        htend_f.eventually (lt_mem_nhds (by linarith))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      have hn1 : (u n).2 < inner ℝ (vec (u n).1) x := by linarith
      simp [Hyp.sign, lineHyp, hn1, hgt]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (hw_meas.mul (measurable_sign _)).aestronglyMeasurable)
    (integrable_const (1 : ℝ)) (fun n => ae_of_all _ fun x => ?_) hae
  rw [Real.norm_eq_abs, abs_mul]
  calc |w x| * |(lineHyp (u n).1 (u n).2).sign x| ≤ 1 * 1 :=
      mul_le_mul (hw_le x) (abs_sign_le_one _ x) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma unifBall_sign_strictAnti {M : ℝ} (hM : 0 < M) (θ : ℝ)
    {c₁ c₂ : ℝ} (hc₁ : -M ≤ c₁) (hc₂ : c₂ ≤ M) (hlt : c₁ < c₂) :
    (∫ x, (lineHyp θ c₂).sign x ∂unifBall 0 M) <
      (∫ x, (lineHyp θ c₁).sign x ∂unifBall 0 M) := by
  have : IsProbabilityMeasure (unifBall 0 M) := unifBall_isProb 0 hM
  let S : Set (E 2) := {x | c₁ < inner ℝ (vec θ) x} ∩ {x | inner ℝ (vec θ) x < c₂}
  have hS_open : IsOpen S :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).inter
      (isOpen_lt (continuous_const.inner continuous_id) continuous_const)
  let xstar : E 2 := ((c₁ + c₂) / 2) • vec θ
  have hxstar_S : xstar ∈ S ∩ Metric.ball 0 M := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change c₁ < inner ℝ (vec θ) xstar
      dsimp [xstar]
      rw [inner_smul_right, real_inner_self_eq_norm_sq, norm_vec, one_pow, mul_one]
      linarith
    · change inner ℝ (vec θ) xstar < c₂
      dsimp [xstar]
      rw [inner_smul_right, real_inner_self_eq_norm_sq, norm_vec, one_pow, mul_one]
      linarith
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, norm_vec, mul_one, Real.norm_eq_abs, abs_lt]
      exact ⟨by linarith, by linarith⟩
  have hvol_pos : 0 < (volume : Measure (E 2)) (S ∩ Metric.closedBall 0 M) :=
    ((hS_open.inter Metric.isOpen_ball).measure_pos volume ⟨xstar, hxstar_S⟩).trans_le
      (measure_mono (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall))
  have hU_pos : 0 < unifBall 0 M S := by
    unfold unifBall
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS_open.measurableSet]
    have hlt_top : (volume : Measure (E 2)) (Metric.closedBall 0 M) < ⊤ :=
      (isCompact_closedBall (0 : E 2) M).measure_lt_top
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hlt_top.ne) hvol_pos.ne'
  have hreal_pos : 0 < (unifBall 0 M).real S :=
    ENNReal.toReal_pos hU_pos.ne' (measure_ne_top _ _)
  have hint1 := integrable_weighted_sign (unifBall 0 M) (w := fun _ => (1 : ℝ))
    measurable_const (fun _ => by norm_num) (lineHyp θ c₁)
  have hint2 := integrable_weighted_sign (unifBall 0 M) (w := fun _ => (1 : ℝ))
    measurable_const (fun _ => by norm_num) (lineHyp θ c₂)
  have hi1 : Integrable (lineHyp θ c₁).sign (unifBall 0 M) := by simpa using hint1
  have hi2 : Integrable (lineHyp θ c₂).sign (unifBall 0 M) := by simpa using hint2
  have hdiff : (∫ x, (lineHyp θ c₁).sign x ∂unifBall 0 M) -
      (∫ x, (lineHyp θ c₂).sign x ∂unifBall 0 M) =
      ∫ x, ((lineHyp θ c₁).sign - (lineHyp θ c₂).sign) x ∂unifBall 0 M :=
    (integral_sub hi1 hi2).symm
  have hpt : ∀ x : E 2, S.indicator (fun _ => (2 : ℝ)) x ≤
      ((lineHyp θ c₁).sign - (lineHyp θ c₂).sign) x := by
    intro x
    change S.indicator (fun _ => (2 : ℝ)) x ≤ (lineHyp θ c₁).sign x - (lineHyp θ c₂).sign x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      rcases hx with ⟨h1, h2⟩
      change c₁ < inner ℝ (vec θ) x at h1
      change inner ℝ (vec θ) x < c₂ at h2
      have hs1 : (lineHyp θ c₁).sign x = 1 := by simp [Hyp.sign, lineHyp, h1]
      have hn2 : ¬ c₂ < inner ℝ (vec θ) x := by linarith
      have hs2 : (lineHyp θ c₂).sign x = -1 := by simp [Hyp.sign, lineHyp, h2, hn2]
      linarith
    · rw [Set.indicator_of_notMem hx]
      linarith [lineHyp_sign_antitone θ hlt.le x]
  have hind_int : Integrable (S.indicator (fun _ => (2 : ℝ))) (unifBall 0 M) :=
    (integrable_const (2 : ℝ)).indicator hS_open.measurableSet
  have hle := integral_mono hind_int (hi1.sub hi2) hpt
  have hind_eq : ∫ x, S.indicator (fun _ => (2 : ℝ)) x ∂unifBall 0 M = 2 * (unifBall 0 M).real S := by
    rw [integral_indicator hS_open.measurableSet, setIntegral_const, smul_eq_mul, mul_comm]
  linarith

lemma sign_integral_at_neg_bound
    (η : Measure (E 2)) [IsProbabilityMeasure η] (hη : η ≪ volume)
    {M : ℝ} (hsupp : η (Metric.closedBall 0 M)ᶜ = 0) (θ : ℝ) :
    ∫ x, (lineHyp θ (-M)).sign x ∂η = 1 := by
  have hnull : η (lineHyp θ (-M)).set = 0 := hη (volume_hyp_set_eq_zero _)
  have hae : ∀ᵐ x ∂η, (lineHyp θ (-M)).sign x = 1 := by
    have hm1 : ∀ᵐ x ∂η, x ∈ Metric.closedBall (0 : E 2) M := by rw [ae_iff]; exact hsupp
    have hm2 : ∀ᵐ x ∂η, x ∉ (lineHyp θ (-M)).set := by rw [ae_iff]; simpa using hnull
    filter_upwards [hm1, hm2] with x hx1 hx2
    have hnx : ‖x‖ ≤ M := by simpa using hx1
    have hcs : |inner ℝ (vec θ) x| ≤ M := by
      calc |inner ℝ (vec θ) x| ≤ ‖vec θ‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ = 1 * ‖x‖ := by rw [norm_vec]
        _ ≤ M := by linarith
    have hge : -M ≤ inner ℝ (vec θ) x := (abs_le.mp hcs).1
    have hne : inner ℝ (vec θ) x ≠ -M := hx2
    have hgt : -M < inner ℝ (vec θ) x := lt_of_le_of_ne hge hne.symm
    simp [Hyp.sign, lineHyp, hgt]
  rw [integral_congr_ae hae]
  simp

lemma sign_integral_at_pos_bound
    (η : Measure (E 2)) [IsProbabilityMeasure η] (hη : η ≪ volume)
    {M : ℝ} (hsupp : η (Metric.closedBall 0 M)ᶜ = 0) (θ : ℝ) :
    ∫ x, (lineHyp θ M).sign x ∂η = -1 := by
  have h1 := sign_integral_at_neg_bound η hη hsupp (θ + Real.pi)
  have hcongr : ∀ x, (lineHyp (θ + Real.pi) (-M)).sign x = -(lineHyp θ M).sign x :=
    lineHyp_add_pi_sign θ M
  simp_rw [hcongr] at h1
  rw [integral_neg] at h1
  linarith

lemma bisect_prob_and_signed_E2
    (μ_m τ : Measure (E 2)) [IsProbabilityMeasure μ_m] [IsProbabilityMeasure τ]
    (hlam_ac : μ_m ≪ volume) (hτ_ac : τ ≪ volume)
    {R : ℝ} (hR : μ_m (Metric.closedBall 0 R)ᶜ = 0)
    {w : E 2 → ℝ} (hw_meas : Measurable w) (hw_le : ∀ x, |w x| ≤ 1) :
    ∃ H : Hyp 2, (∫ x, H.sign x ∂μ_m = 0) ∧ (∫ x, w x * H.sign x ∂τ = 0) := by
  let M : ℝ := max R 0 + 1
  have hM_pos : 0 < M := by dsimp [M]; positivity
  have hRM : R ≤ M := by dsimp [M]; linarith [le_max_left R 0]
  have hlam_M : μ_m (Metric.closedBall 0 M)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr (Metric.closedBall_subset_closedBall hRM)) hR
  let U := unifBall 0 M
  have : IsProbabilityMeasure U := unifBall_isProb 0 hM_pos
  have hU_ac : U ≪ volume := unifBall_ac 0 M
  have hU_M : U (Metric.closedBall 0 M)ᶜ = 0 := unifBall_apply_self_compl 0 M
  let glam (p : ℝ × ℝ) : ℝ := ∫ x, (lineHyp p.1 p.2).sign x ∂μ_m
  let gU (p : ℝ × ℝ) : ℝ := ∫ x, (lineHyp p.1 p.2).sign x ∂U
  let gτ (p : ℝ × ℝ) : ℝ := ∫ x, w x * (lineHyp p.1 p.2).sign x ∂τ
  have hcont_glam : Continuous glam := by
    simpa [glam] using continuous_weighted_sign_integral μ_m hlam_ac
      (w := fun _ => (1 : ℝ)) measurable_const (fun _ => by norm_num)
  have hcont_gU : Continuous gU := by
    simpa [gU] using continuous_weighted_sign_integral U hU_ac
      (w := fun _ => (1 : ℝ)) measurable_const (fun _ => by norm_num)
  have hcont_gτ : Continuous gτ := continuous_weighted_sign_integral τ hτ_ac hw_meas hw_le
  have hglam_anti : ∀ θ {c₁ c₂ : ℝ}, c₁ ≤ c₂ → glam (θ, c₂) ≤ glam (θ, c₁) := by
    intro θ c₁ c₂ hc
    have hi1 : Integrable (lineHyp θ c₂).sign μ_m := by
      simpa using integrable_weighted_sign μ_m (w := fun _ => (1 : ℝ))
        measurable_const (fun _ => by norm_num) (lineHyp θ c₂)
    have hi2 : Integrable (lineHyp θ c₁).sign μ_m := by
      simpa using integrable_weighted_sign μ_m (w := fun _ => (1 : ℝ))
        measurable_const (fun _ => by norm_num) (lineHyp θ c₁)
    exact integral_mono hi1 hi2 (lineHyp_sign_antitone θ hc)
  let F (k : ℕ) (θ c : ℝ) : ℝ :=
    (((k : ℝ) + 1) / ((k : ℝ) + 2)) * glam (θ, c) + (1 / ((k : ℝ) + 2)) * gU (θ, c)
  have hF_cont : ∀ k : ℕ, Continuous (fun p : ℝ × ℝ => F k p.1 p.2) := fun k =>
    (continuous_const.mul hcont_glam).add (continuous_const.mul hcont_gU)
  have hF_strict : ∀ (k : ℕ) (θ : ℝ) {c₁ c₂ : ℝ},
      -M ≤ c₁ → c₂ ≤ M → c₁ < c₂ → F k θ c₂ < F k θ c₁ := by
    intro k θ c₁ c₂ hc₁ hc₂ hlt
    have h1 : glam (θ, c₂) ≤ glam (θ, c₁) := hglam_anti θ hlt.le
    have h2 : gU (θ, c₂) < gU (θ, c₁) := unifBall_sign_strictAnti hM_pos θ hc₁ hc₂ hlt
    have hw1 : 0 ≤ ((k : ℝ) + 1) / ((k : ℝ) + 2) := by positivity
    have hw2 : 0 < 1 / ((k : ℝ) + 2) := by positivity
    dsimp [F]
    linarith [mul_le_mul_of_nonneg_left h1 hw1, mul_lt_mul_of_pos_left h2 hw2]
  have hF_negM : ∀ k θ, F k θ (-M) = 1 := by
    intro k θ
    dsimp [F, glam, gU]
    rw [sign_integral_at_neg_bound μ_m hlam_ac hlam_M θ, sign_integral_at_neg_bound U hU_ac hU_M θ]
    field_simp
    ring
  have hF_posM : ∀ k θ, F k θ M = -1 := by
    intro k θ
    dsimp [F, glam, gU]
    rw [sign_integral_at_pos_bound μ_m hlam_ac hlam_M θ, sign_integral_at_pos_bound U hU_ac hU_M θ]
    field_simp
    ring
  have hF_symm : ∀ k θ c, F k (θ + Real.pi) (-c) = -F k θ c := by
    intro k θ c
    have hl : glam (θ + Real.pi, -c) = -glam (θ, c) := by
      dsimp [glam]; simp_rw [lineHyp_add_pi_sign]; exact integral_neg _
    have hu : gU (θ + Real.pi, -c) = -gU (θ, c) := by
      dsimp [gU]; simp_rw [lineHyp_add_pi_sign]; exact integral_neg _
    dsimp [F]; rw [hl, hu]; ring
  have hgτ_symm : ∀ θ c, gτ (θ + Real.pi, -c) = -gτ (θ, c) := by
    intro θ c
    dsimp [gτ]
    have hpt : ∀ x, w x * (lineHyp (θ + Real.pi) (-c)).sign x = -(w x * (lineHyp θ c).sign x) := by
      intro x; rw [lineHyp_add_pi_sign]; ring
    simp_rw [hpt]
    exact integral_neg _
  have hex_root : ∀ k θ, ∃ c ∈ Set.Icc (-M) M, F k θ c = 0 := by
    intro k θ
    have h0 : (0 : ℝ) ∈ Set.Icc (F k θ M) (F k θ (-M)) := by
      rw [hF_posM, hF_negM]; exact ⟨by norm_num, by norm_num⟩
    have hc : ContinuousOn (fun c => F k θ c) (Set.Icc (-M) M) :=
      ((hF_cont k).comp (continuous_const.prodMk continuous_id)).continuousOn
    exact intermediate_value_Icc' (by linarith) hc h0
  let ck (k : ℕ) (θ : ℝ) : ℝ := Classical.choose (hex_root k θ)
  have hck_mem : ∀ k θ, ck k θ ∈ Set.Icc (-M) M := fun k θ => (Classical.choose_spec (hex_root k θ)).1
  have hck_eq : ∀ k θ, F k θ (ck k θ) = 0 := fun k θ => (Classical.choose_spec (hex_root k θ)).2
  have hck_Ioo : ∀ k θ, -M < ck k θ ∧ ck k θ < M := by
    intro k θ
    rcases hck_mem k θ with ⟨h1, h2⟩
    refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩
    · intro h; have := hck_eq k θ; rw [← h, hF_negM] at this; norm_num at this
    · intro h; have := hck_eq k θ; rw [h, hF_posM] at this; norm_num at this
  have hck_uniq : ∀ k θ {c : ℝ}, c ∈ Set.Icc (-M) M → F k θ c = 0 → c = ck k θ := by
    intro k θ c hc h0
    rcases lt_trichotomy c (ck k θ) with hlt | rfl | hgt
    · have := hF_strict k θ hc.1 (hck_mem k θ).2 hlt
      rw [h0, hck_eq] at this; exact False.elim (lt_irrefl 0 this)
    · rfl
    · have := hF_strict k θ (hck_mem k θ).1 hc.2 hgt
      rw [h0, hck_eq] at this; exact False.elim (lt_irrefl 0 this)
  have hck_pi : ∀ k θ, ck k (θ + Real.pi) = -ck k θ := by
    intro k θ
    symm
    refine hck_uniq k (θ + Real.pi) ⟨by linarith [(hck_mem k θ).2], by linarith [(hck_mem k θ).1]⟩ ?_
    rw [hF_symm, hck_eq, neg_zero]
  have hck_cont : ∀ k, Continuous (ck k) := by
    intro k
    rw [Metric.continuous_iff]
    intro θ₀ ε hε
    obtain ⟨hl₀, hr₀⟩ := hck_Ioo k θ₀
    let δ : ℝ := min (ε / 2) (min (ck k θ₀ - (-M)) (M - ck k θ₀) / 2)
    have hδ_pos : 0 < δ := by dsimp [δ]; positivity
    have hδ_le_ε : δ < ε := by
      calc δ ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith
    have hc_minus_ge : -M ≤ ck k θ₀ - δ := by
      have : δ ≤ min (ck k θ₀ - (-M)) (M - ck k θ₀) / 2 := min_le_right _ _
      have : min (ck k θ₀ - (-M)) (M - ck k θ₀) ≤ ck k θ₀ - (-M) := min_le_left _ _
      linarith
    have hc_plus_le : ck k θ₀ + δ ≤ M := by
      have : δ ≤ min (ck k θ₀ - (-M)) (M - ck k θ₀) / 2 := min_le_right _ _
      have : min (ck k θ₀ - (-M)) (M - ck k θ₀) ≤ M - ck k θ₀ := min_le_right _ _
      linarith
    have hpos_m : 0 < F k θ₀ (ck k θ₀ - δ) := by
      have := hF_strict k θ₀ hc_minus_ge hr₀.le (by linarith)
      rwa [hck_eq] at this
    have hneg_p : F k θ₀ (ck k θ₀ + δ) < 0 := by
      have := hF_strict k θ₀ hl₀.le hc_plus_le (by linarith)
      rwa [hck_eq] at this
    have hF_θ_cont : ∀ c : ℝ, Continuous (fun θ : ℝ => F k θ c) := fun c =>
      Continuous.comp (g := fun p : ℝ × ℝ => F k p.1 p.2) (f := fun θ : ℝ => (θ, c))
        (hF_cont k) (continuous_id'.prodMk continuous_const)
    have hc1 : Continuous (fun θ => F k θ (ck k θ₀ - δ)) := hF_θ_cont (ck k θ₀ - δ)
    have hc2 : Continuous (fun θ => F k θ (ck k θ₀ + δ)) := hF_θ_cont (ck k θ₀ + δ)
    have hev : ∀ᶠ θ in 𝓝 θ₀, 0 < F k θ (ck k θ₀ - δ) ∧ F k θ (ck k θ₀ + δ) < 0 :=
      (hc1.tendsto θ₀ |>.eventually (lt_mem_nhds hpos_m)).and
        (hc2.tendsto θ₀ |>.eventually (gt_mem_nhds hneg_p))
    obtain ⟨η, hη_pos, hη⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨η, hη_pos, fun θ hθ => ?_⟩
    obtain ⟨hm, hp⟩ := hη hθ
    have hgt_m : ck k θ₀ - δ < ck k θ := by
      by_contra hle
      push Not at hle
      by_cases heq : ck k θ = ck k θ₀ - δ
      · rw [← heq, hck_eq] at hm; exact lt_irrefl 0 hm
      · have := hF_strict k θ (hck_mem k θ).1 (by linarith) (lt_of_le_of_ne hle heq)
        rw [hck_eq] at this; linarith
    have hlt_p : ck k θ < ck k θ₀ + δ := by
      by_contra hge
      push Not at hge
      by_cases heq : ck k θ₀ + δ = ck k θ
      · rw [heq, hck_eq] at hp; exact lt_irrefl 0 hp
      · have := hF_strict k θ (by linarith) (hck_mem k θ).2 (lt_of_le_of_ne hge heq)
        rw [hck_eq] at this; linarith
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hex_θ : ∀ k : ℕ, ∃ θ ∈ Set.Icc 0 Real.pi, gτ (θ, ck k θ) = 0 := by
    intro k
    let ψ : ℝ → ℝ := fun θ => gτ (θ, ck k θ)
    have hψ_cont : Continuous ψ := hcont_gτ.comp (continuous_id.prodMk (hck_cont k))
    have hψ_pi : ψ Real.pi = -ψ 0 := by
      dsimp [ψ]
      have hpi : Real.pi = 0 + Real.pi := ( zero_add _ ).symm
      conv_lhs => rw [hpi, hck_pi k 0, hgτ_symm 0 (ck k 0)]
    rcases le_total (ψ 0) 0 with hle | hge
    · refine intermediate_value_Icc Real.pi_pos.le hψ_cont.continuousOn ⟨hle, ?_⟩
      rw [hψ_pi]; linarith
    · refine intermediate_value_Icc' Real.pi_pos.le hψ_cont.continuousOn ⟨?_, hge⟩
      rw [hψ_pi]; linarith
  let θk (k : ℕ) : ℝ := Classical.choose (hex_θ k)
  have hθk_mem : ∀ k, θk k ∈ Set.Icc 0 Real.pi := fun k => (Classical.choose_spec (hex_θ k)).1
  have hθk_eq : ∀ k, gτ (θk k, ck k (θk k)) = 0 := fun k => (Classical.choose_spec (hex_θ k)).2
  let seq (k : ℕ) : ℝ × ℝ := (θk k, ck k (θk k))
  let Kset : Set (ℝ × ℝ) := Set.Icc 0 Real.pi ×ˢ Set.Icc (-M) M
  have hK_compact : IsCompact Kset := isCompact_Icc.prod isCompact_Icc
  let uf : Ultrafilter ℕ := Ultrafilter.of atTop
  have huf_le : (uf : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hmem : Kset ∈ uf.map seq :=
    Ultrafilter.mem_map.mpr (Filter.Eventually.of_forall fun k => ⟨hθk_mem k, hck_mem k (θk k)⟩)
  obtain ⟨p_lim, _, h_tend⟩ := hK_compact.ultrafilter_le_nhds' _ hmem
  refine ⟨lineHyp p_lim.1 p_lim.2, ?_, ?_⟩
  · have htend_glam : Tendsto (fun k => glam (seq k)) (uf : Filter ℕ) (𝓝 (glam p_lim)) :=
      (hcont_glam.tendsto p_lim).comp h_tend
    have hgU_le : ∀ k, |gU (seq k)| ≤ 1 := by
      intro k
      dsimp [gU]
      calc |∫ x, (lineHyp (seq k).1 (seq k).2).sign x ∂U|
        _ ≤ ∫ x, |(lineHyp (seq k).1 (seq k).2).sign x| ∂U := abs_integral_le_integral_abs
        _ ≤ ∫ _x, (1 : ℝ) ∂U := integral_mono ((integrable_weighted_sign U
            (w := fun _ => (1 : ℝ)) measurable_const
            (fun _ => by norm_num) _).abs |> fun h => by simpa using h)
            (integrable_const 1) (abs_sign_le_one _)
        _ = 1 := by simp
    have hglam_bound : ∀ k : ℕ, |glam (seq k)| ≤ 1 / ((k : ℝ) + 1) := by
      intro k
      have h0 := hck_eq k (θk k)
      dsimp [F] at h0
      have hrel : glam (seq k) = -(1 / ((k : ℝ) + 1)) * gU (seq k) := by
        dsimp [seq]
        have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
        have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
        field_simp [hk1, hk2] at h0 ⊢
        linarith
      rw [hrel, abs_mul, abs_neg, abs_of_pos (by positivity)]
      calc (1 / ((k : ℝ) + 1)) * |gU (seq k)| ≤ (1 / ((k : ℝ) + 1)) * 1 :=
          mul_le_mul_of_nonneg_left (hgU_le k) (by positivity)
        _ = 1 / ((k : ℝ) + 1) := mul_one _
    have htend_inv : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have htend_zero : Tendsto (fun k => glam (seq k)) atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _)
        (fun k => by rw [sub_zero, Real.norm_eq_abs]; exact hglam_bound k) htend_inv
    exact tendsto_nhds_unique htend_glam (htend_zero.mono_left huf_le)
  · have htend_gτ : Tendsto (fun k => gτ (seq k)) (uf : Filter ℕ) (𝓝 (gτ p_lim)) :=
      (hcont_gτ.tendsto p_lim).comp h_tend
    have htend_zero : Tendsto (fun k => gτ (seq k)) (uf : Filter ℕ) (𝓝 0) := by
      simp_rw [seq, hθk_eq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique htend_gτ htend_zero

lemma sep_iff_mem_Ioo {a : E 2} (ha : a ≠ 0) (t : ℝ) (p : E 2 × E 2) :
    p ∈ SepMeasures.Sep ⟨a, t, ha⟩ ↔
      t ∈ Set.Ioo (min (inner ℝ a p.1) (inner ℝ a p.2)) (max (inner ℝ a p.1) (inner ℝ a p.2)) := by
  simp only [SepMeasures.Sep, Hyp.pos, Hyp.neg, Set.mem_union, Set.mem_prod, Set.mem_setOf_eq,
    Set.mem_Ioo, lt_max_iff, min_lt_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inr h2, Or.inl h1⟩
    · exact ⟨Or.inl h1, Or.inr h2⟩
  · rintro ⟨hmin, hmax⟩
    rcases hmin with h1 | h1 <;> rcases hmax with h2 | h2
    · exfalso; linarith
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1⟩
    · exfalso; linarith

lemma max_sub_min_eq_abs_sub (u v : ℝ) : max u v - min u v = |u - v| := by
  rcases le_total u v with h | h
  · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]

lemma lintegral_sep_over_t (μ ν : Measure (E 2)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set (E 2 × E 2)} (hS : MeasurableSet S) {a : E 2} (ha : a ≠ 0) :
    ∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep ⟨a, t, ha⟩ ∩ S) ∂volume =
      ∫⁻ p in S, ENNReal.ofReal |inner ℝ a (p.1 - p.2)| ∂(μ.prod ν) := by
  let Q : Set (ℝ × (E 2 × E 2)) :=
    {q | (q.1 < inner ℝ a q.2.1 ∧ inner ℝ a q.2.2 < q.1) ∨
         (inner ℝ a q.2.1 < q.1 ∧ q.1 < inner ℝ a q.2.2)}
  have hQ_open : IsOpen Q := by
    have c1 : Continuous (fun q : ℝ × (E 2 × E 2) => q.1) := continuous_fst
    have c2 : Continuous (fun q : ℝ × (E 2 × E 2) => inner ℝ a q.2.1) :=
      continuous_const.inner (continuous_fst.comp continuous_snd)
    have c3 : Continuous (fun q : ℝ × (E 2 × E 2) => inner ℝ a q.2.2) :=
      continuous_const.inner (continuous_snd.comp continuous_snd)
    exact ((isOpen_lt c1 c2).inter (isOpen_lt c3 c1)).union
      ((isOpen_lt c2 c1).inter (isOpen_lt c1 c3))
  have hmeas : Measurable (fun q : ℝ × (E 2 × E 2) =>
      Q.indicator (1 : ℝ × (E 2 × E 2) → ENNReal) q) :=
    measurable_const.indicator hQ_open.measurableSet
  have h1 : ∀ t : ℝ, (μ.prod ν) (SepMeasures.Sep ⟨a, t, ha⟩ ∩ S) =
      ∫⁻ p in S, Q.indicator (1 : ℝ × (E 2 × E 2) → ENNReal) (t, p) ∂(μ.prod ν) := by
    intro t
    have hfun : (fun p : E 2 × E 2 => Q.indicator (1 : ℝ × (E 2 × E 2) → ENNReal) (t, p)) =
        (SepMeasures.Sep ⟨a, t, ha⟩).indicator (1 : E 2 × E 2 → ENNReal) := by
      ext p
      by_cases hp : p ∈ SepMeasures.Sep ⟨a, t, ha⟩
      · have hq : (t, p) ∈ Q := hp
        simp [Set.indicator_of_mem hp, Set.indicator_of_mem hq]
      · have hq : (t, p) ∉ Q := hp
        simp [Set.indicator_of_notMem hp, Set.indicator_of_notMem hq]
    rw [hfun, lintegral_indicator (measurableSet_sep _), Measure.restrict_restrict (measurableSet_sep _)]
    simp
  simp_rw [h1]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine setLIntegral_congr_fun hS fun p _ => ?_
  have hfun2 : (fun t : ℝ => Q.indicator (1 : ℝ × (E 2 × E 2) → ENNReal) (t, p)) =
      (Set.Ioo (min (inner ℝ a p.1) (inner ℝ a p.2))
        (max (inner ℝ a p.1) (inner ℝ a p.2))).indicator (1 : ℝ → ENNReal) := by
    ext t
    have hiff : (t, p) ∈ Q ↔
        t ∈ Set.Ioo (min (inner ℝ a p.1) (inner ℝ a p.2)) (max (inner ℝ a p.1) (inner ℝ a p.2)) :=
      sep_iff_mem_Ioo ha t p
    by_cases ht : (t, p) ∈ Q
    · simp [Set.indicator_of_mem ht, Set.indicator_of_mem (hiff.mp ht)]
    · simp [Set.indicator_of_notMem ht, Set.indicator_of_notMem (hiff.not.mp ht)]
  rw [hfun2, lintegral_indicator measurableSet_Ioo]
  simp only [Pi.one_apply, lintegral_const, Measure.restrict_apply, MeasurableSet.univ,
    Set.univ_inter, one_mul, Real.volume_Ioo, max_sub_min_eq_abs_sub, ← inner_sub_right]

end

end Aux33

theorem solution (N : Seminorm ℝ (E 2)) (hN : ∀ x, N x = 0 → x = 0) :
    (1 / 3 : ℝ) ≤ cutRatio N (P 2 N) := by
  have h61 : cutRatio N (Pb 2 N) ≤ cutRatio N (P 2 N) :=
    SepMeasures.lemma_6_1 2 (by omega) N hN
  have h62 : cutRatio N (Pbc 2 N) ≤ cutRatio N (Pb 2 N) :=
    SepMeasures.lemma_6_2 2 (by omega) N hN
  refine le_trans ?_ (h62.trans h61)
  have : Nonempty {p : Measure (E 2) × Measure (E 2) // p ∈ Pbc 2 N ∧ 0 < totalDist N p.1 p.2} := by
    obtain ⟨p, hp1, hp2⟩ := Aux33.nonempty_Pbc_two N hN
    exact ⟨⟨p, hp1, hp2⟩⟩
  refine le_ciInf fun ⟨⟨μ, ν⟩, hpbc, hL_pos⟩ => ?_
  rcases hpbc with ⟨⟨⟨⟨hprobμ, hprobν, hffmμ, hffmν⟩, _, _, _⟩, ⟨R, hRμ, hRν⟩⟩, hacμ, hacν⟩
  have := hprobμ
  have := hprobν
  obtain ⟨H₁, bμ₁, bν₁'⟩ := Aux33.bisect_prob_and_signed_E2 μ ν hacμ hacν hRμ
    (w := fun _ => (1 : ℝ)) measurable_const (fun _ => by norm_num)
  have bν₁ : ∫ y, H₁.sign y ∂ν = 0 := by simpa using bν₁'
  obtain ⟨H₂, bμ₂, bν₁₂⟩ := Aux33.bisect_prob_and_signed_E2 μ ν hacμ hacν hRμ
    (Aux33.measurable_sign H₁) (Aux33.abs_sign_le_one H₁)
  obtain ⟨H₃, bν₃, bμ₁₃⟩ := Aux33.bisect_prob_and_signed_E2 ν μ hacν hacμ hRν
    (Aux33.measurable_sign H₁) (Aux33.abs_sign_le_one H₁)
  have hnullμ : ∀ K : Hyp 2, μ K.set = 0 := fun K => hacμ (Aux33.volume_hyp_set_eq_zero K)
  have hnullν : ∀ K : Hyp 2, ν K.set = 0 := fun K => hacν (Aux33.volume_hyp_set_eq_zero K)
  have heq8_ennreal : ∀ K : Hyp 2,
      (μ.prod ν) (SepMeasures.Sep K) ≤
        (μ.prod ν) (SepMeasures.Sep K ∩ SepMeasures.Sep H₁) +
          (μ.prod ν) (SepMeasures.Sep K ∩ SepMeasures.Sep H₂) +
          (μ.prod ν) (SepMeasures.Sep K ∩ SepMeasures.Sep H₃) := by
    intro K
    have hreal := (SepMeasures.eq_8 μ ν H₁ H₂ H₃ K
      (hnullμ H₁) (hnullμ H₂) (hnullμ H₃) (hnullμ K)
      (hnullν H₁) (hnullν H₂) (hnullν H₃) (hnullν K)
      bμ₁ bμ₂ bμ₁₃ bν₁ bν₃ bν₁₂).2
    have hle := ENNReal.ofReal_le_ofReal hreal
    have hconv : ∀ S : Set (E 2 × E 2), ENNReal.ofReal ((μ.prod ν).real S) = (μ.prod ν) S :=
      fun S => ENNReal.ofReal_toReal (measure_ne_top _ _)
    have hr_nn : ∀ S : Set (E 2 × E 2), 0 ≤ (μ.prod ν).real S := fun _ => ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_add (add_nonneg (hr_nn _) (hr_nn _)) (hr_nn _),
      ENNReal.ofReal_add (hr_nn _) (hr_nn _),
      hconv, hconv, hconv, hconv] at hle
    exact hle
  obtain ⟨ρ, hρ_fin, hρ0, hρ_rep⟩ := SepMeasures.pinelis_planar_norm_representation N hN
  have := hρ_fin
  let Kfn (a : E 2) (t : ℝ) : Hyp 2 :=
    if ha : a = 0 then Aux33.lineHyp 0 t else ⟨a, t, ha⟩
  have hdouble : ∀ (S : Set (E 2 × E 2)), MeasurableSet S →
      ∫⁻ a, (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ S) ∂volume) ∂ρ =
        ENNReal.ofReal (∫ p in S, N (p.1 - p.2) ∂(μ.prod ν)) := by
    intro S hS
    have hae_a : (fun a => ∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ S) ∂volume) =ᵐ[ρ]
        (fun a => ∫⁻ p in S, ENNReal.ofReal |inner ℝ a (p.1 - p.2)| ∂(μ.prod ν)) := by
      have hne0 : ∀ᵐ a ∂ρ, a ≠ 0 := by rw [ae_iff]; simpa using hρ0
      filter_upwards [hne0] with a ha
      have hk : ∀ t : ℝ, Kfn a t = ⟨a, t, ha⟩ := fun t => dif_neg ha
      simp_rw [hk]
      exact Aux33.lintegral_sep_over_t μ ν hS ha
    rw [lintegral_congr_ae hae_a]
    have hmeas_ap : Measurable (fun q : E 2 × (E 2 × E 2) =>
        ENNReal.ofReal |inner ℝ q.1 (q.2.1 - q.2.2)|) :=
      ENNReal.measurable_ofReal.comp (continuous_abs.comp
        (continuous_fst.inner ((continuous_fst.comp continuous_snd).sub
          (continuous_snd.comp continuous_snd)))).measurable
    rw [lintegral_lintegral_swap hmeas_ap.aemeasurable]
    have hrep_congr : ∀ p : E 2 × E 2,
        (∫⁻ a, ENNReal.ofReal |inner ℝ a (p.1 - p.2)| ∂ρ) = ENNReal.ofReal (N (p.1 - p.2)) :=
      fun p => (hρ_rep (p.1 - p.2)).symm
    simp_rw [hrep_congr]
    exact (ofReal_integral_eq_lintegral_ofReal
      (Aux33.integrable_dist_prod_E2 N μ ν hffmμ hffmν).integrableOn
      (ae_of_all _ fun p => apply_nonneg N (p.1 - p.2))).symm
  have hL_eq : ∫⁻ a, (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t)) ∂volume) ∂ρ =
      ENNReal.ofReal (totalDist N μ ν) := by
    have hu := hdouble Set.univ MeasurableSet.univ
    simpa [Set.inter_univ, totalDist] using hu
  have hCi_eq : ∀ H : Hyp 2,
      ∫⁻ a, (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H) ∂volume) ∂ρ =
        ENNReal.ofReal (cutVal N μ ν H) := fun H => hdouble _ (Aux33.measurableSet_sep H)
  have hmeas_sep_t : ∀ (a : E 2) (S : Set (E 2 × E 2)), MeasurableSet S →
      Measurable (fun t : ℝ => (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ S)) := by
    intro a S hS
    by_cases ha : a = 0
    · subst ha
      simp only [Kfn, dif_pos]
      let Q0 : Set (ℝ × (E 2 × E 2)) :=
        {q | (q.1 < inner ℝ (Aux33.vec 0) q.2.1 ∧ inner ℝ (Aux33.vec 0) q.2.2 < q.1) ∨
             (inner ℝ (Aux33.vec 0) q.2.1 < q.1 ∧ q.1 < inner ℝ (Aux33.vec 0) q.2.2)}
      have hQ0 : MeasurableSet Q0 := by
        have c1 : Continuous (fun q : ℝ × (E 2 × E 2) => q.1) := continuous_fst
        have c2 : Continuous (fun q : ℝ × (E 2 × E 2) => inner ℝ (Aux33.vec 0) q.2.1) :=
          continuous_const.inner (continuous_fst.comp continuous_snd)
        have c3 : Continuous (fun q : ℝ × (E 2 × E 2) => inner ℝ (Aux33.vec 0) q.2.2) :=
          continuous_const.inner (continuous_snd.comp continuous_snd)
        exact (((isOpen_lt c1 c2).inter (isOpen_lt c3 c1)).union
          ((isOpen_lt c2 c1).inter (isOpen_lt c1 c3))).measurableSet
      have hfn : (fun t : ℝ => (μ.prod ν) (SepMeasures.Sep (Aux33.lineHyp 0 t) ∩ S)) =
          fun t : ℝ => ∫⁻ p in S, Q0.indicator (1 : ℝ × (E 2 × E 2) → ENNReal) (t, p) ∂(μ.prod ν) := by
        ext t
        have hf : (fun p => Q0.indicator (1 : ℝ × (E 2 × E 2) → ENNReal) (t, p)) =
            (SepMeasures.Sep (Aux33.lineHyp 0 t)).indicator (1 : E 2 × E 2 → ENNReal) := by
          ext p
          by_cases hp : p ∈ SepMeasures.Sep (Aux33.lineHyp 0 t)
          · have hq : (t, p) ∈ Q0 := hp
            simp [Set.indicator_of_mem hp, Set.indicator_of_mem hq]
          · have hq : (t, p) ∉ Q0 := hp
            simp [Set.indicator_of_notMem hp, Set.indicator_of_notMem hq]
        rw [hf, lintegral_indicator (Aux33.measurableSet_sep _),
          Measure.restrict_restrict (Aux33.measurableSet_sep _)]
        simp
      rw [hfn]
      exact (measurable_const.indicator hQ0).lintegral_prod_right'
    · simp only [Kfn, dif_neg ha]
      let Qa : Set (ℝ × (E 2 × E 2)) :=
        {q | (q.1 < inner ℝ a q.2.1 ∧ inner ℝ a q.2.2 < q.1) ∨
             (inner ℝ a q.2.1 < q.1 ∧ q.1 < inner ℝ a q.2.2)}
      have hQa : MeasurableSet Qa := by
        have c1 : Continuous (fun q : ℝ × (E 2 × E 2) => q.1) := continuous_fst
        have c2 : Continuous (fun q : ℝ × (E 2 × E 2) => inner ℝ a q.2.1) :=
          continuous_const.inner (continuous_fst.comp continuous_snd)
        have c3 : Continuous (fun q : ℝ × (E 2 × E 2) => inner ℝ a q.2.2) :=
          continuous_const.inner (continuous_snd.comp continuous_snd)
        exact (((isOpen_lt c1 c2).inter (isOpen_lt c3 c1)).union
          ((isOpen_lt c2 c1).inter (isOpen_lt c1 c3))).measurableSet
      have hfn : (fun t : ℝ => (μ.prod ν) (SepMeasures.Sep ⟨a, t, ha⟩ ∩ S)) =
          fun t : ℝ => ∫⁻ p in S, Qa.indicator (1 : ℝ × (E 2 × E 2) → ENNReal) (t, p) ∂(μ.prod ν) := by
        ext t
        have hf : (fun p => Qa.indicator (1 : ℝ × (E 2 × E 2) → ENNReal) (t, p)) =
            (SepMeasures.Sep ⟨a, t, ha⟩).indicator (1 : E 2 × E 2 → ENNReal) := by
          ext p
          by_cases hp : p ∈ SepMeasures.Sep ⟨a, t, ha⟩
          · have hq : (t, p) ∈ Qa := hp
            simp [Set.indicator_of_mem hp, Set.indicator_of_mem hq]
          · have hq : (t, p) ∉ Qa := hp
            simp [Set.indicator_of_notMem hp, Set.indicator_of_notMem hq]
        rw [hf, lintegral_indicator (Aux33.measurableSet_sep _),
          Measure.restrict_restrict (Aux33.measurableSet_sep _)]
        simp
      rw [hfn]
      exact (measurable_const.indicator hQa).lintegral_prod_right'
  have hmeas_a_int : ∀ (S : Set (E 2 × E 2)), MeasurableSet S →
      AEMeasurable (fun a : E 2 =>
        ∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ S) ∂volume) ρ := by
    intro S hS
    have hae_a : (fun a => ∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ S) ∂volume) =ᵐ[ρ]
        (fun a => ∫⁻ p in S, ENNReal.ofReal |inner ℝ a (p.1 - p.2)| ∂(μ.prod ν)) := by
      have hne0 : ∀ᵐ a ∂ρ, a ≠ 0 := by rw [ae_iff]; simpa using hρ0
      filter_upwards [hne0] with a ha
      have hk : ∀ t : ℝ, Kfn a t = ⟨a, t, ha⟩ := fun t => dif_neg ha
      simp_rw [hk]
      exact Aux33.lintegral_sep_over_t μ ν hS ha
    have hm : Measurable (fun q : E 2 × (E 2 × E 2) =>
        ENNReal.ofReal |inner ℝ q.1 (q.2.1 - q.2.2)|) :=
      ENNReal.measurable_ofReal.comp (continuous_abs.comp
        (continuous_fst.inner ((continuous_fst.comp continuous_snd).sub
          (continuous_snd.comp continuous_snd)))).measurable
    exact hm.lintegral_prod_right'.aemeasurable.congr hae_a.symm
  have hineq_enn : ENNReal.ofReal (totalDist N μ ν) ≤
      ENNReal.ofReal (cutVal N μ ν H₁) + ENNReal.ofReal (cutVal N μ ν H₂) +
        ENNReal.ofReal (cutVal N μ ν H₃) := by
    rw [← hL_eq, ← hCi_eq H₁, ← hCi_eq H₂, ← hCi_eq H₃]
    have hpt_a : ∀ a : E 2,
        (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t)) ∂volume) ≤
          (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₁) ∂volume) +
            (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₂) ∂volume) +
            (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₃) ∂volume) := by
      intro a
      have hm1 := hmeas_sep_t a (SepMeasures.Sep H₁) (Aux33.measurableSet_sep H₁)
      have hm2 := hmeas_sep_t a (SepMeasures.Sep H₂) (Aux33.measurableSet_sep H₂)
      calc (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t)) ∂volume)
        _ ≤ ∫⁻ t : ℝ, ((μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₁) +
              (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₂) +
              (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₃)) ∂volume :=
            lintegral_mono fun t => heq8_ennreal (Kfn a t)
        _ = (∫⁻ t : ℝ, ((μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₁) +
              (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₂)) ∂volume) +
              (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₃) ∂volume) :=
            lintegral_add_left (hm1.add hm2) _
        _ = (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₁) ∂volume) +
              (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₂) ∂volume) +
              (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₃) ∂volume) := by
            rw [lintegral_add_left hm1]
    have hma1 := hmeas_a_int (SepMeasures.Sep H₁) (Aux33.measurableSet_sep H₁)
    have hma2 := hmeas_a_int (SepMeasures.Sep H₂) (Aux33.measurableSet_sep H₂)
    calc (∫⁻ a : E 2, (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t)) ∂volume) ∂ρ)
      _ ≤ ∫⁻ a : E 2, ((∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₁) ∂volume) +
            (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₂) ∂volume) +
            (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₃) ∂volume)) ∂ρ :=
          lintegral_mono hpt_a
      _ = (∫⁻ a : E 2, ((∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₁) ∂volume) +
            (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₂) ∂volume)) ∂ρ) +
            (∫⁻ a : E 2, (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₃) ∂volume) ∂ρ) :=
          lintegral_add_left' (hma1.add hma2) _
      _ = (∫⁻ a : E 2, (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₁) ∂volume) ∂ρ) +
            (∫⁻ a : E 2, (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₂) ∂volume) ∂ρ) +
            (∫⁻ a : E 2, (∫⁻ t : ℝ, (μ.prod ν) (SepMeasures.Sep (Kfn a t) ∩ SepMeasures.Sep H₃) ∂volume) ∂ρ) := by
          rw [lintegral_add_left' hma1]
  have hC1_nn : 0 ≤ cutVal N μ ν H₁ := integral_nonneg fun _ => apply_nonneg N _
  have hC2_nn : 0 ≤ cutVal N μ ν H₂ := integral_nonneg fun _ => apply_nonneg N _
  have hC3_nn : 0 ≤ cutVal N μ ν H₃ := integral_nonneg fun _ => apply_nonneg N _
  rw [← ENNReal.ofReal_add hC1_nn hC2_nn, ← ENNReal.ofReal_add (add_nonneg hC1_nn hC2_nn) hC3_nn]
    at hineq_enn
  have hsum_ge : totalDist N μ ν ≤ cutVal N μ ν H₁ + cutVal N μ ν H₂ + cutVal N μ ν H₃ :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hineq_enn
  have hbdd : BddAbove (Set.range fun H : Hyp 2 => cutVal N μ ν H / totalDist N μ ν) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨H, rfl⟩
    have hle : cutVal N μ ν H ≤ totalDist N μ ν :=
      setIntegral_le_integral (Aux33.integrable_dist_prod_E2 N μ ν hffmμ hffmν)
        (ae_of_all _ fun _ => apply_nonneg N _)
    exact (div_le_one hL_pos).mpr hle
  have hex_i : ∃ H : Hyp 2, totalDist N μ ν / 3 ≤ cutVal N μ ν H := by
    by_contra hall
    push Not at hall
    linarith [hall H₁, hall H₂, hall H₃]
  obtain ⟨H_best, hbest⟩ := hex_i
  refine le_ciSup_of_le hbdd H_best ?_
  exact (le_div_iff₀ hL_pos).mpr (by linarith)
