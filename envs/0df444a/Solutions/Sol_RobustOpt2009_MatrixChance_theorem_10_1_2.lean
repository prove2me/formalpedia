-- Prove2me | solution 1 for RobustOpt2009.MatrixChance.theorem_10_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T05:58:02.896636+00:00
-- url     : https://prove2.me/submissions/f5203dea-cee2-42c4-b237-500ead7e4ca3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RobustOpt2009_MatrixChance_theorem_B_5_1

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace MC1012Aux

open RobustOpt2009.MatrixChance

lemma psd_iff_quad {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.IsSymm) :
    M.PosSemidef ↔ ∀ x : Fin m → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rw [posSemidef_iff_dotProduct_mulVec]
  simp [isHermitian_iff_isSymm, hM]

lemma dot_self_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ x ⬝ᵥ x := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

open scoped RealInnerProductSpace in
lemma norm_le_iff {m : ℕ} [NeZero m] (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.IsSymm) (t : ℝ) :
    spectralNorm M ≤ t ↔ 0 ≤ t ∧ ∀ x : Fin m → ℝ, |x ⬝ᵥ (M *ᵥ x)| ≤ t * (x ⬝ᵥ x) := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) M with hT
  have hinner : ∀ y : EuclideanSpace ℝ (Fin m), ⟪T y, y⟫ = (WithLp.ofLp y) ⬝ᵥ (M *ᵥ WithLp.ofLp y) := by
    intro y
    rw [real_inner_comm, hT, inner_toEuclideanCLM]
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin m), ‖y‖ ^ 2 = (WithLp.ofLp y) ⬝ᵥ (WithLp.ofLp y) := by
    intro y
    rw [← real_inner_self_eq_norm_sq]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp
  constructor
  · intro h
    have h0 : 0 ≤ t := le_trans (norm_nonneg _) h
    refine ⟨h0, fun x => ?_⟩
    have hci := abs_real_inner_le_norm (T (WithLp.toLp 2 x)) (WithLp.toLp 2 x)
    rw [hinner] at hci
    have h2 := T.le_opNorm (WithLp.toLp 2 x)
    have h3 := hnorm (WithLp.toLp 2 x)
    simp only at hci h3
    have hn : 0 ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ := norm_nonneg _
    have hTt : ‖T‖ ≤ t := h
    calc |x ⬝ᵥ (M *ᵥ x)| ≤ ‖T (WithLp.toLp 2 x)‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ := hci
      _ ≤ (‖T‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ :=
          mul_le_mul_of_nonneg_right h2 hn
      _ ≤ (t * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ := by gcongr
      _ = t * (x ⬝ᵥ x) := by rw [← h3]; ring
  · rintro ⟨h0, h⟩
    show ‖T‖ ≤ t
    have hsymm : (T : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).IsSymmetric := by
      rw [hT, coe_toEuclideanCLM_eq_toEuclideanLin, isSymmetric_toEuclideanLin_iff]
      simpa [isHermitian_iff_isSymm] using hM
    rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hsymm]
    refine ciSup_le fun y => ?_
    by_cases hy : y = 0
    · subst hy; simpa using h0
    · have hpos : 0 < ‖y‖ ^ 2 := by positivity
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
        abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      have := h (WithLp.ofLp y)
      rw [← hinner, ← hnorm] at this
      simpa using this

lemma isSymm_perturbation {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ l, (B l).IsSymm) (z : Fin L → ℝ) : (perturbation B z).IsSymm := by
  unfold perturbation
  rw [Matrix.IsSymm, transpose_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [transpose_smul, (hB l).eq]

lemma quad_pert {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ) (z : Fin L → ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ (perturbation B z *ᵥ x) = ∑ l, z l * (x ⬝ᵥ (B l *ᵥ x)) := by
  simp [perturbation, Matrix.sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul]

lemma spectralNorm_pert {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ) (z : Fin L → ℝ) :
    RobustOpt2009.MatrixChance.spectralNorm (perturbation B z) = ‖∑ l, z l • Matrix.toEuclideanCLM (𝕜 := ℝ) (B l)‖ := by
  simp [RobustOpt2009.MatrixChance.spectralNorm, perturbation, map_sum, map_smul]

lemma continuous_spectralNorm_pert {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ) :
    Continuous (fun z : Fin L → ℝ => RobustOpt2009.MatrixChance.spectralNorm (perturbation B z)) := by
  simp_rw [spectralNorm_pert]
  fun_prop

lemma spectralNorm_pert_smul {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (z : Fin L → ℝ) : RobustOpt2009.MatrixChance.spectralNorm (perturbation B (c • z)) = |c| * RobustOpt2009.MatrixChance.spectralNorm (perturbation B z) := by
  rw [spectralNorm_pert, spectralNorm_pert]
  have : ∑ l, (c • z) l • Matrix.toEuclideanCLM (𝕜 := ℝ) (B l) =
      c • ∑ l, z l • Matrix.toEuclideanCLM (𝕜 := ℝ) (B l) := by
    rw [Finset.smul_sum]; simp [smul_smul]
  rw [this, norm_smul, Real.norm_eq_abs]

lemma spectralNorm_pert_add {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ) (z z' : Fin L → ℝ) :
    RobustOpt2009.MatrixChance.spectralNorm (perturbation B (z + z')) ≤
      RobustOpt2009.MatrixChance.spectralNorm (perturbation B z) +
        RobustOpt2009.MatrixChance.spectralNorm (perturbation B z') := by
  have e : perturbation B (z + z') = perturbation B z + perturbation B z' := by
    simp [perturbation, add_smul, Finset.sum_add_distrib]
  simp only [RobustOpt2009.MatrixChance.spectralNorm, e, map_add]
  exact norm_add_le _ _

lemma spectralNorm_pert_le_norm {m L : ℕ} [NeZero m] (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ l, (B l).IsSymm) (hvar : (1 - ∑ l, B l * B l).PosSemidef) (z : Fin L → ℝ) :
    RobustOpt2009.MatrixChance.spectralNorm (perturbation B z) ≤ ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin L))‖ := by
  set t := ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin L))‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht2 : t ^ 2 = ∑ l, z l ^ 2 := by
    rw [ht, EuclideanSpace.real_norm_sq_eq]
  rw [norm_le_iff _ (isSymm_perturbation B hB z)]
  refine ⟨ht0, fun x => ?_⟩
  rw [quad_pert]
  have hxx := dot_self_nonneg x
  -- each coefficient
  have hcoef : ∀ l, (x ⬝ᵥ (B l *ᵥ x)) ^ 2 ≤ (x ⬝ᵥ x) * (x ⬝ᵥ ((B l * B l) *ᵥ x)) := by
    intro l
    have h1 : (x ⬝ᵥ (B l *ᵥ x)) ^ 2 ≤ (x ⬝ᵥ x) * ((B l *ᵥ x) ⬝ᵥ (B l *ᵥ x)) := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (B l *ᵥ x)
      simpa [dotProduct, sq] using this
    have h2 : (B l *ᵥ x) ⬝ᵥ (B l *ᵥ x) = x ⬝ᵥ ((B l * B l) *ᵥ x) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, (hB l).eq, dotProduct_comm, mulVec_mulVec]
    rwa [h2] at h1
  have hsumB : ∑ l, x ⬝ᵥ ((B l * B l) *ᵥ x) ≤ x ⬝ᵥ x := by
    have h := (psd_iff_quad _ ?_).1 hvar x
    · have e : x ⬝ᵥ ((1 - ∑ l, B l * B l) *ᵥ x) = x ⬝ᵥ x - ∑ l, x ⬝ᵥ ((B l * B l) *ᵥ x) := by
        simp [sub_mulVec, Matrix.sum_mulVec, dotProduct_sub, dotProduct_sum]
      linarith [e ▸ h]
    · rw [Matrix.IsSymm, transpose_sub, transpose_one, transpose_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [transpose_mul, (hB l).eq]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ z (fun l => x ⬝ᵥ (B l *ᵥ x))
  have hA2 : ∑ l, (x ⬝ᵥ (B l *ᵥ x)) ^ 2 ≤ (x ⬝ᵥ x) * (x ⬝ᵥ x) := by
    calc ∑ l, (x ⬝ᵥ (B l *ᵥ x)) ^ 2 ≤ ∑ l, (x ⬝ᵥ x) * (x ⬝ᵥ ((B l * B l) *ᵥ x)) :=
          Finset.sum_le_sum fun l _ => hcoef l
      _ = (x ⬝ᵥ x) * ∑ l, x ⬝ᵥ ((B l * B l) *ᵥ x) := by rw [Finset.mul_sum]
      _ ≤ (x ⬝ᵥ x) * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_left hsumB hxx
  apply abs_le_of_sq_le_sq _ (mul_nonneg ht0 hxx)
  calc (∑ l, z l * x ⬝ᵥ (B l *ᵥ x)) ^ 2 ≤ (∑ l, z l ^ 2) * ∑ l, (x ⬝ᵥ (B l *ᵥ x)) ^ 2 := hCS
    _ ≤ (∑ l, z l ^ 2) * ((x ⬝ᵥ x) * (x ⬝ᵥ x)) :=
        mul_le_mul_of_nonneg_left hA2 (Finset.sum_nonneg fun l _ => sq_nonneg _)
    _ = (t * (x ⬝ᵥ x)) ^ 2 := by rw [mul_pow, ht2]; ring

lemma gaussianEnvelope_nonneg (t : EReal) : 0 ≤ gaussianEnvelope t := by
  unfold gaussianEnvelope
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

lemma normalTail_top : normalTail ⊤ = 0 := by
  unfold normalTail
  have : {x : ℝ | (⊤ : EReal) < (x : EReal)} = ∅ := by
    ext x; simp
  rw [this]; simp

end MC1012Aux

open RobustOpt2009.MatrixChance MC1012Aux

theorem solution {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] {m L : ℕ} [NeZero m] [NeZero L]
    (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ l, (B l).IsSymm) (hvariance : (1 - ∑ l, B l * B l).PosSemidef)
    (ζ : Fin L → W → ℝ) (hmeas : ∀ l, Measurable (ζ l))
    (hindep : iIndepFun ζ μ) (hgaussian : gaussianCase μ ζ)
    (Υ χ : ℝ) (hΥ : 0 < Υ)
    (hχeq : χ = (μ {w | spectralNorm (perturbation B (fun l => ζ l w)) ≤ Υ}).toReal)
    (hχ : (1 / 2 : ℝ) < χ) :
    ∀ Ω : ℝ, Υ ≤ Ω →
      (μ {w | Ω < spectralNorm (perturbation B (fun l => ζ l w))}).toReal ≤
        normalTail (amplificationArgument χ Υ Ω) ∧
      normalTail (amplificationArgument χ Υ Ω) ≤
        gaussianEnvelope (((Ω / Υ : ℝ) : EReal) * tailQuantile (1 - χ)) := by
  intro Ω hΩ
  let g : EuclideanSpace ℝ (Fin L) → ℝ := fun z => spectralNorm (perturbation B (WithLp.ofLp z))
  have hgc : Continuous g := (continuous_spectralNorm_pert B).comp (PiLp.continuous_ofLp 2 _)
  set Q : Set (EuclideanSpace ℝ (Fin L)) := {z | g z ≤ Υ} with hQ
  have hQc : IsClosed Q := isClosed_le hgc continuous_const
  have hQconv : Convex ℝ Q := by
    intro x hx y hy a b ha hb hab
    simp only [hQ, Set.mem_ofPred_eq, g] at hx hy ⊢
    rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul]
    calc spectralNorm (perturbation B (a • WithLp.ofLp x + b • WithLp.ofLp y))
        ≤ spectralNorm (perturbation B (a • WithLp.ofLp x)) +
            spectralNorm (perturbation B (b • WithLp.ofLp y)) := spectralNorm_pert_add _ _ _
      _ = a * spectralNorm (perturbation B (WithLp.ofLp x)) +
            b * spectralNorm (perturbation B (WithLp.ofLp y)) := by
          rw [spectralNorm_pert_smul, spectralNorm_pert_smul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * Υ + b * Υ := by gcongr
      _ = Υ := by rw [← add_mul, hab, one_mul]
  have hmeasV : Measurable (fun w => (WithLp.toLp 2 (fun l => ζ l w) : EuclideanSpace ℝ (Fin L))) :=
    (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ hmeas)
  have hlaw : μ.map (fun w => (WithLp.toLp 2 (fun l => ζ l w) : EuclideanSpace ℝ (Fin L))) =
      stdGaussian (EuclideanSpace ℝ (Fin L)) := by
    have hpi := (iIndepFun_iff_map_fun_eq_pi_map (fun l => (hmeas l).aemeasurable)).1 hindep
    have hpi' : μ.map (fun w l => ζ l w) = Measure.pi (fun _ : Fin L => gaussianReal 0 1) := by
      rw [hpi]; congr 1; funext l; exact hgaussian l
    rw [← map_pi_eq_stdGaussian, ← hpi', Measure.map_map (PiLp.continuous_toLp 2 _).measurable
      (measurable_pi_lambda _ hmeas)]
    rfl
  have hprob : ∀ S : Set (EuclideanSpace ℝ (Fin L)), MeasurableSet S →
      stdGaussian (EuclideanSpace ℝ (Fin L)) S =
        μ ((fun w => (WithLp.toLp 2 (fun l => ζ l w) : EuclideanSpace ℝ (Fin L))) ⁻¹' S) := by
    intro S hS
    rw [← hlaw, Measure.map_apply hmeasV hS]
  have hQprob : χ ≤ (stdGaussian (EuclideanSpace ℝ (Fin L)) Q).toReal := by
    rw [hprob Q hQc.measurableSet, hχeq]; rfl
  have htail : (μ {w | Ω < spectralNorm (perturbation B (fun l => ζ l w))}).toReal =
      (stdGaussian (EuclideanSpace ℝ (Fin L)) {z | Ω < g z}).toReal := by
    rw [hprob _ (isOpen_lt continuous_const hgc).measurableSet]; rfl
  obtain ⟨hqpos, hball, hdil⟩ := (theorem_B_5_1 (m := L)).1 Q χ hQc hQconv hχ hQprob
  have hΩΥ : 0 ≤ Ω - Υ := by linarith
  by_cases htop : tailQuantile (1 - χ) = ⊤
  · -- Q is everything; the tail event is empty
    have hamp : amplificationArgument χ Υ Ω = ⊤ := by
      unfold amplificationArgument
      rw [htop]
      apply EReal.top_add_of_ne_bot
      have h0 : (0 : EReal) ≤ ((Ω - Υ : ℝ) : EReal) * max 1 (((Υ⁻¹ : ℝ) : EReal) * ⊤) :=
        EReal.mul_nonneg (EReal.coe_nonneg.2 hΩΥ) (le_trans zero_le_one (le_max_left _ _))
      intro h; rw [h] at h0; exact absurd h0 (by simp)
    rw [hamp, normalTail_top, htail]
    refine ⟨?_, gaussianEnvelope_nonneg _⟩
    have hempty : {z : EuclideanSpace ℝ (Fin L) | Ω < g z} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have : z ∈ Q := hball (by rw [htop]; simp)
      exact le_trans this hΩ
    rw [hempty]; simp
  · have hbot : tailQuantile (1 - χ) ≠ ⊥ := ne_bot_of_gt hqpos
    set q0 := (tailQuantile (1 - χ)).toReal with hq0
    have hq : tailQuantile (1 - χ) = (q0 : EReal) := (EReal.coe_toReal htop hbot).symm
    have hq0pos : 0 < q0 := by
      have := hqpos; rw [hq] at this; exact_mod_cast this
    set r := max Υ q0 with hr
    have hballr : Metric.closedBall (0 : EuclideanSpace ℝ (Fin L)) r ⊆ Q := by
      intro x hx
      rw [mem_closedBall_zero_iff] at hx
      rcases le_or_gt ‖x‖ Υ with h | h
      · show g x ≤ Υ
        refine le_trans ?_ h
        have := spectralNorm_pert_le_norm B hB hvariance (WithLp.ofLp x)
        simpa using this
      · have hx' : ‖x‖ ≤ q0 := (le_max_iff.1 hx).resolve_left (not_le.2 h)
        exact hball (by rw [hq]; simp only [Set.mem_ofPred_eq]; exact_mod_cast hx')
    set α := Ω / Υ with hα
    have hα1 : 1 ≤ α := by rw [hα, le_div_iff₀ hΥ]; linarith
    obtain ⟨hd1, hd2, hd3⟩ := hdil r (by rw [hq]; exact_mod_cast le_max_right Υ q0) hballr α hα1
    have hamp : amplificationArgument χ Υ Ω = tailQuantile (1 - χ) + (((α - 1) * r : ℝ) : EReal) := by
      unfold amplificationArgument
      congr 1
      have hmax : ((max 1 (Υ⁻¹ * q0) : ℝ) : EReal) = max 1 ((Υ⁻¹ * q0 : ℝ) : EReal) := by
        rw [← EReal.coe_one]; exact EReal.coe_strictMono.monotone.map_max
      rw [hq, ← EReal.coe_mul, ← hmax, ← EReal.coe_mul]
      congr 1
      have hr' : r = Υ * max 1 (Υ⁻¹ * q0) := by
        rw [hr, mul_max_of_nonneg _ _ hΥ.le, mul_one, mul_inv_cancel_left₀ hΥ.ne']
      rw [hr', hα]
      field_simp
    have hgs : ∀ y, g (α • y) = α * g y := by
      intro y
      simp only [g, WithLp.ofLp_smul]
      rw [spectralNorm_pert_smul, abs_of_pos (by linarith)]
    rw [hamp, htail]
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ hd1
      apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
      rintro z hz ⟨y, hy, rfl⟩
      simp only [Set.mem_ofPred_eq] at hz
      rw [hgs] at hz
      have hy' : g y ≤ Υ := hy
      have : α * g y ≤ α * Υ := mul_le_mul_of_nonneg_left hy' (by linarith)
      have hαΥ : α * Υ = Ω := by rw [hα]; field_simp
      linarith
    · have := gaussianEnvelope_nonneg ((α : EReal) * tailQuantile (1 - χ))
      linarith
