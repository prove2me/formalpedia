-- Prove2me | solution 1 for RobustOpt2009.MatrixChance.theorem_10_1_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T06:05:45.101119+00:00
-- url     : https://prove2.me/submissions/0054ba3c-3944-4dc1-b33c-15914193225a

import Definitions.Def_RobustOpt2009_MatrixChance_Setting
import Theorems.Thm_TalagrandConc1995_thm4_1_1_convex_hull_faithful

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace MC1011Aux

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


/-- the diagonal map `x ↦ (x i i)_i`. -/
def diagMap {L : ℕ} (x : Fin L → Fin L → ℝ) : Fin L → ℝ := fun i => x i i

lemma continuous_diagMap {L : ℕ} : Continuous (diagMap (L := L)) := by
  unfold diagMap; fun_prop

/-- the truncated base set `K`. -/
def baseSet {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ) (Υ : ℝ) : Set (Fin L → ℝ) :=
  {z | RobustOpt2009.MatrixChance.spectralNorm (perturbation B z) ≤ Υ ∧ ∀ l, |z l| ≤ 1}

lemma baseSet_closed {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ) (Υ : ℝ) :
    IsClosed (baseSet B Υ) := by
  unfold baseSet
  rw [Set.ofPred_and]
  refine IsClosed.inter (isClosed_le (continuous_spectralNorm_pert B) continuous_const) ?_
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun l => isClosed_le (by fun_prop) continuous_const

lemma baseSet_compact {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ) (Υ : ℝ) :
    IsCompact (baseSet B Υ) := by
  refine Metric.isCompact_of_isClosed_isBounded (baseSet_closed B Υ) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin L → ℝ)) (r := 1)).subset ?_
  intro z hz
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro l; rw [Real.norm_eq_abs]; exact hz.2 l

lemma baseSet_convex {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ) (Υ : ℝ) :
    Convex ℝ (baseSet B Υ) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, fun l => ?_⟩
  · calc RobustOpt2009.MatrixChance.spectralNorm (perturbation B (a • x + b • y))
        ≤ RobustOpt2009.MatrixChance.spectralNorm (perturbation B (a • x)) +
            RobustOpt2009.MatrixChance.spectralNorm (perturbation B (b • y)) := spectralNorm_pert_add _ _ _
      _ = a * RobustOpt2009.MatrixChance.spectralNorm (perturbation B x) +
            b * RobustOpt2009.MatrixChance.spectralNorm (perturbation B y) := by
          rw [spectralNorm_pert_smul, spectralNorm_pert_smul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * Υ + b * Υ := by gcongr; exact hx.1; exact hy.1
      _ = Υ := by rw [← add_mul, hab, one_mul]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * x l + b * y l| ≤ |a * x l| + |b * y l| := abs_add_le _ _
      _ = a * |x l| + b * |y l| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr; exact hx.2 l; exact hy.2 l
      _ = 1 := by rw [mul_one, mul_one, hab]

/-- the pattern sets `P_s`. -/
def patSet {L : ℕ} (A : Set (Fin L → Fin L → ℝ)) (s : Fin L → ℝ) : Set (Fin L → Fin L → ℝ) :=
  {x | ∃ y ∈ A, ∀ i, s i = 0 → x i = y i}

lemma patSet_closed {L : ℕ} (K : Set (Fin L → ℝ)) (hK : IsCompact K) (s : Fin L → ℝ) :
    IsClosed (patSet (diagMap ⁻¹' K) s) := by
  classical
  let pr : (Fin L → ℝ) → (Fin L → ℝ) := fun z i => if s i = 0 then z i else 0
  have hpr : Continuous pr := by
    refine continuous_pi fun i => ?_
    by_cases h : s i = 0
    · simp only [pr, h, if_true]; exact continuous_apply i
    · simp only [pr, h, if_false]; exact continuous_const
  have e : patSet (diagMap ⁻¹' K) s = (pr ∘ diagMap) ⁻¹' (pr '' K) := by
    ext x
    simp only [patSet, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨y, hy, hxy⟩
      refine ⟨diagMap y, hy, funext fun i => ?_⟩
      by_cases h : s i = 0
      · simp only [pr, h, if_true, diagMap, hxy i h]
      · simp only [pr, h, if_false]
    · rintro ⟨k, hk, hkx⟩
      refine ⟨fun i => if s i = 0 then x i else Function.update (x i) i (k i), ?_, ?_⟩
      · have : diagMap (fun i => if s i = 0 then x i else Function.update (x i) i (k i)) = k := by
          funext i
          by_cases h : s i = 0
          · have := congrFun hkx i
            simp only [pr, h, if_true, diagMap] at this
            simp only [diagMap, h, if_true]; exact this.symm
          · simp [diagMap, h]
        rw [this]; exact hk
      · intro i hi; simp [hi]
  rw [e]
  exact (hK.image hpr).isClosed.preimage (hpr.comp continuous_diagMap)

open TalagrandConc.ConvexHull in
lemma fc_measurable {L : ℕ} (A : Set (Fin L → Fin L → ℝ))
    (hP : ∀ s, MeasurableSet (patSet A s)) : Measurable (fun x => fc A x) := by
  classical
  let toR : (Fin L → Bool) → (Fin L → ℝ) := fun b i => if b i then 1 else 0
  let φ : (Fin L → Fin L → ℝ) → ((Fin L → Bool) → Bool) :=
    fun x b => decide (x ∈ patSet A (toR b))
  let H : ((Fin L → Bool) → Bool) → ENNReal := fun F =>
    ⨅ s ∈ convexHull ℝ {s : Fin L → ℝ | ∃ b, F b = true ∧ s = toR b},
      ENNReal.ofReal (Real.sqrt (∑ i, s i ^ 2))
  have hU : ∀ x, U A x = {s : Fin L → ℝ | ∃ b, φ x b = true ∧ s = toR b} := by
    intro x
    ext s
    simp only [U, Set.mem_ofPred_eq, φ, decide_eq_true_eq]
    constructor
    · rintro ⟨h01, hy⟩
      refine ⟨fun i => decide (s i = 1), ?_, ?_⟩
      · have : toR (fun i => decide (s i = 1)) = s := by
          funext i
          rcases h01 i with h | h <;> simp [toR, h]
        rw [this]; exact hy
      · funext i
        rcases h01 i with h | h <;> simp [toR, h]
    · rintro ⟨b, hb, rfl⟩
      refine ⟨fun i => ?_, hb⟩
      by_cases h : b i <;> simp [toR, h]
  have hfc : (fun x => fc A x) = H ∘ φ := by
    funext x
    simp only [Function.comp_apply, H, fc, V, hU x]
  rw [hfc]
  refine Measurable.comp (Measurable.of_discrete) ?_
  refine measurable_pi_iff.2 fun b => ?_
  refine measurable_to_countable' fun c => ?_
  cases c
  · have : (fun x => φ x b) ⁻¹' {false} = (patSet A (toR b))ᶜ := by
      ext x; simp [φ]
    rw [this]; exact (hP _).compl
  · have : (fun x => φ x b) ⁻¹' {true} = patSet A (toR b) := by
      ext x; simp [φ]
    rw [this]; exact hP _

open TalagrandConc.ConvexHull in
lemma key {m L : ℕ} [NeZero m] (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ l, (B l).IsSymm) (hvar : (1 - ∑ l, B l * B l).PosSemidef) (Υ : ℝ)
    (x : Fin L → Fin L → ℝ) (hx : ∀ l, |diagMap x l| ≤ 1) (s : Fin L → ℝ)
    (hs : s ∈ V (diagMap ⁻¹' baseSet B Υ) x) :
    RobustOpt2009.MatrixChance.spectralNorm (perturbation B (diagMap x)) ≤
      Υ + 2 * Real.sqrt (∑ i, s i ^ 2) := by
  set K := baseSet B Υ with hK
  set d := diagMap x with hd
  let W : Set (Fin L → ℝ) := {t | ∃ z ∈ K, ∀ i, |d i - z i| ≤ 2 * t i}
  have hWconv : Convex ℝ W := by
    rintro t1 ⟨z1, hz1, h1⟩ t2 ⟨z2, hz2, h2⟩ a b ha hb hab
    refine ⟨a • z1 + b • z2, baseSet_convex B Υ hz1 hz2 ha hb hab, fun i => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : d i - (a * z1 i + b * z2 i) = a * (d i - z1 i) + b * (d i - z2 i) := by
      have : d i = (a + b) * d i := by rw [hab, one_mul]
      linear_combination this
    rw [e]
    calc |a * (d i - z1 i) + b * (d i - z2 i)| ≤ |a * (d i - z1 i)| + |b * (d i - z2 i)| :=
          abs_add_le _ _
      _ = a * |d i - z1 i| + b * |d i - z2 i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (2 * t1 i) + b * (2 * t2 i) := by gcongr; exact h1 i; exact h2 i
      _ = 2 * (a * t1 i + b * t2 i) := by ring
  have hUW : U (diagMap ⁻¹' K) x ⊆ W := by
    rintro u ⟨hu01, y, hy, hyu⟩
    refine ⟨diagMap y, hy, fun i => ?_⟩
    rcases hu01 i with h | h
    · rw [h, hd]; simp [diagMap, hyu i h]
    · rw [h]
      have h1 := hx i
      have h2 := hy.2 i
      calc |d i - diagMap y i| ≤ |d i| + |diagMap y i| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add h1 h2
        _ = 2 * 1 := by norm_num
  obtain ⟨z, hz, hdz⟩ := convexHull_min hUW hWconv hs
  have hnorm : ‖(WithLp.toLp 2 (d - z) : EuclideanSpace ℝ (Fin L))‖ ≤ 2 * Real.sqrt (∑ i, s i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    have h4 : (2 : ℝ) = Real.sqrt 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Real.norm_eq_abs, sq_abs, PiLp.toLp_apply, Pi.sub_apply]
    have := hdz i
    have h0 : 0 ≤ 2 * s i := le_trans (abs_nonneg _) this
    have := sq_le_sq' (by linarith [neg_abs_le (d i - z i)]) (le_trans (le_abs_self _) this)
    nlinarith [this]
  have hsplit : d = z + (d - z) := by abel
  calc RobustOpt2009.MatrixChance.spectralNorm (perturbation B d)
      = RobustOpt2009.MatrixChance.spectralNorm (perturbation B (z + (d - z))) := by rw [← hsplit]
    _ ≤ RobustOpt2009.MatrixChance.spectralNorm (perturbation B z) +
          RobustOpt2009.MatrixChance.spectralNorm (perturbation B (d - z)) := spectralNorm_pert_add _ _ _
    _ ≤ Υ + ‖(WithLp.toLp 2 (d - z) : EuclideanSpace ℝ (Fin L))‖ :=
        add_le_add hz.1 (spectralNorm_pert_le_norm B hB hvar _)
    _ ≤ Υ + 2 * Real.sqrt (∑ i, s i ^ 2) := by linarith

end MC1011Aux

open RobustOpt2009.MatrixChance MC1011Aux

theorem solution {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] {m L : ℕ} [NeZero m] [NeZero L]
    (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ l, (B l).IsSymm) (hvariance : (1 - ∑ l, B l * B l).PosSemidef)
    (ζ : Fin L → W → ℝ) (hmeas : ∀ l, Measurable (ζ l))
    (hindep : iIndepFun ζ μ) (hbounded : boundedCase μ ζ)
    (Υ χ : ℝ) (hΥ : 0 < Υ)
    (hχeq : χ = (μ {w | spectralNorm (perturbation B (fun l => ζ l w)) ≤ Υ}).toReal)
    (hχ : 0 < χ) :
    ∀ Ω : ℝ, Υ < Ω →
      (μ {w | Ω < spectralNorm (perturbation B (fun l => ζ l w))}).toReal ≤
        (1 / χ) * Real.exp (-((Ω - Υ) ^ 2) / 16) := by
  intro Ω hΩ
  classical
  set ν : Fin L → Measure ℝ := fun l => μ.map (ζ l) with hν
  have hνp : ∀ l, IsProbabilityMeasure (ν l) := fun l => Measure.isProbabilityMeasure_map (hmeas l).aemeasurable
  set μ₀ : Measure (Fin L → ℝ) := Measure.pi ν with hμ₀
  set P : Measure (Fin L → Fin L → ℝ) := Measure.pi (fun _ : Fin L => μ₀) with hP
  have hζv : Measurable (fun w => fun l => ζ l w) := measurable_pi_lambda _ hmeas
  have hlaw : μ.map (fun w l => ζ l w) = μ₀ :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun l => (hmeas l).aemeasurable)).1 hindep
  have hdiagmeas : Measurable (diagMap (L := L)) := continuous_diagMap.measurable
  have hdiag : P.map diagMap = μ₀ := by
    have : ∀ i : Fin L, SigmaFinite (μ₀.map (fun v : Fin L → ℝ => v i)) := fun i => by
      have := Measure.isProbabilityMeasure_map (μ := μ₀) (measurable_pi_apply i).aemeasurable
      infer_instance
    have h1 := Measure.pi_map_pi (μ := fun _ : Fin L => μ₀) (f := fun i (v : Fin L → ℝ) => v i)
      (fun i => (measurable_pi_apply i).aemeasurable)
    have h2 : ∀ i, μ₀.map (fun v : Fin L → ℝ => v i) = ν i := by
      intro i
      have := Measure.pi_map_eval (μ := ν) i
      simp only [measure_univ, Finset.prod_const_one, one_smul] at this
      exact this
    have h3 : (fun i => μ₀.map (fun v : Fin L → ℝ => v i)) = ν := funext h2
    simp only [h3] at h1
    exact h1
  have hrel : ∀ S : Set (Fin L → ℝ), MeasurableSet S →
      μ ((fun w l => ζ l w) ⁻¹' S) = P (diagMap ⁻¹' S) := by
    intro S hS
    rw [← Measure.map_apply hζv hS, hlaw, ← hdiag, Measure.map_apply hdiagmeas hS]
  have hcube_μ : ∀ᵐ w ∂μ, ∀ l, |ζ l w| ≤ 1 := ae_all_iff.2 fun l => (hbounded l).1
  set C : Set (Fin L → ℝ) := {z | ∀ l, |z l| ≤ 1} with hC
  have hCc : IsClosed C := by
    rw [hC, Set.ofPred_forall]
    exact isClosed_iInter fun l => isClosed_le (by fun_prop) continuous_const
  have hcubeP : ∀ᵐ x ∂P, ∀ l, |diagMap x l| ≤ 1 := by
    rw [ae_iff] at hcube_μ ⊢
    have e1 : {x | ¬∀ l, |diagMap x l| ≤ 1} = diagMap ⁻¹' Cᶜ := rfl
    have e2 : {w | ¬∀ l, |ζ l w| ≤ 1} = (fun w l => ζ l w) ⁻¹' Cᶜ := rfl
    rw [e1, ← hrel _ hCc.measurableSet.compl, ← e2]
    exact hcube_μ
  set K := baseSet B Υ with hK
  set A : Set (Fin L → Fin L → ℝ) := diagMap ⁻¹' K with hA
  have hKm : MeasurableSet K := (baseSet_closed B Υ).measurableSet
  have hPA : P A = μ {w | spectralNorm (perturbation B (fun l => ζ l w)) ≤ Υ} := by
    rw [hA, ← hrel K hKm]
    apply measure_congr
    filter_upwards [hcube_μ] with w hw
    apply propext
    change (spectralNorm (perturbation B (fun l => ζ l w)) ≤ Υ ∧ ∀ l, |ζ l w| ≤ 1) ↔ _
    exact ⟨fun h => h.1, fun h => ⟨h, hw⟩⟩
  have hPA' : P A = ENNReal.ofReal χ := by
    rw [hPA, hχeq, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hAm : MeasurableSet A := hKm.preimage hdiagmeas
  have hfcm : Measurable (fun x => TalagrandConc.ConvexHull.fc A x) :=
    fc_measurable A (fun s => (patSet_closed K (baseSet_compact B Υ) s).measurableSet)
  obtain ⟨hT, -⟩ := TalagrandConc1995.thm4_1_1_convex_hull_faithful μ₀ A hAm hfcm
  have hAne : A.Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero (μ := P)
    rw [hPA']; exact (ENNReal.ofReal_pos.2 hχ).ne'
  obtain ⟨y0, hy0⟩ := hAne
  have hfin : ∀ x, TalagrandConc.ConvexHull.fc A x ≠ ⊤ := by
    intro x
    have hmem : (fun _ : Fin L => (1 : ℝ)) ∈ TalagrandConc.ConvexHull.V A x := by
      apply subset_convexHull
      exact ⟨fun i => Or.inr rfl, y0, hy0, fun i h => absurd h one_ne_zero⟩
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact iInf₂_le _ hmem
  set c : ENNReal := ENNReal.ofReal (Real.exp ((Ω - Υ) ^ 2 / 16)) with hc
  set g : (Fin L → Fin L → ℝ) → ENNReal :=
    fun x => ENNReal.ofReal (Real.exp ((TalagrandConc.ConvexHull.fc A x).toReal ^ 2 / 4)) with hg
  have hpt : ∀ᵐ x ∂P, Ω < spectralNorm (perturbation B (diagMap x)) → c ≤ g x := by
    filter_upwards [hcubeP] with x hx hlt
    have hlow : ENNReal.ofReal ((Ω - Υ) / 2) ≤ TalagrandConc.ConvexHull.fc A x := by
      refine le_iInf₂ fun s hs => ENNReal.ofReal_le_ofReal ?_
      have := key B hB hvariance Υ x hx s hs
      linarith
    have hreal : (Ω - Υ) / 2 ≤ (TalagrandConc.ConvexHull.fc A x).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin x)).1 hlow
    have hpos : 0 ≤ (Ω - Υ) / 2 := by linarith
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := mul_le_mul hreal hreal hpos (le_trans hpos hreal)
    nlinarith [this]
  have hgm : AEMeasurable g P :=
    (((hfcm.ennreal_toReal.pow_const 2).div_const 4).exp.ennreal_ofReal).aemeasurable
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmk := meas_ge_le_lintegral_div hgm hc0 hctop
  have hsub : P {x | Ω < spectralNorm (perturbation B (diagMap x))} ≤ P {x | c ≤ g x} :=
    measure_mono_ae (by filter_upwards [hpt] with x hx h using hx h)
  have htailS : MeasurableSet {z : Fin L → ℝ | Ω < spectralNorm (perturbation B z)} :=
    (isOpen_lt continuous_const (continuous_spectralNorm_pert B)).measurableSet
  have htail : μ {w | Ω < spectralNorm (perturbation B (fun l => ζ l w))} =
      P {x | Ω < spectralNorm (perturbation B (diagMap x))} := hrel _ htailS
  have hbound : μ {w | Ω < spectralNorm (perturbation B (fun l => ζ l w))} ≤
      (ENNReal.ofReal χ)⁻¹ / c := by
    rw [htail, ← hPA']
    exact le_trans hsub (le_trans hmk (ENNReal.div_le_div_right hT c))
  have hne : (ENNReal.ofReal χ)⁻¹ / c ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hχ).ne') hc0
  refine le_trans (ENNReal.toReal_mono hne hbound) (le_of_eq ?_)
  rw [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hχ.le, hc,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, neg_div, Real.exp_neg]
  ring
