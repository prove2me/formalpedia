-- Prove2me | solution 1 for TimeInconsLQ.Sufficient.theorem_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T14:10:31.917373+00:00
-- url     : https://prove2.me/submissions/56f4d994-048c-401b-b2c3-659245268fad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Sufficient_Model
import Definitions.Def_TimeInconsLQ_Sufficient_Adjoint
import Theorems.Thm_TimeInconsLQ_Sufficient_proposition_3_1
import Theorems.Thm_TimeInconsLQ_Sufficient_second_adjoint_psd
import Theorems.Thm_TimeInconsLQ_Sufficient_second_adjoint_exists
import Theorems.Thm_TimeInconsLQ_Sufficient_state_unique

open MeasureTheory ProbabilityTheory Filter Topology TimeInconsLQ.Sufficient
open scoped ENNReal NNReal Matrix

namespace TILQSuffRed

variable {Ω : Type*} [MeasurableSpace Ω] {n l d : ℕ}

lemma prod_restrict_univ (P : Measure Ω) [IsFiniteMeasure P] (S : Set ℝ) :
    (volume.restrict S).prod P = (volume.prod P).restrict (S ×ˢ Set.univ) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

/-- From `∀ s ∈ S, ∀ᵐ ω` to `∀ᵐ ω, ∀ᵐ s ∈ S`, for a measurable set. -/
lemma ae_ae_of_forall (P : Measure Ω) [IsFiniteMeasure P] {S : Set ℝ} (hS : MeasurableSet S)
    {E : Set (ℝ × Ω)} (hE : MeasurableSet E) (h : ∀ s ∈ S, ∀ᵐ ω ∂P, (s, ω) ∈ E) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict S), (s, ω) ∈ E := by
  have h1 : ∀ᵐ q ∂(volume.restrict S).prod P, q ∈ E :=
    (Measure.ae_prod_mem_iff_ae_ae_mem hE).2 (ae_restrict_of_forall_mem hS h)
  have h2 : ∀ᵐ q ∂P.prod (volume.restrict S), q.swap ∈ E :=
    (Measure.measurePreserving_swap (μ := P) (ν := volume.restrict S)).quasiMeasurePreserving.ae h1
  exact Measure.ae_ae_of_ae_prod h2

/-- From product-a.e. to `∀ᵐ ω, ∀ᵐ s`. -/
lemma ae_ae_of_prod (P : Measure Ω) [IsFiniteMeasure P] {S : Set ℝ}
    {p : ℝ × Ω → Prop} (h : ∀ᵐ q ∂(volume.restrict S).prod P, p q) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict S), p (s, ω) := by
  have h2 : ∀ᵐ q ∂P.prod (volume.restrict S), p q.swap :=
    (Measure.measurePreserving_swap (μ := P) (ν := volume.restrict S)).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod h2

/-- Clamped joint strong measurability of a strongly progressive process. -/
lemma prog_clamp {E : Type*} [TopologicalSpace E] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {f : ℝ≥0 → Ω → E} (hf : IsStronglyProgressive 𝓕 f) (T : ℝ≥0) :
    StronglyMeasurable (fun q : ℝ × Ω => f (min q.1.toNNReal T) q.2) := by
  have h := hf T
  let φ : ℝ × Ω → Set.Iic T × Ω := fun q => (⟨min q.1.toNNReal T, Set.mem_Iic.2 (min_le_right _ _)⟩, q.2)
  have hφ : @Measurable (ℝ × Ω) (Set.Iic T × Ω) _
      (Subtype.instMeasurableSpace.prod (𝓕 T)) φ := by
    apply @Measurable.prodMk _ _ _ _ _ (𝓕 T)
    · exact ((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk
    · exact measurable_snd.mono le_rfl (𝓕.le T)
  exact h.comp_measurable hφ

lemma norm_mulVec_le {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (x : Fin k → ℝ) :
    ‖A *ᵥ x‖ ≤ k * ‖Matrix.of.symm A‖ * ‖x‖ := by
  have h0 : 0 ≤ (k : ℝ) * ‖Matrix.of.symm A‖ * ‖x‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Real.norm_eq_abs]
  calc |∑ j, A i j * x j| ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, ‖Matrix.of.symm A‖ * ‖x‖ := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        have h1 : |A i j| ≤ ‖Matrix.of.symm A‖ := by
          have := norm_le_pi_norm (Matrix.of.symm A i) j
          have h2 := norm_le_pi_norm (Matrix.of.symm A) i
          simpa [Real.norm_eq_abs] using this.trans h2
        have h3 : |x j| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
        exact mul_le_mul h1 h3 (abs_nonneg _) (norm_nonneg _)
    _ = k * ‖Matrix.of.symm A‖ * ‖x‖ := by simp [Finset.sum_const]; ring

lemma norm_transpose_le {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) :
    ‖Matrix.of.symm Aᵀ‖ ≤ ‖Matrix.of.symm A‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have := norm_le_pi_norm (Matrix.of.symm A j) i
  have h2 := norm_le_pi_norm (Matrix.of.symm A) j
  simpa using this.trans h2

lemma abs_dotProduct_le {k : ℕ} (a b : Fin k → ℝ) : |a ⬝ᵥ b| ≤ k * ‖a‖ * ‖b‖ := by
  simp only [dotProduct]
  calc |∑ j, a j * b j| ≤ ∑ j, |a j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, ‖a‖ * ‖b‖ := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm a j)
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm b j) (abs_nonneg _) (norm_nonneg _)
    _ = k * ‖a‖ * ‖b‖ := by simp [Finset.sum_const]; ring


lemma aesm_of_clamp {E : Type*} [TopologicalSpace E] (P : Measure Ω) [IsFiniteMeasure P]
    {S : Set ℝ} (hS : MeasurableSet S) {F G : ℝ × Ω → E} (hG : StronglyMeasurable G)
    (h : ∀ q : ℝ × Ω, q.1 ∈ S → F q = G q) :
    AEStronglyMeasurable F ((volume.restrict S).prod P) := by
  rw [prod_restrict_univ]
  exact hG.aestronglyMeasurable.congr
    (ae_restrict_of_forall_mem (hS.prod MeasurableSet.univ) fun q hq => (h q hq.1).symm)

lemma aesm_prog {E : Type*} [TopologicalSpace E] (P : Measure Ω) [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {g : ℝ≥0 → Ω → E} (hg : IsStronglyProgressive 𝓕 g)
    (T : ℝ≥0) {S : Set ℝ} (hS : MeasurableSet S) {F : ℝ × Ω → E}
    (hF : ∀ q : ℝ × Ω, q.1 ∈ S → F q = g (min q.1.toNNReal T) q.2) :
    AEStronglyMeasurable F ((volume.restrict S).prod P) :=
  aesm_of_clamp P hS (prog_clamp hg T) hF

lemma ess_bound {E : Type*} [Norm E] (M : Data Ω n l d) [IsFiniteMeasure M.P]
    {f : ℝ≥0 → Ω → E} (hf : EssBounded M f) {S : Set ℝ} (hS : S ⊆ Set.Icc 0 (M.T : ℝ)) :
    ∃ K : ℝ, ∀ᵐ q ∂((volume.restrict S).prod M.P), ‖f q.1.toNNReal q.2‖ ≤ K := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨K, ?_⟩
  rw [prod_restrict_univ] at hK ⊢
  exact ae_restrict_of_ae_restrict_of_subset (Set.prod_mono hS le_rfl) hK

lemma memLp_two_of_lintegral {E : Type*} [NormedAddCommGroup E] (P : Measure Ω) [IsFiniteMeasure P]
    {S : Set ℝ} {F : ℝ × Ω → E} (hF : AEStronglyMeasurable F ((volume.restrict S).prod P))
    (h : ∫⁻ ω, ∫⁻ s in S, ‖F (s, ω)‖ₑ ^ 2 ∂volume ∂P < ⊤) :
    MemLp F 2 ((volume.restrict S).prod P) := by
  refine ⟨hF, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  have h2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by simp
  simp_rw [h2, ENNReal.rpow_natCast]
  rw [lintegral_prod_symm _ (hF.enorm.pow_const 2)]
  exact h

lemma toNNReal_facts {t T : ℝ≥0} {s : ℝ} (hs : s ∈ Set.Icc (t : ℝ) T) :
    min s.toNNReal T = s.toNNReal ∧ t ≤ s.toNNReal := by
  have h0 : (0 : ℝ) ≤ s := le_trans t.2 hs.1
  exact ⟨min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2), (Real.le_toNNReal_iff_coe_le h0).2 hs.1⟩


lemma norm_matmul_le {m k r : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin k) (Fin r) ℝ) :
    ‖Matrix.of.symm (A * B)‖ ≤ k * ‖Matrix.of.symm A‖ * ‖Matrix.of.symm B‖ := by
  have h0 : 0 ≤ (k : ℝ) * ‖Matrix.of.symm A‖ * ‖Matrix.of.symm B‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  have hA : ∀ i c, |A i c| ≤ ‖Matrix.of.symm A‖ := fun i c => by
    have := norm_le_pi_norm (Matrix.of.symm A i) c
    have h2 := norm_le_pi_norm (Matrix.of.symm A) i
    simpa [Real.norm_eq_abs] using this.trans h2
  have hB : ∀ c j, |B c j| ≤ ‖Matrix.of.symm B‖ := fun c j => by
    have := norm_le_pi_norm (Matrix.of.symm B c) j
    have h2 := norm_le_pi_norm (Matrix.of.symm B) c
    simpa [Real.norm_eq_abs] using this.trans h2
  show |(A * B) i j| ≤ _
  rw [Matrix.mul_apply]
  calc |∑ c, A i c * B c j| ≤ ∑ c, |A i c * B c j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : Fin k, ‖Matrix.of.symm A‖ * ‖Matrix.of.symm B‖ := by
        apply Finset.sum_le_sum; intro c _
        rw [abs_mul]
        exact mul_le_mul (hA i c) (hB c j) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp [Finset.sum_const]; ring

lemma norm_of_le_matEntries {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    ‖Matrix.of.symm A‖ ≤ ‖Peng1990.SMP.matEntries A‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  exact norm_le_pi_norm (Peng1990.SMP.matEntries A) (i, j)

lemma entries_matEntries {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    Peng1990.SMP.entriesMat (Peng1990.SMP.matEntries A) = A := by
  ext i j; simp [Peng1990.SMP.entriesMat, Peng1990.SMP.matEntries]

lemma continuous_entriesMat {k : ℕ} :
    Continuous (Peng1990.SMP.entriesMat : (Fin k × Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ) :=
  continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

section LamSec
variable (M : Data Ω n l d) (hM : Standing M) (u : ℝ≥0 → Ω → Fin l → ℝ)
  (t : ℝ≥0) (p : ℝ≥0 → Ω → Fin n → ℝ) (k : Fin d → ℝ≥0 → Ω → Fin n → ℝ)

include hM in
lemma lam_memLp (hu : Admissible M u)
    (hpP : IsStronglyProgressive (filt M) (fun s ω => if t ≤ s then p s ω else 0))
    (hkP : ∀ j, IsStronglyProgressive (filt M) (fun s ω => if t ≤ s then k j s ω else 0))
    (hpL : ∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) M.T, ‖p s.toNNReal ω‖ₑ ^ 2 ∂volume ∂M.P < ⊤)
    (hkL : ∀ j, ∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) M.T, ‖k j s.toNNReal ω‖ₑ ^ 2 ∂volume ∂M.P < ⊤)
    {S : Set ℝ} (hS : MeasurableSet S) (hSt : S ⊆ Set.Icc (t : ℝ) M.T) :
    MemLp (fun q : ℝ × Ω => Lam M u p k q.1.toNNReal q.2) 2 ((volume.restrict S).prod M.P) := by
  have := hM.prob
  have hS0 : S ⊆ Set.Icc 0 (M.T : ℝ) := fun s hs => ⟨le_trans t.2 (hSt hs).1, (hSt hs).2⟩
  -- measurability of the factors
  have mp : AEStronglyMeasurable (fun q : ℝ × Ω => p q.1.toNNReal q.2)
      ((volume.restrict S).prod M.P) := by
    refine aesm_prog M.P hpP M.T hS fun q hq => ?_
    obtain ⟨h1, h2⟩ := toNNReal_facts (hSt hq)
    simp [h1, h2]
  have mk : ∀ j, AEStronglyMeasurable (fun q : ℝ × Ω => k j q.1.toNNReal q.2)
      ((volume.restrict S).prod M.P) := by
    intro j
    refine aesm_prog M.P (hkP j) M.T hS fun q hq => ?_
    obtain ⟨h1, h2⟩ := toNNReal_facts (hSt hq)
    simp [h1, h2]
  have mu : AEStronglyMeasurable (fun q : ℝ × Ω => u q.1.toNNReal q.2)
      ((volume.restrict S).prod M.P) := by
    refine aesm_prog M.P hu.1 M.T hS fun q hq => ?_
    obtain ⟨h1, h2⟩ := toNNReal_facts (hSt hq)
    simp [h1]
  have mB : AEStronglyMeasurable (fun q : ℝ × Ω => M.B q.1.toNNReal q.2)
      ((volume.restrict S).prod M.P) := by
    refine aesm_prog M.P hM.B_prog M.T hS fun q hq => ?_
    obtain ⟨h1, h2⟩ := toNNReal_facts (hSt hq)
    simp [h1]
  have mD : ∀ j, AEStronglyMeasurable (fun q : ℝ × Ω => M.D j q.1.toNNReal q.2)
      ((volume.restrict S).prod M.P) := by
    intro j
    refine aesm_prog M.P (hM.D_prog j) M.T hS fun q hq => ?_
    obtain ⟨h1, h2⟩ := toNNReal_facts (hSt hq)
    simp [h1]
  have mR : AEStronglyMeasurable (fun q : ℝ × Ω => M.R q.1.toNNReal q.2)
      ((volume.restrict S).prod M.P) := by
    refine aesm_prog M.P hM.R_prog M.T hS fun q hq => ?_
    obtain ⟨h1, h2⟩ := toNNReal_facts (hSt hq)
    simp [h1]
  -- L² of p, k, u
  have Lp : MemLp (fun q : ℝ × Ω => p q.1.toNNReal q.2) 2 ((volume.restrict S).prod M.P) :=
    memLp_two_of_lintegral M.P mp (lt_of_le_of_lt (lintegral_mono fun ω =>
      lintegral_mono_set hSt) hpL)
  have Lk : ∀ j, MemLp (fun q : ℝ × Ω => k j q.1.toNNReal q.2) 2
      ((volume.restrict S).prod M.P) := fun j =>
    memLp_two_of_lintegral M.P (mk j) (lt_of_le_of_lt (lintegral_mono fun ω =>
      lintegral_mono_set hSt) (hkL j))
  have Lu : MemLp (fun q : ℝ × Ω => u q.1.toNNReal q.2) 2 ((volume.restrict S).prod M.P) :=
    memLp_two_of_lintegral M.P mu (lt_of_le_of_lt (lintegral_mono fun ω =>
      lintegral_mono_set hS0) hu.2)
  obtain ⟨KB, hKB⟩ := ess_bound M hM.B_bdd hS0
  obtain ⟨KR, hKR⟩ := ess_bound M hM.R_bdd hS0
  have hKD : ∀ j, ∃ K : ℝ, ∀ᵐ q ∂((volume.restrict S).prod M.P),
      ‖Matrix.of.symm (M.D j q.1.toNNReal q.2)‖ ≤ K := fun j => ess_bound M (hM.D_bdd j) hS0
  choose KD hKD using hKD
  have t1 : MemLp (fun q : ℝ × Ω => M.B q.1.toNNReal q.2 *ᵥ p q.1.toNNReal q.2) 2
      ((volume.restrict S).prod M.P) := by
    refine Lp.of_le_mul (c := n * KB) ?_ ?_
    · exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable₂
        mB mp
    · filter_upwards [hKB] with q hq
      refine (norm_mulVec_le _ _).trans ?_
      have : (n : ℝ) * ‖Matrix.of.symm (M.B q.1.toNNReal q.2)‖ ≤ n * KB :=
        mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have t2 : ∀ j, MemLp (fun q : ℝ × Ω => (M.D j q.1.toNNReal q.2)ᵀ *ᵥ k j q.1.toNNReal q.2) 2
      ((volume.restrict S).prod M.P) := by
    intro j
    refine (Lk j).of_le_mul (c := n * KD j) ?_ ?_
    · exact Continuous.comp_aestronglyMeasurable₂
        (g := fun (A : Matrix (Fin n) (Fin l) ℝ) (x : Fin n → ℝ) => Aᵀ *ᵥ x)
        (Continuous.matrix_mulVec (continuous_fst.matrix_transpose) continuous_snd) (mD j) (mk j)
    · filter_upwards [hKD j] with q hq
      refine (norm_mulVec_le _ _).trans ?_
      have : (n : ℝ) * ‖Matrix.of.symm (M.D j q.1.toNNReal q.2)ᵀ‖ ≤ n * KD j :=
        mul_le_mul_of_nonneg_left ((norm_transpose_le _).trans hq) (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have t3 : MemLp (fun q : ℝ × Ω => M.R q.1.toNNReal q.2 *ᵥ u q.1.toNNReal q.2) 2
      ((volume.restrict S).prod M.P) := by
    refine Lu.of_le_mul (c := l * KR) ?_ ?_
    · exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable₂
        mR mu
    · filter_upwards [hKR] with q hq
      refine (norm_mulVec_le _ _).trans ?_
      have : (l : ℝ) * ‖Matrix.of.symm (M.R q.1.toNNReal q.2)‖ ≤ l * KR :=
        mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have t2' := memLp_finsetSum (s := Finset.univ) (fun j _ => t2 j)
  exact (t1.add t2').add t3

include hM in
lemma H_section_integrable (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hPP : IsStronglyProgressive (filt M)
      (fun s ω => if t ≤ s then Peng1990.SMP.matEntries (Pm s ω) else 0))
    (hPL : ∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) M.T,
      ‖Peng1990.SMP.matEntries (Pm s.toNNReal ω)‖ₑ ^ 2 ∂volume ∂M.P < ⊤)
    (v : Ω → Fin l → ℝ) (hv : StronglyMeasurable[filt M t] v)
    {S : Set ℝ} [IsFiniteMeasure (volume.restrict S)] (hS : MeasurableSet S)
    (hSt : S ⊆ Set.Icc (t : ℝ) M.T) :
    ∀ᵐ ω ∂M.P, Integrable (fun s : ℝ => (Hmat M Pm s.toNNReal ω *ᵥ v ω) ⬝ᵥ v ω)
      (volume.restrict S) := by
  have := hM.prob
  have hS0 : S ⊆ Set.Icc 0 (M.T : ℝ) := fun s hs => ⟨le_trans t.2 (hSt hs).1, (hSt hs).2⟩
  have mPe : AEStronglyMeasurable (fun q : ℝ × Ω => Peng1990.SMP.matEntries (Pm q.1.toNNReal q.2))
      ((volume.restrict S).prod M.P) := by
    refine aesm_prog M.P hPP M.T hS fun q hq => ?_
    obtain ⟨h1, h2⟩ := toNNReal_facts (hSt hq)
    simp [h1, h2]
  have mP : AEStronglyMeasurable (fun q : ℝ × Ω => Pm q.1.toNNReal q.2)
      ((volume.restrict S).prod M.P) := by
    have := continuous_entriesMat.comp_aestronglyMeasurable mPe
    simpa [Function.comp_def, entries_matEntries] using this
  have mD : ∀ j, AEStronglyMeasurable (fun q : ℝ × Ω => M.D j q.1.toNNReal q.2)
      ((volume.restrict S).prod M.P) := by
    intro j
    refine aesm_prog M.P (hM.D_prog j) M.T hS fun q hq => ?_
    obtain ⟨h1, h2⟩ := toNNReal_facts (hSt hq)
    simp [h1]
  have mR : AEStronglyMeasurable (fun q : ℝ × Ω => M.R q.1.toNNReal q.2)
      ((volume.restrict S).prod M.P) := by
    refine aesm_prog M.P hM.R_prog M.T hS fun q hq => ?_
    obtain ⟨h1, h2⟩ := toNNReal_facts (hSt hq)
    simp [h1]
  have hv' : StronglyMeasurable v := hv.mono ((filt M).le t)
  have mv : AEStronglyMeasurable (fun q : ℝ × Ω => v q.2) ((volume.restrict S).prod M.P) :=
    (hv'.comp_measurable measurable_snd).aestronglyMeasurable
  have mH : AEStronglyMeasurable (fun q : ℝ × Ω => Hmat M Pm q.1.toNNReal q.2)
      ((volume.restrict S).prod M.P) := by
    unfold Hmat
    refine mR.add ?_
    refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    exact Continuous.comp_aestronglyMeasurable₂
      (g := fun (D : Matrix (Fin n) (Fin l) ℝ) (P : Matrix (Fin n) (Fin n) ℝ) => Dᵀ * P * D)
      (((continuous_fst.matrix_transpose).matrix_mul continuous_snd).matrix_mul continuous_fst)
      (mD j) mP
  have PL : Integrable (fun q : ℝ × Ω => ‖Peng1990.SMP.matEntries (Pm q.1.toNNReal q.2)‖)
      ((volume.restrict S).prod M.P) :=
    ((memLp_two_of_lintegral M.P mPe (lt_of_le_of_lt (lintegral_mono fun ω =>
      lintegral_mono_set hSt) hPL)).integrable one_le_two).norm
  obtain ⟨KR, hKR⟩ := ess_bound M hM.R_bdd hS0
  have hKD : ∀ j, ∃ K : ℝ, ∀ᵐ q ∂((volume.restrict S).prod M.P),
      ‖Matrix.of.symm (M.D j q.1.toNNReal q.2)‖ ≤ K := fun j => ess_bound M (hM.D_bdd j) hS0
  choose KD hKD using hKD
  set g : ℝ × Ω → ℝ := fun q =>
    ((Hmat M Pm q.1.toNNReal q.2 *ᵥ v q.2) ⬝ᵥ v q.2) / (1 + ‖v q.2‖ ^ 2) with hg
  have mg : AEStronglyMeasurable g ((volume.restrict S).prod M.P) := by
    refine Continuous.comp_aestronglyMeasurable₂
      (g := fun (A : Matrix (Fin l) (Fin l) ℝ) (x : Fin l → ℝ) => ((A *ᵥ x) ⬝ᵥ x) / (1 + ‖x‖ ^ 2))
      ?_ mH mv
    refine Continuous.div ((Continuous.matrix_mulVec continuous_fst continuous_snd).dotProduct
      continuous_snd) (continuous_const.add (continuous_snd.norm.pow 2)) fun x => by positivity
  have gi : Integrable g ((volume.restrict S).prod M.P) := by
    refine Integrable.mono' ((integrable_const (l * l * KR)).add
      (PL.const_mul (l * l * ∑ j, n * n * (KD j * KD j)))) mg ?_
    have hKD' : ∀ᵐ q ∂((volume.restrict S).prod M.P),
        ∀ j, ‖Matrix.of.symm (M.D j q.1.toNNReal q.2)‖ ≤ KD j := ae_all_iff.2 hKD
    filter_upwards [hKR, hKD'] with q hR hD
    set H := Hmat M Pm q.1.toNNReal q.2
    set x := v q.2
    set P := Pm q.1.toNNReal q.2
    have hH : ‖Matrix.of.symm H‖ ≤ KR + ∑ j, n * n * (KD j * KD j) *
        ‖Peng1990.SMP.matEntries P‖ := by
      have e : Matrix.of.symm H = Matrix.of.symm (M.R q.1.toNNReal q.2) +
          ∑ j, Matrix.of.symm ((M.D j q.1.toNNReal q.2)ᵀ * P * M.D j q.1.toNNReal q.2) := rfl
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add hR ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      set Dj := M.D j q.1.toNNReal q.2
      have e1 := norm_matmul_le (Djᵀ * P) Dj
      have e2 := norm_matmul_le Djᵀ P
      have e3 := norm_transpose_le Dj
      have e4 := norm_of_le_matEntries P
      have hD0 : 0 ≤ ‖Matrix.of.symm Dj‖ := norm_nonneg _
      have hDj := hD j
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      calc ‖Matrix.of.symm (Djᵀ * P * Dj)‖
          ≤ n * ‖Matrix.of.symm (Djᵀ * P)‖ * ‖Matrix.of.symm Dj‖ := e1
        _ ≤ n * (n * ‖Matrix.of.symm Dj‖ * ‖Peng1990.SMP.matEntries P‖) *
              ‖Matrix.of.symm Dj‖ := by
            gcongr
            exact e2.trans (by gcongr)
        _ ≤ n * (n * KD j * ‖Peng1990.SMP.matEntries P‖) * KD j := by
            have hK0 : 0 ≤ KD j := hD0.trans hDj
            have h1 : (n : ℝ) * ‖Matrix.of.symm Dj‖ * ‖Peng1990.SMP.matEntries P‖ ≤
                n * KD j * ‖Peng1990.SMP.matEntries P‖ := by gcongr
            exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hn) hDj hD0
              (mul_nonneg hn (mul_nonneg (mul_nonneg hn hK0) (norm_nonneg _)))
        _ = n * n * (KD j * KD j) * ‖Peng1990.SMP.matEntries P‖ := by ring
    have hv1 : 0 < 1 + ‖x‖ ^ 2 := by positivity
    have hnum : |(H *ᵥ x) ⬝ᵥ x| ≤ l * l * ‖Matrix.of.symm H‖ * ‖x‖ ^ 2 := by
      have a1 := abs_dotProduct_le (H *ᵥ x) x
      have a2 := norm_mulVec_le H x
      calc |(H *ᵥ x) ⬝ᵥ x| ≤ l * ‖H *ᵥ x‖ * ‖x‖ := a1
        _ ≤ l * (l * ‖Matrix.of.symm H‖ * ‖x‖) * ‖x‖ := by gcongr
        _ = _ := by ring
    have hX0 : 0 ≤ (l : ℝ) * l * ‖Matrix.of.symm H‖ := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hv1, div_le_iff₀ hv1]
    calc |(H *ᵥ x) ⬝ᵥ x| ≤ l * l * ‖Matrix.of.symm H‖ * ‖x‖ ^ 2 := hnum
      _ ≤ l * l * ‖Matrix.of.symm H‖ * (1 + ‖x‖ ^ 2) := by gcongr; linarith
      _ ≤ (l * l * KR + l * l * ∑ j, n * n * (KD j * KD j) *
            ‖Peng1990.SMP.matEntries P‖) * (1 + ‖x‖ ^ 2) := by
          gcongr
          have := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ l * l)
          rw [mul_add] at this
          exact this
      _ = _ := by
        simp only [Pi.add_apply]
        rw [← Finset.sum_mul]
        ring
  filter_upwards [gi.prod_left_ae] with ω hω
  have := hω.const_mul (1 + ‖v ω‖ ^ 2)
  refine this.congr (Eventually.of_forall fun s => ?_)
  have hv1 : 0 < 1 + ‖v ω‖ ^ 2 := by positivity
  simp only [hg]
  field_simp

end LamSec

lemma memLp_two_of_lintegral_prod {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : α → E} (hF : AEStronglyMeasurable F μ)
    (h : ∫⁻ q, ‖F q‖ₑ ^ 2 ∂μ < ⊤) : MemLp F 2 μ := by
  refine ⟨hF, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  have h2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by simp
  simp_rw [h2, ENNReal.rpow_natCast]
  exact h

lemma lintegral_of_memLp_two {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : α → E} (hF : MemLp F 2 μ) : ∫⁻ q, ‖F q‖ₑ ^ 2 ∂μ < ⊤ := by
  have := hF.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at this
  have h2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by simp
  simp_rw [h2, ENNReal.rpow_natCast] at this
  exact this

omit [MeasurableSpace Ω] in
lemma lintegral_sq_condExp_le {m0 : MeasurableSpace Ω} (m : MeasurableSpace Ω)
    (P : @Measure Ω m0) (f : Ω → ℝ) :
    ∫⁻ ω, ‖condExp m P f ω‖ₑ ^ 2 ∂P ≤ ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P := by
  have h := eLpNorm_condExp_le_eLpNorm (m := m) (μ := P) f (p := 2) one_le_two
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at h
  have h2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by simp
  simp_rw [h2, ENNReal.rpow_natCast] at h
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 1 / ((2 : ℕ) : ℝ))).1 h

lemma memLp_coord {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → Fin l → ℝ}
    (hF : MemLp F 2 μ) (i : Fin l) : MemLp (fun q => F q i) 2 μ :=
  hF.of_le_mul (c := 1) ((continuous_apply i).comp_aestronglyMeasurable hF.1)
    (Eventually.of_forall fun q => by simpa using norm_le_pi_norm (F q) i)

lemma integrable_dot {α : Type*} [MeasurableSpace α] {μ : Measure α} {F G : α → Fin l → ℝ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) : Integrable (fun q => F q ⬝ᵥ G q) μ := by
  simp only [dotProduct]
  refine integrable_finsetSum _ fun i _ => ?_
  exact (memLp_coord hF i).integrable_mul (memLp_coord hG i)

section CondFub
variable (M : Data Ω n l d) (hM : Standing M) (t : ℝ≥0)

include hM in
lemma v_memLp (v : Ω → Fin l → ℝ) (hv : StronglyMeasurable[filt M t] v)
    (hv2 : ∫⁻ ω, ‖v ω‖ₑ ^ 2 ∂M.P < ⊤) {S : Set ℝ} [IsFiniteMeasure (volume.restrict S)] :
    MemLp (fun q : ℝ × Ω => v q.2) 2 ((volume.restrict S).prod M.P) := by
  have := hM.prob
  have hv' : StronglyMeasurable v := hv.mono ((filt M).le t)
  refine memLp_two_of_lintegral M.P (hv'.comp_measurable measurable_snd).aestronglyMeasurable ?_
  simp only [setLIntegral_const]
  have hS : volume S ≠ ⊤ := by
    have := measure_ne_top (volume.restrict S) Set.univ
    simpa using this
  simp_rw [mul_comm _ (volume S)]
  rw [lintegral_const_mul' _ _ hS]
  exact ENNReal.mul_lt_top hS.lt_top hv2

include hM in
lemma cond_fubini (Λ : ℝ≥0 → Ω → Fin l → ℝ) {S : Set ℝ} [IsFiniteMeasure (volume.restrict S)]
    (hS : MeasurableSet S) (hSt : S ⊆ Set.Ioc (t : ℝ) M.T)
    (hΛ : MemLp (fun q : ℝ × Ω => Λ q.1.toNNReal q.2) 2 ((volume.restrict S).prod M.P))
    (Lhat : ℝ → Ω → Fin l → ℝ)
    (hLm : Measurable[MeasurableSpace.comap Prod.fst (borel ℝ) ⊔
          MeasurableSpace.comap Prod.snd (filt M t)] (fun q : ℝ × Ω => Lhat q.1 q.2))
    (hLv : ∀ᵐ s ∂(volume.restrict (Set.Ioc (t : ℝ) M.T)), ∀ i,
          (fun ω => Lhat s ω i) =ᵐ[M.P] condExp (filt M t) M.P (fun ω => Λ s.toNNReal ω i))
    (v : Ω → Fin l → ℝ) (hv : StronglyMeasurable[filt M t] v)
    (hv2 : ∫⁻ ω, ‖v ω‖ₑ ^ 2 ∂M.P < ⊤) :
    Integrable (fun ω => ∫ s in S, Λ s.toNNReal ω ⬝ᵥ v ω) M.P ∧
    (fun ω => ∫ s in S, Lhat s ω ⬝ᵥ v ω) =ᵐ[M.P]
      condExp (filt M t) M.P (fun ω => ∫ s in S, Λ s.toNNReal ω ⬝ᵥ v ω) := by
  have := hM.prob
  set μS := (volume.restrict S).prod M.P with hμS
  have vL := v_memLp M hM t v hv hv2 (S := S)
  have hv' : StronglyMeasurable v := hv.mono ((filt M).le t)
  -- Lhat measurability
  have hLm' : Measurable (fun q : ℝ × Ω => Lhat q.1 q.2) :=
    hLm.mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono ((filt M).le t))) le_rfl
  have mL : AEStronglyMeasurable (fun q : ℝ × Ω => Lhat q.1 q.2) μS :=
    hLm'.aestronglyMeasurable
  -- Lhat is L²
  have hLv' : ∀ᵐ s ∂(volume.restrict S), ∀ i,
      (fun ω => Lhat s ω i) =ᵐ[M.P] condExp (filt M t) M.P (fun ω => Λ s.toNNReal ω i) :=
    ae_restrict_of_ae_restrict_of_subset hSt hLv
  have LL : ∀ i, MemLp (fun q : ℝ × Ω => Lhat q.1 q.2 i) 2 μS := by
    intro i
    have mLi : AEStronglyMeasurable (fun q : ℝ × Ω => Lhat q.1 q.2 i) μS :=
      (continuous_apply i).comp_aestronglyMeasurable mL
    refine memLp_two_of_lintegral_prod mLi ?_
    have mΛi := (memLp_coord hΛ i)
    refine lt_of_le_of_lt ?_ (lintegral_of_memLp_two mΛi)
    rw [lintegral_prod _ (mLi.enorm.pow_const 2), lintegral_prod _ (mΛi.1.enorm.pow_const 2)]
    refine lintegral_mono_ae ?_
    filter_upwards [hLv'] with s hs
    calc ∫⁻ ω, ‖Lhat s ω i‖ₑ ^ 2 ∂M.P
        = ∫⁻ ω, ‖condExp (filt M t) M.P (fun ω => Λ s.toNNReal ω i) ω‖ₑ ^ 2 ∂M.P :=
          lintegral_congr_ae ((hs i).mono fun ω h => by simp only [h])
      _ ≤ _ := lintegral_sq_condExp_le (filt M t) M.P _
  have GΛ : Integrable (fun q : ℝ × Ω => Λ q.1.toNNReal q.2 ⬝ᵥ v q.2) μS := integrable_dot hΛ vL
  have GLh : Integrable (fun q : ℝ × Ω => Lhat q.1 q.2 ⬝ᵥ v q.2) μS := by
    simp only [dotProduct]
    exact integrable_finsetSum _ fun i _ => (LL i).integrable_mul (memLp_coord vL i)
  have hJ : Integrable (fun ω => ∫ s in S, Λ s.toNNReal ω ⬝ᵥ v ω) M.P := GΛ.integral_prod_right
  refine ⟨hJ, ?_⟩
  have hLi : Integrable (fun ω => ∫ s in S, Lhat s ω ⬝ᵥ v ω) M.P := GLh.integral_prod_right
  -- measurability of the candidate w.r.t. 𝓕ₜ
  have hLsm : StronglyMeasurable[filt M t] (fun ω => ∫ s in S, Lhat s ω ⬝ᵥ v ω) := by
    have hvm : Measurable[filt M t] v := hv.measurable
    have hf : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ (filt M t)) _
        (fun q : ℝ × Ω => Lhat q.1 q.2 ⬝ᵥ v q.2) := by
      have h1 : @Measurable (ℝ × Ω) (Fin l → ℝ) (@Prod.instMeasurableSpace ℝ Ω _ (filt M t)) _
          (fun q : ℝ × Ω => Lhat q.1 q.2) := hLm
      have h2 : @Measurable (ℝ × Ω) (Fin l → ℝ) (@Prod.instMeasurableSpace ℝ Ω _ (filt M t)) _
          (fun q : ℝ × Ω => v q.2) := hvm.comp (@measurable_snd ℝ Ω _ (filt M t))
      exact (Continuous.dotProduct continuous_fst continuous_snd).measurable.comp (h1.prodMk h2)
    exact @StronglyMeasurable.integral_prod_left ℝ Ω ℝ _ (filt M t) (volume.restrict S) _ _ _
      (fun s ω => Lhat s ω ⬝ᵥ v ω) hf.stronglyMeasurable
  -- per-time identities
  have aΛv : ∀ i, Integrable (fun q : ℝ × Ω => Λ q.1.toNNReal q.2 i * v q.2 i) μS := fun i =>
    (memLp_coord hΛ i).integrable_mul (memLp_coord vL i)
  have aΛ : ∀ i, Integrable (fun q : ℝ × Ω => Λ q.1.toNNReal q.2 i) μS := fun i =>
    (memLp_coord hΛ i).integrable one_le_two
  have aLv : ∀ i, Integrable (fun q : ℝ × Ω => Lhat q.1 q.2 i * v q.2 i) μS := fun i =>
    (LL i).integrable_mul (memLp_coord vL i)
  have hs_good : ∀ᵐ s ∂(volume.restrict S), (∀ i,
      (fun ω => Lhat s ω i) =ᵐ[M.P] condExp (filt M t) M.P (fun ω => Λ s.toNNReal ω i)) ∧
      (∀ i, Integrable (fun ω => Λ s.toNNReal ω i * v ω i) M.P) ∧
      (∀ i, Integrable (fun ω => Λ s.toNNReal ω i) M.P) ∧
      (∀ i, Integrable (fun ω => Lhat s ω i * v ω i) M.P) := by
    filter_upwards [hLv', ae_all_iff.2 fun i => (aΛv i).prod_right_ae,
      ae_all_iff.2 fun i => (aΛ i).prod_right_ae, ae_all_iff.2 fun i => (aLv i).prod_right_ae]
      with s h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  refine ae_eq_condExp_of_forall_setIntegral_eq ((filt M).le t) hJ
    (fun A _ _ => hLi.integrableOn) ?_ hLsm.aestronglyMeasurable
  intro A hA _
  have hA' : MeasurableSet A := (filt M).le t A hA
  have hres : (volume.restrict S).prod (M.P.restrict A) = μS.restrict (Set.univ ×ˢ A) := by
    rw [hμS, ← Measure.prod_restrict, Measure.restrict_univ]
  have key : ∀ (G : ℝ × Ω → ℝ), Integrable G μS →
      ∫ ω in A, (∫ s in S, G (s, ω)) ∂M.P = ∫ s in S, (∫ ω in A, G (s, ω) ∂M.P) := by
    intro G hG
    have hG' : Integrable G ((volume.restrict S).prod (M.P.restrict A)) := by
      rw [hres]; exact hG.restrict
    rw [← integral_prod_symm _ hG', integral_prod _ hG']
  rw [key (fun q => Lhat q.1 q.2 ⬝ᵥ v q.2) GLh, key (fun q => Λ q.1.toNNReal q.2 ⬝ᵥ v q.2) GΛ]
  refine integral_congr_ae ?_
  filter_upwards [hs_good] with s ⟨h1, h2, h3, h4⟩
  simp only [dotProduct]
  rw [integral_finsetSum _ fun i _ => (h4 i).integrableOn,
    integral_finsetSum _ fun i _ => (h2 i).integrableOn]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : ∫ ω in A, Lhat s ω i * v ω i ∂M.P =
      ∫ ω in A, condExp (filt M t) M.P (fun ω => Λ s.toNNReal ω i) ω * v ω i ∂M.P := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [h1 i] with ω hω
    rw [hω]
  have hvi : StronglyMeasurable[filt M t] (fun ω => v ω i) :=
    (continuous_apply i).comp_stronglyMeasurable hv
  have e2 := condExp_mul_of_stronglyMeasurable_right (m := filt M t) (μ := M.P) hvi (h2 i) (h3 i)
  rw [e1]
  calc ∫ ω in A, condExp (filt M t) M.P (fun ω => Λ s.toNNReal ω i) ω * v ω i ∂M.P
      = ∫ ω in A, condExp (filt M t) M.P
          ((fun ω => Λ s.toNNReal ω i) * fun ω => v ω i) ω ∂M.P := by
        refine integral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [e2] with ω hω
        rw [hω]; rfl
    _ = ∫ ω in A, ((fun ω => Λ s.toNNReal ω i) * fun ω => v ω i) ω ∂M.P :=
        setIntegral_condExp ((filt M).le t) (h2 i) hA
    _ = _ := rfl

end CondFub

lemma quad_split {k : ℕ} (R : Matrix (Fin l) (Fin l) ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (D : Fin d → Matrix (Fin k) (Fin l) ℝ) (x : Fin l → ℝ) :
    ((R + ∑ j, (D j)ᵀ * P * D j) *ᵥ x) ⬝ᵥ x =
      (R *ᵥ x) ⬝ᵥ x + ∑ j, (P *ᵥ (D j *ᵥ x)) ⬝ᵥ (D j *ᵥ x) := by
  rw [Matrix.add_mulVec, add_dotProduct, Matrix.sum_mulVec, sum_dotProduct]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, dotProduct_comm]

lemma psd_quad {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosSemidef) (x : Fin k → ℝ) :
    0 ≤ (A *ᵥ x) ⬝ᵥ x := by
  have := hA.dotProduct_mulVec_nonneg x
  simpa [dotProduct_comm] using this

section KeySec
variable (M : Data Ω n l d) (hM : Standing M) (t : ℝ≥0)

include hM in
lemma H_quad_nonneg (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hPP : IsStronglyProgressive (filt M)
      (fun s ω => if t ≤ s then Peng1990.SMP.matEntries (Pm s ω) else 0))
    (hpsd : ∀ s : ℝ≥0, t ≤ s → s ≤ M.T → ∀ᵐ ω ∂M.P, (Pm s ω).PosSemidef)
    (v : Ω → Fin l → ℝ) (hv : StronglyMeasurable[filt M t] v)
    {S : Set ℝ} (hS : MeasurableSet S) (hSt : S ⊆ Set.Icc (t : ℝ) M.T) :
    ∀ᵐ ω ∂M.P, ∀ᵐ s ∂(volume.restrict S), 0 ≤ (Hmat M Pm s.toNNReal ω *ᵥ v ω) ⬝ᵥ v ω := by
  have := hM.prob
  have hS0 : S ⊆ Set.Icc 0 (M.T : ℝ) := fun s hs => ⟨le_trans t.2 (hSt hs).1, (hSt hs).2⟩
  -- R part
  have hR : ∀ᵐ ω ∂M.P, ∀ᵐ s ∂(volume.restrict S), (M.R s.toNNReal ω).PosSemidef := by
    have h := hM.R_psd
    rw [prod_restrict_univ] at h
    have h' : ∀ᵐ q ∂((volume.restrict S).prod M.P), (M.R q.1.toNNReal q.2).PosSemidef := by
      rw [prod_restrict_univ]
      exact ae_restrict_of_ae_restrict_of_subset (Set.prod_mono hS0 le_rfl) h
    exact ae_ae_of_prod M.P h'
  -- P part, via a measurable clamped expression
  have hv' : StronglyMeasurable v := hv.mono ((filt M).le t)
  set e : ℝ × Ω → ℝ := fun q => ∑ j, (Peng1990.SMP.entriesMat
      ((fun s ω => if t ≤ s then Peng1990.SMP.matEntries (Pm s ω) else 0)
        (min q.1.toNNReal M.T) q.2) *ᵥ (M.D j (min q.1.toNNReal M.T) q.2 *ᵥ v q.2)) ⬝ᵥ
        (M.D j (min q.1.toNNReal M.T) q.2 *ᵥ v q.2) with he
  have em : StronglyMeasurable e := by
    refine Finset.stronglyMeasurable_fun_sum _ fun j _ => ?_
    have h1 := prog_clamp hPP M.T
    have h2 := prog_clamp (hM.D_prog j) M.T
    have h3 : StronglyMeasurable (fun q : ℝ × Ω => v q.2) := hv'.comp_measurable measurable_snd
    have hc : Continuous (fun z : (Fin n × Fin n → ℝ) × Matrix (Fin n) (Fin l) ℝ × (Fin l → ℝ) =>
        (Peng1990.SMP.entriesMat z.1 *ᵥ (z.2.1 *ᵥ z.2.2)) ⬝ᵥ (z.2.1 *ᵥ z.2.2)) := by
      have hDx : Continuous (fun z : (Fin n × Fin n → ℝ) × Matrix (Fin n) (Fin l) ℝ ×
          (Fin l → ℝ) => z.2.1 *ᵥ z.2.2) :=
        Continuous.matrix_mulVec continuous_snd.fst continuous_snd.snd
      exact ((continuous_entriesMat.comp continuous_fst).matrix_mulVec hDx).dotProduct hDx
    have key := hc.comp_stronglyMeasurable (h1.prodMk (h2.prodMk h3))
    exact key
  have hE : MeasurableSet {q : ℝ × Ω | 0 ≤ e q} := measurableSet_le measurable_const em.measurable
  have hP : ∀ᵐ ω ∂M.P, ∀ᵐ s ∂(volume.restrict S), (s, ω) ∈ {q : ℝ × Ω | 0 ≤ e q} := by
    refine ae_ae_of_forall M.P hS hE fun s hs => ?_
    obtain ⟨h1, h2⟩ := toNNReal_facts (hSt hs)
    have h3 : s.toNNReal ≤ M.T := by rw [← h1]; exact min_le_right _ _
    filter_upwards [hpsd s.toNNReal h2 h3] with ω hω
    simp only [he, h1, h2, if_true, entries_matEntries]
    exact Finset.sum_nonneg fun j _ => psd_quad hω _
  filter_upwards [hR, hP] with ω h1 h2
  filter_upwards [h1, h2, ae_restrict_mem hS] with s hs1 hs2 hs3
  obtain ⟨f1, f2⟩ := toNNReal_facts (hSt hs3)
  simp only [he, f1, f2, if_true, entries_matEntries] at hs2
  unfold Hmat
  rw [quad_split]
  exact add_nonneg (psd_quad hs1 _) hs2

include hM in
lemma key_lower (u : ℝ≥0 → Ω → Fin l → ℝ) (hu : Admissible M u) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (k : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (hp : FirstAdjoint M X t p k)
    (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) (K : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hP : SecondAdjoint M t Pm K)
    (hpsd : ∀ s : ℝ≥0, t ≤ s → s ≤ M.T → ∀ᵐ ω ∂M.P, (Pm s ω).PosSemidef)
    (Lhat : ℝ → Ω → Fin l → ℝ)
    (hLm : Measurable[MeasurableSpace.comap Prod.fst (borel ℝ) ⊔
          MeasurableSpace.comap Prod.snd (filt M t)] (fun q : ℝ × Ω => Lhat q.1 q.2))
    (hLv : ∀ᵐ s ∂(volume.restrict (Set.Ioc (t : ℝ) M.T)), ∀ i,
          (fun ω => Lhat s ω i) =ᵐ[M.P] condExp (filt M t) M.P (fun ω => Lam M u p k s.toNNReal ω i))
    (v : Ω → Fin l → ℝ) (hv : StronglyMeasurable[filt M t] v)
    (hv2 : ∫⁻ ω, ‖v ω‖ₑ ^ 2 ∂M.P < ⊤) (ε : ℝ) (hε : 0 < ε) (hεT : (t : ℝ) + ε ≤ M.T) :
    ∀ᵐ ω ∂M.P, min 0 (∫ s in Set.Ioc (t : ℝ) ((t : ℝ) + ε), Lhat s ω ⬝ᵥ v ω) ≤
      condExp (filt M t) M.P (fun ω' => ∫ s in Set.Icc (t : ℝ) ((t : ℝ) + ε),
            (Lam M u p k s.toNNReal ω' ⬝ᵥ v ω'
              + (1 / 2 : ℝ) * ((Hmat M Pm s.toNNReal ω' *ᵥ v ω') ⬝ᵥ v ω'))) ω := by
  have := hM.prob
  set S := Set.Ioc (t : ℝ) ((t : ℝ) + ε) with hSdef
  have hSm : MeasurableSet S := measurableSet_Ioc
  have hSt : S ⊆ Set.Ioc (t : ℝ) M.T := Set.Ioc_subset_Ioc le_rfl hεT
  have hSt' : S ⊆ Set.Icc (t : ℝ) M.T := hSt.trans Set.Ioc_subset_Icc_self
  have hΛ := lam_memLp M hM u t p k hu hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hSm hSt'
  obtain ⟨hJ, hCE⟩ := cond_fubini M hM t (Lam M u p k) hSm hSt hΛ Lhat hLm hLv v hv hv2
  simp_rw [integral_Icc_eq_integral_Ioc]
  by_cases hI : Integrable (fun ω' => ∫ s in S, (Lam M u p k s.toNNReal ω' ⬝ᵥ v ω'
      + (1 / 2 : ℝ) * ((Hmat M Pm s.toNNReal ω' *ᵥ v ω') ⬝ᵥ v ω'))) M.P
  swap
  · rw [condExp_of_not_integrable hI]
    exact Eventually.of_forall fun ω => min_le_left _ _
  have hf_int : ∀ᵐ ω ∂M.P, Integrable (fun s : ℝ => Lam M u p k s.toNNReal ω ⬝ᵥ v ω)
      (volume.restrict S) :=
    (integrable_dot hΛ (v_memLp M hM t v hv hv2 (S := S))).prod_left_ae
  have hg_int := H_section_integrable M hM t Pm hP.2.2.1 hP.2.2.2.2.1 v hv hSm hSt'
  have hg_nn := H_quad_nonneg M hM t Pm hP.2.2.1 hpsd v hv hSm hSt'
  have hJI : (fun ω => ∫ s in S, Lam M u p k s.toNNReal ω ⬝ᵥ v ω) ≤ᵐ[M.P]
      (fun ω' => ∫ s in S, (Lam M u p k s.toNNReal ω' ⬝ᵥ v ω'
        + (1 / 2 : ℝ) * ((Hmat M Pm s.toNNReal ω' *ᵥ v ω') ⬝ᵥ v ω'))) := by
    filter_upwards [hf_int, hg_int, hg_nn] with ω h1 h2 h3
    rw [integral_add h1 (h2.const_mul (1 / 2))]
    have : 0 ≤ ∫ s in S, (1 / 2 : ℝ) * ((Hmat M Pm s.toNNReal ω *ᵥ v ω) ⬝ᵥ v ω) :=
      integral_nonneg_of_ae (h3.mono fun s hs => by positivity)
    linarith
  have hmono := condExp_mono (m := filt M t) hJ hI hJI
  filter_upwards [hmono, hCE] with ω h1 h2
  rw [← h2] at h1
  exact (min_le_right _ _).trans h1

end KeySec

lemma avg_tendsto (t : ℝ) (L : ℝ → Fin l → ℝ) (hL : Tendsto L (𝓝[>] t) (𝓝 0)) (x : Fin l → ℝ)
    (εs : ℕ → ℝ) (hε : ∀ m, 0 < εs m) (hε0 : Tendsto εs atTop (𝓝 0)) :
    Tendsto (fun m => (∫ s in Set.Ioc t (t + εs m), L s ⬝ᵥ x) / εs m) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  set c : ℝ := l * ‖x‖ + 1 with hc
  have hc0 : 0 < c := by positivity
  have hδ : 0 < η / (2 * c) := by positivity
  have h1 := (Metric.tendsto_nhds.1 hL) (η / (2 * c)) hδ
  obtain ⟨w, hw, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
  have hw' : 0 < w - t := sub_pos.2 hw
  filter_upwards [(Metric.tendsto_nhds.1 hε0) (w - t) hw'] with m hm
  have hεm := hε m
  have hlt : εs m < w - t := by
    have := hm; rw [Real.dist_eq, sub_zero, abs_of_pos hεm] at this; exact this
  have hbound : ∀ s ∈ Set.Ioc t (t + εs m), ‖L s ⬝ᵥ x‖ ≤ l * (η / (2 * c)) * ‖x‖ := by
    intro s hs
    have hs' : s ∈ Set.Ioo t w := ⟨hs.1, by linarith [hs.2]⟩
    have hd := hsub hs'
    simp only [Set.mem_setOf_eq, dist_zero_right] at hd
    rw [Real.norm_eq_abs]
    refine (abs_dotProduct_le _ _).trans ?_
    gcongr
  have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) (by simp) hbound
  rw [Real.volume_real_Ioc_of_le (by linarith)] at hI
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hεm, div_lt_iff₀ hεm]
  rw [Real.norm_eq_abs] at hI
  have : (l : ℝ) * (η / (2 * c)) * ‖x‖ < η := by
    have e : (l : ℝ) * (η / (2 * c)) * ‖x‖ = η * (l * ‖x‖) / (2 * c) := by ring
    rw [e, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg x]
  calc |∫ s in Set.Ioc t (t + εs m), L s ⬝ᵥ x| ≤ l * (η / (2 * c)) * ‖x‖ * (t + εs m - t) := hI
    _ = l * (η / (2 * c)) * ‖x‖ * εs m := by ring
    _ < η * εs m := by gcongr

section Transfer
variable (M : Data Ω n l d) (hM : Standing M)

include hM in
lemma firstAdjoint_transfer (X X' : ℝ≥0 → Ω → Fin n → ℝ)
    (hXp : IsStronglyProgressive (filt M) X) (hX'p : IsStronglyProgressive (filt M) X')
    (hXX : ∀ s : ℝ≥0, s ≤ M.T → X s =ᵐ[M.P] X' s) (t : ℝ≥0) (ht : t < M.T)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (k : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (hp : FirstAdjoint M X t p k) : FirstAdjoint M X' t p k := by
  have := hM.prob
  obtain ⟨h1, h2, h3, h4, J, hJ, hr⟩ := hp
  refine ⟨h1, h2, h3, h4, J, hJ, fun r htr hrT => ?_⟩
  -- a.e. path equality on [0, T]
  have hE : MeasurableSet {q : ℝ × Ω | X (min q.1.toNNReal M.T) q.2 = X' (min q.1.toNNReal M.T) q.2} :=
    (prog_clamp hXp M.T).measurableSet_eq_fun (prog_clamp hX'p M.T)
  have hpath : ∀ᵐ ω ∂M.P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) M.T)),
      (s, ω) ∈ {q : ℝ × Ω | X (min q.1.toNNReal M.T) q.2 = X' (min q.1.toNNReal M.T) q.2} := by
    refine ae_ae_of_forall M.P measurableSet_Icc hE fun s hs => ?_
    have hsT : s.toNNReal ≤ M.T := Real.toNNReal_le_iff_le_coe.2 hs.2
    filter_upwards [hXX s.toNNReal hsT] with ω hω
    simp only [Set.mem_setOf_eq, min_eq_left hsT, hω]
  have hT := hXX M.T le_rfl
  have ht' := hXX t ht.le
  have hcond : ∀ i, (fun ω => condExp (filt M t) M.P (fun ω' => X M.T ω' i) ω) =ᵐ[M.P]
      (fun ω => condExp (filt M t) M.P (fun ω' => X' M.T ω' i) ω) := fun i =>
    condExp_congr_ae (hT.mono fun ω h => by simp only [h])
  filter_upwards [hr r htr hrT, hpath, hT, ht', ae_all_iff.2 hcond] with ω ⟨hint, heq⟩ hpω hTω htω hcω
  have hsub : Set.Icc (r : ℝ) M.T ⊆ Set.Icc (0 : ℝ) M.T := fun s hs => ⟨le_trans r.2 hs.1, hs.2⟩
  have hfeq : (fun s : ℝ => (M.A s.toNNReal)ᵀ *ᵥ p s.toNNReal ω +
        ∑ j, (M.C j s.toNNReal ω)ᵀ *ᵥ k j s.toNNReal ω + M.Q s.toNNReal ω *ᵥ X s.toNNReal ω)
      =ᵐ[volume.restrict (Set.Icc (r : ℝ) M.T)]
      (fun s : ℝ => (M.A s.toNNReal)ᵀ *ᵥ p s.toNNReal ω +
        ∑ j, (M.C j s.toNNReal ω)ᵀ *ᵥ k j s.toNNReal ω + M.Q s.toNNReal ω *ᵥ X' s.toNNReal ω) := by
    have := ae_restrict_of_ae_restrict_of_subset hsub hpω
    filter_upwards [this, ae_restrict_mem measurableSet_Icc] with s hs hs2
    have hsT : s.toNNReal ≤ M.T := Real.toNNReal_le_iff_le_coe.2 hs2.2
    simp only [Set.mem_setOf_eq, min_eq_left hsT] at hs
    rw [hs]
  refine ⟨hint.congr_fun_ae hfeq, fun i => ?_⟩
  rw [heq i, integral_congr_ae hfeq]
  have hcv : condVec M t (X M.T) ω = condVec M t (X' M.T) ω := funext fun i => hcω i
  simp only [hcv, hTω, htω]

end Transfer

end TILQSuffRed

open TILQSuffRed in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n l d : ℕ} (M : Data Ω n l d)
    (hM : Standing M) (u : ℝ≥0 → Ω → Fin l → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (p : ℝ≥0 → ℝ≥0 → Ω → Fin n → ℝ) (k : ℝ≥0 → Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (hu : Admissible M u) (hX : IsState M u X)
    (hp : ∀ t : ℝ≥0, t < M.T → FirstAdjoint M X t (p t) (k t))
    (h34 : Cond34 M (fun t => Lam M u (p t) (k t))) :
    IsEquilibrium M u := by
  have := hM.prob
  refine ⟨hu, ⟨X, hX⟩, ?_⟩
  intro X' hX' t ht v hv hv2 εs hεpos hε0 Xε hXε
  have hXX := state_unique M hM u hu X X' hX hX'
  have hp' := firstAdjoint_transfer M hM X X' hX.1 hX'.1 hXX t ht (p t) (k t) (hp t ht)
  obtain ⟨Pm, K, hPK⟩ := second_adjoint_exists M hM t ht
  have hpsd := second_adjoint_psd M hM t ht Pm K hPK
  have h31 := proposition_3_1 M hM u X' hu hX' t ht (p t) (k t) hp' Pm K hPK v hv hv2 εs hεpos
    hε0 Xε hXε
  obtain ⟨-, Lhat, hLm, hLv, hLt⟩ := h34 t ht
  have hev : ∀ᶠ m in atTop, (t : ℝ) + εs m ≤ M.T := by
    have hTt : (0 : ℝ) < M.T - t := sub_pos.2 (by exact_mod_cast ht)
    filter_upwards [hε0.eventually (gt_mem_nhds hTt)] with m hm
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hKL : ∀ᵐ ω ∂M.P, ∀ m, N ≤ m →
      min 0 (∫ s in Set.Ioc (t : ℝ) ((t : ℝ) + εs m), Lhat s ω ⬝ᵥ v ω) ≤
      condExp (filt M t) M.P (fun ω' => ∫ s in Set.Icc (t : ℝ) ((t : ℝ) + εs m),
            (Lam M u (p t) (k t) s.toNNReal ω' ⬝ᵥ v ω'
              + (1 / 2 : ℝ) * ((Hmat M Pm s.toNNReal ω' *ᵥ v ω') ⬝ᵥ v ω'))) ω := by
    rw [ae_all_iff]
    intro m
    by_cases hm : N ≤ m
    · filter_upwards [key_lower M hM t u hu X' (p t) (k t) hp' Pm K hPK hpsd Lhat hLm hLv v hv hv2
        (εs m) (hεpos m) (hN m hm)] with ω h _
      exact h
    · exact Eventually.of_forall fun ω h => absurd h hm
  filter_upwards [h31, hKL, hLt] with ω h1 h2 h3
  have hA := avg_tendsto (t : ℝ) (fun s => Lhat s ω) h3 (v ω) εs hεpos hε0
  set Δ : ℕ → ℝ := fun m =>
    cost M t (X' t) (spike u t (εs m) v) (Xε m) ω - cost M t (X' t) u X' ω with hΔ
  set c : ℕ → ℝ := fun m => condExp (filt M t) M.P (fun ω' => ∫ s in Set.Icc (t : ℝ) ((t : ℝ) + εs m),
            (Lam M u (p t) (k t) s.toNNReal ω' ⬝ᵥ v ω'
              + (1 / 2 : ℝ) * ((Hmat M Pm s.toNNReal ω' *ᵥ v ω') ⬝ᵥ v ω'))) ω with hc
  set L : ℕ → ℝ := fun m => ∫ s in Set.Ioc (t : ℝ) ((t : ℝ) + εs m), Lhat s ω ⬝ᵥ v ω with hL
  have ha : Tendsto (fun m => (Δ m - c m) / εs m + min 0 (L m / εs m)) atTop (𝓝 0) := by
    have hmin : Tendsto (fun m => min 0 (L m / εs m)) atTop (𝓝 (min 0 0)) :=
      tendsto_const_nhds.min hA
    have h := h1.add hmin
    rw [min_self, add_zero] at h
    exact h
  have hle : ∀ᶠ m in atTop, (Δ m - c m) / εs m + min 0 (L m / εs m) ≤ Δ m / εs m := by
    filter_upwards [eventually_ge_atTop N] with m hm
    have hε := hεpos m
    have e1 : min 0 (L m / εs m) = min 0 (L m) / εs m := by
      rw [← min_div_div_right hε.le, zero_div]
    have e2 : min 0 (L m) / εs m ≤ c m / εs m := div_le_div_of_nonneg_right (h2 m hm) hε.le
    rw [e1]
    have e3 : (Δ m - c m) / εs m + c m / εs m = Δ m / εs m := by
      field_simp; ring
    linarith
  have hlim : Tendsto (fun m => (((Δ m - c m) / εs m + min 0 (L m / εs m) : ℝ) : EReal)) atTop
      (𝓝 ((0 : ℝ) : EReal)) := (continuous_coe_real_ereal.tendsto 0).comp ha
  calc (0 : EReal) = ((0 : ℝ) : EReal) := rfl
    _ = liminf (fun m => (((Δ m - c m) / εs m + min 0 (L m / εs m) : ℝ) : EReal)) atTop :=
        hlim.liminf_eq.symm
    _ ≤ liminf (fun m => ((Δ m / εs m : ℝ) : EReal)) atTop :=
        liminf_le_liminf (hle.mono fun m h => EReal.coe_le_coe_iff.2 h)
