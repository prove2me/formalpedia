-- Prove2me | solution 1 for SinkhornDRO.BSMD.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:53:06.428471+00:00
-- url     : https://prove2.me/submissions/cdf68f25-a850-4384-846a-f3edf40cd872
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_MirrorSetup
import Definitions.Def_SinkhornDRO_BSMD_Objective
import Definitions.Def_SinkhornDRO_BSMD_Estimators
import Theorems.Thm_SinkhornDRO_BSMD_unbiased_estimators
import Theorems.Thm_SinkhornDRO_BSMD_lemma_EC_6_I
import Theorems.Thm_SinkhornDRO_BSMD_lemma_EC_6_III_a
import Theorems.Thm_SinkhornDRO_BSMD_lemma_EC_7
import Theorems.Thm_SinkhornDRO_BSMD_rtmlmc_second_moment

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Aux_BSMDT2
open SinkhornDRO.BSMD

lemma N_zero {d : ℕ} (𝒩 : MirrorNorm d) : 𝒩.N 0 = 0 := by
  have := 𝒩.smul_eq 0 0
  simpa using this

lemma inner_le_of_N {d : ℕ} (𝒩 : MirrorNorm d) (y x : Param d) (hx : 𝒩.N x ≤ 1) :
    ⟪y, x⟫ ≤ ‖y‖ / 𝒩.c := by
  have h1 := 𝒩.lower x
  have hc := 𝒩.c_pos
  have hx' : ‖x‖ ≤ 1 / 𝒩.c := by rw [le_div_iff₀ hc]; linarith
  calc ⟪y, x⟫ ≤ ‖y‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ ‖y‖ * (1 / 𝒩.c) := by gcongr
    _ = ‖y‖ / 𝒩.c := by ring

lemma dual_bdd {d : ℕ} (𝒩 : MirrorNorm d) (y : Param d) :
    BddAbove (Set.range fun x : {x : Param d // 𝒩.N x ≤ 1} => ⟪y, (x : Param d)⟫) := by
  refine ⟨‖y‖ / 𝒩.c, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact inner_le_of_N 𝒩 y x x.2

instance unitBall_nonempty {d : ℕ} (𝒩 : MirrorNorm d) : Nonempty {x : Param d // 𝒩.N x ≤ 1} :=
  ⟨⟨0, by rw [N_zero]; norm_num⟩⟩

lemma dual_le {d : ℕ} (𝒩 : MirrorNorm d) (y : Param d) : dualNorm 𝒩 y ≤ ‖y‖ / 𝒩.c :=
  ciSup_le fun x => inner_le_of_N 𝒩 y x x.2

lemma dual_nonneg {d : ℕ} (𝒩 : MirrorNorm d) (y : Param d) : 0 ≤ dualNorm 𝒩 y := by
  have := le_ciSup (dual_bdd 𝒩 y) ⟨0, by rw [N_zero]; norm_num⟩
  rw [show (0:ℝ) = ⟪y, (0:Param d)⟫ by simp]
  exact this

lemma dual_sq_le {d : ℕ} (𝒩 : MirrorNorm d) (y : Param d) :
    dualNorm 𝒩 y ^ 2 ≤ (𝒩.c ^ 2)⁻¹ * ‖y‖ ^ 2 := by
  have h1 := dual_le 𝒩 y
  have h0 := dual_nonneg 𝒩 y
  have hc := 𝒩.c_pos
  calc dualNorm 𝒩 y ^ 2 ≤ (‖y‖ / 𝒩.c) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (𝒩.c ^ 2)⁻¹ * ‖y‖ ^ 2 := by field_simp

lemma dual_lip {d : ℕ} (𝒩 : MirrorNorm d) : Continuous (dualNorm 𝒩) := by
  refine (LipschitzWith.of_le_add_mul' (1 / 𝒩.c) (fun y1 y2 => ?_)).continuous
  refine ciSup_le fun x => ?_
  have h1 : ⟪y2, (x : Param d)⟫ ≤ dualNorm 𝒩 y2 := le_ciSup (dual_bdd 𝒩 y2) x
  have h2 := inner_le_of_N 𝒩 (y1 - y2) x x.2
  rw [inner_sub_left] at h2
  rw [dist_eq_norm]
  have : ‖y1 - y2‖ / 𝒩.c = 1 / 𝒩.c * ‖y1 - y2‖ := by ring
  linarith

lemma f_cont {d : ℕ} {Z : Type*} (f : Param d → Z → ℝ) (Lf : ℝ) (hA2II : Asm2Lipschitz f Lf)
    (z : Z) : Continuous fun θ => f θ z := by
  refine (LipschitzWith.of_le_add_mul' Lf (fun θ1 θ2 => ?_)).continuous
  have := hA2II z θ1 θ2
  rw [dist_eq_norm]
  linarith [le_abs_self (f θ1 z - f θ2 z)]

lemma f_meas {d : ℕ} {Z : Type*} [MeasurableSpace Z] (f : Param d → Z → ℝ)
    (hf_meas : ∀ θ, Measurable (f θ)) (Lf : ℝ) (hA2II : Asm2Lipschitz f Lf) :
    Measurable (Function.uncurry f) :=
  measurable_uncurry_of_continuous_of_measurable (f_cont f Lf hA2II) hf_meas

lemma blockGrad_meas {d : ℕ} {Z : Type*} [MeasurableSpace Z] (lam eps : ℝ)
    (f : Param d → Z → ℝ) (sg : Param d → Z → Param d)
    (hf : Measurable (Function.uncurry f)) (hsg : Measurable (Function.uncurry sg))
    {n : ℕ} (S : Finset (Fin n)) :
    Measurable (fun p : Param d × (Fin n → Z) => blockGrad lam eps f sg p.1 p.2 S) := by
  unfold blockGrad
  have hj : ∀ j : Fin n, Measurable (fun p : Param d × (Fin n → Z) => (p.1, p.2 j)) :=
    fun j => measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)
  have hE : ∀ j : Fin n, Measurable
      (fun p : Param d × (Fin n → Z) => Real.exp (f p.1 (p.2 j) / (lam * eps))) :=
    fun j => Real.measurable_exp.comp ((hf.comp (hj j)).div_const _)
  have hS : Measurable (fun p : Param d × (Fin n → Z) =>
      ∑ k ∈ S, Real.exp (f p.1 (p.2 k) / (lam * eps))) :=
    Finset.measurable_sum _ (fun k _ => hE k)
  exact Finset.measurable_sum _ (fun j _ => ((hE j).div hS).smul (hsg.comp (hj j)))

lemma levelG_meas {d : ℕ} {Z : Type*} [MeasurableSpace Z] (lam eps : ℝ)
    (f : Param d → Z → ℝ) (sg : Param d → Z → Param d)
    (hf : Measurable (Function.uncurry f)) (hsg : Measurable (Function.uncurry sg)) (ℓ : ℕ) :
    Measurable (fun p : Param d × (Fin (2 ^ ℓ) → Z) => levelG lam eps f sg ℓ p.1 p.2) := by
  cases ℓ with
  | zero => exact blockGrad_meas lam eps f sg hf hsg _
  | succ ℓ =>
    have e : (fun p : Param d × (Fin (2 ^ (ℓ + 1)) → Z) => levelG lam eps f sg (ℓ + 1) p.1 p.2)
        = fun p => blockGrad lam eps f sg p.1 p.2 Finset.univ
            - (1 / 2 : ℝ) • blockGrad lam eps f sg p.1 p.2 (lowHalf ℓ)
            - (1 / 2 : ℝ) • blockGrad lam eps f sg p.1 p.2 (highHalf ℓ) := rfl
    rw [e]
    exact (((blockGrad_meas lam eps f sg hf hsg _).sub
      ((blockGrad_meas lam eps f sg hf hsg _).const_smul (1 / 2 : ℝ))).sub
      ((blockGrad_meas lam eps f sg hf hsg _).const_smul (1 / 2 : ℝ)))

lemma vSG_meas {d : ℕ} {Z : Type*} [MeasurableSpace Z] (lam eps : ℝ)
    (f : Param d → Z → ℝ) (sg : Param d → Z → Param d)
    (hf : Measurable (Function.uncurry f)) (hsg : Measurable (Function.uncurry sg)) (L : ℕ) :
    Measurable (Function.uncurry (vSG lam eps f sg L)) :=
  (blockGrad_meas lam eps f sg hf hsg Finset.univ).comp
    (measurable_fst.prodMk measurable_snd.snd)

lemma vRT_meas {d : ℕ} {Z : Type*} [MeasurableSpace Z] (lam eps : ℝ)
    (f : Param d → Z → ℝ) (sg : Param d → Z → Param d)
    (hf : Measurable (Function.uncurry f)) (hsg : Measurable (Function.uncurry sg)) (L : ℕ) :
    Measurable (Function.uncurry (vRT lam eps f sg L)) := by
  let g : (Param d × (Fin (2 ^ L) → Z)) × Fin (L + 1) → Param d :=
    fun q => (levelProb L q.2)⁻¹ • levelG lam eps f sg q.2 q.1.1 (truncSamples q.2 q.1.2)
  have hg : Measurable g := by
    refine measurable_from_prod_countable_left (fun ℓ => ?_)
    have ht : Measurable (fun zs : Fin (2 ^ L) → Z => truncSamples (Z := Z) ℓ zs) :=
      measurable_pi_lambda _ (fun j => measurable_pi_apply _)
    show Measurable fun x : Param d × (Fin (2 ^ L) → Z) =>
      (levelProb L ℓ)⁻¹ • levelG lam eps f sg ℓ x.1 (truncSamples ℓ x.2)
    have h2 : Measurable fun x : Param d × (Fin (2 ^ L) → Z) =>
        levelG lam eps f sg ℓ x.1 (truncSamples ℓ x.2) :=
      (levelG_meas lam eps f sg hf hsg ℓ).comp (measurable_fst.prodMk (ht.comp measurable_snd))
    exact h2.const_smul (levelProb L ℓ)⁻¹
  have he : Measurable (fun p : Param d × (Fin (L + 1) × Z × (Fin (2 ^ L) → Z)) =>
      ((p.1, p.2.2.2), p.2.1)) :=
    (measurable_fst.prodMk measurable_snd.snd.snd).prodMk measurable_snd.fst
  exact hg.comp he

lemma objF_le {d : ℕ} {Z : Type*} [MeasurableSpace Z] (Θ : Set (Param d))
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf B : ℝ) (hA2II : Asm2Lipschitz f Lf) (hA2III : Asm2Bounded Θ f B)
    (θ0 : Param d) (hθ0 : θ0 ∈ Θ) (θ1 θ2 : Param d) :
    objF P Q lam eps f θ1 ≤ objF P Q lam eps f θ2 + |Lf| * dist θ1 θ2 := by
  have ha : 0 < lam * eps := mul_pos hlam heps
  have hb : ∀ θ z, -(|Lf| * ‖θ - θ0‖) ≤ f θ z ∧ f θ z ≤ B + |Lf| * ‖θ - θ0‖ := by
    intro θ z
    have h1 := hA2II z θ θ0
    have h2 := hA2III θ0 hθ0 z
    have h3 : Lf * ‖θ - θ0‖ ≤ |Lf| * ‖θ - θ0‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self Lf) (norm_nonneg _)
    have h4 := abs_le.mp (h1.trans h3)
    constructor <;> linarith [h4.1, h4.2, h2.1, h2.2]
  have hlip : ∀ z, f θ1 z ≤ f θ2 z + |Lf| * dist θ1 θ2 := by
    intro z
    have h1 := hA2II z θ1 θ2
    have h3 : Lf * ‖θ1 - θ2‖ ≤ |Lf| * ‖θ1 - θ2‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self Lf) (norm_nonneg _)
    rw [dist_eq_norm]
    linarith [le_abs_self (f θ1 z - f θ2 z)]
  have hEm : ∀ θ, Measurable (fun z => Real.exp (f θ z / (lam * eps))) :=
    fun θ => Real.measurable_exp.comp ((hf_meas θ).div_const _)
  have hInt : ∀ θ x, Integrable (fun z => Real.exp (f θ z / (lam * eps))) (Q x) := by
    intro θ x
    refine Integrable.of_bound (hEm θ).aestronglyMeasurable
      (Real.exp ((B + |Lf| * ‖θ - θ0‖) / (lam * eps))) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hb θ z).2 ha.le)
  have hlow : ∀ θ x, Real.exp (-(|Lf| * ‖θ - θ0‖) / (lam * eps))
      ≤ ∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x) := by
    intro θ x
    have := integral_mono (integrable_const (Real.exp (-(|Lf| * ‖θ - θ0‖) / (lam * eps))))
      (hInt θ x) (fun z => Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hb θ z).1 ha.le))
    simpa using this
  have hup : ∀ θ x, ∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x)
      ≤ Real.exp ((B + |Lf| * ‖θ - θ0‖) / (lam * eps)) := by
    intro θ x
    have := integral_mono (hInt θ x)
      (integrable_const (Real.exp ((B + |Lf| * ‖θ - θ0‖) / (lam * eps))))
      (fun z => Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hb θ z).2 ha.le))
    simpa using this
  have hIm : ∀ θ, Measurable (fun x => ∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x)) := by
    intro θ
    have : StronglyMeasurable (fun p : Z × Z => Real.exp (f θ p.2 / (lam * eps))) :=
      ((hEm θ).comp measurable_snd).stronglyMeasurable
    exact (this.integral_kernel_prod_right' (κ := Q)).measurable
  have hgInt : ∀ θ, Integrable
      (fun x => lam * eps * Real.log (∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x))) P := by
    intro θ
    refine Integrable.of_bound (((hIm θ).log).const_mul _).aestronglyMeasurable
      (lam * eps * (|Lf| * ‖θ - θ0‖ / (lam * eps) + |(B + |Lf| * ‖θ - θ0‖) / (lam * eps)|))
      (Filter.Eventually.of_forall fun x => ?_)
    have hl := hlow θ x
    have hu := hup θ x
    have hpos : 0 < ∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x) :=
      lt_of_lt_of_le (Real.exp_pos _) hl
    have l1 := Real.log_le_log (Real.exp_pos _) hl
    have l2 := Real.log_le_log hpos hu
    rw [Real.log_exp] at l1 l2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos ha]
    gcongr
    rw [abs_le]
    have e1 : -(|Lf| * ‖θ - θ0‖) / (lam * eps) = -(|Lf| * ‖θ - θ0‖ / (lam * eps)) := by ring
    have hn1 : 0 ≤ |Lf| * ‖θ - θ0‖ / (lam * eps) := by positivity
    have hn2 := le_abs_self ((B + |Lf| * ‖θ - θ0‖) / (lam * eps))
    have hn3 := abs_nonneg ((B + |Lf| * ‖θ - θ0‖) / (lam * eps))
    constructor <;> linarith
  unfold objF
  have hpt : ∀ x, lam * eps * Real.log (∫ z, Real.exp (f θ1 z / (lam * eps)) ∂(Q x))
      ≤ lam * eps * Real.log (∫ z, Real.exp (f θ2 z / (lam * eps)) ∂(Q x))
        + |Lf| * dist θ1 θ2 := by
    intro x
    have hpos2 : 0 < ∫ z, Real.exp (f θ2 z / (lam * eps)) ∂(Q x) :=
      lt_of_lt_of_le (Real.exp_pos _) (hlow θ2 x)
    have hpos1 : 0 < ∫ z, Real.exp (f θ1 z / (lam * eps)) ∂(Q x) :=
      lt_of_lt_of_le (Real.exp_pos _) (hlow θ1 x)
    have hmono : ∫ z, Real.exp (f θ1 z / (lam * eps)) ∂(Q x)
        ≤ ∫ z, Real.exp (|Lf| * dist θ1 θ2 / (lam * eps)) * Real.exp (f θ2 z / (lam * eps)) ∂(Q x) := by
      refine integral_mono (hInt θ1 x) ((hInt θ2 x).const_mul _) (fun z => ?_)
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith [hlip z]) ha.le
    rw [integral_const_mul] at hmono
    have := Real.log_le_log hpos1 hmono
    rw [Real.log_mul (Real.exp_pos _).ne' hpos2.ne', Real.log_exp] at this
    have e : lam * eps * (|Lf| * dist θ1 θ2 / (lam * eps)) = |Lf| * dist θ1 θ2 := by
      field_simp
    nlinarith
  calc ∫ x, lam * eps * Real.log (∫ z, Real.exp (f θ1 z / (lam * eps)) ∂(Q x)) ∂P
      ≤ ∫ x, (lam * eps * Real.log (∫ z, Real.exp (f θ2 z / (lam * eps)) ∂(Q x))
        + |Lf| * dist θ1 θ2) ∂P :=
        integral_mono (hgInt θ1) ((hgInt θ2).add (integrable_const _)) hpt
    _ = _ := by rw [integral_add (hgInt θ2) (integrable_const _)]; simp

lemma objF_meas {d : ℕ} {Z : Type*} [MeasurableSpace Z] (Θ : Set (Param d))
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf B : ℝ) (hA2II : Asm2Lipschitz f Lf) (hA2III : Asm2Bounded Θ f B)
    (θ0 : Param d) (hθ0 : θ0 ∈ Θ) : Measurable (objF P Q lam eps f) :=
  (LipschitzWith.of_le_add_mul' |Lf| (objF_le Θ P Q lam eps hlam heps f hf_meas Lf B hA2II hA2III
    θ0 hθ0)).continuous.measurable

lemma bias_small (lam eps B δ : ℝ) (hlam : 0 < lam) (heps : 0 < eps) (hδ : 0 < δ) :
    2 * (lam * eps * Real.exp (2 * (B / (lam * eps))) * ((2 : ℝ) ^ (levelL lam eps B δ + 1))⁻¹)
      ≤ δ / 2 := by
  have hApos : 0 < 2 * lam * eps * Real.exp (2 * (B / (lam * eps))) / δ := by positivity
  have hL : Real.log (2 * lam * eps * Real.exp (2 * (B / (lam * eps))) / δ) / Real.log 2
      ≤ (levelL lam eps B δ : ℝ) := by
    unfold levelL
    calc _ ≤ (⌈Real.log (2 * lam * eps * Real.exp (2 * (B / (lam * eps))) / δ)
          / Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ _ := by exact_mod_cast le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : 2 * lam * eps * Real.exp (2 * (B / (lam * eps))) / δ
      ≤ (2:ℝ) ^ (levelL lam eps B δ) := by
    rw [div_le_iff₀ hlog2] at hL
    rw [← Real.log_le_log_iff hApos (by positivity), Real.log_pow]
    linarith
  rw [div_le_iff₀ hδ] at h2
  have hp : (0:ℝ) < 2 ^ levelL lam eps B δ := by positivity
  rw [pow_succ]
  rw [show 2 * (lam * eps * Real.exp (2 * (B / (lam * eps))) * (2 ^ levelL lam eps B δ * 2)⁻¹)
    = (2 * lam * eps * Real.exp (2 * (B / (lam * eps)))) / (2 ^ levelL lam eps B δ) / 2 by
      field_simp]
  have : (2 * lam * eps * Real.exp (2 * (B / (lam * eps)))) / (2 ^ levelL lam eps B δ) ≤ δ := by
    rw [div_le_iff₀ hp]; linarith
  linarith

lemma step_bound (M D κ δ : ℝ) (T : ℕ) (hM : 0 ≤ M) (hκ : 0 < κ) (hδ : 0 < δ) (hT : 0 < T)
    (hTb : 8 * M ^ 2 * D / (κ * δ ^ 2) ≤ T) : M * Real.sqrt (2 * D / (κ * T)) ≤ δ / 2 := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  calc M * Real.sqrt (2 * D / (κ * T)) = Real.sqrt (M ^ 2 * (2 * D / (κ * T))) := by
        rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]
    _ ≤ Real.sqrt ((δ / 2) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ (by positivity)] at hTb
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith
    _ = δ / 2 := Real.sqrt_sq (by linarith)

end Aux_BSMDT2

open SinkhornDRO.BSMD Aux_BSMDT2 in
theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (𝒩 : MirrorNorm d) (κ : ℝ) (ω : Param d → ℝ) (ω' : Param d → Param d)
    (hω : IsDistGen Θ 𝒩 κ ω ω')
    (prox : Param d → Param d → Param d) (hprox : IsProxMap Θ ω ω' prox)
    (hprox_meas : Measurable (Function.uncurry prox))
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf B : ℝ) (hA2I : Asm2Convex f) (hA2II : Asm2Lipschitz f Lf) (hA2III : Asm2Bounded Θ f B)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg)
    (hsg_meas : Measurable (Function.uncurry sg))
    (δ : ℝ) (hδ : 0 < δ)
    (θ0 : Param d) (hθ0 : θ0 ∈ Θ)
    (θstar : Param d)
    (hθstar : θstar ∈ Θ ∧ ∀ θ ∈ Θ, objF P Q lam eps f θstar ≤ objF P Q lam eps f θ)
    (θbar : Param d)
    (hθbar : θbar ∈ Θ ∧ ∀ θ ∈ Θ,
      objFℓ P Q lam eps f (levelL lam eps B δ) θbar ≤ objFℓ P Q lam eps f (levelL lam eps B δ) θ)
    [IsProbabilityMeasure (levelLaw P Q (2 ^ levelL lam eps B δ))]
    [IsProbabilityMeasure (rtLaw P Q (levelL lam eps B δ))] :
    let K := B / (lam * eps)
    let L := levelL lam eps B δ
    let D := bregman ω ω' θ0 θbar
    -- (I) SG estimator
    (let T := iterSG Lf κ 𝒩.c D δ
     let h := stepSG Lf κ 𝒩.c D T
     Integrable (fun ξ : Fin T → Z × (Fin (2 ^ L) → Z) =>
         objF P Q lam eps f (bsmdAvg prox (vSG lam eps f sg L) h θ0 ξ))
         (Measure.pi fun _ => levelLaw P Q (2 ^ L)) ∧
       ∫ ξ, objF P Q lam eps f (bsmdAvg prox (vSG lam eps f sg L) h θ0 ξ)
           ∂(Measure.pi fun _ : Fin T => levelLaw P Q (2 ^ L))
         - objF P Q lam eps f θstar ≤ δ) ∧
    -- (II) RT-MLMC estimator
    (let T := iterRT L Lf K κ 𝒩.c D δ
     let h := stepRT L Lf K κ 𝒩.c D T
     Integrable (fun ξ : Fin T → Fin (L + 1) × Z × (Fin (2 ^ L) → Z) =>
         objF P Q lam eps f (bsmdAvg prox (vRT lam eps f sg L) h θ0 ξ))
         (Measure.pi fun _ => rtLaw P Q L) ∧
       ∫ ξ, objF P Q lam eps f (bsmdAvg prox (vRT lam eps f sg L) h θ0 ξ)
           ∂(Measure.pi fun _ : Fin T => rtLaw P Q L)
         - objF P Q lam eps f θstar ≤ δ) := by
  intro K L D
  have hκ : 0 < κ := hω.2.2.1
  have hc : 0 < 𝒩.c := 𝒩.c_pos
  -- degenerate case `L_f ≤ 0`: the loss does not depend on `θ`
  rcases le_or_gt Lf 0 with hLf | hLf
  · have hfc : ∀ θ, f θ = f θstar := fun θ => funext fun z => by
      have h1 := (hA2II z θ θstar).trans
        (mul_nonpos_of_nonpos_of_nonneg hLf (norm_nonneg _))
      exact sub_eq_zero.mp (abs_nonpos_iff.mp h1)
    have hF : objF P Q lam eps f = fun _ => objF P Q lam eps f θstar := by
      funext θ
      simp only [objF, hfc θ]
    rw [hF]
    refine ⟨⟨integrable_const _, ?_⟩, ⟨integrable_const _, ?_⟩⟩ <;> simp <;> linarith
  have hfm := f_meas f hf_meas Lf hA2II
  have hsgθ : ∀ θ, Measurable (sg θ) := fun θ =>
    hsg_meas.comp (measurable_const.prodMk measurable_id)
  have hFm : Measurable (objF P Q lam eps f) :=
    objF_meas Θ P Q lam eps hlam heps f hf_meas Lf B hA2II hA2III θ0 hθ0
  have hL1 : 1 ≤ L := le_max_left _ _
  obtain ⟨hU1, -, -, hU4⟩ := unbiased_estimators Θ hΘc hΘv P Q lam eps hlam heps f hf_meas Lf B
    hA2I hA2II hA2III sg hsg hsgθ
  have hbias : ∀ θ ∈ Θ, |objFℓ P Q lam eps f L θ - objF P Q lam eps f θ|
      ≤ lam * eps * Real.exp (2 * (B / (lam * eps))) * ((2 : ℝ) ^ (L + 1))⁻¹ :=
    lemma_EC_6_I Θ hΘc hΘv P Q lam eps hlam heps f hf_meas B hA2III L
  have hbias2 := bias_small lam eps B δ hlam heps hδ
  let sgbar : Param d → Param d := fun θ =>
    ∫ ζ, levelg lam eps f sg L θ ζ.2 ∂(levelLaw P Q (2 ^ L))
  have hsgbar : ∀ θ ∈ Θ, ∀ θ' ∈ Θ,
      objFℓ P Q lam eps f L θ + ⟪sgbar θ, θ' - θ⟫ ≤ objFℓ P Q lam eps f L θ' :=
    fun θ hθ => (hU1 L θ hθ).2
  refine ⟨?_, ?_⟩
  · -- (I) SG
    intro T h
    have hM : 0 < Lf / 𝒩.c := div_pos hLf hc
    have hT : 0 < T := lt_of_lt_of_le Nat.one_pos (le_max_left 1 _ : 1 ≤ iterSG Lf κ 𝒩.c D δ)
    have hvsq : ∀ θ ∈ Θ, Integrable (fun s => dualNorm 𝒩 (vSG lam eps f sg L θ s) ^ 2)
        (levelLaw P Q (2 ^ L)) ∧
        ∫ s, dualNorm 𝒩 (vSG lam eps f sg L θ s) ^ 2 ∂(levelLaw P Q (2 ^ L)) ≤ (Lf / 𝒩.c) ^ 2 := by
      intro θ hθ
      obtain ⟨hi, hle⟩ := lemma_EC_6_III_a Θ hΘc hΘv P Q lam eps hlam heps f hf_meas Lf hA2I
        hA2II sg hsg hsgθ L θ hθ
      have hvm : Measurable (vSG lam eps f sg L θ) :=
        (vSG_meas lam eps f sg hfm hsg_meas L).comp (measurable_const.prodMk measurable_id)
      have hint : Integrable (fun s => dualNorm 𝒩 (vSG lam eps f sg L θ s) ^ 2)
          (levelLaw P Q (2 ^ L)) := by
        refine (hi.const_mul (𝒩.c ^ 2)⁻¹).mono'
          (((dual_lip 𝒩).measurable.comp hvm).pow_const 2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact dual_sq_le 𝒩 _
      refine ⟨hint, ?_⟩
      calc ∫ s, dualNorm 𝒩 (vSG lam eps f sg L θ s) ^ 2 ∂(levelLaw P Q (2 ^ L))
          ≤ ∫ s, (𝒩.c ^ 2)⁻¹ * ‖levelg lam eps f sg L θ s.2‖ ^ 2 ∂(levelLaw P Q (2 ^ L)) :=
            integral_mono hint (hi.const_mul _) (fun s => dual_sq_le 𝒩 _)
        _ = (𝒩.c ^ 2)⁻¹ * ∫ s, ‖levelg lam eps f sg L θ s.2‖ ^ 2 ∂(levelLaw P Q (2 ^ L)) :=
            integral_const_mul _ _
        _ ≤ (𝒩.c ^ 2)⁻¹ * Lf ^ 2 := by gcongr
        _ = (Lf / 𝒩.c) ^ 2 := by field_simp
    have key := lemma_EC_7 Θ hΘc hΘv 𝒩 κ ω ω' hω prox hprox hprox_meas (objF P Q lam eps f)
      (objFℓ P Q lam eps f L) hFm _ hbias sgbar hsgbar (levelLaw P Q (2 ^ L))
      (vSG lam eps f sg L) (vSG_meas lam eps f sg hfm hsg_meas L) (Lf / 𝒩.c) hM
      (fun θ hθ => (hU1 L θ hθ).1) (fun θ _ => rfl) hvsq θbar hθbar θstar hθstar θ0 hθ0 T hT
    have hh : h = Real.sqrt (2 * κ * bregman ω ω' θ0 θbar / (T * (Lf / 𝒩.c) ^ 2)) := by
      show stepSG Lf κ 𝒩.c D T = _
      unfold stepSG
      congr 1
      field_simp
      rfl
    obtain ⟨k1, k2⟩ := key
    rw [hh]
    refine ⟨k1, ?_⟩
    rw [integral_sub k1 (integrable_const _)] at k2
    simp only [integral_const, probReal_univ, one_smul] at k2
    have hTb : 8 * (Lf / 𝒩.c) ^ 2 * D / (κ * δ ^ 2) ≤ T := by
      have h1 : (⌈8 * Lf ^ 2 * D / (κ * 𝒩.c ^ 2 * δ ^ 2)⌉₊ : ℝ) ≤ T := by
        exact_mod_cast (le_max_right _ _ : _ ≤ iterSG Lf κ 𝒩.c D δ)
      have h2 := Nat.le_ceil (8 * Lf ^ 2 * D / (κ * 𝒩.c ^ 2 * δ ^ 2))
      have e : 8 * (Lf / 𝒩.c) ^ 2 * D / (κ * δ ^ 2) = 8 * Lf ^ 2 * D / (κ * 𝒩.c ^ 2 * δ ^ 2) := by
        field_simp
      linarith
    have hs := step_bound (Lf / 𝒩.c) D κ δ T hM.le hκ hδ hT hTb
    linarith
  · -- (II) RT-MLMC
    intro T h
    have hmpos : 0 < msqRT L Lf K 𝒩.c := by unfold msqRT; positivity
    have hM : 0 < Real.sqrt (msqRT L Lf K 𝒩.c) := Real.sqrt_pos.mpr hmpos
    have hMsq : Real.sqrt (msqRT L Lf K 𝒩.c) ^ 2 = msqRT L Lf K 𝒩.c := Real.sq_sqrt hmpos.le
    have hT : 0 < T := lt_of_lt_of_le Nat.one_pos (le_max_left 1 _ : 1 ≤ iterRT L Lf K κ 𝒩.c D δ)
    have hvsq : ∀ θ ∈ Θ, Integrable (fun s => dualNorm 𝒩 (vRT lam eps f sg L θ s) ^ 2)
        (rtLaw P Q L) ∧
        ∫ s, dualNorm 𝒩 (vRT lam eps f sg L θ s) ^ 2 ∂(rtLaw P Q L)
          ≤ Real.sqrt (msqRT L Lf K 𝒩.c) ^ 2 := by
      intro θ hθ
      obtain ⟨i1, -, -, -, -, b⟩ := rtmlmc_second_moment Θ hΘc hΘv 𝒩 P Q lam eps hlam heps f
        hf_meas Lf B hA2I hA2II hA2III sg hsg hsgθ L hL1 θ hθ
      exact ⟨i1, b.trans hMsq.ge⟩
    have key := lemma_EC_7 Θ hΘc hΘv 𝒩 κ ω ω' hω prox hprox hprox_meas (objF P Q lam eps f)
      (objFℓ P Q lam eps f L) hFm _ hbias sgbar hsgbar (rtLaw P Q L)
      (vRT lam eps f sg L) (vRT_meas lam eps f sg hfm hsg_meas L) _ hM
      (fun θ hθ => (hU4 L hL1 θ hθ).1) (fun θ hθ => (hU4 L hL1 θ hθ).2) hvsq θbar hθbar
      θstar hθstar θ0 hθ0 T hT
    have hh : h = Real.sqrt (2 * κ * bregman ω ω' θ0 θbar
        / (T * Real.sqrt (msqRT L Lf K 𝒩.c) ^ 2)) := by
      rw [hMsq]; rfl
    obtain ⟨k1, k2⟩ := key
    rw [hh]
    refine ⟨k1, ?_⟩
    rw [integral_sub k1 (integrable_const _)] at k2
    simp only [integral_const, probReal_univ, one_smul] at k2
    have hTb : 8 * Real.sqrt (msqRT L Lf K 𝒩.c) ^ 2 * D / (κ * δ ^ 2) ≤ T := by
      have h1n : ⌈(16 * ((L : ℝ) + 1)) * Lf ^ 2 * D * Real.exp (4 * K)
          / (κ * 𝒩.c ^ 2 * δ ^ 2)⌉₊ ≤ iterRT L Lf K κ 𝒩.c D δ := by
        unfold iterRT; exact le_max_right _ _
      have h1 : (⌈(16 * ((L : ℝ) + 1)) * Lf ^ 2 * D * Real.exp (4 * K)
          / (κ * 𝒩.c ^ 2 * δ ^ 2)⌉₊ : ℝ) ≤ T := Nat.cast_le.mpr h1n
      have h2 := Nat.le_ceil ((16 * ((L : ℝ) + 1)) * Lf ^ 2 * D * Real.exp (4 * K)
          / (κ * 𝒩.c ^ 2 * δ ^ 2))
      have e : 8 * Real.sqrt (msqRT L Lf K 𝒩.c) ^ 2 * D / (κ * δ ^ 2)
          = (16 * ((L : ℝ) + 1)) * Lf ^ 2 * D * Real.exp (4 * K)
            / (κ * 𝒩.c ^ 2 * δ ^ 2) := by
        rw [hMsq]; unfold msqRT; field_simp; ring
      linarith
    have hs := step_bound _ D κ δ T hM.le hκ hδ hT hTb
    linarith
