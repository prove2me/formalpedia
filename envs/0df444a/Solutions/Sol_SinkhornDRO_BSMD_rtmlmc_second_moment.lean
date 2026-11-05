-- Prove2me | solution 1 for SinkhornDRO.BSMD.rtmlmc_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T06:03:45.226062+00:00
-- url     : https://prove2.me/submissions/a28cd082-0d5e-426f-a58f-e568363ed912

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_MirrorSetup
import Definitions.Def_SinkhornDRO_BSMD_Objective
import Definitions.Def_SinkhornDRO_BSMD_Estimators
import Theorems.Thm_SinkhornDRO_BSMD_lemma_EC_6_III_b

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Aux_BSMDRT
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


lemma pi_meas {Z : Type*} [MeasurableSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) :
    Measurable (fun x => Measure.pi fun _ : Fin n => Q x) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm
    isPiSystem_pi ?_
  rintro _ ⟨s, hs, rfl⟩
  simp only [Measure.pi_pi]
  exact Finset.measurable_prod _ (fun i _ => Q.measurable_coe (hs i (Set.mem_univ i)))

lemma kern_meas {Z : Type*} [MeasurableSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) :
    Measurable (fun x : Z => (Measure.dirac x).prod (Measure.pi fun _ : Fin n => Q x)) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_prod.symm
    isPiSystem_prod ?_
  rintro _ ⟨A, hA, B, hB, rfl⟩
  simp only [Measure.prod_prod]
  exact ((Measure.measurable_coe (show MeasurableSet A from hA)).comp Measure.measurable_dirac).mul
    ((Measure.measurable_coe (show MeasurableSet B from hB)).comp (pi_meas Q n))

lemma levelLaw_prob {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) : IsProbabilityMeasure (levelLaw P Q n) := by
  constructor
  unfold levelLaw
  rw [Measure.bind_apply MeasurableSet.univ (kern_meas Q n).aemeasurable]
  simp

lemma pi_marg {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e) :
    (Measure.pi fun _ : Fin n => μ).map (fun zs => zs ∘ e) = Measure.pi fun _ : Fin m => μ := by
  classical
  have hm : Measurable (fun zs : Fin n → Z => zs ∘ e) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  set t : Fin n → Set Z := Function.extend e s (fun _ => Set.univ) with ht
  have hpre : (fun zs : Fin n → Z => zs ∘ e) ⁻¹' (Set.univ.pi s) = Set.univ.pi t := by
    ext zs
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp]
    constructor
    · intro h i
      by_cases hi : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := hi
        rw [show t (e j) = s j from he.extend_apply s _ j]; exact h j
      · rw [show t i = Set.univ from Function.extend_apply' _ _ _ hi]; trivial
    · intro h j
      have := h (e j)
      rwa [show t (e j) = s j from he.extend_apply s _ j] at this
  rw [hpre, Measure.pi_pi]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image e))]
  · rw [Finset.prod_image (fun a _ b _ h => he h)]
    exact Finset.prod_congr rfl (fun j _ => by rw [show t (e j) = s j from he.extend_apply s _ j])
  · intro i _ hi
    have : ¬ ∃ j, e j = i := by simpa using hi
    rw [show t i = Set.univ from Function.extend_apply' _ _ _ this, measure_univ]

lemma levelLaw_marg {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] {m n : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) :
    (levelLaw P Q n).map (fun ζ : Z × (Fin n → Z) => (ζ.1, ζ.2 ∘ e)) = levelLaw P Q m := by
  have hm : Measurable (fun zs : Fin n → Z => zs ∘ e) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have hg : Measurable (fun ζ : Z × (Fin n → Z) => (ζ.1, ζ.2 ∘ e)) :=
    measurable_fst.prodMk (hm.comp measurable_snd)
  ext s hs
  rw [Measure.map_apply hg hs]
  unfold levelLaw
  rw [Measure.bind_apply (hg hs) (kern_meas Q n).aemeasurable,
    Measure.bind_apply hs (kern_meas Q m).aemeasurable]
  refine lintegral_congr (fun x => ?_)
  rw [← Measure.map_apply hg hs]
  congr 1
  have : (fun ζ : Z × (Fin n → Z) => (ζ.1, ζ.2 ∘ e)) = Prod.map id (fun zs => zs ∘ e) := rfl
  rw [this, ← Measure.map_prod_map _ _ measurable_id hm, Measure.map_id, pi_marg (Q x) e he]

lemma integral_marg {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] {m n : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) (ψ : Z × (Fin m → Z) → E) (hψ : StronglyMeasurable ψ) :
    ∫ ζ, ψ (ζ.1, ζ.2 ∘ e) ∂(levelLaw P Q n) = ∫ ζ, ψ ζ ∂(levelLaw P Q m) := by
  have hm : Measurable (fun zs : Fin n → Z => zs ∘ e) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have hg : Measurable (fun ζ : Z × (Fin n → Z) => (ζ.1, ζ.2 ∘ e)) :=
    measurable_fst.prodMk (hm.comp measurable_snd)
  rw [← levelLaw_marg P Q e he, integral_map hg.aemeasurable hψ.aestronglyMeasurable]

lemma sg_bound {d : ℕ} {Z : Type*} (f : Param d → Z → ℝ) (Lf : ℝ) (hA2II : Asm2Lipschitz f Lf)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg) (θ : Param d) (z : Z) :
    ‖sg θ z‖ ≤ |Lf| := by
  have h1 := hsg θ z (θ + sg θ z)
  have h2 := hA2II z (θ + sg θ z) θ
  rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h1
  rw [add_sub_cancel_left] at h2
  have h3 : ‖sg θ z‖ ^ 2 ≤ |Lf| * ‖sg θ z‖ := by
    have := le_abs_self (f (θ + sg θ z) z - f θ z)
    have := mul_le_mul_of_nonneg_right (le_abs_self Lf) (norm_nonneg (sg θ z))
    linarith
  rcases eq_or_lt_of_le (norm_nonneg (sg θ z)) with h | h
  · rw [← h]; exact abs_nonneg _
  · nlinarith

lemma blockGrad_norm_le {d : ℕ} {Z : Type*} (lam eps : ℝ) (f : Param d → Z → ℝ) (Lf : ℝ)
    (hA2II : Asm2Lipschitz f Lf) (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg)
    (θ : Param d) {n : ℕ} (zs : Fin n → Z) (S : Finset (Fin n)) :
    ‖blockGrad lam eps f sg θ zs S‖ ≤ |Lf| := by
  unfold blockGrad
  set e : Fin n → ℝ := fun j => Real.exp (f θ (zs j) / (lam * eps)) with he
  have hepos : ∀ j, 0 < e j := fun j => Real.exp_pos _
  have hS : 0 ≤ ∑ k ∈ S, e k := Finset.sum_nonneg (fun k _ => (hepos k).le)
  calc ‖∑ j ∈ S, (e j / ∑ k ∈ S, e k) • sg θ (zs j)‖
      ≤ ∑ j ∈ S, ‖(e j / ∑ k ∈ S, e k) • sg θ (zs j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ S, (e j / ∑ k ∈ S, e k) * |Lf| := by
        apply Finset.sum_le_sum; intro j _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hepos j).le hS)]
        exact mul_le_mul_of_nonneg_left (sg_bound f Lf hA2II sg hsg θ (zs j))
          (div_nonneg (hepos j).le hS)
    _ = (∑ j ∈ S, e j) / (∑ k ∈ S, e k) * |Lf| := by rw [← Finset.sum_mul, ← Finset.sum_div]
    _ ≤ 1 * |Lf| := by gcongr; exact div_self_le_one _
    _ = |Lf| := one_mul _

lemma levelG_norm_le {d : ℕ} {Z : Type*} (lam eps : ℝ) (f : Param d → Z → ℝ) (Lf : ℝ)
    (hA2II : Asm2Lipschitz f Lf) (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg)
    (ℓ : ℕ) (θ : Param d) (zs : Fin (2 ^ ℓ) → Z) :
    ‖levelG lam eps f sg ℓ θ zs‖ ≤ 2 * |Lf| := by
  cases ℓ with
  | zero =>
    exact (blockGrad_norm_le lam eps f Lf hA2II sg hsg θ zs _).trans
      (by linarith [abs_nonneg Lf])
  | succ ℓ =>
    have e : levelG lam eps f sg (ℓ + 1) θ zs = blockGrad lam eps f sg θ zs Finset.univ
        - (1 / 2 : ℝ) • blockGrad lam eps f sg θ zs (lowHalf ℓ)
        - (1 / 2 : ℝ) • blockGrad lam eps f sg θ zs (highHalf ℓ) := rfl
    rw [e]
    have h1 := blockGrad_norm_le lam eps f Lf hA2II sg hsg θ zs Finset.univ
    have h2 := blockGrad_norm_le lam eps f Lf hA2II sg hsg θ zs (lowHalf ℓ)
    have h3 := blockGrad_norm_le lam eps f Lf hA2II sg hsg θ zs (highHalf ℓ)
    have n1 := norm_sub_le (blockGrad lam eps f sg θ zs Finset.univ
        - (1 / 2 : ℝ) • blockGrad lam eps f sg θ zs (lowHalf ℓ))
      ((1 / 2 : ℝ) • blockGrad lam eps f sg θ zs (highHalf ℓ))
    have n2 := norm_sub_le (blockGrad lam eps f sg θ zs Finset.univ)
      ((1 / 2 : ℝ) • blockGrad lam eps f sg θ zs (lowHalf ℓ))
    rw [norm_smul] at n1 n2
    norm_num at n1 n2
    linarith

lemma levelProb_pos (L : ℕ) (ℓ : ℕ) : 0 < levelProb L ℓ := by
  unfold levelProb
  have : ((2:ℝ) ^ L)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  exact div_pos (by positivity) (by linarith)

lemma levelProb_inv (L : ℕ) (ℓ : ℕ) :
    (levelProb L ℓ)⁻¹ = 2 ^ ℓ * (2 - ((2:ℝ) ^ L)⁻¹) := by
  unfold levelProb
  rw [inv_div, div_eq_mul_inv, inv_inv, mul_comm]

lemma rt_finite {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (L : ℕ) : IsFiniteMeasure (rtLaw P Q L) := by
  have := levelLaw_prob P Q (2 ^ L)
  constructor
  unfold rtLaw
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine ENNReal.sum_lt_top.mpr (fun ℓ _ => ?_)
  rw [Measure.smul_apply, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp

lemma rt_integral {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (L : ℕ)
    (φ : Fin (L + 1) × Z × (Fin (2 ^ L) → Z) → ℝ) (hφm : Measurable φ)
    (hφ : ∀ ℓ : Fin (L + 1), Integrable (fun ζ => φ (ℓ, ζ)) (levelLaw P Q (2 ^ L))) :
    ∫ ζ, φ ζ ∂(rtLaw P Q L) = ∑ ℓ : Fin (L + 1), levelProb L ℓ * ∫ ζ, φ (ℓ, ζ) ∂(levelLaw P Q (2 ^ L)) := by
  have hmk : ∀ ℓ : Fin (L + 1), Measurable (fun ζ : Z × (Fin (2 ^ L) → Z) => (ℓ, ζ)) :=
    fun ℓ => measurable_const.prodMk measurable_id
  unfold rtLaw
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [integral_smul_measure, integral_map (hmk ℓ).aemeasurable hφm.aestronglyMeasurable,
      ENNReal.toReal_ofReal (levelProb_pos L ℓ).le, smul_eq_mul]
  · intro ℓ _
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    rw [integrable_map_measure hφm.aestronglyMeasurable (hmk ℓ).aemeasurable]
    exact hφ ℓ

lemma blockGradθ_meas {d : ℕ} {Z : Type*} [MeasurableSpace Z] (lam eps : ℝ)
    (f : Param d → Z → ℝ) (sg : Param d → Z → Param d) (θ : Param d)
    (hf : Measurable (f θ)) (hsg : Measurable (sg θ)) {n : ℕ} (S : Finset (Fin n)) :
    Measurable (fun zs : Fin n → Z => blockGrad lam eps f sg θ zs S) := by
  unfold blockGrad
  have hE : ∀ j : Fin n, Measurable
      (fun zs : Fin n → Z => Real.exp (f θ (zs j) / (lam * eps))) :=
    fun j => Real.measurable_exp.comp ((hf.comp (measurable_pi_apply j)).div_const _)
  have hS : Measurable (fun zs : Fin n → Z =>
      ∑ k ∈ S, Real.exp (f θ (zs k) / (lam * eps))) :=
    Finset.measurable_sum _ (fun k _ => hE k)
  exact Finset.measurable_sum _ (fun j _ => ((hE j).div hS).smul (hsg.comp (measurable_pi_apply j)))

lemma levelGθ_meas {d : ℕ} {Z : Type*} [MeasurableSpace Z] (lam eps : ℝ)
    (f : Param d → Z → ℝ) (sg : Param d → Z → Param d) (θ : Param d)
    (hf : Measurable (f θ)) (hsg : Measurable (sg θ)) (ℓ : ℕ) :
    Measurable (fun zs : Fin (2 ^ ℓ) → Z => levelG lam eps f sg ℓ θ zs) := by
  cases ℓ with
  | zero => exact blockGradθ_meas lam eps f sg θ hf hsg _
  | succ ℓ =>
    have e : (fun zs : Fin (2 ^ (ℓ + 1)) → Z => levelG lam eps f sg (ℓ + 1) θ zs)
        = fun zs => blockGrad lam eps f sg θ zs Finset.univ
            - (1 / 2 : ℝ) • blockGrad lam eps f sg θ zs (lowHalf ℓ)
            - (1 / 2 : ℝ) • blockGrad lam eps f sg θ zs (highHalf ℓ) := rfl
    rw [e]
    exact (((blockGradθ_meas lam eps f sg θ hf hsg _).sub
      ((blockGradθ_meas lam eps f sg θ hf hsg _).const_smul (1 / 2 : ℝ))).sub
      ((blockGradθ_meas lam eps f sg θ hf hsg _).const_smul (1 / 2 : ℝ)))

lemma vRTθ_meas {d : ℕ} {Z : Type*} [MeasurableSpace Z] (lam eps : ℝ)
    (f : Param d → Z → ℝ) (sg : Param d → Z → Param d) (θ : Param d)
    (hf : Measurable (f θ)) (hsg : Measurable (sg θ)) (L : ℕ) :
    Measurable (vRT lam eps f sg L θ) := by
  refine measurable_from_prod_countable_right (fun ℓ => ?_)
  have ht : Measurable (fun zs : Fin (2 ^ L) → Z => truncSamples (Z := Z) ℓ zs) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have h2 : Measurable fun y : Z × (Fin (2 ^ L) → Z) =>
      levelG lam eps f sg ℓ θ (truncSamples ℓ y.2) :=
    (levelGθ_meas lam eps f sg θ hf hsg ℓ).comp (ht.comp measurable_snd)
  exact h2.const_smul (levelProb L ℓ)⁻¹

end Aux_BSMDRT

open SinkhornDRO.BSMD Aux_BSMDRT in
theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ) (𝒩 : MirrorNorm d)
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf B : ℝ) (hA2I : Asm2Convex f) (hA2II : Asm2Lipschitz f Lf) (hA2III : Asm2Bounded Θ f B)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg) (hsg_meas : ∀ θ, Measurable (sg θ))
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ θ ∈ Θ,
      Integrable (fun ζ => dualNorm 𝒩 (vRT lam eps f sg L θ ζ) ^ 2) (rtLaw P Q L) ∧
      Integrable (fun ζ => ‖vRT lam eps f sg L θ ζ‖ ^ 2) (rtLaw P Q L) ∧
      ∫ ζ, dualNorm 𝒩 (vRT lam eps f sg L θ ζ) ^ 2 ∂(rtLaw P Q L)
        ≤ (𝒩.c ^ 2)⁻¹ * ∫ ζ, ‖vRT lam eps f sg L θ ζ‖ ^ 2 ∂(rtLaw P Q L) ∧
      ∫ ζ, ‖vRT lam eps f sg L θ ζ‖ ^ 2 ∂(rtLaw P Q L)
        = ∑ ℓ : Fin (L + 1), (levelProb L ℓ)⁻¹ *
            ∫ ζ, ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ (ℓ : ℕ))) ∧
      ∑ ℓ : Fin (L + 1), (levelProb L ℓ)⁻¹ *
            ∫ ζ, ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ (ℓ : ℕ)))
        ≤ 2 * (L + 1) * Lf ^ 2 * Real.exp (4 * (B / (lam * eps))) ∧
      ∫ ζ, dualNorm 𝒩 (vRT lam eps f sg L θ ζ) ^ 2 ∂(rtLaw P Q L)
        ≤ msqRT L Lf (B / (lam * eps)) 𝒩.c := by
  intro θ hθ
  have := levelLaw_prob P Q (2 ^ L)
  have := rt_finite P Q L
  have hvm : Measurable (vRT lam eps f sg L θ) :=
    vRTθ_meas lam eps f sg θ (hf_meas θ) (hsg_meas θ) L
  set C : ℝ := (∑ ℓ : Fin (L + 1), |(levelProb L ℓ)⁻¹|) * (2 * |Lf|) with hC
  have hvb : ∀ ζ, ‖vRT lam eps f sg L θ ζ‖ ≤ C := by
    intro ζ
    show ‖(levelProb L ζ.1)⁻¹ • levelG lam eps f sg ζ.1 θ (truncSamples ζ.1 ζ.2.2)‖ ≤ C
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : |(levelProb L ζ.1)⁻¹| ≤ ∑ ℓ : Fin (L + 1), |(levelProb L ℓ)⁻¹| :=
      Finset.single_le_sum (f := fun ℓ : Fin (L + 1) => |(levelProb L ℓ)⁻¹|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    exact mul_le_mul h1 (levelG_norm_le lam eps f Lf hA2II sg hsg _ θ _) (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hsq : ∀ ζ, ‖vRT lam eps f sg L θ ζ‖ ^ 2 ≤ C ^ 2 := fun ζ =>
    pow_le_pow_left₀ (norm_nonneg _) (hvb ζ) 2
  have hdm : Measurable (fun ζ => dualNorm 𝒩 (vRT lam eps f sg L θ ζ) ^ 2) :=
    ((dual_lip 𝒩).measurable.comp hvm).pow_const 2
  have hIb : Integrable (fun ζ => ‖vRT lam eps f sg L θ ζ‖ ^ 2) (rtLaw P Q L) := by
    refine Integrable.of_bound (hvm.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq ζ
  have hIa : Integrable (fun ζ => dualNorm 𝒩 (vRT lam eps f sg L θ ζ) ^ 2) (rtLaw P Q L) := by
    refine Integrable.of_bound hdm.aestronglyMeasurable ((𝒩.c ^ 2)⁻¹ * C ^ 2)
      (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (dual_sq_le 𝒩 _).trans (mul_le_mul_of_nonneg_left (hsq ζ) (by positivity))
  have hCc : ∫ ζ, dualNorm 𝒩 (vRT lam eps f sg L θ ζ) ^ 2 ∂(rtLaw P Q L)
      ≤ (𝒩.c ^ 2)⁻¹ * ∫ ζ, ‖vRT lam eps f sg L θ ζ‖ ^ 2 ∂(rtLaw P Q L) := by
    rw [← integral_const_mul]
    exact integral_mono hIa (hIb.const_mul _) (fun ζ => dual_sq_le 𝒩 _)
  have hD : ∫ ζ, ‖vRT lam eps f sg L θ ζ‖ ^ 2 ∂(rtLaw P Q L)
      = ∑ ℓ : Fin (L + 1), (levelProb L ℓ)⁻¹ *
          ∫ ζ, ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ (ℓ : ℕ))) := by
    rw [rt_integral P Q L _ (hvm.norm.pow_const 2) (fun ℓ => ?_)]
    · refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      have hp := levelProb_pos L ℓ
      have hle : 2 ^ (ℓ : ℕ) ≤ 2 ^ L :=
        Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp ℓ.isLt)
      have e1 : ∀ ζ : Z × (Fin (2 ^ L) → Z), ‖vRT lam eps f sg L θ (ℓ, ζ)‖ ^ 2
          = (levelProb L ℓ)⁻¹ ^ 2 *
            ‖levelG lam eps f sg ℓ θ (ζ.2 ∘ Fin.castLE hle)‖ ^ 2 := by
        intro ζ
        show ‖(levelProb L ℓ)⁻¹ • levelG lam eps f sg ℓ θ (truncSamples ℓ ζ.2)‖ ^ 2 = _
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        rfl
      rw [integral_congr_ae (Filter.Eventually.of_forall e1), integral_const_mul]
      have hm := integral_marg P Q (Fin.castLE hle) (Fin.castLE_injective hle)
        (fun ζ' : Z × (Fin (2 ^ (ℓ : ℕ)) → Z) => ‖levelG lam eps f sg ℓ θ ζ'.2‖ ^ 2)
        ((((levelGθ_meas lam eps f sg θ (hf_meas θ) (hsg_meas θ) ℓ).comp
          measurable_snd).norm.pow_const 2).stronglyMeasurable)
      dsimp only at hm
      rw [hm]
      field_simp
    · refine Integrable.of_bound ((hvm.norm.pow_const 2).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable (C ^ 2)
        (Filter.Eventually.of_forall fun ζ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsq _
  have hE : ∑ ℓ : Fin (L + 1), (levelProb L ℓ)⁻¹ *
          ∫ ζ, ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ (ℓ : ℕ)))
        ≤ 2 * (L + 1) * Lf ^ 2 * Real.exp (4 * (B / (lam * eps))) := by
    calc _ ≤ ∑ ℓ : Fin (L + 1), 2 * (Lf ^ 2 * Real.exp (4 * (B / (lam * eps)))) := by
          refine Finset.sum_le_sum (fun ℓ _ => ?_)
          have hb := (lemma_EC_6_III_b Θ hΘc hΘv P Q lam eps hlam heps f hf_meas Lf B hA2I
            hA2II hA2III sg hsg hsg_meas ℓ θ hθ).2
          have hx : ((2:ℝ) ^ L)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
          have hx0 : 0 ≤ ((2:ℝ) ^ L)⁻¹ := by positivity
          rw [levelProb_inv]
          have hq : 0 ≤ (2:ℝ) ^ (ℓ : ℕ) * (2 - ((2:ℝ) ^ L)⁻¹) := by
            apply mul_nonneg (by positivity); linarith
          calc (2:ℝ) ^ (ℓ : ℕ) * (2 - ((2:ℝ) ^ L)⁻¹) *
                ∫ ζ, ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ (ℓ : ℕ)))
              ≤ (2:ℝ) ^ (ℓ : ℕ) * (2 - ((2:ℝ) ^ L)⁻¹) *
                (Lf ^ 2 * Real.exp (4 * (B / (lam * eps))) * ((2 : ℝ) ^ (ℓ : ℕ))⁻¹) :=
                mul_le_mul_of_nonneg_left hb hq
            _ = (2 - ((2:ℝ) ^ L)⁻¹) * (Lf ^ 2 * Real.exp (4 * (B / (lam * eps)))) := by
                field_simp
            _ ≤ 2 * (Lf ^ 2 * Real.exp (4 * (B / (lam * eps)))) := by
                apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  refine ⟨hIa, hIb, hCc, hD, hE, ?_⟩
  calc _ ≤ (𝒩.c ^ 2)⁻¹ * ∫ ζ, ‖vRT lam eps f sg L θ ζ‖ ^ 2 ∂(rtLaw P Q L) := hCc
    _ ≤ (𝒩.c ^ 2)⁻¹ * (2 * (L + 1) * Lf ^ 2 * Real.exp (4 * (B / (lam * eps)))) := by
        rw [hD]; exact mul_le_mul_of_nonneg_left hE (by positivity)
    _ = msqRT L Lf (B / (lam * eps)) 𝒩.c := by unfold msqRT; ring
