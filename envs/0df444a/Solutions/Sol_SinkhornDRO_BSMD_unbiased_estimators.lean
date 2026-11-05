-- Prove2me | solution 1 for SinkhornDRO.BSMD.unbiased_estimators
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T06:11:26.74919+00:00
-- url     : https://prove2.me/submissions/b153bcf3-a8be-4546-8d6b-c3fca4d357e3

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_MirrorSetup
import Definitions.Def_SinkhornDRO_BSMD_Objective
import Definitions.Def_SinkhornDRO_BSMD_Estimators

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Aux_BSMDUE
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


lemma rt_integralE {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (L : ℕ)
    (φ : Fin (L + 1) × Z × (Fin (2 ^ L) → Z) → E) (hφm : StronglyMeasurable φ)
    (hφ : ∀ ℓ : Fin (L + 1), Integrable (fun ζ => φ (ℓ, ζ)) (levelLaw P Q (2 ^ L))) :
    ∫ ζ, φ ζ ∂(rtLaw P Q L)
      = ∑ ℓ : Fin (L + 1), levelProb L ℓ • ∫ ζ, φ (ℓ, ζ) ∂(levelLaw P Q (2 ^ L)) := by
  have hmk : ∀ ℓ : Fin (L + 1), Measurable (fun ζ : Z × (Fin (2 ^ L) → Z) => (ℓ, ζ)) :=
    fun ℓ => measurable_const.prodMk measurable_id
  unfold rtLaw
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [integral_smul_measure, integral_map (hmk ℓ).aemeasurable hφm.aestronglyMeasurable,
      ENNReal.toReal_ofReal (levelProb_pos L ℓ).le]
  · intro ℓ _
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    rw [integrable_map_measure hφm.aestronglyMeasurable (hmk ℓ).aemeasurable]
    exact hφ ℓ

lemma blockGrad_map {d : ℕ} {Z : Type*} (lam eps : ℝ) (f : Param d → Z → ℝ)
    (sg : Param d → Z → Param d) (θ : Param d) {m n : ℕ} (e : Fin m ↪ Fin n)
    (zs : Fin n → Z) :
    blockGrad lam eps f sg θ zs (Finset.univ.map e) = blockGrad lam eps f sg θ (zs ∘ e) Finset.univ := by
  unfold blockGrad
  rw [Finset.sum_map, Finset.sum_map]
  rfl

/-- embedding of the low half -/
def embLow (ℓ : ℕ) : Fin (2 ^ ℓ) ↪ Fin (2 ^ (ℓ + 1)) :=
  ⟨fun j => ⟨j.val, by have := j.isLt; rw [pow_succ]; omega⟩,
    fun a b h => by simp only [Fin.mk.injEq] at h; exact Fin.ext h⟩

/-- embedding of the high half -/
def embHigh (ℓ : ℕ) : Fin (2 ^ ℓ) ↪ Fin (2 ^ (ℓ + 1)) :=
  ⟨fun j => ⟨j.val + 2 ^ ℓ, by have := j.isLt; rw [pow_succ]; omega⟩,
    fun a b h => by simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩

lemma lowHalf_eq (ℓ : ℕ) : lowHalf ℓ = Finset.univ.map (embLow ℓ) := by
  ext j
  simp only [lowHalf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · intro h; exact ⟨⟨j.val, h⟩, by ext; rfl⟩
  · rintro ⟨i, rfl⟩; exact i.isLt

lemma highHalf_eq (ℓ : ℕ) : highHalf ℓ = Finset.univ.map (embHigh ℓ) := by
  ext j
  simp only [highHalf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · intro h
    have hj : j.val < 2 ^ ℓ * 2 := by
      have h1 := j.isLt
      have h2 : 2 ^ (ℓ + 1) = 2 ^ ℓ * 2 := pow_succ 2 ℓ
      omega
    refine ⟨⟨j.val - 2 ^ ℓ, by omega⟩, ?_⟩
    ext
    show j.val - 2 ^ ℓ + 2 ^ ℓ = j.val
    omega
  · rintro ⟨i, rfl⟩; show 2 ^ ℓ ≤ i.val + 2 ^ ℓ; omega

/-- the log-sum-exp subgradient inequality -/
lemma U_subgrad {d : ℕ} {Z : Type*} (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg)
    (ℓ : ℕ) (θ θ' : Param d) (zs : Fin (2 ^ ℓ) → Z) :
    lam * eps * Real.log (((2 : ℝ) ^ ℓ)⁻¹ * ∑ j, Real.exp (f θ (zs j) / (lam * eps)))
      + ⟪levelg lam eps f sg ℓ θ zs, θ' - θ⟫
      ≤ lam * eps * Real.log (((2 : ℝ) ^ ℓ)⁻¹ * ∑ j, Real.exp (f θ' (zs j) / (lam * eps))) := by
  have ha : 0 < lam * eps := mul_pos hlam heps
  set a : Fin (2 ^ ℓ) → ℝ := fun j => f θ (zs j) / (lam * eps) with ha_def
  set b : Fin (2 ^ ℓ) → ℝ := fun j => f θ' (zs j) / (lam * eps) with hb_def
  have hne : (Finset.univ : Finset (Fin (2 ^ ℓ))).Nonempty := ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩
  set Sa := ∑ j, Real.exp (a j) with hSa
  set Sb := ∑ j, Real.exp (b j) with hSb
  have hSa_pos : 0 < Sa := Finset.sum_pos (fun j _ => Real.exp_pos _) hne
  have hSb_pos : 0 < Sb := Finset.sum_pos (fun j _ => Real.exp_pos _) hne
  set w : Fin (2 ^ ℓ) → ℝ := fun j => Real.exp (a j) / Sa with hw
  have hw1 : ∑ j, w j = 1 := by rw [hw]; simp only; rw [← Finset.sum_div, div_self hSa_pos.ne']
  have hw0 : ∀ j, 0 ≤ w j := fun j => div_nonneg (Real.exp_pos _).le hSa_pos.le
  set s := ∑ j, w j * (b j - a j) with hs
  -- Σ w_j e^{b_j - a_j} = Sb / Sa ≥ e^s
  have hratio : Sb / Sa = ∑ j, w j * Real.exp (b j - a j) := by
    rw [hSb, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hw]; simp only
    rw [Real.exp_sub]; field_simp
  have hge : Real.exp s ≤ Sb / Sa := by
    rw [hratio]
    have : ∀ j, w j * Real.exp s * (1 + (b j - a j - s)) ≤ w j * Real.exp (b j - a j) := by
      intro j
      have h1 := Real.add_one_le_exp (b j - a j - s)
      have h2 : Real.exp s * Real.exp (b j - a j - s) = Real.exp (b j - a j) := by
        rw [← Real.exp_add]; ring_nf
      have h3 : 0 ≤ w j * Real.exp s := mul_nonneg (hw0 j) (Real.exp_pos _).le
      calc w j * Real.exp s * (1 + (b j - a j - s))
          ≤ w j * Real.exp s * Real.exp (b j - a j - s) := by
            apply mul_le_mul_of_nonneg_left (by linarith) h3
        _ = w j * Real.exp (b j - a j) := by rw [mul_assoc, h2]
    calc Real.exp s = ∑ j, w j * Real.exp s * (1 + (b j - a j - s)) := by
          have e1 : ∀ j, w j * Real.exp s * (1 + (b j - a j - s))
              = Real.exp s * (w j + w j * (b j - a j) - s * w j) := fun j => by ring
          rw [Finset.sum_congr rfl (fun j _ => e1 j), ← Finset.mul_sum, Finset.sum_sub_distrib,
            Finset.sum_add_distrib, ← Finset.mul_sum, hw1, ← hs]
          ring
      _ ≤ _ := Finset.sum_le_sum (fun j _ => this j)
  have hlog : s ≤ Real.log Sb - Real.log Sa := by
    rw [← Real.log_div hSb_pos.ne' hSa_pos.ne']
    exact (Real.le_log_iff_exp_le (div_pos hSb_pos hSa_pos)).mpr hge
  -- inner product bound
  have hinner : ⟪levelg lam eps f sg ℓ θ zs, θ' - θ⟫ ≤ lam * eps * s := by
    unfold levelg blockGrad
    rw [sum_inner]
    rw [hs, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [real_inner_smul_left]
    have hj := hsg θ (zs j) θ'
    have : ⟪sg θ (zs j), θ' - θ⟫ ≤ lam * eps * (b j - a j) := by
      rw [hb_def, ha_def]; simp only
      rw [← sub_div, mul_div_cancel₀ _ ha.ne']; linarith
    have hwj : Real.exp (f θ (zs j) / (lam * eps)) / ∑ k, Real.exp (f θ (zs k) / (lam * eps))
        = w j := rfl
    rw [hwj]
    calc w j * ⟪sg θ (zs j), θ' - θ⟫ ≤ w j * (lam * eps * (b j - a j)) :=
          mul_le_mul_of_nonneg_left this (hw0 j)
      _ = lam * eps * (w j * (b j - a j)) := by ring
  have hc : (0:ℝ) < ((2 : ℝ) ^ ℓ)⁻¹ := by positivity
  rw [Real.log_mul hc.ne' hSa_pos.ne', Real.log_mul hc.ne' hSb_pos.ne']
  nlinarith

end Aux_BSMDUE

open SinkhornDRO.BSMD Aux_BSMDUE in
theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf B : ℝ) (hA2I : Asm2Convex f) (hA2II : Asm2Lipschitz f Lf) (hA2III : Asm2Bounded Θ f B)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg) (hsg_meas : ∀ θ, Measurable (sg θ)) :
    (∀ (ℓ : ℕ), ∀ θ ∈ Θ,
      Integrable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => levelg lam eps f sg ℓ θ ζ.2)
          (levelLaw P Q (2 ^ ℓ)) ∧
        ∀ θ' ∈ Θ, objFℓ P Q lam eps f ℓ θ +
            ⟪∫ ζ, levelg lam eps f sg ℓ θ ζ.2 ∂(levelLaw P Q (2 ^ ℓ)), θ' - θ⟫
          ≤ objFℓ P Q lam eps f ℓ θ') ∧
    (∀ θ ∈ Θ,
      ∫ ζ, levelG lam eps f sg 0 θ ζ.2 ∂(levelLaw P Q (2 ^ 0))
        = ∫ ζ, levelg lam eps f sg 0 θ ζ.2 ∂(levelLaw P Q (2 ^ 0))) ∧
    (∀ (ℓ : ℕ), ∀ θ ∈ Θ,
      ∫ ζ, levelG lam eps f sg (ℓ + 1) θ ζ.2 ∂(levelLaw P Q (2 ^ (ℓ + 1)))
        = ∫ ζ, levelg lam eps f sg (ℓ + 1) θ ζ.2 ∂(levelLaw P Q (2 ^ (ℓ + 1)))
          - ∫ ζ, levelg lam eps f sg ℓ θ ζ.2 ∂(levelLaw P Q (2 ^ ℓ))) ∧
    (∀ (L : ℕ), 1 ≤ L → ∀ θ ∈ Θ,
      Integrable (vRT lam eps f sg L θ) (rtLaw P Q L) ∧
        ∫ ζ, vRT lam eps f sg L θ ζ ∂(rtLaw P Q L)
          = ∫ ζ, vSG lam eps f sg L θ ζ ∂(levelLaw P Q (2 ^ L))) := by
  have ha : 0 < lam * eps := mul_pos hlam heps
  -- integrability of block gradients
  have hbInt : ∀ (n : ℕ) (S : Finset (Fin n)) (θ : Param d),
      Integrable (fun ζ : Z × (Fin n → Z) => blockGrad lam eps f sg θ ζ.2 S) (levelLaw P Q n) := by
    intro n S θ
    have := levelLaw_prob P Q n
    exact Integrable.of_bound
      ((blockGradθ_meas lam eps f sg θ (hf_meas θ) (hsg_meas θ) S).comp
        measurable_snd).aestronglyMeasurable |Lf|
      (Filter.Eventually.of_forall fun ζ => blockGrad_norm_le lam eps f Lf hA2II sg hsg θ ζ.2 S)
  have hgInt : ∀ (ℓ : ℕ) (θ : Param d), Integrable
      (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => levelg lam eps f sg ℓ θ ζ.2) (levelLaw P Q (2 ^ ℓ)) :=
    fun ℓ θ => hbInt _ Finset.univ θ
  -- halves
  have hhalf : ∀ (ℓ : ℕ) (θ : Param d),
      (∫ ζ, blockGrad lam eps f sg θ ζ.2 (lowHalf ℓ) ∂(levelLaw P Q (2 ^ (ℓ + 1)))
        = ∫ ζ, levelg lam eps f sg ℓ θ ζ.2 ∂(levelLaw P Q (2 ^ ℓ))) ∧
      (∫ ζ, blockGrad lam eps f sg θ ζ.2 (highHalf ℓ) ∂(levelLaw P Q (2 ^ (ℓ + 1)))
        = ∫ ζ, levelg lam eps f sg ℓ θ ζ.2 ∂(levelLaw P Q (2 ^ ℓ))) := by
    intro ℓ θ
    have hgm : StronglyMeasurable (fun ζ' : Z × (Fin (2 ^ ℓ) → Z) => levelg lam eps f sg ℓ θ ζ'.2) :=
      ((blockGradθ_meas lam eps f sg θ (hf_meas θ) (hsg_meas θ) _).comp
        measurable_snd).stronglyMeasurable
    constructor
    · have hm := integral_marg P Q (embLow ℓ) (embLow ℓ).injective _ hgm
      dsimp only at hm
      rw [← hm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      simp only [lowHalf_eq, blockGrad_map]
      rfl
    · have hm := integral_marg P Q (embHigh ℓ) (embHigh ℓ).injective _ hgm
      dsimp only at hm
      rw [← hm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      simp only [highHalf_eq, blockGrad_map]
      rfl
  have hG3 : ∀ (ℓ : ℕ) (θ : Param d),
      ∫ ζ, levelG lam eps f sg (ℓ + 1) θ ζ.2 ∂(levelLaw P Q (2 ^ (ℓ + 1)))
        = ∫ ζ, levelg lam eps f sg (ℓ + 1) θ ζ.2 ∂(levelLaw P Q (2 ^ (ℓ + 1)))
          - ∫ ζ, levelg lam eps f sg ℓ θ ζ.2 ∂(levelLaw P Q (2 ^ ℓ)) := by
    intro ℓ θ
    have e : (fun ζ : Z × (Fin (2 ^ (ℓ + 1)) → Z) => levelG lam eps f sg (ℓ + 1) θ ζ.2)
        = fun ζ => levelg lam eps f sg (ℓ + 1) θ ζ.2
            - (1 / 2 : ℝ) • blockGrad lam eps f sg θ ζ.2 (lowHalf ℓ)
            - (1 / 2 : ℝ) • blockGrad lam eps f sg θ ζ.2 (highHalf ℓ) := rfl
    have i1 : Integrable (fun ζ : Z × (Fin (2 ^ (ℓ + 1)) → Z) =>
        (1 / 2 : ℝ) • blockGrad lam eps f sg θ ζ.2 (lowHalf ℓ)) (levelLaw P Q (2 ^ (ℓ + 1))) :=
      (hbInt (2 ^ (ℓ + 1)) (lowHalf ℓ) θ).smul (1 / 2 : ℝ)
    have i2 : Integrable (fun ζ : Z × (Fin (2 ^ (ℓ + 1)) → Z) =>
        (1 / 2 : ℝ) • blockGrad lam eps f sg θ ζ.2 (highHalf ℓ)) (levelLaw P Q (2 ^ (ℓ + 1))) :=
      (hbInt (2 ^ (ℓ + 1)) (highHalf ℓ) θ).smul (1 / 2 : ℝ)
    have i3 : Integrable (fun ζ : Z × (Fin (2 ^ (ℓ + 1)) → Z) =>
        levelg lam eps f sg (ℓ + 1) θ ζ.2 - (1 / 2 : ℝ) • blockGrad lam eps f sg θ ζ.2 (lowHalf ℓ))
        (levelLaw P Q (2 ^ (ℓ + 1))) := (hgInt (ℓ + 1) θ).sub i1
    rw [e, integral_sub i3 i2, integral_sub (hgInt (ℓ + 1) θ) i1, integral_smul, integral_smul,
      (hhalf ℓ θ).1, (hhalf ℓ θ).2, sub_sub, ← add_smul]
    norm_num
  refine ⟨?_, fun θ _ => rfl, fun ℓ θ _ => hG3 ℓ θ, ?_⟩
  · -- part 1
    intro ℓ θ hθ
    refine ⟨hgInt ℓ θ, fun θ' hθ' => ?_⟩
    have := levelLaw_prob P Q (2 ^ ℓ)
    have hUint : ∀ θ ∈ Θ, Integrable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) =>
        lam * eps * Real.log (((2 : ℝ) ^ ℓ)⁻¹ * ∑ j, Real.exp (f θ (ζ.2 j) / (lam * eps))))
        (levelLaw P Q (2 ^ ℓ)) := by
      intro θ hθ
      have hm : Measurable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) =>
          lam * eps * Real.log (((2 : ℝ) ^ ℓ)⁻¹ * ∑ j, Real.exp (f θ (ζ.2 j) / (lam * eps)))) := by
        refine ((Measurable.const_mul ?_ _).log).const_mul _
        exact Finset.measurable_sum _ (fun j _ => Real.measurable_exp.comp
          (((hf_meas θ).comp ((measurable_pi_apply j).comp measurable_snd)).div_const _))
      refine Integrable.of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall fun ζ => ?_)
      have hp : (0:ℝ) < 2 ^ ℓ := by positivity
      have hS1 : ((2:ℝ) ^ ℓ) ≤ ∑ j, Real.exp (f θ (ζ.2 j) / (lam * eps)) := by
        calc ((2:ℝ) ^ ℓ) = ∑ _j : Fin (2 ^ ℓ), (1:ℝ) := by simp
          _ ≤ _ := Finset.sum_le_sum (fun j _ => Real.one_le_exp
              (div_nonneg (hA2III θ hθ (ζ.2 j)).1 ha.le))
      have hS2 : ∑ j, Real.exp (f θ (ζ.2 j) / (lam * eps))
          ≤ ((2:ℝ) ^ ℓ) * Real.exp (B / (lam * eps)) := by
        calc ∑ j, Real.exp (f θ (ζ.2 j) / (lam * eps))
            ≤ ∑ _j : Fin (2 ^ ℓ), Real.exp (B / (lam * eps)) :=
              Finset.sum_le_sum (fun j _ => Real.exp_le_exp.mpr
                (div_le_div_of_nonneg_right (hA2III θ hθ (ζ.2 j)).2 ha.le))
          _ = _ := by simp
      set x := ((2 : ℝ) ^ ℓ)⁻¹ * ∑ j, Real.exp (f θ (ζ.2 j) / (lam * eps)) with hx
      have hx1 : 1 ≤ x := by
        rw [hx, ← div_eq_inv_mul, le_div_iff₀ hp]; linarith
      have hx2 : x ≤ Real.exp (B / (lam * eps)) := by
        rw [hx, ← div_eq_inv_mul, div_le_iff₀ hp]; linarith
      have l0 := Real.log_nonneg hx1
      have l1 := Real.log_le_log (by linarith) hx2
      rw [Real.log_exp] at l1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.le l0)]
      calc lam * eps * Real.log x ≤ lam * eps * (B / (lam * eps)) :=
            mul_le_mul_of_nonneg_left l1 ha.le
        _ = B := by field_simp
    unfold objFℓ
    rw [real_inner_comm, ← integral_inner (hgInt ℓ θ),
      ← integral_add (hUint θ hθ) ((hgInt ℓ θ).const_inner _)]
    refine integral_mono ((hUint θ hθ).add ((hgInt ℓ θ).const_inner _)) (hUint θ' hθ')
      (fun ζ => ?_)
    have := U_subgrad lam eps hlam heps f sg hsg ℓ θ θ' ζ.2
    rw [real_inner_comm] at this
    exact this
  · -- part 4
    intro L _ θ hθ
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
    have hint : Integrable (vRT lam eps f sg L θ) (rtLaw P Q L) :=
      Integrable.of_bound hvm.aestronglyMeasurable C (Filter.Eventually.of_forall hvb)
    refine ⟨hint, ?_⟩
    rw [rt_integralE P Q L _ hvm.stronglyMeasurable (fun ℓ => Integrable.of_bound
      (hvm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ζ => hvb _))]
    have hterm : ∀ ℓ : Fin (L + 1),
        levelProb L ℓ • ∫ ζ, vRT lam eps f sg L θ (ℓ, ζ) ∂(levelLaw P Q (2 ^ L))
          = ∫ ζ, levelG lam eps f sg ℓ θ ζ.2 ∂(levelLaw P Q (2 ^ (ℓ : ℕ))) := by
      intro ℓ
      have hp := levelProb_pos L ℓ
      have hle : 2 ^ (ℓ : ℕ) ≤ 2 ^ L :=
        Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp ℓ.isLt)
      have e1 : ∫ ζ, vRT lam eps f sg L θ (ℓ, ζ) ∂(levelLaw P Q (2 ^ L))
          = (levelProb L ℓ)⁻¹ • ∫ ζ, levelG lam eps f sg ℓ θ (ζ.2 ∘ Fin.castLE hle)
              ∂(levelLaw P Q (2 ^ L)) := by
        show ∫ ζ, (levelProb L ℓ)⁻¹ • levelG lam eps f sg ℓ θ (ζ.2 ∘ Fin.castLE hle)
          ∂(levelLaw P Q (2 ^ L)) = _
        exact integral_smul _ _
      rw [e1, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
      have hm := integral_marg P Q (Fin.castLE hle) (Fin.castLE_injective hle)
        (fun ζ' : Z × (Fin (2 ^ (ℓ : ℕ)) → Z) => levelG lam eps f sg ℓ θ ζ'.2)
        (((levelGθ_meas lam eps f sg θ (hf_meas θ) (hsg_meas θ) ℓ).comp
          measurable_snd).stronglyMeasurable)
      dsimp only at hm
      exact hm
    rw [Finset.sum_congr rfl (fun ℓ _ => hterm ℓ)]
    have hs := Fin.sum_univ_eq_sum_range
      (fun ℓ : ℕ => ∫ ζ, levelG lam eps f sg ℓ θ ζ.2 ∂(levelLaw P Q (2 ^ ℓ))) (L + 1)
    rw [hs, Finset.sum_range_succ', Finset.sum_congr rfl (fun ℓ _ => hG3 ℓ θ),
      Finset.sum_range_sub (fun ℓ : ℕ => ∫ ζ, levelg lam eps f sg ℓ θ ζ.2 ∂(levelLaw P Q (2 ^ ℓ)))]
    show _ = ∫ ζ, levelg lam eps f sg L θ ζ.2 ∂(levelLaw P Q (2 ^ L))
    have h0 : ∫ ζ, levelG lam eps f sg 0 θ ζ.2 ∂(levelLaw P Q (2 ^ 0))
        = ∫ ζ, levelg lam eps f sg 0 θ ζ.2 ∂(levelLaw P Q (2 ^ 0)) := rfl
    rw [h0]
    abel
