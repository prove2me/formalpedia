-- Prove2me | solution 1 for SinkhornDRO.BSMD.lemma_EC_6_III_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T06:21:31.124246+00:00
-- url     : https://prove2.me/submissions/18664eba-1c95-419b-b9cf-023d96072910

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_MirrorSetup
import Definitions.Def_SinkhornDRO_BSMD_Objective
import Definitions.Def_SinkhornDRO_BSMD_Estimators

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Aux_BSMD6b
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


/-- the kernel `x ↦ δ_x ⊗ Q_x^{⊗ n}` -/
noncomputable def kerN {Z : Type*} [MeasurableSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (n : ℕ) : Kernel Z (Z × (Fin n → Z)) :=
  ⟨fun x => (Measure.dirac x).prod (Measure.pi fun _ : Fin n => Q x), kern_meas Q n⟩

instance kerN_markov {Z : Type*} [MeasurableSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (n : ℕ) : IsMarkovKernel (kerN Q n) :=
  ⟨fun x => by unfold kerN; simp only [Kernel.coe_mk]; infer_instance⟩

lemma levelLaw_eq {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) :
    levelLaw P Q n = (kerN Q n ∘ₖ Kernel.const Unit P) () := by
  rw [Kernel.comp_apply, Kernel.const_apply]; rfl

lemma levelLaw_integral {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) (ψ : Z × (Fin n → Z) → ℝ)
    (hψm : StronglyMeasurable ψ) (hψ : Integrable ψ (levelLaw P Q n)) :
    ∫ ζ, ψ ζ ∂(levelLaw P Q n)
      = ∫ x, ∫ zs, ψ (x, zs) ∂(Measure.pi fun _ : Fin n => Q x) ∂P := by
  rw [levelLaw_eq] at hψ ⊢
  rw [ProbabilityTheory.Kernel.integral_comp hψ, Kernel.const_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ∫ y, ψ y ∂((Measure.dirac x).prod _) = _
  rw [Measure.dirac_prod, integral_map measurable_prodMk_left.aemeasurable
    hψm.aestronglyMeasurable]

lemma levelLaw_integrable_inner {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ)
    (ψ : Z × (Fin n → Z) → ℝ) (hψm : StronglyMeasurable ψ) (hψ : Integrable ψ (levelLaw P Q n)) :
    Integrable (fun x => ∫ zs, ψ (x, zs) ∂(Measure.pi fun _ : Fin n => Q x)) P := by
  rw [levelLaw_eq] at hψ
  have := hψ.integral_comp
  rw [Kernel.const_apply] at this
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  show ∫ y, ψ y ∂((Measure.dirac x).prod _) = _
  rw [Measure.dirac_prod, integral_map measurable_prodMk_left.aemeasurable
    hψm.aestronglyMeasurable]

lemma pi_coord_integral {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (i : Fin n) (φ : Z → ℝ) (hφ : Measurable φ) :
    ∫ zs, φ (zs i) ∂(Measure.pi fun _ : Fin n => μ) = ∫ z, φ z ∂μ := by
  have h := (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq
  conv_rhs => rw [← h]
  rw [integral_map (measurable_pi_apply i).aemeasurable hφ.aestronglyMeasurable]

lemma pi_pair_integral {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) (φ ψ : Z → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    ∫ zs, φ (zs i) * ψ (zs j) ∂(Measure.pi fun _ : Fin n => μ)
      = (∫ z, φ z ∂μ) * ∫ z, ψ z ∂μ := by
  have he : Function.Injective (![i, j] : Fin 2 → Fin n) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have hm : Measurable (fun zs : Fin n → Z => zs ∘ ![i, j]) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have h1 := integral_map hm.aemeasurable (μ := Measure.pi fun _ : Fin n => μ)
    (f := fun w : Fin 2 → Z => φ (w 0) * ψ (w 1))
    ((hφ.comp (measurable_pi_apply 0)).mul (hψ.comp (measurable_pi_apply 1))).aestronglyMeasurable
  rw [pi_marg μ _ he] at h1
  simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
  rw [← h1]
  have := integral_fin_nat_prod_eq_prod (μ := fun _ : Fin 2 => μ) (![φ, ψ] : Fin 2 → Z → ℝ)
  simpa [Fin.prod_univ_two] using this

lemma pi_var {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (σ : Fin n → ℝ) (φ : Z → ℝ) (hφ : Measurable φ) (R : ℝ) (hR : ∀ z, |φ z| ≤ R)
    (h0 : ∫ z, φ z ∂μ = 0) :
    ∫ zs, (∑ j, σ j * φ (zs j)) ^ 2 ∂(Measure.pi fun _ : Fin n => μ)
      = (∑ j, σ j ^ 2) * ∫ z, φ z ^ 2 ∂μ := by
  have hint : ∀ i j : Fin n, Integrable (fun zs : Fin n → Z => σ i * φ (zs i) * (σ j * φ (zs j)))
      (Measure.pi fun _ : Fin n => μ) := by
    intro i j
    refine Integrable.of_bound (((measurable_const.mul (hφ.comp (measurable_pi_apply i))).mul
      (measurable_const.mul (hφ.comp (measurable_pi_apply j))))).aestronglyMeasurable
      (|σ i| * R * (|σ j| * R)) (Filter.Eventually.of_forall fun zs => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have := hR (zs i); have := hR (zs j)
    have h0R : 0 ≤ R := (abs_nonneg _).trans (hR (zs i))
    gcongr
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j)),
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum _ (fun j _ => hint i j), Finset.sum_eq_single i]
  · have e : ∀ zs : Fin n → Z, σ i * φ (zs i) * (σ i * φ (zs i)) = σ i * σ i * (φ (zs i) * φ (zs i)) :=
      fun zs => by ring
    simp_rw [e]
    rw [integral_const_mul, pi_coord_integral μ i (fun z => φ z * φ z) (hφ.mul hφ)]
  · intro j _ hji
    have e : ∀ zs : Fin n → Z, σ i * φ (zs i) * (σ j * φ (zs j)) = σ i * σ j * (φ (zs i) * φ (zs j)) :=
      fun zs => by ring
    simp_rw [e]
    rw [integral_const_mul, pi_pair_integral μ i j (Ne.symm hji) φ φ hφ hφ, h0]
    ring
  · simp

/-- sign vector: `+1` on the low half, `-1` on the high half -/
noncomputable def sgnv (ℓ : ℕ) (j : Fin (2 ^ (ℓ + 1))) : ℝ := if j.val < 2 ^ ℓ then 1 else -1

lemma high_eq_filter_not (ℓ : ℕ) :
    highHalf ℓ = Finset.univ.filter (fun j : Fin (2 ^ (ℓ + 1)) => ¬ j.val < 2 ^ ℓ) := by
  unfold highHalf; ext j; simp [not_lt]

lemma sum_split {M : Type*} [AddCommMonoid M] (ℓ : ℕ) (u : Fin (2 ^ (ℓ + 1)) → M) :
    ∑ j, u j = ∑ j ∈ lowHalf ℓ, u j + ∑ j ∈ highHalf ℓ, u j := by
  rw [high_eq_filter_not]
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j.val < 2 ^ ℓ) u).symm

lemma card_low (ℓ : ℕ) : (lowHalf ℓ).card = 2 ^ ℓ := by
  rw [lowHalf_eq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma card_high (ℓ : ℕ) : (highHalf ℓ).card = 2 ^ ℓ := by
  rw [highHalf_eq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma sum_sgnv_mul (ℓ : ℕ) (u : Fin (2 ^ (ℓ + 1)) → ℝ) :
    ∑ j, sgnv ℓ j * u j = ∑ j ∈ lowHalf ℓ, u j - ∑ j ∈ highHalf ℓ, u j := by
  rw [sum_split ℓ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    have : j.val < 2 ^ ℓ := by simpa [lowHalf] using hj
    simp [sgnv, this]
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    have : ¬ j.val < 2 ^ ℓ := by rw [high_eq_filter_not] at hj; simpa using hj
    simp [sgnv, this]

lemma sum_sgnv (ℓ : ℕ) : ∑ j, sgnv ℓ j = 0 := by
  have := sum_sgnv_mul ℓ (fun _ => 1)
  simp only [mul_one] at this
  rw [this, Finset.sum_const, Finset.sum_const, card_low, card_high]
  simp

lemma sum_sgnv_sq (ℓ : ℕ) : ∑ j, sgnv ℓ j ^ 2 = 2 ^ (ℓ + 1) := by
  have : ∀ j, sgnv ℓ j ^ 2 = 1 := fun j => by unfold sgnv; split_ifs <;> norm_num
  simp [this]

lemma G_pointwise {d : ℕ} {Z : Type*} (lam eps : ℝ) (f : Param d → Z → ℝ) (Lf : ℝ)
    (hA2II : Asm2Lipschitz f Lf) (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg)
    (θ : Param d) (ℓ : ℕ) (zs : Fin (2 ^ (ℓ + 1)) → Z)
    (hone : ∀ j, 1 ≤ Real.exp (f θ (zs j) / (lam * eps))) :
    ‖levelG lam eps f sg (ℓ + 1) θ zs‖
      ≤ |Lf| * |∑ j, sgnv ℓ j * Real.exp (f θ (zs j) / (lam * eps))| / 2 ^ (ℓ + 1) := by
  set e : Fin (2 ^ (ℓ + 1)) → ℝ := fun j => Real.exp (f θ (zs j) / (lam * eps)) with he
  have hbg : ∀ S' : Finset (Fin (2 ^ (ℓ + 1))), blockGrad lam eps f sg θ zs S'
      = ∑ j ∈ S', (e j / ∑ k ∈ S', e k) • sg θ (zs j) := fun S' => rfl
  set SL := ∑ j ∈ lowHalf ℓ, e j with hSL
  set SH := ∑ j ∈ highHalf ℓ, e j with hSH
  set S := ∑ j, e j with hSdef
  have hS : S = SL + SH := sum_split ℓ e
  have hSL1 : (2:ℝ) ^ ℓ ≤ SL := by
    have := Finset.card_nsmul_le_sum (lowHalf ℓ) e 1 (fun j _ => hone j)
    rw [card_low, nsmul_eq_mul, mul_one] at this; exact_mod_cast this
  have hSH1 : (2:ℝ) ^ ℓ ≤ SH := by
    have := Finset.card_nsmul_le_sum (highHalf ℓ) e 1 (fun j _ => hone j)
    rw [card_high, nsmul_eq_mul, mul_one] at this; exact_mod_cast this
  have hp : (0:ℝ) < 2 ^ ℓ := by positivity
  have hSLp : 0 < SL := lt_of_lt_of_le hp hSL1
  have hSHp : 0 < SH := lt_of_lt_of_le hp hSH1
  have hSp : 0 < S := by rw [hS]; linarith
  have hS2 : (2:ℝ) ^ (ℓ + 1) ≤ S := by rw [hS, pow_succ]; linarith
  set α := 1 / S - 1 / (2 * SL) with hα
  set β := 1 / S - 1 / (2 * SH) with hβ
  have hG : levelG lam eps f sg (ℓ + 1) θ zs
      = ∑ j ∈ lowHalf ℓ, (e j * α) • sg θ (zs j) + ∑ j ∈ highHalf ℓ, (e j * β) • sg θ (zs j) := by
    show blockGrad lam eps f sg θ zs Finset.univ
        - (1 / 2 : ℝ) • blockGrad lam eps f sg θ zs (lowHalf ℓ)
        - (1 / 2 : ℝ) • blockGrad lam eps f sg θ zs (highHalf ℓ) = _
    rw [hbg, hbg, hbg, sum_split ℓ (fun j => (e j / ∑ k, e k) • sg θ (zs j))]
    rw [← hSL, ← hSH, ← hSdef]
    have h1 : ∑ j ∈ lowHalf ℓ, (e j / S) • sg θ (zs j)
        - (1 / 2 : ℝ) • ∑ j ∈ lowHalf ℓ, (e j / SL) • sg θ (zs j)
        = ∑ j ∈ lowHalf ℓ, (e j * α) • sg θ (zs j) := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_smul, ← sub_smul, hα]; congr 1; ring
    have h2 : ∑ j ∈ highHalf ℓ, (e j / S) • sg θ (zs j)
        - (1 / 2 : ℝ) • ∑ j ∈ highHalf ℓ, (e j / SH) • sg θ (zs j)
        = ∑ j ∈ highHalf ℓ, (e j * β) • sg θ (zs j) := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_smul, ← sub_smul, hβ]; congr 1; ring
    rw [← h1, ← h2]
    abel
  have hnorm : ∀ (T : Finset (Fin (2 ^ (ℓ + 1)))) (c : ℝ),
      ‖∑ j ∈ T, (e j * c) • sg θ (zs j)‖ ≤ |c| * (∑ j ∈ T, e j) * |Lf| := by
    intro T c
    calc ‖∑ j ∈ T, (e j * c) • sg θ (zs j)‖ ≤ ∑ j ∈ T, ‖(e j * c) • sg θ (zs j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ T, (e j * |c|) * |Lf| := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left (sg_bound f Lf hA2II sg hsg θ (zs j))
            (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
      _ = |c| * (∑ j ∈ T, e j) * |Lf| := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          ring
  have hαS : |α| * SL = |SL - SH| / (2 * S) := by
    rw [← abs_of_pos hSLp, ← abs_mul, abs_of_pos hSLp,
      show α * SL = (SL - SH) / (2 * S) by rw [hα, hS]; field_simp; ring,
      abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * S)]
  have hβS : |β| * SH = |SL - SH| / (2 * S) := by
    rw [← abs_of_pos hSHp, ← abs_mul, abs_of_pos hSHp,
      show β * SH = (SH - SL) / (2 * S) by rw [hβ, hS]; field_simp; ring,
      abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * S), abs_sub_comm]
  rw [hG, sum_sgnv_mul ℓ e, ← hSL, ← hSH]
  calc ‖∑ j ∈ lowHalf ℓ, (e j * α) • sg θ (zs j) + ∑ j ∈ highHalf ℓ, (e j * β) • sg θ (zs j)‖
      ≤ |α| * SL * |Lf| + |β| * SH * |Lf| := (norm_add_le _ _).trans (add_le_add (hnorm _ _) (hnorm _ _))
    _ = |Lf| * |SL - SH| / S := by rw [hαS, hβS]; field_simp; ring
    _ ≤ |Lf| * |SL - SH| / 2 ^ (ℓ + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hS2

end Aux_BSMD6b

open SinkhornDRO.BSMD Aux_BSMD6b in
theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf B : ℝ) (hA2I : Asm2Convex f) (hA2II : Asm2Lipschitz f Lf) (hA2III : Asm2Bounded Θ f B)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg) (hsg_meas : ∀ θ, Measurable (sg θ))
    (ℓ : ℕ) :
    ∀ θ ∈ Θ,
      Integrable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2)
          (levelLaw P Q (2 ^ ℓ)) ∧
        ∫ ζ, ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ ℓ))
          ≤ Lf ^ 2 * Real.exp (4 * (B / (lam * eps))) * ((2 : ℝ) ^ ℓ)⁻¹ := by
  intro θ hθ
  have := levelLaw_prob P Q (2 ^ ℓ)
  have ha : 0 < lam * eps := mul_pos hlam heps
  obtain ⟨z0⟩ := nonempty_of_isProbabilityMeasure P
  have hB : 0 ≤ B := (hA2III θ hθ z0).1.trans (hA2III θ hθ z0).2
  have hK : 0 ≤ B / (lam * eps) := div_nonneg hB ha.le
  have hGm : Measurable (fun zs : Fin (2 ^ ℓ) → Z => levelG lam eps f sg ℓ θ zs) :=
    levelGθ_meas lam eps f sg θ (hf_meas θ) (hsg_meas θ) ℓ
  have hGb : ∀ zs, ‖levelG lam eps f sg ℓ θ zs‖ ^ 2 ≤ (2 * |Lf|) ^ 2 := fun zs =>
    pow_le_pow_left₀ (norm_nonneg _) (levelG_norm_le lam eps f Lf hA2II sg hsg ℓ θ zs) 2
  have hint : Integrable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => ‖levelG lam eps f sg ℓ θ ζ.2‖ ^ 2)
      (levelLaw P Q (2 ^ ℓ)) := by
    refine Integrable.of_bound ((hGm.comp measurable_snd).norm.pow_const 2).aestronglyMeasurable
      ((2 * |Lf|) ^ 2) (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hGb ζ.2
  refine ⟨hint, ?_⟩
  cases ℓ with
  | zero =>
    have hpt : ∀ ζ : Z × (Fin (2 ^ 0) → Z), ‖levelG lam eps f sg 0 θ ζ.2‖ ^ 2 ≤ Lf ^ 2 := by
      intro ζ
      rw [← sq_abs Lf]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (blockGrad_norm_le lam eps f Lf hA2II sg hsg θ ζ.2 _) 2
    calc ∫ ζ, ‖levelG lam eps f sg 0 θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ 0))
        ≤ ∫ _ζ, Lf ^ 2 ∂(levelLaw P Q (2 ^ 0)) := integral_mono hint (integrable_const _) hpt
      _ = Lf ^ 2 := by simp
      _ ≤ Lf ^ 2 * Real.exp (4 * (B / (lam * eps))) * ((2 : ℝ) ^ 0)⁻¹ := by
          rw [pow_zero, inv_one, mul_one]
          exact le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by positivity))
  | succ ℓ =>
    set E := Real.exp (B / (lam * eps)) with hE
    have he1 : ∀ z, 1 ≤ Real.exp (f θ z / (lam * eps)) := fun z =>
      Real.one_le_exp (div_nonneg (hA2III θ hθ z).1 ha.le)
    have heE : ∀ z, Real.exp (f θ z / (lam * eps)) ≤ E := fun z =>
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hA2III θ hθ z).2 ha.le)
    have hem : Measurable (fun z => Real.exp (f θ z / (lam * eps))) :=
      Real.measurable_exp.comp ((hf_meas θ).div_const _)
    rw [levelLaw_integral P Q _ (fun ζ => ‖levelG lam eps f sg (ℓ + 1) θ ζ.2‖ ^ 2)
      ((hGm.comp measurable_snd).norm.pow_const 2).stronglyMeasurable hint]
    have hinner : ∀ x, ∫ zs, ‖levelG lam eps f sg (ℓ + 1) θ (x, zs).2‖ ^ 2
        ∂(Measure.pi fun _ : Fin (2 ^ (ℓ + 1)) => Q x)
          ≤ Lf ^ 2 * Real.exp (4 * (B / (lam * eps))) * ((2 : ℝ) ^ (ℓ + 1))⁻¹ := by
      intro x
      set m := ∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x) with hm
      have heI : Integrable (fun z => Real.exp (f θ z / (lam * eps))) (Q x) := by
        refine Integrable.of_bound hem.aestronglyMeasurable E
          (Filter.Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact heE z
      have hm1 : 1 ≤ m := by
        have := integral_mono (integrable_const 1) heI he1
        simpa using this
      have hmE : m ≤ E := by
        have := integral_mono heI (integrable_const E) heE
        simpa using this
      set φ : Z → ℝ := fun z => Real.exp (f θ z / (lam * eps)) - m with hφ
      have hφm : Measurable φ := hem.sub measurable_const
      have hφ0 : ∫ z, φ z ∂(Q x) = 0 := by
        rw [hφ, integral_sub heI (integrable_const _)]; simp [← hm]
      have hφR : ∀ z, |φ z| ≤ E := by
        intro z
        rw [abs_le]
        have := he1 z; have := heE z
        constructor <;> simp only [hφ] <;> linarith
      have hvar := pi_var (Q x) (sgnv ℓ) φ hφm E hφR hφ0
      rw [sum_sgnv_sq] at hvar
      have hpt : ∀ zs : Fin (2 ^ (ℓ + 1)) → Z, ‖levelG lam eps f sg (ℓ + 1) θ zs‖ ^ 2
          ≤ Lf ^ 2 / ((2:ℝ) ^ (ℓ + 1)) ^ 2 * (∑ j, sgnv ℓ j * φ (zs j)) ^ 2 := by
        intro zs
        have h1 := G_pointwise lam eps f Lf hA2II sg hsg θ ℓ zs (fun j => he1 _)
        have hs : ∑ j, sgnv ℓ j * Real.exp (f θ (zs j) / (lam * eps))
            = ∑ j, sgnv ℓ j * φ (zs j) := by
          have : ∑ j, sgnv ℓ j * φ (zs j)
              = ∑ j, sgnv ℓ j * Real.exp (f θ (zs j) / (lam * eps)) - (∑ j, sgnv ℓ j) * m := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [hφ]; ring
          rw [this, sum_sgnv]; ring
        rw [hs] at h1
        calc ‖levelG lam eps f sg (ℓ + 1) θ zs‖ ^ 2
            ≤ (|Lf| * |∑ j, sgnv ℓ j * φ (zs j)| / 2 ^ (ℓ + 1)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ = _ := by rw [div_pow, mul_pow, sq_abs, sq_abs]; ring
      have hsm : Measurable (fun zs : Fin (2 ^ (ℓ + 1)) → Z => (∑ j, sgnv ℓ j * φ (zs j)) ^ 2) :=
        (Finset.measurable_sum _ (fun j _ =>
          measurable_const.mul (hφm.comp (measurable_pi_apply j)))).pow_const 2
      have hsb : ∀ zs : Fin (2 ^ (ℓ + 1)) → Z,
          (∑ j, sgnv ℓ j * φ (zs j)) ^ 2 ≤ (∑ j : Fin (2 ^ (ℓ + 1)), |sgnv ℓ j| * E) ^ 2 := by
        intro zs
        rw [← sq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hφR _) (abs_nonneg _)
      have hI2 : Integrable (fun zs : Fin (2 ^ (ℓ + 1)) → Z => (∑ j, sgnv ℓ j * φ (zs j)) ^ 2)
          (Measure.pi fun _ : Fin (2 ^ (ℓ + 1)) => Q x) := by
        refine Integrable.of_bound hsm.aestronglyMeasurable
          ((∑ j : Fin (2 ^ (ℓ + 1)), |sgnv ℓ j| * E) ^ 2)
          (Filter.Eventually.of_forall fun zs => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsb zs
      have hI1 : Integrable (fun zs : Fin (2 ^ (ℓ + 1)) → Z =>
          ‖levelG lam eps f sg (ℓ + 1) θ zs‖ ^ 2) (Measure.pi fun _ : Fin (2 ^ (ℓ + 1)) => Q x) := by
        refine Integrable.of_bound (hGm.norm.pow_const 2).aestronglyMeasurable ((2 * |Lf|) ^ 2)
          (Filter.Eventually.of_forall fun zs => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hGb zs
      have hφ2 : ∫ z, φ z ^ 2 ∂(Q x) ≤ E ^ 2 := by
        have hb : ∀ z, φ z ^ 2 ≤ E ^ 2 := fun z => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hφR z) 2
        have := integral_mono (Integrable.of_bound (μ := Q x) (hφm.pow_const 2).aestronglyMeasurable (E ^ 2)
          (Filter.Eventually.of_forall fun z => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb z))
          (integrable_const (E ^ 2)) hb
        simpa using this
      have hE2 : E ^ 2 ≤ Real.exp (4 * (B / (lam * eps))) := by
        rw [hE, ← Real.exp_nat_mul]; push_cast
        exact Real.exp_le_exp.mpr (by nlinarith)
      have hp : (0:ℝ) < 2 ^ (ℓ + 1) := by positivity
      calc ∫ zs, ‖levelG lam eps f sg (ℓ + 1) θ (x, zs).2‖ ^ 2
            ∂(Measure.pi fun _ : Fin (2 ^ (ℓ + 1)) => Q x)
          ≤ ∫ zs, Lf ^ 2 / ((2:ℝ) ^ (ℓ + 1)) ^ 2 * (∑ j, sgnv ℓ j * φ (zs j)) ^ 2
            ∂(Measure.pi fun _ : Fin (2 ^ (ℓ + 1)) => Q x) :=
            integral_mono hI1 (hI2.const_mul _) hpt
        _ = Lf ^ 2 / ((2:ℝ) ^ (ℓ + 1)) ^ 2 * ((2:ℝ) ^ (ℓ + 1) * ∫ z, φ z ^ 2 ∂(Q x)) := by
            rw [integral_const_mul, hvar]
        _ ≤ Lf ^ 2 / ((2:ℝ) ^ (ℓ + 1)) ^ 2 * ((2:ℝ) ^ (ℓ + 1) * Real.exp (4 * (B / (lam * eps)))) := by
            gcongr; exact hφ2.trans hE2
        _ = Lf ^ 2 * Real.exp (4 * (B / (lam * eps))) * ((2 : ℝ) ^ (ℓ + 1))⁻¹ := by
            field_simp
    calc ∫ x, ∫ zs, ‖levelG lam eps f sg (ℓ + 1) θ (x, zs).2‖ ^ 2
          ∂(Measure.pi fun _ : Fin (2 ^ (ℓ + 1)) => Q x) ∂P
        ≤ ∫ _x, Lf ^ 2 * Real.exp (4 * (B / (lam * eps))) * ((2 : ℝ) ^ (ℓ + 1))⁻¹ ∂P :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
            integral_nonneg (fun zs => sq_nonneg _)) (integrable_const _)
            (Filter.Eventually.of_forall hinner)
      _ = _ := by simp
