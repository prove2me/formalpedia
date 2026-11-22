-- Prove2me | solution 1 for RobustOpt2009.MatrixChance.borell_enlargement_B_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T21:16:30.738791+00:00
-- url     : https://prove2.me/submissions/4b241409-45bc-4d68-ab0c-5de1f428091c

import Definitions.Def_RobustOpt2009_MatrixChance_Setting
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Theorems.Thm_RobustOpt2009_MatrixChance_gaussian_smooth_approximation
import Theorems.Thm_RobustOpt2009_MatrixChance_bobkov_smooth_gaussian

open MeasureTheory ProbabilityTheory RobustOpt2009.MatrixChance Filter Topology Set
open scoped BigOperators RealInnerProductSpace NNReal ENNReal

namespace BorellProof

open OAI.GaussianPropeller.Quantile
/-! ### Section 1: Linking `normalTail`, `tailQuantile` with `φ`, `Φ`, `q`, `I` -/

private lemma gaussianPDFReal_zero_one_eq_φ (x : ℝ) : gaussianPDFReal 0 1 x = φ x := by
  simp [gaussianPDFReal, φ, neg_div]

private lemma normalTail_coe (t : ℝ) : normalTail (t : EReal) = 1 - Φ t := by
  unfold normalTail
  have hset : {x : ℝ | (t : EReal) < (x : EReal)} = Ioi t := by
    ext x
    simp [EReal.coe_lt_coe_iff]
  rw [hset, gaussianReal_apply_eq_integral 0 one_ne_zero (Ioi t)]
  have hnn : 0 ≤ ∫ x in Ioi t, gaussianPDFReal 0 1 x :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => gaussianPDFReal_nonneg 0 1 x
  rw [ENNReal.toReal_ofReal hnn]
  have heq : (∫ x in Ioi t, gaussianPDFReal 0 1 x) = ∫ x in Ioi t, φ x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    exact gaussianPDFReal_zero_one_eq_φ x
  rw [heq, Φ_eq_one_sub_tail]
  ring

private lemma normalTail_top : normalTail (⊤ : EReal) = 0 := by
  unfold normalTail
  simp

private lemma normalTail_bot : normalTail (⊥ : EReal) = 1 := by
  unfold normalTail
  have hset : {x : ℝ | (⊥ : EReal) < (x : EReal)} = univ := by
    ext x
    simp [EReal.bot_lt_coe]
  rw [hset]
  simp

private lemma Φ_q {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : Φ (q p) = p := by
  unfold q
  rw [dif_pos hp]
  have h := cdfIso.apply_symm_apply ⟨p, hp⟩
  exact congrArg Subtype.val h

private lemma q_Φ (x : ℝ) : q (Φ x) = x := by
  have hmem : Φ x ∈ Ioo (0 : ℝ) 1 := by
    rw [← range_Φ]
    exact mem_range_self x
  unfold q
  rw [dif_pos hmem]
  have h : (⟨Φ x, hmem⟩ : Ioo (0 : ℝ) 1) = cdfIso x := rfl
  rw [h]
  exact cdfIso.symm_apply_apply x

private lemma q_le_iff {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (t : ℝ) : q p ≤ t ↔ p ≤ Φ t := by
  rw [← strictMono_Φ.le_iff_le, Φ_q hp]

private lemma le_q_iff {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (t : ℝ) : t ≤ q p ↔ Φ t ≤ p := by
  rw [← strictMono_Φ.le_iff_le, Φ_q hp]

private lemma q_mono {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) : q a ≤ q b := by
  rw [q_le_iff ha, Φ_q hb]
  exact hab

private lemma tailQuantile_one_sub {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    tailQuantile (1 - α) = (q α : EReal) := by
  unfold tailQuantile
  have hset : {t : EReal | normalTail t ≤ 1 - α} = Ici (q α : EReal) := by
    ext t
    cases t using EReal.rec with
    | bot =>
      simp only [mem_ofPred_eq, normalTail_bot, mem_Ici, le_bot_iff, EReal.coe_ne_bot, iff_false,
        not_le]
      linarith
    | top =>
      simp only [mem_ofPred_eq, normalTail_top, mem_Ici, le_top, iff_true]
      linarith
    | coe r =>
      simp only [mem_ofPred_eq, normalTail_coe, mem_Ici, EReal.coe_le_coe_iff]
      rw [q_le_iff ⟨hα0, hα1⟩]
      constructor <;> intro h <;> linarith
  rw [hset, csInf_Ici]

/-! ### Section 2: Calculus of `q` and `I` on `(0, 1)` -/

private lemma I_pos (p : ℝ) : 0 < I p := φ_pos (q p)

private lemma I_Φ (x : ℝ) : I (Φ x) = φ x := by
  rw [I, q_Φ]

private lemma continuousOn_q : ContinuousOn q (Ioo (0 : ℝ) 1) := by
  have hhomeo : Continuous (fun y : Ioo (0 : ℝ) 1 => (cdfIso.toHomeomorph.symm y : ℝ)) :=
    cdfIso.toHomeomorph.symm.continuous
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (Ioo (0 : ℝ) 1).domRestrict q = fun y : Ioo (0 : ℝ) 1 => cdfIso.toHomeomorph.symm y := by
    ext y
    simp [Set.domRestrict, q, y.2, OrderIso.toHomeomorph]
  rw [heq]
  exact hhomeo

private lemma hasDerivAt_q {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : HasDerivAt q (I p)⁻¹ p := by
  have hcont : ContinuousAt q p :=
    continuousOn_q.continuousAt (Ioo_mem_nhds hp.1 hp.2)
  have hΦ : HasDerivAt Φ (I p) (q p) := by
    simpa [I] using hasDerivAt_Φ (q p)
  have hinv : ∀ᶠ y in 𝓝 p, Φ (q y) = y := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with y hy
    exact Φ_q hy
  exact hΦ.of_local_left_inverse hcont (ne_of_gt (I_pos p)) hinv

private lemma hasDerivAt_I {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : HasDerivAt I (-q p) p := by
  have hcomp : HasDerivAt I (-q p * φ (q p) * (I p)⁻¹) p :=
    (hasDerivAt_φ (q p)).comp p (hasDerivAt_q hp)
  refine hcomp.congr_deriv ?_
  have hne : φ (q p) ≠ 0 := ne_of_gt (φ_pos (q p))
  unfold I
  field_simp [hne]

private lemma hasDerivAt_I_sq {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => I x ^ 2) (-2 * q p * I p) p := by
  refine ((hasDerivAt_I hp).pow 2).congr_deriv ?_
  norm_num
  ring

private lemma hasDerivAt_neg_q_mul_I {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => -(q x * I x)) (q p ^ 2 - 1) p := by
  refine (((hasDerivAt_q hp).mul (hasDerivAt_I hp)).neg).congr_deriv ?_
  have hne : I p ≠ 0 := ne_of_gt (I_pos p)
  field_simp [hne]
  ring

private lemma φ_le_one (x : ℝ) : φ x ≤ 1 := by
  unfold φ
  have hpi : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.one_le_sqrt]
    linarith [Real.pi_gt_three]
  have h1 : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
  have h2 : Real.exp (-x ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg x]
  nlinarith [Real.exp_pos (-x ^ 2 / 2), inv_pos.mpr (lt_of_lt_of_le zero_lt_one hpi)]

private lemma abs_q_le_on_Icc {η p : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 - η)
    (hp : p ∈ Icc η (1 - η)) : |q p| ≤ max |q η| |q (1 - η)| := by
  have hη_mem : η ∈ Ioo (0 : ℝ) 1 := ⟨hη0, by linarith⟩
  have h1η_mem : 1 - η ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hp_mem : p ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hη0 hp.1, lt_of_le_of_lt hp.2 (by linarith)⟩
  have hlo : q η ≤ q p := q_mono hη_mem hp_mem hp.1
  have hhi : q p ≤ q (1 - η) := q_mono hp_mem h1η_mem hp.2
  rw [abs_le]
  constructor
  · exact le_trans (neg_le_neg (le_max_left _ _)) (le_trans (neg_abs_le _) hlo)
  · exact le_trans hhi (le_trans (le_abs_self _) (le_max_right _ _))

private lemma φ_ge_on_Icc {η p : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 - η)
    (hp : p ∈ Icc η (1 - η)) : φ (max |q η| |q (1 - η)|) ≤ I p := by
  set Q := max |q η| |q (1 - η)|
  have habs : |q p| ≤ Q := abs_q_le_on_Icc hη0 hη1 hp
  have hsq : q p ^ 2 ≤ Q ^ 2 := by
    have hQ : 0 ≤ Q := le_trans (abs_nonneg _) (le_max_left _ _)
    nlinarith [sq_abs (q p), abs_nonneg (q p)]
  unfold I φ
  gcongr

private lemma norm_smulRight_le {E' V : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E' →L[ℝ] ℝ) (v : V) :
    ‖L.smulRight v‖ ≤ ‖L‖ * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul, Real.norm_eq_abs]
  calc |L x| * ‖v‖ ≤ (‖L‖ * ‖x‖) * ‖v‖ := by gcongr; exact ContinuousLinearMap.le_opNorm L x
    _ = ‖L‖ * ‖v‖ * ‖x‖ := by ring

private lemma hasFDerivAt_congr_deriv {E' V : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : E' → V} {L₁ L₂ : E' →L[ℝ] V} {x : E'}
    (h : HasFDerivAt f L₁ x) (heq : L₁ = L₂) : HasFDerivAt f L₂ x :=
  heq ▸ h
private lemma continuous_clm_add_sub_sub {α E' W : Type*} [TopologicalSpace α]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {a b c d : α → (E' →L[ℝ] W)}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous (fun x => (a x + b x) - c x - d x) :=
  ((ha.add hb).sub hc).sub hd

private lemma norm_smul_clm {E' W : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup W] [NormedSpace ℝ W] (c : ℝ) (T : E' →L[ℝ] W) :
    ‖c • T‖ = |c| * ‖T‖ := by
  rw [norm_smul, Real.norm_eq_abs]

private lemma norm_clm_add_sub_sub_le {E' W : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup W] [NormedSpace ℝ W] (a b c d : E' →L[ℝ] W) :
    ‖(a + b) - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  calc ‖(a + b) - c - d‖ ≤ ‖(a + b) - c‖ + ‖d‖ := norm_sub_le _ _
    _ ≤ ‖a + b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _
/-! ### Section 4: Smooth `C³_b` functions valued in `[η, 1 - η]` -/

private structure SmoothC3Bounded (m : ℕ) where
  f : EuclideanSpace ℝ (Fin m) → ℝ
  g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)
  K : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
  M : EuclideanSpace ℝ (Fin m) →
    (EuclideanSpace ℝ (Fin m) →L[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
  η : ℝ
  hη_pos : 0 < η
  hη_le : η ≤ 1 - η
  hf_mem : ∀ x, f x ∈ Icc η (1 - η)
  hf_deriv : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x
  hg_deriv : ∀ x, HasFDerivAt g (K x) x
  hK_deriv : ∀ x, HasFDerivAt K (M x) x
  hM_cont : Continuous M
  hK_symm : ∀ x v w, ⟪K x v, w⟫ = ⟪v, K x w⟫
  Cg : ℝ
  CK : ℝ
  CM : ℝ
  hCg_nn : 0 ≤ Cg
  hCK_nn : 0 ≤ CK
  hCM_nn : 0 ≤ CM
  hg_bound : ∀ x, ‖g x‖ ≤ Cg
  hK_bound : ∀ x, ‖K x‖ ≤ CK
  hM_bound : ∀ x, ‖M x‖ ≤ CM

private noncomputable def rankOne {m : ℕ} (gh : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (innerSL ℝ (gh x)).smulRight (gh x)

private noncomputable def rankOneDeriv {m : ℕ}
    (gh : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (Kh : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
  let E := EuclideanSpace ℝ (Fin m)
  let toDualCLM : E →L[ℝ] (E →L[ℝ] ℝ) := (InnerProductSpace.toDual ℝ E).toContinuousLinearMap
  ((ContinuousLinearMap.smulRightL ℝ E E).flip (gh x)).comp (toDualCLM.comp (Kh x))
  + (ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ (gh x))).comp (Kh x)

private lemma hasFDerivAt_rankOne {m : ℕ}
    {gh : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {Kh : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    (hgh_deriv : ∀ x, HasFDerivAt gh (Kh x) x) (x : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (rankOne gh) (rankOneDeriv gh Kh x) x := by
  let E := EuclideanSpace ℝ (Fin m)
  let toDualCLM : E →L[ℝ] (E →L[ℝ] ℝ) := (InnerProductSpace.toDual ℝ E).toContinuousLinearMap
  have h1 : HasFDerivAt (fun y => innerSL ℝ (gh y)) (toDualCLM.comp (Kh x)) x :=
    toDualCLM.hasFDerivAt.comp x (hgh_deriv x)
  have h2 := (ContinuousLinearMap.smulRightL ℝ E E).isBoundedBilinearMap.hasFDerivAt
    (innerSL ℝ (gh x), gh x)
  have h3 := h2.comp x (h1.prodMk (hgh_deriv x))
  refine hasFDerivAt_congr_deriv h3 ?_
  ext v w
  simp [rankOneDeriv, toDualCLM, IsBoundedBilinearMap.deriv_apply]
  exact add_comm _ _

private lemma continuous_rankOneDeriv {m : ℕ}
    {gh : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {Kh : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    (hgh_cont : Continuous gh) (hKh_cont : Continuous Kh) :
    Continuous (rankOneDeriv gh Kh) := by
  let E := EuclideanSpace ℝ (Fin m)
  let toDualCLM : E →L[ℝ] (E →L[ℝ] ℝ) := (InnerProductSpace.toDual ℝ E).toContinuousLinearMap
  have h1 : Continuous (fun x => (ContinuousLinearMap.smulRightL ℝ E E).flip (gh x)) :=
    (ContinuousLinearMap.smulRightL ℝ E E).flip.continuous.comp hgh_cont
  have h2 : Continuous (fun x => toDualCLM.comp (Kh x)) :=
    (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ) toDualCLM).continuous.comp hKh_cont
  have h3 : Continuous (fun x => ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ (gh x))) :=
    (ContinuousLinearMap.smulRightL ℝ E E).continuous.comp ((innerSL ℝ).continuous.comp hgh_cont)
  exact (h1.clm_comp h2).add (h3.clm_comp hKh_cont)

private lemma norm_rankOneDeriv_le {m : ℕ}
    {gh : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {Kh : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    {Cgh CKh : ℝ} (hCgh : 0 ≤ Cgh) (hCKh : 0 ≤ CKh)
    (hgh_bound : ∀ x, ‖gh x‖ ≤ Cgh) (hKh_bound : ∀ x, ‖Kh x‖ ≤ CKh)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖rankOneDeriv gh Kh x‖ ≤ 2 * Cgh * CKh := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have heval : rankOneDeriv gh Kh x v w = ⟪Kh x v, w⟫ • gh x + ⟪gh x, w⟫ • Kh x v := by
    simp [rankOneDeriv]
  rw [heval]
  calc ‖⟪Kh x v, w⟫ • gh x + ⟪gh x, w⟫ • Kh x v‖
      ≤ ‖⟪Kh x v, w⟫ • gh x‖ + ‖⟪gh x, w⟫ • Kh x v‖ := norm_add_le _ _
    _ = |⟪Kh x v, w⟫| * ‖gh x‖ + |⟪gh x, w⟫| * ‖Kh x v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (‖Kh x v‖ * ‖w‖) * ‖gh x‖ + (‖gh x‖ * ‖w‖) * ‖Kh x v‖ := by
        gcongr
        · exact abs_real_inner_le_norm _ _
        · exact abs_real_inner_le_norm _ _
    _ ≤ ((CKh * ‖v‖) * ‖w‖) * Cgh + (Cgh * ‖w‖) * (CKh * ‖v‖) := by
        have hKv : ‖Kh x v‖ ≤ CKh * ‖v‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hKh_bound x)
        gcongr <;> exact hgh_bound x
    _ = 2 * Cgh * CKh * ‖v‖ * ‖w‖ := by ring

private noncomputable def phiCompM {m : ℕ}
    (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (gh : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (Kh : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (Mh : EuclideanSpace ℝ (Fin m) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))))
    (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
  (((-h x * φ (h x)) • innerSL ℝ (gh x)).smulRight (Kh x) + φ (h x) • Mh x)
  - (((1 - h x ^ 2) * φ (h x)) • innerSL ℝ (gh x)).smulRight (rankOne gh x)
  - (h x * φ (h x)) • rankOneDeriv gh Kh x

private lemma continuous_phiCompM {m : ℕ}
    {h : EuclideanSpace ℝ (Fin m) → ℝ}
    {gh : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {Kh : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    {Mh : EuclideanSpace ℝ (Fin m) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))}
    (hh_cont : Continuous h) (hgh_cont : Continuous gh)
    (hKh_cont : Continuous Kh) (hMh_cont : Continuous Mh)
    (hR1_cont : Continuous (rankOne gh)) (hDR1_cont : Continuous (rankOneDeriv gh Kh)) :
    Continuous (phiCompM h gh Kh Mh) := by
  let E := EuclideanSpace ℝ (Fin m)
  have hφh_cont : Continuous (fun x => φ (h x)) := continuous_φ.comp hh_cont
  have hinner_gh_cont : Continuous (fun x => innerSL ℝ (gh x)) := (innerSL ℝ).continuous.comp hgh_cont
  have hc1 : Continuous (fun x => (-h x * φ (h x)) • innerSL ℝ (gh x)) :=
    (hh_cont.neg.mul hφh_cont).smul hinner_gh_cont
  have hc2 : Continuous (fun x => ((1 - h x ^ 2) * φ (h x)) • innerSL ℝ (gh x)) :=
    (((continuous_const (y := (1 : ℝ))).sub (hh_cont.pow 2)).mul hφh_cont).smul hinner_gh_cont
  have hA : Continuous (fun x => ((-h x * φ (h x)) • innerSL ℝ (gh x)).smulRight (Kh x)) :=
    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] E)).continuous.comp hc1).clm_apply hKh_cont
  have hB : Continuous (fun x => φ (h x) • Mh x) := hφh_cont.smul hMh_cont
  have hC : Continuous (fun x => (((1 - h x ^ 2) * φ (h x)) • innerSL ℝ (gh x)).smulRight (rankOne gh x)) :=
    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] E)).continuous.comp hc2).clm_apply hR1_cont
  have hD : Continuous (fun x => (h x * φ (h x)) • rankOneDeriv gh Kh x) :=
    (hh_cont.mul hφh_cont).smul hDR1_cont
  exact continuous_clm_add_sub_sub hA hB hC hD

private lemma norm_phiCompM_le {m : ℕ}
    {h : EuclideanSpace ℝ (Fin m) → ℝ}
    {gh : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {Kh : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    {Mh : EuclideanSpace ℝ (Fin m) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))}
    {Ch Cgh CKh CMh : ℝ} (hCh : 0 ≤ Ch) (hCgh : 0 ≤ Cgh) (hCKh : 0 ≤ CKh) (hCMh : 0 ≤ CMh)
    (hh_bound : ∀ x, |h x| ≤ Ch)
    (hgh_bound : ∀ x, ‖gh x‖ ≤ Cgh)
    (hKh_bound : ∀ x, ‖Kh x‖ ≤ CKh)
    (hMh_bound : ∀ x, ‖Mh x‖ ≤ CMh)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖phiCompM h gh Kh Mh x‖ ≤
      Ch * Cgh * CKh + CMh + (1 + Ch ^ 2) * Cgh ^ 3 + Ch * (2 * Cgh * CKh) := by
  have hφ_nn : 0 ≤ φ (h x) := (φ_pos _).le
  have hR1_b : ‖rankOne gh x‖ ≤ Cgh ^ 2 := by
    calc ‖rankOne gh x‖ ≤ ‖innerSL ℝ (gh x)‖ * ‖gh x‖ := norm_smulRight_le _ _
      _ = ‖gh x‖ * ‖gh x‖ := by rw [innerSL_apply_norm]
      _ ≤ Cgh * Cgh := by gcongr <;> exact hgh_bound x
      _ = Cgh ^ 2 := (sq Cgh).symm
  have hDR1_b : ‖rankOneDeriv gh Kh x‖ ≤ 2 * Cgh * CKh :=
    norm_rankOneDeriv_le hCgh hCKh hgh_bound hKh_bound x
  have h1 : ‖((-h x * φ (h x)) • innerSL ℝ (gh x)).smulRight (Kh x)‖ ≤ Ch * Cgh * CKh := by
    calc ‖((-h x * φ (h x)) • innerSL ℝ (gh x)).smulRight (Kh x)‖
        ≤ ‖(-h x * φ (h x)) • innerSL ℝ (gh x)‖ * ‖Kh x‖ :=
          norm_smulRight_le _ _
      _ = |h x| * φ (h x) * ‖gh x‖ * ‖Kh x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hφ_nn,
            innerSL_apply_norm]
      _ ≤ Ch * 1 * Cgh * CKh := by
          gcongr
          · exact hh_bound x
          · exact φ_le_one _
          · exact hgh_bound x
          · exact hKh_bound x
      _ = Ch * Cgh * CKh := by ring
  have h2 : ‖φ (h x) • Mh x‖ ≤ CMh := by
    rw [norm_smul_clm, abs_of_nonneg hφ_nn]
    calc φ (h x) * ‖Mh x‖ ≤ 1 * CMh := by gcongr; exact φ_le_one _; exact hMh_bound x
      _ = CMh := one_mul _
  have h3 : ‖(((1 - h x ^ 2) * φ (h x)) • innerSL ℝ (gh x)).smulRight (rankOne gh x)‖ ≤
      (1 + Ch ^ 2) * Cgh ^ 3 := by
    have habs1 : |1 - h x ^ 2| ≤ 1 + Ch ^ 2 := by
      have hsq : h x ^ 2 ≤ Ch ^ 2 := by nlinarith [sq_abs (h x), abs_nonneg (h x), hh_bound x]
      calc |1 - h x ^ 2| ≤ |1| + |h x ^ 2| := abs_sub _ _
        _ = 1 + h x ^ 2 := by rw [abs_one, abs_of_nonneg (sq_nonneg _)]
        _ ≤ 1 + Ch ^ 2 := by linarith
    calc ‖(((1 - h x ^ 2) * φ (h x)) • innerSL ℝ (gh x)).smulRight (rankOne gh x)‖
        ≤ ‖((1 - h x ^ 2) * φ (h x)) • innerSL ℝ (gh x)‖ * ‖rankOne gh x‖ :=
          norm_smulRight_le _ _
      _ = |1 - h x ^ 2| * φ (h x) * ‖gh x‖ * ‖rankOne gh x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hφ_nn,
            innerSL_apply_norm]
      _ ≤ (1 + Ch ^ 2) * 1 * Cgh * Cgh ^ 2 := by
          gcongr
          · exact φ_le_one _
          · exact hgh_bound x
      _ = (1 + Ch ^ 2) * Cgh ^ 3 := by ring
  have h4 : ‖(h x * φ (h x)) • rankOneDeriv gh Kh x‖ ≤ Ch * (2 * Cgh * CKh) := by
    rw [norm_smul_clm, abs_mul, abs_of_nonneg hφ_nn]
    calc |h x| * φ (h x) * ‖rankOneDeriv gh Kh x‖
        ≤ Ch * 1 * (2 * Cgh * CKh) := by
          gcongr
          · exact hh_bound x
          · exact φ_le_one _
      _ = Ch * (2 * Cgh * CKh) := by ring
  dsimp only [phiCompM]
  exact (norm_clm_add_sub_sub_le _ _ _ _).trans (by linarith)

/-- Composing `Φ` with a bounded `C³_b` function `h` produces a `SmoothC3Bounded` datum. -/
private noncomputable def SmoothC3Bounded.of_Φ_comp {m : ℕ}
    {h : EuclideanSpace ℝ (Fin m) → ℝ}
    {gh : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {Kh : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    {Mh : EuclideanSpace ℝ (Fin m) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))}
    {Ch Cgh CKh CMh : ℝ} (hCh : 0 ≤ Ch) (hCgh : 0 ≤ Cgh) (hCKh : 0 ≤ CKh) (hCMh : 0 ≤ CMh)
    (hh_bound : ∀ x, |h x| ≤ Ch)
    (hh_deriv : ∀ x, HasFDerivAt h (innerSL ℝ (gh x)) x)
    (hgh_deriv : ∀ x, HasFDerivAt gh (Kh x) x)
    (hKh_deriv : ∀ x, HasFDerivAt Kh (Mh x) x)
    (hMh_cont : Continuous Mh)
    (hKh_symm : ∀ x v w, ⟪Kh x v, w⟫ = ⟪v, Kh x w⟫)
    (hgh_bound : ∀ x, ‖gh x‖ ≤ Cgh)
    (hKh_bound : ∀ x, ‖Kh x‖ ≤ CKh)
    (hMh_bound : ∀ x, ‖Mh x‖ ≤ CMh) : SmoothC3Bounded m := by
  let E := EuclideanSpace ℝ (Fin m)
  let f : E → ℝ := fun x => Φ (h x)
  let g : E → E := fun x => φ (h x) • gh x
  let R1 : E → (E →L[ℝ] E) := rankOne gh
  let K : E → (E →L[ℝ] E) := fun x => φ (h x) • Kh x - (h x * φ (h x)) • R1 x
  let DR1 : E → (E →L[ℝ] (E →L[ℝ] E)) := rankOneDeriv gh Kh
  let M : E → (E →L[ℝ] (E →L[ℝ] E)) := phiCompM h gh Kh Mh
  have hη_pos : 0 < Φ (-Ch) := Φ_pos (-Ch)
  have hη_le : Φ (-Ch) ≤ 1 - Φ (-Ch) := by
    have h0 : Φ (-Ch) ≤ Φ 0 := strictMono_Φ.monotone (by linarith)
    have hhalf : Φ 0 = 1 / 2 := by
      have hneg := Φ_neg 0
      simp only [neg_zero] at hneg
      linarith
    linarith
  have hf_mem : ∀ x, f x ∈ Icc (Φ (-Ch)) (1 - Φ (-Ch)) := fun x => by
    have habs := abs_le.mp (hh_bound x)
    constructor
    · exact strictMono_Φ.monotone habs.1
    · have h1 : Φ (h x) ≤ Φ Ch := strictMono_Φ.monotone habs.2
      have h2 : Φ Ch = 1 - Φ (-Ch) := by
        have := Φ_neg Ch
        linarith
      linarith
  have hφh_deriv : ∀ x, HasFDerivAt (fun y => φ (h y)) ((-h x * φ (h x)) • innerSL ℝ (gh x)) x :=
    fun x => (hasDerivAt_φ (h x)).comp_hasFDerivAt x (hh_deriv x)
  have hsφh_deriv : ∀ x, HasFDerivAt (fun y => h y * φ (h y))
      (((1 - h x ^ 2) * φ (h x)) • innerSL ℝ (gh x)) x := fun x => by
    have hd : HasDerivAt (fun s => s * φ s) ((1 - h x ^ 2) * φ (h x)) (h x) :=
      ((hasDerivAt_id (h x)).mul (hasDerivAt_φ (h x))).congr_deriv (by simp only [id_eq]; ring)
    exact hd.comp_hasFDerivAt x (hh_deriv x)
  have hR1_deriv : ∀ x, HasFDerivAt R1 (DR1 x) x := hasFDerivAt_rankOne hgh_deriv
  have hf_deriv : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x := fun x => by
    have h1 := (hasDerivAt_Φ (h x)).comp_hasFDerivAt x (hh_deriv x)
    have heq : φ (h x) • innerSL ℝ (gh x) = innerSL ℝ (g x) := by
      ext v
      simp [g]
    rw [← heq]
    exact h1
  have hg_deriv : ∀ x, HasFDerivAt g (K x) x := fun x => by
    have h1 := (hφh_deriv x).smul (hgh_deriv x)
    have heq : φ (h x) • Kh x +
        ((-h x * φ (h x)) • innerSL ℝ (gh x)).smulRight (gh x) = K x := by
      ext v
      simp only [K, R1, rankOne, add_apply, sub_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
      rw [smul_smul, sub_eq_add_neg, ← neg_smul]
      have hs : (-h x * φ (h x)) * ⟪gh x, v⟫ = -(h x * φ (h x) * ⟪gh x, v⟫) := by ring
      rw [hs]
    rw [← heq]
    exact h1
  have hK_deriv : ∀ x, HasFDerivAt K (M x) x := fun x => by
    have h1 := (hφh_deriv x).smul (hKh_deriv x)
    have h2 := (hsφh_deriv x).smul (hR1_deriv x)
    have hsub := h1.sub h2
    have heq : (φ (h x) • Mh x + ((-h x * φ (h x)) • innerSL ℝ (gh x)).smulRight (Kh x)) -
        ((h x * φ (h x)) • DR1 x +
          (((1 - h x ^ 2) * φ (h x)) • innerSL ℝ (gh x)).smulRight (R1 x)) = M x := by
      ext v w
      simp only [M, phiCompM, R1, DR1, add_apply, sub_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
      abel
    rw [← heq]
    exact hsub
  have hh_cont : Continuous h := continuous_iff_continuousAt.mpr fun x => (hh_deriv x).continuousAt
  have hgh_cont : Continuous gh := continuous_iff_continuousAt.mpr fun x => (hgh_deriv x).continuousAt
  have hKh_cont : Continuous Kh := continuous_iff_continuousAt.mpr fun x => (hKh_deriv x).continuousAt
  have hR1_cont : Continuous R1 := continuous_iff_continuousAt.mpr fun x => (hR1_deriv x).continuousAt
  have hDR1_cont : Continuous DR1 := continuous_rankOneDeriv hgh_cont hKh_cont
  have hM_cont : Continuous M :=
    continuous_phiCompM hh_cont hgh_cont hKh_cont hMh_cont hR1_cont hDR1_cont
  have hK_symm : ∀ x v w, ⟪K x v, w⟫ = ⟪v, K x w⟫ := fun x v w => by
    simp only [K, R1, rankOne, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, hKh_symm x v w]
    rw [real_inner_comm v (gh x)]
    ring
  have hR1_bound : ∀ x, ‖R1 x‖ ≤ Cgh ^ 2 := fun x => by
    calc ‖R1 x‖ ≤ ‖innerSL ℝ (gh x)‖ * ‖gh x‖ := norm_smulRight_le _ _
      _ = ‖gh x‖ * ‖gh x‖ := by rw [innerSL_apply_norm]
      _ ≤ Cgh * Cgh := by gcongr <;> exact hgh_bound x
      _ = Cgh ^ 2 := (sq Cgh).symm
  have hg_bound : ∀ x, ‖g x‖ ≤ Cgh := fun x => by
    have hφ_nn : 0 ≤ φ (h x) := (φ_pos _).le
    dsimp only [g]
    rw [norm_smul, Real.norm_of_nonneg hφ_nn]
    calc φ (h x) * ‖gh x‖ ≤ 1 * Cgh := by gcongr; exact φ_le_one _; exact hgh_bound x
      _ = Cgh := one_mul _
  have hK_bound : ∀ x, ‖K x‖ ≤ CKh + Ch * Cgh ^ 2 := fun x => by
    have hφ_nn : 0 ≤ φ (h x) := (φ_pos _).le
    dsimp only [K]
    calc ‖φ (h x) • Kh x - (h x * φ (h x)) • R1 x‖
        ≤ ‖φ (h x) • Kh x‖ + ‖(h x * φ (h x)) • R1 x‖ := norm_sub_le _ _
      _ = φ (h x) * ‖Kh x‖ + |h x| * φ (h x) * ‖R1 x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hφ_nn, Real.norm_eq_abs,
            abs_mul, abs_of_nonneg hφ_nn]
      _ ≤ 1 * CKh + Ch * 1 * Cgh ^ 2 := by
          gcongr
          · exact φ_le_one _
          · exact hKh_bound x
          · exact hh_bound x
          · exact φ_le_one _
          · exact hR1_bound x
      _ = CKh + Ch * Cgh ^ 2 := by ring
  have hM_bound : ∀ x, ‖M x‖ ≤
      Ch * Cgh * CKh + CMh + (1 + Ch ^ 2) * Cgh ^ 3 + Ch * (2 * Cgh * CKh) :=
    norm_phiCompM_le hCh hCgh hCKh hCMh hh_bound hgh_bound hKh_bound hMh_bound
  exact
    { f := f, g := g, K := K, M := M
      η := Φ (-Ch), hη_pos := hη_pos, hη_le := hη_le
      hf_mem := hf_mem, hf_deriv := hf_deriv, hg_deriv := hg_deriv
      hK_deriv := hK_deriv, hM_cont := hM_cont, hK_symm := hK_symm
      Cg := Cgh, CK := CKh + Ch * Cgh ^ 2
      CM := Ch * Cgh * CKh + CMh + (1 + Ch ^ 2) * Cgh ^ 3 + Ch * (2 * Cgh * CKh)
      hCg_nn := hCgh, hCK_nn := by positivity, hCM_nn := by positivity
      hg_bound := hg_bound, hK_bound := hK_bound, hM_bound := hM_bound }

/-! ### Section 6: From Bobkov's inequality to Borell's enlargement inequality -/

section BorellFromBobkov

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian (EuclideanSpace ℝ (Fin m))

/-- Main interior case: `0 < α < 1`, `0 < ε`. -/
private lemma borell_enlargement_interior (X : Set E) (α ε : ℝ)
    (hX : IsClosed X) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε)
    (hprob : α ≤ (γ X).toReal) :
    (γ {x | ε < Metric.infDist x X}).toReal ≤ 1 - Φ (q α + ε) := by
  -- Suffices to show Φ (q α + ε) ≤ (γ {x | Metric.infDist x X ≤ ε}).toReal
  have hmeas_le : MeasurableSet {x : E | Metric.infDist x X ≤ ε} :=
    (isClosed_le (Metric.continuous_infDist_pt X) continuous_const).measurableSet
  have hcompl_eq : {x : E | ε < Metric.infDist x X} = {x : E | Metric.infDist x X ≤ ε}ᶜ := by
    ext x; simp [not_le]
  have hcompl_prob : (γ {x | ε < Metric.infDist x X}).toReal =
      1 - (γ {x | Metric.infDist x X ≤ ε}).toReal := by
    rw [hcompl_eq, prob_compl_eq_one_sub hmeas_le]
    rw [ENNReal.toReal_sub_of_le (prob_le_one) ENNReal.one_ne_top, ENNReal.toReal_one]
  rw [hcompl_prob]
  suffices hmain : Φ (q α + ε) ≤ (γ {x | Metric.infDist x X ≤ ε}).toReal by linarith
  -- Suffices to show for every δ ∈ (0, ε / 4): Φ (q α + ε - 4 * δ) ≤ γ{d ≤ ε}
  suffices hdelta : ∀ δ : ℝ, 0 < δ → 4 * δ < ε →
      Φ (q α + ε - 4 * δ) ≤ (γ {x | Metric.infDist x X ≤ ε}).toReal by
    have htend : Tendsto (fun n : ℕ => Φ (q α + ε - 4 * (ε / (5 * (n + 1 : ℝ)))))
        atTop (𝓝 (Φ (q α + ε))) := by
      have hsub : Tendsto (fun n : ℕ => q α + ε - 4 * (ε / (5 * (n + 1 : ℝ))))
          atTop (𝓝 (q α + ε)) := by
        have h0 : Tendsto (fun n : ℕ => 4 * (ε / (5 * (n + 1 : ℝ)))) atTop (𝓝 0) := by
          have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
            tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          have hmul := hinv.const_mul (4 * ε / 5)
          simp only [mul_zero] at hmul
          refine hmul.congr fun n => ?_
          have hne : (n : ℝ) + 1 ≠ 0 := by positivity
          field_simp [hne]
        simpa using tendsto_const_nhds.sub h0
      exact (continuous_Φ.tendsto _).comp hsub
    refine le_of_tendsto htend (Filter.Eventually.of_forall fun n => ?_)
    have hpos : 0 < ε / (5 * ((n : ℝ) + 1)) := by positivity
    have hlt : 4 * (ε / (5 * ((n : ℝ) + 1))) < ε := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have h5 : 4 < 5 * ((n : ℝ) + 1) := by linarith
      calc 4 * (ε / (5 * ((n : ℝ) + 1)))
          = ε * (4 / (5 * ((n : ℝ) + 1))) := by ring
        _ < ε * 1 := by
            gcongr
            rw [div_lt_one (by positivity)]
            exact h5
        _ = ε := mul_one _
    exact hdelta _ hpos hlt
  intro δ hδ h4δ
  set R : ℝ := ε + 1
  have hR_pos : 0 < R := by linarith
  let dR : E → ℝ := fun x => min (Metric.infDist x X) R
  have hdR_cont : Continuous dR := (Metric.continuous_infDist_pt X).min continuous_const
  have hdR_mem : ∀ x, dR x ∈ Icc 0 R := fun x =>
    ⟨le_min Metric.infDist_nonneg hR_pos.le, min_le_right _ _⟩
  have hdR_lip : ∀ x y, |dR x - dR y| ≤ ‖x - y‖ := fun x y => by
    have h1 : |Metric.infDist x X - Metric.infDist y X| ≤ ‖x - y‖ := by
      rw [abs_le]
      constructor
      · have := Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := X)
        rw [dist_eq_norm, norm_sub_rev] at this
        linarith
      · have := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := X)
        rw [dist_eq_norm] at this
        linarith
    have h2 : |min (Metric.infDist x X) R - min (Metric.infDist y X) R| ≤
        |Metric.infDist x X - Metric.infDist y X| := by
      rcases le_total (Metric.infDist x X) R with hx | hx <;>
      rcases le_total (Metric.infDist y X) R with hy | hy
      · rw [min_eq_left hx, min_eq_left hy]
      · rw [min_eq_left hx, min_eq_right hy, abs_of_nonpos (by linarith),
          abs_of_nonpos (by linarith)]
        linarith
      · rw [min_eq_right hx, min_eq_left hy, abs_of_nonneg (by linarith),
          abs_of_nonneg (by linarith)]
        linarith
      · rw [min_eq_right hx, min_eq_right hy, sub_self, abs_zero]
        exact abs_nonneg _
    exact h2.trans h1
  -- Obtain C³_b 1-Lipschitz approximation F₃ with |F₃ - dR| ≤ δ
  obtain ⟨F₃, g₃, K₃, M₃, CK₃, CM₃, hF₃_mem, hF₃_err, hF₃_deriv, hg₃_deriv, hK₃_deriv,
    hM₃_cont, hK₃_symm, hg₃_norm, hK₃_bound, hM₃_bound⟩ :=
    RobustOpt2009.MatrixChance.gaussian_smooth_approximation hdR_cont hR_pos.le hdR_mem hdR_lip hδ
  have hCK₃_nn : 0 ≤ CK₃ := le_trans (norm_nonneg (K₃ 0)) (hK₃_bound 0)
  have hCM₃_nn : 0 ≤ CM₃ := le_trans (norm_nonneg (M₃ 0)) (hM₃_bound 0)
  -- For any λ > 0, prove the λ-parametrized lower bound
  have hlambda : ∀ lam : ℝ, 0 < lam →
      Φ (q (Φ (lam * δ) * α) + (lam / Real.sqrt (1 + lam ^ 2)) * (ε - 4 * δ)) ≤
        (γ {x | Metric.infDist x X ≤ ε}).toReal + Φ (-lam * δ) := by
    intro lam hlam
    let f : ℝ → E → ℝ := fun r x => Φ (lam * (r - F₃ x))
    let ψ : ℝ → ℝ := fun r => ∫ x, f r x ∂γ
    have hf_cont : ∀ r, Continuous (f r) := fun r =>
      continuous_Φ.comp (continuous_const.mul (continuous_const.sub
        (continuous_iff_continuousAt.mpr fun x => (hF₃_deriv x).continuousAt)))
    have hf_Ioo : ∀ r x, f r x ∈ Ioo (0 : ℝ) 1 := fun r x => by
      rw [← range_Φ]; exact mem_range_self _
    have hψ_Ioo : ∀ r, ψ r ∈ Ioo (0 : ℝ) 1 := fun r => by
      set B : ℝ := lam * (|r| + R)
      have hlo : ∀ x, Φ (-B) ≤ f r x := fun x => by
        apply strictMono_Φ.monotone
        have hm := hF₃_mem x
        have hr : -|r| ≤ r := neg_abs_le r
        nlinarith [hm.1, hm.2]
      have hhi : ∀ x, f r x ≤ Φ B := fun x => by
        apply strictMono_Φ.monotone
        have hm := hF₃_mem x
        have hr : r ≤ |r| := le_abs_self r
        nlinarith [hm.1, hm.2]
      have hint : Integrable (f r) γ :=
        Integrable.of_bound (hf_cont r).aestronglyMeasurable 1
          (ae_of_all _ fun x => by
            rw [Real.norm_of_nonneg (hf_Ioo r x).1.le]; exact (hf_Ioo r x).2.le)
      constructor
      · calc (0 : ℝ) < Φ (-B) := Φ_pos (-B)
          _ = ∫ _x, Φ (-B) ∂γ := by simp
          _ ≤ ∫ x, f r x ∂γ := integral_mono (integrable_const _) hint hlo
      · calc ∫ x, f r x ∂γ ≤ ∫ _x, Φ B ∂γ := integral_mono hint (integrable_const _) hhi
          _ = Φ B := by simp
          _ < 1 := by
              have hmem : Φ B ∈ Ioo (0 : ℝ) 1 := by rw [← range_Φ]; exact mem_range_self _
              exact hmem.2
    -- Differentiate ψ(r) w.r.t. r
    have hψ_deriv : ∀ r : ℝ,
        HasDerivAt ψ (∫ x, lam * φ (lam * (r - F₃ x)) ∂γ) r := fun r => by
      have hF_meas : ∀ᶠ s in 𝓝 r, AEStronglyMeasurable (f s) γ :=
        Filter.Eventually.of_forall fun s => (hf_cont s).aestronglyMeasurable
      have hF_int : Integrable (f r) γ :=
        Integrable.of_bound (hf_cont r).aestronglyMeasurable 1
          (ae_of_all _ fun x => by
            rw [Real.norm_of_nonneg (hf_Ioo r x).1.le]; exact (hf_Ioo r x).2.le)
      let F' : ℝ → E → ℝ := fun s x => lam * φ (lam * (s - F₃ x))
      have hF'_meas : AEStronglyMeasurable (F' r) γ :=
        (continuous_const.mul (continuous_φ.comp (continuous_const.mul
          (continuous_const.sub (continuous_iff_continuousAt.mpr fun x =>
            (hF₃_deriv x).continuousAt))))).aestronglyMeasurable
      have hbound : ∀ x, ∀ s ∈ (univ : Set ℝ), ‖F' s x‖ ≤ lam := fun x s _ => by
        dsimp only [F']
        rw [Real.norm_of_nonneg (mul_nonneg hlam.le (φ_pos _).le)]
        calc lam * φ (lam * (s - F₃ x)) ≤ lam * 1 := by gcongr; exact φ_le_one _
          _ = lam := mul_one _
      have hdiff : ∀ x, ∀ s ∈ (univ : Set ℝ), HasDerivAt (fun τ => f τ x) (F' s x) s :=
        fun x s _ => by
          have h1 : HasDerivAt (fun τ => lam * (τ - F₃ x)) lam s := by
            have := ((hasDerivAt_id s).sub_const (F₃ x)).const_mul lam
            simpa using this
          have h2 := (hasDerivAt_Φ (lam * (s - F₃ x))).comp s h1
          refine h2.congr_deriv ?_
          dsimp only [F']; ring
      exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le univ_mem hF_meas hF_int hF'_meas
        (ae_of_all _ hbound) (integrable_const lam) (ae_of_all _ hdiff)).2
    -- Apply Bobkov's inequality to `f r` for each `r`
    have hslope : ∀ r : ℝ,
        lam / Real.sqrt (1 + lam ^ 2) ≤ deriv (fun s => q (ψ s)) r := fun r => by
      let S_r : SmoothC3Bounded m := SmoothC3Bounded.of_Φ_comp
        (h := fun x => lam * (r - F₃ x))
        (gh := fun x => (-lam) • g₃ x)
        (Kh := fun x => (-lam) • K₃ x)
        (Mh := fun x => (-lam) • M₃ x)
        (Ch := lam * (|r| + R)) (Cgh := lam) (CKh := lam * CK₃) (CMh := lam * CM₃)
        (by positivity) hlam.le (by positivity) (by positivity)
        (fun x => by
          rw [abs_mul, abs_of_pos hlam]
          gcongr
          calc |r - F₃ x| ≤ |r| + |F₃ x| := abs_sub _ _
            _ = |r| + F₃ x := by rw [abs_of_nonneg (hF₃_mem x).1]
            _ ≤ |r| + R := by linarith [(hF₃_mem x).2])
        (fun x => by
          have h := ((hasFDerivAt_const r x).sub (hF₃_deriv x)).const_mul lam
          refine hasFDerivAt_congr_deriv h ?_
          ext v
          simp)
        (fun x => (hg₃_deriv x).const_smul (-lam))
        (fun x => (hK₃_deriv x).const_smul (-lam))
        (hM₃_cont.const_smul (-lam))
        (fun x v w => by
          simp only [smul_apply, real_inner_smul_left, real_inner_smul_right,
            hK₃_symm x v w])
        (fun x => by
          rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hlam]
          calc lam * ‖g₃ x‖ ≤ lam * 1 := by gcongr; exact hg₃_norm x
            _ = lam := mul_one _)
        (fun x => by
          rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hlam]
          gcongr; exact hK₃_bound x)
        (fun x => by
          rw [norm_smul_clm, abs_neg, abs_of_pos hlam]
          gcongr; exact hM₃_bound x)
      have hbob := RobustOpt2009.MatrixChance.bobkov_smooth_gaussian
        S_r.f S_r.g S_r.K S_r.M S_r.η S_r.Cg S_r.CK S_r.CM S_r.hη_pos S_r.hη_le
        S_r.hf_mem S_r.hf_deriv S_r.hg_deriv S_r.hK_deriv S_r.hM_cont S_r.hK_symm
        S_r.hCg_nn S_r.hCK_nn S_r.hCM_nn S_r.hg_bound S_r.hK_bound S_r.hM_bound
      have hSr_f : S_r.f = f r := rfl
      have hSr_g : ∀ x, ‖S_r.g x‖ ≤ lam * φ (lam * (r - F₃ x)) := fun x => by
        have hφ_nn : 0 ≤ φ (lam * (r - F₃ x)) := (φ_pos _).le
        change ‖φ (lam * (r - F₃ x)) • ((-lam) • g₃ x)‖ ≤ lam * φ (lam * (r - F₃ x))
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hφ_nn, Real.norm_eq_abs,
          abs_neg, abs_of_pos hlam]
        calc φ (lam * (r - F₃ x)) * (lam * ‖g₃ x‖)
            ≤ φ (lam * (r - F₃ x)) * (lam * 1) := by gcongr; exact hg₃_norm x
          _ = lam * φ (lam * (r - F₃ x)) := by ring
      have hbob_ub : I (ψ r) ≤ Real.sqrt (1 + lam ^ 2) * ∫ x, φ (lam * (r - F₃ x)) ∂γ := by
        rw [← integral_const_mul]
        have hI_eq : I (ψ r) = I (∫ z, S_r.f z ∂γ) := rfl
        rw [hI_eq]
        refine hbob.trans ?_
        have hint_rhs : Integrable (fun x => Real.sqrt (1 + lam ^ 2) * φ (lam * (r - F₃ x))) γ :=
          Integrable.of_bound
            (continuous_const.mul (continuous_φ.comp (continuous_const.mul
              (continuous_const.sub (continuous_iff_continuousAt.mpr fun x =>
                (hF₃_deriv x).continuousAt))))).aestronglyMeasurable
            (Real.sqrt (1 + lam ^ 2)) (ae_of_all _ fun x => by
              rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (φ_pos _).le)]
              calc Real.sqrt (1 + lam ^ 2) * φ (lam * (r - F₃ x))
                  ≤ Real.sqrt (1 + lam ^ 2) * 1 := by gcongr; exact φ_le_one _
                _ = Real.sqrt (1 + lam ^ 2) := mul_one _)
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => Real.sqrt_nonneg _) hint_rhs
          (ae_of_all _ fun x => ?_)
        have hIf : I (S_r.f x) = φ (lam * (r - F₃ x)) := I_Φ _
        dsimp only
        rw [hIf]
        calc Real.sqrt (φ (lam * (r - F₃ x)) ^ 2 + ‖S_r.g x‖ ^ 2)
            ≤ Real.sqrt (φ (lam * (r - F₃ x)) ^ 2 + (lam * φ (lam * (r - F₃ x))) ^ 2) := by
              apply Real.sqrt_le_sqrt
              gcongr
              exact hSr_g x
          _ = Real.sqrt ((1 + lam ^ 2) * φ (lam * (r - F₃ x)) ^ 2) := by ring_nf
          _ = Real.sqrt (1 + lam ^ 2) * φ (lam * (r - F₃ x)) := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (φ_pos _).le]
      have hqψ_deriv : HasDerivAt (fun s => q (ψ s))
          ((I (ψ r))⁻¹ * ∫ x, lam * φ (lam * (r - F₃ x)) ∂γ) r :=
        (hasDerivAt_q (hψ_Ioo r)).comp r (hψ_deriv r)
      rw [hqψ_deriv.deriv, integral_const_mul]
      have hIpos : 0 < I (ψ r) := I_pos (ψ r)
      have hsq_pos : 0 < Real.sqrt (1 + lam ^ 2) := Real.sqrt_pos.mpr (by positivity)
      rw [div_le_iff₀ hsq_pos]
      have h1 : lam * I (ψ r) ≤
          lam * (Real.sqrt (1 + lam ^ 2) * ∫ x, φ (lam * (r - F₃ x)) ∂γ) := by
        gcongr
      calc lam = (I (ψ r))⁻¹ * (lam * I (ψ r)) := by field_simp [hIpos.ne']
        _ ≤ (I (ψ r))⁻¹ * (lam * (Real.sqrt (1 + lam ^ 2) * ∫ x, φ (lam * (r - F₃ x)) ∂γ)) := by
            gcongr
        _ = (I (ψ r))⁻¹ * (lam * ∫ x, φ (lam * (r - F₃ x)) ∂γ) * Real.sqrt (1 + lam ^ 2) := by ring
    -- Apply MVT on `[2 * δ, ε - 2 * δ]`
    have hqψ_diff : Differentiable ℝ (fun s => q (ψ s)) := fun r =>
      ((hasDerivAt_q (hψ_Ioo r)).comp r (hψ_deriv r)).differentiableAt
    have hmvt := mul_sub_le_image_sub_of_le_deriv hqψ_diff hslope (show 2 * δ ≤ ε - 2 * δ by linarith)
    have hgap : q (ψ (2 * δ)) + (lam / Real.sqrt (1 + lam ^ 2)) * (ε - 4 * δ) ≤
        q (ψ (ε - 2 * δ)) := by
      have : ε - 2 * δ - 2 * δ = ε - 4 * δ := by ring
      linarith
    -- Lower bound on ψ (2 * δ)
    have hψ_lo : Φ (lam * δ) * α ≤ ψ (2 * δ) := by
      have hint : Integrable (f (2 * δ)) γ :=
        Integrable.of_bound (hf_cont _).aestronglyMeasurable 1
          (ae_of_all _ fun x => by
            rw [Real.norm_of_nonneg (hf_Ioo _ x).1.le]; exact (hf_Ioo _ x).2.le)
      have hint_ind : Integrable (X.indicator (fun _ => Φ (lam * δ))) γ :=
        (integrable_const _).indicator hX.measurableSet
      have hpt : ∀ x, X.indicator (fun _ => Φ (lam * δ)) x ≤ f (2 * δ) x := fun x => by
        by_cases hx : x ∈ X
        · simp only [indicator_of_mem hx]
          have hdR0 : dR x = 0 := by
            simp [dR, Metric.infDist_zero_of_mem hx, hR_pos.le]
          have hF₃_le : F₃ x ≤ δ := by
            have := abs_le.mp (hF₃_err x)
            linarith
          apply strictMono_Φ.monotone
          nlinarith
        · simp only [indicator_of_notMem hx]
          exact (hf_Ioo (2 * δ) x).1.le
      calc Φ (lam * δ) * α ≤ Φ (lam * δ) * (γ X).toReal := by
            gcongr; exact (Φ_pos _).le
        _ = (γ X).toReal * Φ (lam * δ) := mul_comm _ _
        _ = ∫ x, X.indicator (fun _ => Φ (lam * δ)) x ∂γ := by
            rw [integral_indicator_const _ hX.measurableSet, smul_eq_mul, Measure.real_def]
        _ ≤ ∫ x, f (2 * δ) x ∂γ := integral_mono hint_ind hint hpt
    -- Upper bound on ψ (ε - 2 * δ)
    have hψ_hi : ψ (ε - 2 * δ) ≤ (γ {x | Metric.infDist x X ≤ ε}).toReal + Φ (-lam * δ) := by
      have hint : Integrable (f (ε - 2 * δ)) γ :=
        Integrable.of_bound (hf_cont _).aestronglyMeasurable 1
          (ae_of_all _ fun x => by
            rw [Real.norm_of_nonneg (hf_Ioo _ x).1.le]; exact (hf_Ioo _ x).2.le)
      have hpt : ∀ x, f (ε - 2 * δ) x ≤
          {x : E | Metric.infDist x X ≤ ε}.indicator (fun _ => (1 : ℝ)) x + Φ (-lam * δ) := fun x => by
        by_cases hx : x ∈ {x : E | Metric.infDist x X ≤ ε}
        · simp only [indicator_of_mem hx]
          linarith [(hf_Ioo (ε - 2 * δ) x).2, Φ_pos (-lam * δ)]
        · simp only [indicator_of_notMem hx, zero_add]
          change ¬ Metric.infDist x X ≤ ε at hx
          push Not at hx
          have hdR_ge : ε ≤ dR x := le_min hx.le (by linarith)
          have hF₃_ge : ε - δ ≤ F₃ x := by
            have := abs_le.mp (hF₃_err x)
            linarith
          apply strictMono_Φ.monotone
          nlinarith
      have hint_ind : Integrable ({x : E | Metric.infDist x X ≤ ε}.indicator (fun _ => (1 : ℝ))) γ :=
        (integrable_const (1 : ℝ)).indicator hmeas_le
      calc ψ (ε - 2 * δ) = ∫ x, f (ε - 2 * δ) x ∂γ := rfl
        _ ≤ ∫ x, ({x : E | Metric.infDist x X ≤ ε}.indicator (fun _ => (1 : ℝ)) x + Φ (-lam * δ)) ∂γ :=
            integral_mono hint (hint_ind.add (integrable_const _)) hpt
        _ = (∫ x, {x : E | Metric.infDist x X ≤ ε}.indicator (fun _ => (1 : ℝ)) x ∂γ) +
            (∫ _x, Φ (-lam * δ) ∂γ) := integral_add hint_ind (integrable_const _)
        _ = (γ {x | Metric.infDist x X ≤ ε}).toReal + Φ (-lam * δ) := by
            rw [integral_indicator_const _ hmeas_le, smul_eq_mul, mul_one, Measure.real_def,
              integral_const, probReal_univ, one_smul]
    have hα_mem : Φ (lam * δ) * α ∈ Ioo (0 : ℝ) 1 := by
      have hΦpos : 0 < Φ (lam * δ) := Φ_pos _
      have hΦlt : Φ (lam * δ) < 1 := by
        have h : Φ (lam * δ) ∈ Ioo (0 : ℝ) 1 := by rw [← range_Φ]; exact mem_range_self _
        exact h.2
      exact ⟨mul_pos hΦpos hα0, by nlinarith⟩
    have hq_lo : q (Φ (lam * δ) * α) ≤ q (ψ (2 * δ)) :=
      q_mono hα_mem (hψ_Ioo (2 * δ)) hψ_lo
    calc Φ (q (Φ (lam * δ) * α) + (lam / Real.sqrt (1 + lam ^ 2)) * (ε - 4 * δ))
        ≤ Φ (q (ψ (ε - 2 * δ))) := strictMono_Φ.monotone (by linarith)
      _ = ψ (ε - 2 * δ) := Φ_q (hψ_Ioo (ε - 2 * δ))
      _ ≤ (γ {x | Metric.infDist x X ≤ ε}).toReal + Φ (-lam * δ) := hψ_hi
  -- Send lam → +∞
  have htend_lhs : Tendsto
      (fun lam : ℝ => Φ (q (Φ (lam * δ) * α) + (lam / Real.sqrt (1 + lam ^ 2)) * (ε - 4 * δ)))
      atTop (𝓝 (Φ (q α + ε - 4 * δ))) := by
    have hΦ1 : Tendsto (fun lam : ℝ => Φ (lam * δ) * α) atTop (𝓝 α) := by
      have h1 : Tendsto (fun lam : ℝ => lam * δ) atTop atTop :=
        Tendsto.atTop_mul_const hδ tendsto_id
      simpa using (tendsto_Φ_atTop.comp h1).mul_const α
    have hq1 : Tendsto (fun lam : ℝ => q (Φ (lam * δ) * α)) atTop (𝓝 (q α)) :=
      (continuousOn_q.continuousAt (Ioo_mem_nhds hα0 hα1)).tendsto.comp hΦ1
    have hratio : Tendsto (fun lam : ℝ => lam / Real.sqrt (1 + lam ^ 2)) atTop (𝓝 1) := by
      have hinv2 : Tendsto (fun lam : ℝ => 1 / lam ^ 2 + 1) atTop (𝓝 1) := by
        have h0 : Tendsto (fun lam : ℝ => 1 / lam ^ 2) atTop (𝓝 0) := by
          simpa [one_div, Function.comp_def] using
            tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
        simpa using h0.add tendsto_const_nhds
      have hsq : Tendsto (fun lam : ℝ => (Real.sqrt (1 / lam ^ 2 + 1))⁻¹) atTop (𝓝 1) := by
        simpa using ((Real.continuous_sqrt.tendsto 1).comp hinv2).inv₀ (by norm_num)
      refine hsq.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
      have h1 : 1 + lam ^ 2 = lam ^ 2 * (1 / lam ^ 2 + 1) := by field_simp [hlam.ne']
      rw [h1, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hlam.le]
      field_simp [hlam.ne', (Real.sqrt_pos.mpr (by positivity : 0 < 1 / lam ^ 2 + 1)).ne']
    have harg : Tendsto
        (fun lam : ℝ => q (Φ (lam * δ) * α) + (lam / Real.sqrt (1 + lam ^ 2)) * (ε - 4 * δ))
        atTop (𝓝 (q α + ε - 4 * δ)) := by
      have h := hq1.add (hratio.mul_const (ε - 4 * δ))
      simpa [one_mul, add_sub_assoc] using h
    exact (continuous_Φ.tendsto _).comp harg
  have htend_rhs : Tendsto
      (fun lam : ℝ => (γ {x | Metric.infDist x X ≤ ε}).toReal + Φ (-lam * δ))
      atTop (𝓝 (γ {x | Metric.infDist x X ≤ ε}).toReal) := by
    have hneg : Tendsto (fun lam : ℝ => -lam * δ) atTop atBot := by
      have h1 : Tendsto (fun lam : ℝ => -(lam * δ)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (Tendsto.atTop_mul_const hδ tendsto_id)
      simpa [neg_mul] using h1
    simpa using tendsto_const_nhds.add (tendsto_Φ_atBot.comp hneg)
  exact le_of_tendsto_of_tendsto htend_lhs htend_rhs
    (Filter.eventually_gt_atTop (0 : ℝ) |>.mono fun lam hlam => hlambda lam hlam)

end BorellFromBobkov

end BorellProof

theorem solution {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m))) (α ε : ℝ)
    (hX : IsClosed X) (hα : 0 < α) (hε : 0 ≤ ε)
    (hprob : α ≤ ((stdGaussian (EuclideanSpace ℝ (Fin m))) X).toReal) :
    ((stdGaussian (EuclideanSpace ℝ (Fin m))) {x | ε < Metric.infDist x X}).toReal ≤
      normalTail (tailQuantile (1 - α) + (ε : EReal)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin m))
  have hsub_compl : {x : EuclideanSpace ℝ (Fin m) | ε < Metric.infDist x X} ⊆ Xᶜ := by
    intro x hx hxX
    change ε < Metric.infDist x X at hx
    have h0 : Metric.infDist x X = 0 := Metric.infDist_zero_of_mem hxX
    linarith
  have hle_compl : (γ {x | ε < Metric.infDist x X}).toReal ≤ 1 - α := by
    have h1 : γ {x | ε < Metric.infDist x X} ≤ γ Xᶜ := measure_mono hsub_compl
    have h2 : (γ {x | ε < Metric.infDist x X}).toReal ≤ (γ Xᶜ).toReal :=
      ENNReal.toReal_mono (measure_ne_top γ Xᶜ) h1
    rw [prob_compl_eq_one_sub hX.measurableSet,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one] at h2
    linarith
  -- Case 1: α ≥ 1
  by_cases hα1 : 1 ≤ α
  · have hzero : (γ {x | ε < Metric.infDist x X}).toReal = 0 :=
      le_antisymm (by linarith) ENNReal.toReal_nonneg
    rw [hzero]
    exact ENNReal.toReal_nonneg
  push Not at hα1
  rw [BorellProof.tailQuantile_one_sub hα hα1, ← EReal.coe_add, BorellProof.normalTail_coe]
  -- Case 2: ε = 0
  rcases eq_or_lt_of_le hε with rfl | hε_pos
  · rw [add_zero, BorellProof.Φ_q ⟨hα, hα1⟩]
    exact hle_compl
  -- Case 3: 0 < α < 1 and 0 < ε
  exact BorellProof.borell_enlargement_interior X α ε hX hα hα1 hε_pos hprob
