-- Prove2me | solution 1 for RobustOpt2009.MatrixChance.bobkov_smooth_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T21:11:13.474398+00:00
-- url     : https://prove2.me/submissions/088e47d8-a600-47f1-b78c-a8d1fc57ce3a

import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Theorems.Thm_OAI_GaussianPropeller_HeatConvolution_fderiv_heat
import Theorems.Thm_OAI_GaussianPropeller_HeatConvolution_heat_equation
import Theorems.Thm_OAI_GaussianPropeller_HeatConvolution_stein_trace

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators RealInnerProductSpace NNReal ENNReal

open OAI.GaussianPropeller.Quantile
open OAI.GaussianPropeller.HeatConvolution

namespace BorellBobkov

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

section GaussianSmoothing

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian (EuclideanSpace ℝ (Fin m))

private lemma integrable_norm_stdGaussian : Integrable (fun z : E => ‖z‖) γ :=
  (IsGaussian.integrable_id (μ := γ)).norm
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

private lemma continuous_shift_scale (x : E) (r : ℝ) : Continuous (fun z : E => x + r • z) :=
  continuous_const.add (continuous_id.const_smul r)

private lemma integrable_heat_integrand {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : E → V} (hFc : Continuous F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (t : ℝ) (x : E) :
    Integrable (fun z : E => F (x + Real.sqrt t • z)) γ :=
  Integrable.of_bound (hFc.comp (continuous_shift_scale x (Real.sqrt t))).aestronglyMeasurable
    B (ae_of_all _ fun _ => hB _)

private lemma heat_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : E → V) (x : E) : heat F 0 x = F x := by
  simp [heat]

private lemma heat_one_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : E → V) : heat F 1 0 = ∫ z, F z ∂γ := by
  simp [heat]

private lemma norm_heat_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : E → V} {B : ℝ} (_hB0 : 0 ≤ B) (hB : ∀ x, ‖F x‖ ≤ B) (t : ℝ) (x : E) :
    ‖heat F t x‖ ≤ B := by
  unfold heat
  calc ‖∫ z, F (x + Real.sqrt t • z) ∂γ‖
      ≤ ∫ z, ‖F (x + Real.sqrt t • z)‖ ∂γ := norm_integral_le_integral_norm _
    _ ≤ ∫ _z, B ∂γ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          (integrable_const B) (ae_of_all _ fun z => hB _)
    _ = B := by simp

private lemma continuous_heat {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : E → V} (hFc : Continuous F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    Continuous (fun p : ℝ × E => heat F p.1 p.2) := by
  refine continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
  · intro p
    exact (hFc.comp (continuous_shift_scale p.2 (Real.sqrt p.1))).aestronglyMeasurable
  · intro p
    exact ae_of_all _ fun z => hB _
  · exact ae_of_all _ fun z => hFc.comp (continuous_snd.add
      ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))

private lemma heat_mem_Icc {F : E → ℝ} {lo hi : ℝ} (hFc : Continuous F)
    (hF : ∀ x, F x ∈ Icc lo hi) (t : ℝ) (x : E) : heat F t x ∈ Icc lo hi := by
  have hbound : ∀ u, ‖F u‖ ≤ max |lo| |hi| := fun u => by
    rw [Real.norm_eq_abs, abs_le]
    have h := hF u
    exact ⟨le_trans (neg_le_neg (le_max_left _ _)) (le_trans (neg_abs_le _) h.1),
      le_trans h.2 (le_trans (le_abs_self _) (le_max_right _ _))⟩
  have hint : Integrable (fun z => F (x + Real.sqrt t • z)) γ :=
    integrable_heat_integrand hFc hbound t x
  unfold heat
  constructor
  · calc lo = ∫ _z, lo ∂γ := by simp
      _ ≤ ∫ z, F (x + Real.sqrt t • z) ∂γ :=
          integral_mono (integrable_const _) hint fun z => (hF _).1
  · calc ∫ z, F (x + Real.sqrt t • z) ∂γ
        ≤ ∫ _z, hi ∂γ := integral_mono hint (integrable_const _) fun z => (hF _).2
      _ = hi := by simp

private lemma heat_clm_eval {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {F : E → (E →L[ℝ] V)} (hFc : Continuous F) {B : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) (v : E) (t : ℝ) (x : E) :
    heat F t x v = heat (fun y => F y v) t x := by
  unfold heat
  exact ((ContinuousLinearMap.apply ℝ V v).integral_comp_comm
    (integrable_heat_integrand hFc hB t x)).symm
private lemma heat_innerSL_eq {g : E → E} (hgc : Continuous g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    (t : ℝ) (x : E) :
    heat (fun y => innerSL ℝ (g y)) t x = innerSL ℝ (heat g t x) := by
  unfold heat
  have hint : Integrable (fun z => g (x + Real.sqrt t • z)) γ :=
    integrable_heat_integrand hgc hB t x
  exact (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.integral_comp_comm hint


end GaussianSmoothing

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

/-! ### Section 5: Bakry–Ledoux heat-semigroup proof of Bobkov's inequality -/

section BakryLedoux

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian (EuclideanSpace ℝ (Fin m))
local notation "eb" => EuclideanSpace.basisFun (Fin m) ℝ

/-- Total-derivative helper: differentiating `s ↦ F s (r s • z)` from partial derivatives
when the time derivative `Ft` is jointly continuous on `(a, b) × E`. -/
private lemma hasDerivAt_time_space {F Ft : ℝ → E → ℝ} {Fx : E → E}
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) {r : ℝ → ℝ} {r' : ℝ} (hr : HasDerivAt r r' t₀) (z : E)
    (hFt : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun τ => F τ x) (Ft s x) s)
    (hFx : HasFDerivAt (F t₀) (innerSL ℝ (Fx (r t₀ • z))) (r t₀ • z))
    (hFt_cont : ContinuousOn (fun p : ℝ × E => Ft p.1 p.2) (Ioo a b ×ˢ univ)) :
    HasDerivAt (fun s => F s (r s • z))
      (Ft t₀ (r t₀ • z) + r' * ⟪Fx (r t₀ • z), z⟫) t₀ := by
  set x₀ : E := r t₀ • z
  have h1 : HasDerivAt (fun s => F t₀ (r s • z)) (r' * ⟪Fx x₀, z⟫) t₀ := by
    have hcomp : HasDerivAt (fun s => F t₀ (r s • z)) (innerSL ℝ (Fx x₀) (r' • z)) t₀ :=
      hFx.comp_hasDerivAt t₀ (hr.smul_const z)
    refine hcomp.congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun s => F s (r s • z) - F t₀ (r s • z)) (Ft t₀ x₀) t₀ := by
    rw [hasDerivAt_iff_isLittleO]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hcont_at : ContinuousAt (fun p : ℝ × E => Ft p.1 p.2) (t₀, x₀) :=
      hFt_cont.continuousAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht₀, mem_univ _⟩)
    rw [Metric.continuousAt_iff] at hcont_at
    obtain ⟨δ₁, hδ₁, hclose⟩ := hcont_at c hc
    have hIoo : Ioo a b ∈ 𝓝 t₀ := Ioo_mem_nhds ht₀.1 ht₀.2
    obtain ⟨δ₂, hδ₂, hball⟩ := Metric.mem_nhds_iff.mp hIoo
    have hr_cont : ContinuousAt (fun s => r s • z) t₀ := hr.continuousAt.smul continuousAt_const
    rw [Metric.continuousAt_iff] at hr_cont
    obtain ⟨δ₃, hδ₃, hr_close⟩ := hr_cont δ₁ hδ₁
    set δ := min (min δ₁ δ₂) δ₃
    have hδ : 0 < δ := lt_min (lt_min hδ₁ hδ₂) hδ₃
    filter_upwards [Metric.ball_mem_nhds t₀ hδ] with s hs
    have hs1 : dist s t₀ < δ₁ := lt_of_lt_of_le hs (le_trans (min_le_left _ _) (min_le_left _ _))
    have hs2 : dist s t₀ < δ₂ := lt_of_lt_of_le hs (le_trans (min_le_left _ _) (min_le_right _ _))
    have hs3 : dist s t₀ < δ₃ := lt_of_lt_of_le hs (min_le_right _ _)
    have hx_close : dist (r s • z) x₀ < δ₁ := hr_close hs3
    -- Apply MVT on segment `[t₀, s]` (i.e. `uIcc t₀ s`) to `τ ↦ F τ (r s • z) - τ * Ft t₀ x₀`
    let ψ : ℝ → ℝ := fun τ => F τ (r s • z) - τ * Ft t₀ x₀
    have hψ_deriv : ∀ τ ∈ uIcc t₀ s,
        HasDerivWithinAt ψ (Ft τ (r s • z) - Ft t₀ x₀) (uIcc t₀ s) τ := fun τ hτ => by
      have hτ_dist : dist τ t₀ < δ₂ := by
        rw [Real.dist_eq] at hs2 ⊢
        rcases le_total t₀ s with hle | hge
        · rw [uIcc_of_le hle] at hτ
          rw [abs_of_nonneg (sub_nonneg.mpr hτ.1)]
          linarith [hτ.1, hτ.2, abs_of_nonneg (sub_nonneg.mpr hle)]
        · rw [uIcc_of_ge hge] at hτ
          rw [abs_of_nonpos (sub_nonpos.mpr hτ.2)]
          linarith [hτ.1, hτ.2, abs_of_nonpos (sub_nonpos.mpr hge)]
      have hτ_Ioo : τ ∈ Ioo a b := hball hτ_dist
      have hd := (hFt τ hτ_Ioo (r s • z)).sub ((hasDerivAt_id τ).mul_const (Ft t₀ x₀))
      exact (hd.congr_deriv (by ring)).hasDerivWithinAt
    have hψ_bound : ∀ τ ∈ uIcc t₀ s, ‖Ft τ (r s • z) - Ft t₀ x₀‖ ≤ c := fun τ hτ => by
      have hτ_dist : dist τ t₀ < δ₁ := by
        rw [Real.dist_eq] at hs1 ⊢
        rcases le_total t₀ s with hle | hge
        · rw [uIcc_of_le hle] at hτ
          rw [abs_of_nonneg (sub_nonneg.mpr hτ.1)]
          linarith [hτ.1, hτ.2, abs_of_nonneg (sub_nonneg.mpr hle)]
        · rw [uIcc_of_ge hge] at hτ
          rw [abs_of_nonpos (sub_nonpos.mpr hτ.2)]
          linarith [hτ.1, hτ.2, abs_of_nonpos (sub_nonpos.mpr hge)]
      have hp_dist : dist (τ, r s • z) (t₀, x₀) < δ₁ := by
        rw [Prod.dist_eq]
        exact max_lt hτ_dist hx_close
      exact (hclose hp_dist).le
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun τ hτ => hψ_deriv τ hτ) hψ_bound (convex_uIcc t₀ s)
      left_mem_uIcc right_mem_uIcc
    have heq : (F s (r s • z) - F t₀ (r s • z)) - (F t₀ (r t₀ • z) - F t₀ (r t₀ • z)) -
        (s - t₀) * Ft t₀ x₀ = ψ s - ψ t₀ := by
      dsimp only [ψ]; ring
    simpa only [Real.norm_eq_abs, smul_eq_mul, heq] using hmvt
  have hfun : (fun s => F s (r s • z)) =
      fun s => (F s (r s • z) - F t₀ (r s • z)) + F t₀ (r s • z) := by
    ext s; ring
  rw [hfun]
  exact h2.add h1

private lemma parseval_sq (v : E) : ∑ i : Fin m, ⟪v, eb i⟫ ^ 2 = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm (eb i) v, EuclideanSpace.basisFun_inner, Real.norm_eq_abs, sq_abs]

private lemma sum_inner_mul_inner (v w : E) : ∑ i : Fin m, ⟪v, eb i⟫ * ⟪w, eb i⟫ = ⟪v, w⟫ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm (eb i) v, real_inner_comm (eb i) w, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner]
  simp [mul_comm]

/-- Cauchy–Schwarz for symmetric operators in Hilbert–Schmidt norm. -/
private lemma norm_apply_sq_le_hs {K : E →L[ℝ] E} (hK : ∀ v w, ⟪K v, w⟫ = ⟪v, K w⟫) (g : E) :
    ‖K g‖ ^ 2 ≤ ‖g‖ ^ 2 * ∑ i : Fin m, ‖K (eb i)‖ ^ 2 := by
  rw [← parseval_sq (K g), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hK g (eb i)]
  have h := abs_real_inner_le_norm g (K (eb i))
  calc ⟪g, K (eb i)⟫ ^ 2 = |⟪g, K (eb i)⟫| ^ 2 := (sq_abs _).symm
    _ ≤ (‖g‖ * ‖K (eb i)‖) ^ 2 := by gcongr
    _ = ‖g‖ ^ 2 * ‖K (eb i)‖ ^ 2 := mul_pow _ _ 2

/-- Core Bakry–Ledoux pointwise algebraic inequality. -/
private lemma bakry_ledoux_pointwise {Ival qval c : ℝ} (hI : 0 < Ival) (hc : 0 < c)
    {g : E} {K : E →L[ℝ] E} (hK : ∀ v w, ⟪K v, w⟫ = ⟪v, K w⟫) :
    let A := Ival ^ 2 + c * ‖g‖ ^ 2
    let S := ∑ i : Fin m, ‖K (eb i)‖ ^ 2
    let V := (-(qval * Ival)) • g + c • K g
    A * (-qval ^ 2 * ‖g‖ ^ 2 - c * S) + ‖V‖ ^ 2 ≤ 0 := by
  intro A S V
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hKg_sq : ‖K g‖ ^ 2 ≤ ‖g‖ ^ 2 * S := norm_apply_sq_le_hs hK g
  have hKg_le : ‖K g‖ ≤ ‖g‖ * Real.sqrt S := by
    have h1 : ‖K g‖ ^ 2 ≤ (‖g‖ * Real.sqrt S) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hS_nn]
      exact hKg_sq
    nlinarith [norm_nonneg (K g), mul_nonneg (norm_nonneg g) (Real.sqrt_nonneg S)]
  have hinner_abs : |⟪g, K g⟫| ≤ ‖g‖ ^ 2 * Real.sqrt S := by
    calc |⟪g, K g⟫| ≤ ‖g‖ * ‖K g‖ := abs_real_inner_le_norm g (K g)
      _ ≤ ‖g‖ * (‖g‖ * Real.sqrt S) := by gcongr
      _ = ‖g‖ ^ 2 * Real.sqrt S := by ring
  have hV_sq : ‖V‖ ^ 2 = qval ^ 2 * Ival ^ 2 * ‖g‖ ^ 2 - 2 * c * qval * Ival * ⟪g, K g⟫
      + c ^ 2 * ‖K g‖ ^ 2 := by
    dsimp only [V]
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_of_nonneg hc.le]
    have h1 : |-(qval * Ival)| ^ 2 = qval ^ 2 * Ival ^ 2 := by
      rw [sq_abs]; ring
    nlinarith
  have hcross : -2 * qval * Ival * ⟪g, K g⟫ ≤ qval ^ 2 * ‖g‖ ^ 4 + Ival ^ 2 * S := by
    have h1 : -2 * qval * Ival * ⟪g, K g⟫ ≤ 2 * |qval| * Ival * |⟪g, K g⟫| := by
      have hle : -(qval * ⟪g, K g⟫) ≤ |qval * ⟪g, K g⟫| := neg_le_abs _
      rw [abs_mul] at hle
      nlinarith
    have h2 : 2 * |qval| * Ival * |⟪g, K g⟫| ≤ 2 * (|qval| * ‖g‖ ^ 2) * (Ival * Real.sqrt S) := by
      have := mul_le_mul_of_nonneg_left hinner_abs (by positivity : 0 ≤ 2 * |qval| * Ival)
      linarith
    have h3 : 2 * (|qval| * ‖g‖ ^ 2) * (Ival * Real.sqrt S) ≤
        (|qval| * ‖g‖ ^ 2) ^ 2 + (Ival * Real.sqrt S) ^ 2 := by
      nlinarith [sq_nonneg (|qval| * ‖g‖ ^ 2 - Ival * Real.sqrt S)]
    have h4 : (|qval| * ‖g‖ ^ 2) ^ 2 + (Ival * Real.sqrt S) ^ 2 =
        qval ^ 2 * ‖g‖ ^ 4 + Ival ^ 2 * S := by
      rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hS_nn]; ring
    linarith
  have hexpand : A * (-qval ^ 2 * ‖g‖ ^ 2 - c * S) + ‖V‖ ^ 2 =
      c * ((-2 * qval * Ival * ⟪g, K g⟫ - (qval ^ 2 * ‖g‖ ^ 4 + Ival ^ 2 * S))
        - c * (‖g‖ ^ 2 * S - ‖K g‖ ^ 2)) := by
    rw [hV_sq]; dsimp only [A]; ring
  rw [hexpand]
  have hterm1 : -2 * qval * Ival * ⟪g, K g⟫ - (qval ^ 2 * ‖g‖ ^ 4 + Ival ^ 2 * S) ≤ 0 := by
    linarith
  have hterm2 : 0 ≤ c * (‖g‖ ^ 2 * S - ‖K g‖ ^ 2) := by
    exact mul_nonneg hc.le (sub_nonneg.mpr hKg_sq)
  exact mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith)

private lemma norm_eb (k : Fin m) : ‖eb k‖ = 1 :=
  (EuclideanSpace.basisFun (Fin m) ℝ).orthonormal.1 k

/-- Time derivative of `‖heat S.g s x‖ ^ 2` via coordinate-wise `heat_equation`. -/
private lemma heat_grad_norm_sq_tderiv (S : SmoothC3Bounded m) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => ‖heat S.g s x‖ ^ 2)
      (∑ i : Fin m, ⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫) t := by
  have hg_cont : Continuous S.g := continuous_iff_continuousAt.mpr fun y => (S.hg_deriv y).continuousAt
  have hgk_tderiv : ∀ (k : Fin m),
      HasDerivAt (fun s => ⟪heat S.g s x, eb k⟫)
        ((∑ i : Fin m, ⟪heat S.M t x (eb i) (eb k), eb i⟫) / 2) t := fun k => by
    let Fk : E → ℝ := fun y => ⟪S.g y, eb k⟫
    let gk : E → E := fun y => S.K y (eb k)
    let Kk : E → (E →L[ℝ] E) := fun y => (ContinuousLinearMap.apply ℝ E (eb k)).comp (S.M y)
    have hFk_deriv : ∀ y, HasFDerivAt Fk (innerSL ℝ (gk y)) y := fun y => by
      have hFk_eq : Fk = fun u => innerSL ℝ (eb k) (S.g u) := by
        ext u; simp [Fk, real_inner_comm]
      rw [hFk_eq]
      have h1 := ((innerSL ℝ (eb k)).hasFDerivAt).comp y (S.hg_deriv y)
      refine hasFDerivAt_congr_deriv h1 ?_
      ext v
      simp [gk, S.hK_symm]
    have hgk_deriv : ∀ y, HasFDerivAt gk (Kk y) y := fun y =>
      (ContinuousLinearMap.apply ℝ E (eb k)).hasFDerivAt.comp y (S.hK_deriv y)
    have hKk_cont : Continuous Kk :=
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) E
        (ContinuousLinearMap.apply ℝ E (eb k))).continuous.comp S.hM_cont
    have hFk_b : ∀ y, ‖Fk y‖ ≤ S.Cg := fun y => by
      calc ‖⟪S.g y, eb k⟫‖ = |⟪S.g y, eb k⟫| := Real.norm_eq_abs _
        _ ≤ ‖S.g y‖ * ‖eb k‖ := abs_real_inner_le_norm _ _
        _ = ‖S.g y‖ := by rw [norm_eb, mul_one]
        _ ≤ S.Cg := S.hg_bound y
    have hgk_b : ∀ y, ‖gk y‖ ≤ S.CK := fun y => by
      calc ‖S.K y (eb k)‖ ≤ ‖S.K y‖ * ‖eb k‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖S.K y‖ := by rw [norm_eb, mul_one]
        _ ≤ S.CK := S.hK_bound y
    have hKk_b : ∀ y, ‖Kk y‖ ≤ S.CM := fun y => by
      refine ContinuousLinearMap.opNorm_le_bound _ S.hCM_nn fun v => ?_
      calc ‖S.M y v (eb k)‖ ≤ ‖S.M y v‖ * ‖eb k‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖S.M y v‖ := by rw [norm_eb, mul_one]
        _ ≤ ‖S.M y‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ S.CM * ‖v‖ := by gcongr; exact S.hM_bound y
    have heq := heat_equation hFk_deriv hgk_deriv hKk_cont hFk_b hgk_b hKk_b ht x
    have hfun : (fun s => heat Fk s x) = (fun s => ⟪heat S.g s x, eb k⟫) := by
      ext s
      have hint : Integrable (fun z => S.g (x + Real.sqrt s • z)) γ :=
        integrable_heat_integrand hg_cont S.hg_bound s x
      have hc := (innerSL ℝ (eb k)).integral_comp_comm hint
      simpa [Fk, heat, real_inner_comm] using hc
    have hval : ∀ i : Fin m, ⟪heat Kk t x (eb i), eb i⟫ = ⟪heat S.M t x (eb i) (eb k), eb i⟫ := fun i => by
      have h1 : heat Kk t x (eb i) = heat (fun y => S.M y (eb i) (eb k)) t x := by
        simpa [Kk] using heat_clm_eval hKk_cont hKk_b (eb i) t x
      have hMi_cont : Continuous (fun y => S.M y (eb i)) := S.hM_cont.clm_apply continuous_const
      have hMi_b : ∀ y, ‖S.M y (eb i)‖ ≤ S.CM := fun y =>
        (ContinuousLinearMap.le_opNorm _ _).trans (by rw [norm_eb, mul_one]; exact S.hM_bound y)
      have h2 : heat S.M t x (eb i) (eb k) = heat (fun y => S.M y (eb i) (eb k)) t x := by
        rw [heat_clm_eval S.hM_cont S.hM_bound (eb i) t x]
        exact heat_clm_eval hMi_cont hMi_b (eb k) t x
      rw [h1, h2]
    rw [hfun] at heq
    refine heq.congr_deriv ?_
    congr 1
    exact Finset.sum_congr rfl fun i _ => hval i
  have hfun : (fun s => ‖heat S.g s x‖ ^ 2) = fun s => ∑ k : Fin m, ⟪heat S.g s x, eb k⟫ ^ 2 := by
    ext s; exact (parseval_sq (heat S.g s x)).symm
  rw [hfun]
  have hsum : HasDerivAt (fun s => ∑ k : Fin m, ⟪heat S.g s x, eb k⟫ ^ 2)
      (∑ k : Fin m, 2 * ⟪heat S.g t x, eb k⟫ *
        ((∑ i : Fin m, ⟪heat S.M t x (eb i) (eb k), eb i⟫) / 2)) t := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    refine ((hgk_tderiv k).pow 2).congr_deriv ?_
    norm_num
  refine hsum.congr_deriv ?_
  calc ∑ k : Fin m, 2 * ⟪heat S.g t x, eb k⟫ *
        ((∑ i : Fin m, ⟪heat S.M t x (eb i) (eb k), eb i⟫) / 2)
      = ∑ k : Fin m, ∑ i : Fin m, ⟪heat S.g t x, eb k⟫ * ⟪heat S.M t x (eb i) (eb k), eb i⟫ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.mul_sum]; ring
    _ = ∑ i : Fin m, ∑ k : Fin m, ⟪heat S.g t x, eb k⟫ * ⟪heat S.M t x (eb i) (eb k), eb i⟫ :=
          Finset.sum_comm
    _ = ∑ i : Fin m, ⟪heat S.M t x (eb i) (∑ k : Fin m, ⟪heat S.g t x, eb k⟫ • eb k), eb i⟫ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [map_sum, map_smul, sum_inner, real_inner_smul_left]
    _ = ∑ i : Fin m, ⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 2
          have hrepr := (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr' (heat S.g t x)
          simpa [EuclideanSpace.basisFun_inner, real_inner_comm] using hrepr

/-! Auxiliary Bakry–Ledoux definitions for `S : SmoothC3Bounded m`. -/

private noncomputable def bA (S : SmoothC3Bounded m) (t : ℝ) (x : E) : ℝ :=
  I (heat S.f t x) ^ 2 + (1 - t) * ‖heat S.g t x‖ ^ 2

private noncomputable def bΨ (S : SmoothC3Bounded m) (t : ℝ) (x : E) : ℝ :=
  Real.sqrt (bA S t x)

private noncomputable def bV (S : SmoothC3Bounded m) (t : ℝ) (x : E) : E :=
  (-(q (heat S.f t x) * I (heat S.f t x))) • heat S.g t x + (1 - t) • heat S.K t x (heat S.g t x)

private noncomputable def bGradΨ (S : SmoothC3Bounded m) (t : ℝ) (x : E) : E :=
  (bΨ S t x)⁻¹ • bV S t x

private noncomputable def bDV (S : SmoothC3Bounded m) (t : ℝ) (x : E) : E →L[ℝ] E :=
  ((q (heat S.f t x) ^ 2 - 1) • innerSL ℝ (heat S.g t x)).smulRight (heat S.g t x)
  + (-(q (heat S.f t x) * I (heat S.f t x))) • heat S.K t x
  + (1 - t) • ((heat S.M t x).flip (heat S.g t x) + (heat S.K t x).comp (heat S.K t x))

private noncomputable def bHessΨ (S : SmoothC3Bounded m) (t : ℝ) (x : E) : E →L[ℝ] E :=
  (-(bA S t x * bΨ S t x)⁻¹ • innerSL ℝ (bV S t x)).smulRight (bV S t x)
  + (bΨ S t x)⁻¹ • bDV S t x

private noncomputable def bDtA (S : SmoothC3Bounded m) (t : ℝ) (x : E) : ℝ :=
  -(q (heat S.f t x) * I (heat S.f t x)) * (∑ i : Fin m, ⟪heat S.K t x (eb i), eb i⟫)
  - ‖heat S.g t x‖ ^ 2
  + (1 - t) * (∑ i : Fin m, ⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫)

private noncomputable def bDtΨ (S : SmoothC3Bounded m) (t : ℝ) (x : E) : ℝ :=
  bDtA S t x / (2 * bΨ S t x)

private lemma SmoothC3Bounded.hf_cont (S : SmoothC3Bounded m) : Continuous S.f :=
  continuous_iff_continuousAt.mpr fun x => (S.hf_deriv x).continuousAt

private lemma SmoothC3Bounded.hg_cont (S : SmoothC3Bounded m) : Continuous S.g :=
  continuous_iff_continuousAt.mpr fun x => (S.hg_deriv x).continuousAt

private lemma SmoothC3Bounded.hK_cont (S : SmoothC3Bounded m) : Continuous S.K :=
  continuous_iff_continuousAt.mpr fun x => (S.hK_deriv x).continuousAt

private lemma SmoothC3Bounded.hf_bound (S : SmoothC3Bounded m) (x : E) : ‖S.f x‖ ≤ 1 := by
  have hm := S.hf_mem x
  rw [Real.norm_of_nonneg (le_trans S.hη_pos.le hm.1)]
  linarith [hm.2, S.hη_pos]

private lemma heat_K_symm (S : SmoothC3Bounded m) (t : ℝ) (x v w : E) :
    ⟪heat S.K t x v, w⟫ = ⟪v, heat S.K t x w⟫ := by
  have hint : Integrable (fun z => S.K (x + Real.sqrt t • z)) γ :=
    integrable_heat_integrand S.hK_cont S.hK_bound t x
  have h1 : ⟪heat S.K t x v, w⟫ = ∫ z, ⟪S.K (x + Real.sqrt t • z) v, w⟫ ∂γ := by
    let ev : (E →L[ℝ] E) →L[ℝ] ℝ := (innerSL ℝ w).comp (ContinuousLinearMap.apply ℝ E v)
    have hc := ev.integral_comp_comm hint
    simpa [ev, heat, real_inner_comm] using hc.symm
  have h2 : ⟪v, heat S.K t x w⟫ = ∫ z, ⟪v, S.K (x + Real.sqrt t • z) w⟫ ∂γ := by
    let ev : (E →L[ℝ] E) →L[ℝ] ℝ := (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E w)
    have hc := ev.integral_comp_comm hint
    simpa [ev, heat] using hc.symm
  rw [h1, h2]
  exact integral_congr_ae (ae_of_all _ fun z => S.hK_symm _ v w)

private lemma bA_lower (S : SmoothC3Bounded m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
    φ (max |q S.η| |q (1 - S.η)|) ^ 2 ≤ bA S t x := by
  have hu_mem : heat S.f t x ∈ Icc S.η (1 - S.η) := heat_mem_Icc S.hf_cont S.hf_mem t x
  have hI_lo : φ (max |q S.η| |q (1 - S.η)|) ≤ I (heat S.f t x) :=
    φ_ge_on_Icc S.hη_pos S.hη_le hu_mem
  have h1 : φ (max |q S.η| |q (1 - S.η)|) ^ 2 ≤ I (heat S.f t x) ^ 2 := by
    nlinarith [φ_pos (max |q S.η| |q (1 - S.η)|)]
  have h2 : 0 ≤ (1 - t) * ‖heat S.g t x‖ ^ 2 := mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg _)
  dsimp only [bA]; linarith

private lemma bA_pos (S : SmoothC3Bounded m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
    0 < bA S t x :=
  lt_of_lt_of_le (sq_pos_of_pos (φ_pos _)) (bA_lower S ht x)

private lemma bΨ_lower (S : SmoothC3Bounded m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
    φ (max |q S.η| |q (1 - S.η)|) ≤ bΨ S t x := by
  have h := Real.sqrt_le_sqrt (bA_lower S ht x)
  rwa [Real.sqrt_sq (φ_pos _).le] at h

private lemma bΨ_pos (S : SmoothC3Bounded m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
    0 < bΨ S t x :=
  lt_of_lt_of_le (φ_pos _) (bΨ_lower S ht x)

/-- Spatial and time derivatives of `bΨ`, `bGradΨ`, and the pointwise Bakry–Ledoux PDE inequality. -/
private lemma bobkov_derivs_and_pde (S : SmoothC3Bounded m) :
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, HasFDerivAt (bΨ S t) (innerSL ℝ (bGradΨ S t x)) x) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, HasFDerivAt (bGradΨ S t) (bHessΨ S t x) x) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, HasDerivAt (fun s => bΨ S s x) (bDtΨ S t x) t) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      bDtΨ S t x - (∑ i : Fin m, ⟪bHessΨ S t x (eb i), eb i⟫) / 2 ≤ 0) := by
  have hu_Ioo : ∀ t x, heat S.f t x ∈ Ioo (0 : ℝ) 1 := fun t x => by
    have hm := heat_mem_Icc S.hf_cont S.hf_mem t x
    exact ⟨lt_of_lt_of_le S.hη_pos hm.1, lt_of_le_of_lt hm.2 (by linarith [S.hη_pos])⟩
  have hu_fderiv : ∀ t x, HasFDerivAt (heat S.f t) (innerSL ℝ (heat S.g t x)) x := fun t x => by
    have h := fderiv_heat (F := S.f) (D := fun y => innerSL ℝ (S.g y))
      S.hf_deriv ((InnerProductSpace.toDual ℝ E).continuous.comp S.hg_cont)
      S.hf_bound (fun y => by simpa [innerSL_apply_norm] using S.hg_bound y) t x
    rwa [heat_innerSL_eq S.hg_cont S.hg_bound t x] at h
  have hg_fderiv : ∀ t x, HasFDerivAt (heat S.g t) (heat S.K t x) x := fun t x =>
    fderiv_heat S.hg_deriv S.hK_cont S.hg_bound S.hK_bound t x
  have hK_fderiv : ∀ t x, HasFDerivAt (heat S.K t) (heat S.M t x) x := fun t x =>
    fderiv_heat S.hK_deriv S.hM_cont S.hK_bound S.hM_bound t x
  have hA_fderiv : ∀ t x, HasFDerivAt (bA S t) (innerSL ℝ ((2 : ℝ) • bV S t x)) x := fun t x => by
    have h1 : HasFDerivAt (fun y => I (heat S.f t y) ^ 2)
        ((-2 * q (heat S.f t x) * I (heat S.f t x)) • innerSL ℝ (heat S.g t x)) x :=
      (hasDerivAt_I_sq (hu_Ioo t x)).comp_hasFDerivAt x (hu_fderiv t x)
    have h2 : HasFDerivAt (fun y => ‖heat S.g t y‖ ^ 2)
        ((2 : ℝ) • innerSL ℝ (heat S.K t x (heat S.g t x))) x := by
      have hsq : (fun y => ‖heat S.g t y‖ ^ 2) = fun y => ⟪heat S.g t y, heat S.g t y⟫ := by
        ext y; exact (real_inner_self_eq_norm_sq _).symm
      rw [hsq]
      refine hasFDerivAt_congr_deriv ((hg_fderiv t x).inner ℝ (hg_fderiv t x)) ?_
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        fderivInnerCLM_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
      rw [real_inner_comm (heat S.K t x v) (heat S.g t x), heat_K_symm S t x (heat S.g t x) v,
        real_inner_comm (heat S.g t x) (heat S.K t x v), ← heat_K_symm S t x (heat S.g t x) v]
      ring
    refine hasFDerivAt_congr_deriv (h1.add (h2.const_mul (1 - t))) ?_
    ext v
    simp only [bV, add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, inner_add_left,
      real_inner_smul_left]
    ring
  have hΨ_fderiv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      HasFDerivAt (bΨ S t) (innerSL ℝ (bGradΨ S t x)) x := fun t ht x => by
    have h := (Real.hasDerivAt_sqrt (bA_pos S ht x).ne').comp_hasFDerivAt x (hA_fderiv t x)
    refine hasFDerivAt_congr_deriv h ?_
    ext v
    simp only [bGradΨ, bΨ, smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_smul_left]
    ring
  have hV_fderiv : ∀ t x, HasFDerivAt (bV S t) (bDV S t x) x := fun t x => by
    have h1 := ((hasDerivAt_neg_q_mul_I (hu_Ioo t x)).comp_hasFDerivAt x
      (hu_fderiv t x)).smul (hg_fderiv t x)
    have h2 := ((hK_fderiv t x).clm_apply (hg_fderiv t x)).const_smul (1 - t)
    refine hasFDerivAt_congr_deriv (h1.add h2) ?_
    ext v
    simp only [bDV, Function.comp_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    abel
  have hgradΨ_fderiv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      HasFDerivAt (bGradΨ S t) (bHessΨ S t x) x := fun t ht x => by
    have hinv : HasFDerivAt (fun y => (bΨ S t y)⁻¹)
        (-(bA S t x * bΨ S t x)⁻¹ • innerSL ℝ (bV S t x)) x := by
      have h1 := (hasDerivAt_inv (bΨ_pos S ht x).ne').comp_hasFDerivAt x (hΨ_fderiv t ht x)
      refine hasFDerivAt_congr_deriv h1 ?_
      ext v
      have hsq : bΨ S t x ^ 2 = bA S t x := Real.sq_sqrt (bA_pos S ht x).le
      simp only [bGradΨ, smul_apply, innerSL_apply_apply, real_inner_smul_left, smul_eq_mul]
      have hΨne : bΨ S t x ≠ 0 := (bΨ_pos S ht x).ne'
      rw [← hsq]
      field_simp [hΨne]
    refine hasFDerivAt_congr_deriv (hinv.smul (hV_fderiv t x)) ?_
    ext v
    simp only [bHessΨ, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply]
    abel
  have hA_tderiv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, HasDerivAt (fun s => bA S s x) (bDtA S t x) t := by
    intro t ht x
    have hu_td := heat_equation S.hf_deriv S.hg_deriv S.hK_cont S.hf_bound S.hg_bound S.hK_bound
      ht.1 x
    have h1 := (hasDerivAt_I_sq (hu_Ioo t x)).comp t hu_td
    have h1t : HasDerivAt (fun s : ℝ => 1 - s) (-1) t :=
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).congr_deriv (by ring)
    have h2 := h1t.mul (heat_grad_norm_sq_tderiv S ht.1 x)
    refine (h1.add h2).congr_deriv ?_
    dsimp only [bDtA]; ring
  have hΨ_tderiv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, HasDerivAt (fun s => bΨ S s x) (bDtΨ S t x) t := by
    intro t ht x
    have h := (Real.hasDerivAt_sqrt (bA_pos S ⟨ht.1.le, ht.2.le⟩ x).ne').comp t (hA_tderiv t ht x)
    refine h.congr_deriv ?_
    dsimp only [bDtΨ, bΨ]; ring
  have hpde : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      bDtΨ S t x - (∑ i : Fin m, ⟪bHessΨ S t x (eb i), eb i⟫) / 2 ≤ 0 := fun t ht x => by
    have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hA_gt : 0 < bA S t x := bA_pos S htIcc x
    have hΨ_gt : 0 < bΨ S t x := bΨ_pos S htIcc x
    have hDV_tr : ∑ i : Fin m, ⟪bDV S t x (eb i), eb i⟫ =
        (q (heat S.f t x) ^ 2 - 1) * ‖heat S.g t x‖ ^ 2
        - q (heat S.f t x) * I (heat S.f t x) * (∑ i : Fin m, ⟪heat S.K t x (eb i), eb i⟫)
        + (1 - t) * (∑ i : Fin m, ⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫)
        + (1 - t) * (∑ i : Fin m, ‖heat S.K t x (eb i)‖ ^ 2) := by
      have hterm : ∀ i : Fin m, ⟪bDV S t x (eb i), eb i⟫ =
          (q (heat S.f t x) ^ 2 - 1) * ⟪heat S.g t x, eb i⟫ ^ 2
          + (-(q (heat S.f t x) * I (heat S.f t x))) * ⟪heat S.K t x (eb i), eb i⟫
          + (1 - t) * ⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫
          + (1 - t) * ‖heat S.K t x (eb i)‖ ^ 2 := fun i => by
        simp only [bDV, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
          inner_add_left, real_inner_smul_left]
        have hKK : ⟪heat S.K t x (heat S.K t x (eb i)), eb i⟫ = ‖heat S.K t x (eb i)‖ ^ 2 := by
          rw [heat_K_symm S t x (heat S.K t x (eb i)) (eb i), real_inner_self_eq_norm_sq]
        rw [hKK]; ring
      simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, parseval_sq]
      ring
    have hlap : ∑ i : Fin m, ⟪bHessΨ S t x (eb i), eb i⟫ =
        -(bA S t x * bΨ S t x)⁻¹ * ‖bV S t x‖ ^ 2 +
          (bΨ S t x)⁻¹ * (∑ i : Fin m, ⟪bDV S t x (eb i), eb i⟫) := by
      have hterm : ∀ i : Fin m, ⟪bHessΨ S t x (eb i), eb i⟫ =
          -(bA S t x * bΨ S t x)⁻¹ * ⟪bV S t x, eb i⟫ ^ 2 +
            (bΨ S t x)⁻¹ * ⟪bDV S t x (eb i), eb i⟫ := fun i => by
        simp only [bHessΨ, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
          innerSL_apply_apply, inner_add_left, real_inner_smul_left]
        ring
      simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, parseval_sq]
    have hdiff_A : bDtA S t x - ∑ i : Fin m, ⟪bDV S t x (eb i), eb i⟫ =
        -q (heat S.f t x) ^ 2 * ‖heat S.g t x‖ ^ 2 -
          (1 - t) * ∑ i : Fin m, ‖heat S.K t x (eb i)‖ ^ 2 := by
      rw [hDV_tr]; dsimp only [bDtA]; ring
    have hrewrite : bDtΨ S t x - (∑ i : Fin m, ⟪bHessΨ S t x (eb i), eb i⟫) / 2 =
        (bA S t x * (bDtA S t x - ∑ i : Fin m, ⟪bDV S t x (eb i), eb i⟫) + ‖bV S t x‖ ^ 2) /
          (2 * bA S t x * bΨ S t x) := by
      rw [hlap]; dsimp only [bDtΨ]
      field_simp [hA_gt.ne', hΨ_gt.ne']; ring
    rw [hrewrite, hdiff_A]
    refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
    exact bakry_ledoux_pointwise (I_pos (heat S.f t x)) (sub_pos.mpr ht.2) (heat_K_symm S t x)
  exact ⟨hΨ_fderiv, hgradΨ_fderiv, hΨ_tderiv, hpde⟩

/-- Uniform bounds for `bGradΨ`, `bHessΨ`, `bDtΨ`. -/
private lemma bobkov_bounds (S : SmoothC3Bounded m) :
    ∃ (Cgrad Chess Cdt : ℝ),
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖bGradΨ S t x‖ ≤ Cgrad) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖bHessΨ S t x‖ ≤ Chess) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, |bDtΨ S t x| ≤ Cdt) := by
  have hCg_nn : 0 ≤ S.Cg := S.hCg_nn
  have hCK_nn : 0 ≤ S.CK := S.hCK_nn
  have hCM_nn : 0 ≤ S.CM := S.hCM_nn
  set Q : ℝ := max |q S.η| |q (1 - S.η)|
  set c₀ : ℝ := φ Q
  have hQ_nn : 0 ≤ Q := le_trans (abs_nonneg _) (le_max_left _ _)
  have hc₀_pos : 0 < c₀ := φ_pos Q
  have hu_mem : ∀ t x, heat S.f t x ∈ Icc S.η (1 - S.η) := fun t x =>
    heat_mem_Icc S.hf_cont S.hf_mem t x
  have hq_bound : ∀ t x, |q (heat S.f t x)| ≤ Q := fun t x =>
    abs_q_le_on_Icc S.hη_pos S.hη_le (hu_mem t x)
  have hI_upper : ∀ t x, I (heat S.f t x) ≤ 1 := fun t x => φ_le_one _
  have hg_bound : ∀ t x, ‖heat S.g t x‖ ≤ S.Cg := fun t x => norm_heat_le hCg_nn S.hg_bound t x
  have hK_bound : ∀ t x, ‖heat S.K t x‖ ≤ S.CK := fun t x => norm_heat_le hCK_nn S.hK_bound t x
  have hM_bound : ∀ t x, ‖heat S.M t x‖ ≤ S.CM := fun t x => norm_heat_le hCM_nn S.hM_bound t x
  set CV : ℝ := Q * S.Cg + S.CK * S.Cg
  have hCV_nn : 0 ≤ CV := by positivity
  have hV_bound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖bV S t x‖ ≤ CV := fun t ht x => by
    have hI_nn : 0 ≤ I (heat S.f t x) := (I_pos _).le
    dsimp only [bV]
    calc ‖(-(q (heat S.f t x) * I (heat S.f t x))) • heat S.g t x +
          (1 - t) • heat S.K t x (heat S.g t x)‖
        ≤ ‖(-(q (heat S.f t x) * I (heat S.f t x))) • heat S.g t x‖ +
          ‖(1 - t) • heat S.K t x (heat S.g t x)‖ := norm_add_le _ _
      _ = |q (heat S.f t x)| * I (heat S.f t x) * ‖heat S.g t x‖ +
          (1 - t) * ‖heat S.K t x (heat S.g t x)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_neg, abs_mul,
            abs_of_nonneg hI_nn, Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]
      _ ≤ Q * 1 * S.Cg + 1 * (S.CK * S.Cg) := by
          have hKg : ‖heat S.K t x (heat S.g t x)‖ ≤ S.CK * S.Cg :=
            (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hK_bound t x; exact hg_bound t x)
          gcongr
          · exact hq_bound t x
          · exact hI_upper t x
          · exact hg_bound t x
          · linarith [ht.1]
      _ = CV := by dsimp only [CV]; ring
  have hgradΨ_bound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖bGradΨ S t x‖ ≤ c₀⁻¹ * CV := fun t ht x => by
    dsimp only [bGradΨ]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (bΨ_pos S ht x).le)]
    gcongr
    · exact bΨ_lower S ht x
    · exact hV_bound t ht x
  set CDV : ℝ := (Q ^ 2 + 1) * S.Cg ^ 2 + Q * S.CK + (S.CM * S.Cg + S.CK ^ 2)
  have hDV_bound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖bDV S t x‖ ≤ CDV := fun t ht x => by
    have hI_nn : 0 ≤ I (heat S.f t x) := (I_pos _).le
    have h1 : ‖((q (heat S.f t x) ^ 2 - 1) • innerSL ℝ (heat S.g t x)).smulRight (heat S.g t x)‖ ≤
        (Q ^ 2 + 1) * S.Cg ^ 2 := by
      have habs : |q (heat S.f t x) ^ 2 - 1| ≤ Q ^ 2 + 1 := by
        have hsq : q (heat S.f t x) ^ 2 ≤ Q ^ 2 := by
          nlinarith [sq_abs (q (heat S.f t x)), abs_nonneg (q (heat S.f t x)), hq_bound t x]
        calc |q (heat S.f t x) ^ 2 - 1| ≤ |q (heat S.f t x) ^ 2| + |1| := abs_sub _ _
          _ = q (heat S.f t x) ^ 2 + 1 := by rw [abs_of_nonneg (sq_nonneg _), abs_one]
          _ ≤ Q ^ 2 + 1 := by linarith
      calc ‖((q (heat S.f t x) ^ 2 - 1) • innerSL ℝ (heat S.g t x)).smulRight (heat S.g t x)‖
          ≤ ‖(q (heat S.f t x) ^ 2 - 1) • innerSL ℝ (heat S.g t x)‖ * ‖heat S.g t x‖ :=
            norm_smulRight_le _ _
        _ = |q (heat S.f t x) ^ 2 - 1| * ‖heat S.g t x‖ * ‖heat S.g t x‖ := by
            rw [norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
        _ ≤ (Q ^ 2 + 1) * S.Cg * S.Cg := by gcongr <;> exact hg_bound t x
        _ = (Q ^ 2 + 1) * S.Cg ^ 2 := by ring
    have h2 : ‖(-(q (heat S.f t x) * I (heat S.f t x))) • heat S.K t x‖ ≤ Q * S.CK := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hI_nn]
      calc |q (heat S.f t x)| * I (heat S.f t x) * ‖heat S.K t x‖ ≤ Q * 1 * S.CK := by
            gcongr; exact hq_bound t x; exact hI_upper t x; exact hK_bound t x
        _ = Q * S.CK := by ring
    have h3 : ‖(1 - t) • ((heat S.M t x).flip (heat S.g t x) +
        (heat S.K t x).comp (heat S.K t x))‖ ≤ S.CM * S.Cg + S.CK ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]
      have hflip : ‖(heat S.M t x).flip (heat S.g t x)‖ ≤ S.CM * S.Cg := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        calc ‖heat S.M t x v (heat S.g t x)‖ ≤ ‖heat S.M t x v‖ * ‖heat S.g t x‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ (S.CM * ‖v‖) * S.Cg := by
              gcongr
              · exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hM_bound t x)
              · exact hg_bound t x
          _ = S.CM * S.Cg * ‖v‖ := by ring
      have hcomp : ‖(heat S.K t x).comp (heat S.K t x)‖ ≤ S.CK ^ 2 := by
        calc ‖(heat S.K t x).comp (heat S.K t x)‖ ≤ ‖heat S.K t x‖ * ‖heat S.K t x‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ S.CK * S.CK := by gcongr <;> exact hK_bound t x
          _ = S.CK ^ 2 := (sq S.CK).symm
      calc (1 - t) * ‖(heat S.M t x).flip (heat S.g t x) + (heat S.K t x).comp (heat S.K t x)‖
          ≤ 1 * (‖(heat S.M t x).flip (heat S.g t x)‖ + ‖(heat S.K t x).comp (heat S.K t x)‖) := by
            gcongr; linarith [ht.1]; exact norm_add_le _ _
        _ ≤ S.CM * S.Cg + S.CK ^ 2 := by linarith
    dsimp only [bDV, CDV]
    calc ‖((q (heat S.f t x) ^ 2 - 1) • innerSL ℝ (heat S.g t x)).smulRight (heat S.g t x)
          + (-(q (heat S.f t x) * I (heat S.f t x))) • heat S.K t x
          + (1 - t) • ((heat S.M t x).flip (heat S.g t x) + (heat S.K t x).comp (heat S.K t x))‖
        ≤ ‖((q (heat S.f t x) ^ 2 - 1) • innerSL ℝ (heat S.g t x)).smulRight (heat S.g t x)
          + (-(q (heat S.f t x) * I (heat S.f t x))) • heat S.K t x‖
          + ‖(1 - t) • ((heat S.M t x).flip (heat S.g t x) + (heat S.K t x).comp (heat S.K t x))‖ :=
            norm_add_le _ _
      _ ≤ ‖((q (heat S.f t x) ^ 2 - 1) • innerSL ℝ (heat S.g t x)).smulRight (heat S.g t x)‖
          + ‖(-(q (heat S.f t x) * I (heat S.f t x))) • heat S.K t x‖
          + ‖(1 - t) • ((heat S.M t x).flip (heat S.g t x) + (heat S.K t x).comp (heat S.K t x))‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ (Q ^ 2 + 1) * S.Cg ^ 2 + Q * S.CK + (S.CM * S.Cg + S.CK ^ 2) := by linarith
  have hhessΨ_bound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      ‖bHessΨ S t x‖ ≤ (c₀ ^ 3)⁻¹ * CV ^ 2 + c₀⁻¹ * CDV := fun t ht x => by
    have h1 : ‖(-(bA S t x * bΨ S t x)⁻¹ • innerSL ℝ (bV S t x)).smulRight (bV S t x)‖ ≤
        (c₀ ^ 3)⁻¹ * CV ^ 2 := by
      have hden : c₀ ^ 3 ≤ bA S t x * bΨ S t x := by
        have hA := bA_lower S ht x
        have hΨ := bΨ_lower S ht x
        calc c₀ ^ 3 = c₀ ^ 2 * c₀ := by ring
          _ ≤ bA S t x * bΨ S t x := mul_le_mul hA hΨ hc₀_pos.le (bA_pos S ht x).le
      calc ‖(-(bA S t x * bΨ S t x)⁻¹ • innerSL ℝ (bV S t x)).smulRight (bV S t x)‖
          ≤ ‖-(bA S t x * bΨ S t x)⁻¹ • innerSL ℝ (bV S t x)‖ * ‖bV S t x‖ :=
            norm_smulRight_le _ _
        _ = (bA S t x * bΨ S t x)⁻¹ * ‖bV S t x‖ * ‖bV S t x‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_neg,
              abs_of_nonneg (inv_nonneg.mpr (mul_nonneg (bA_pos S ht x).le (bΨ_pos S ht x).le)),
              innerSL_apply_norm]
        _ ≤ (c₀ ^ 3)⁻¹ * CV * CV := by gcongr <;> exact hV_bound t ht x
        _ = (c₀ ^ 3)⁻¹ * CV ^ 2 := by ring
    have h2 : ‖(bΨ S t x)⁻¹ • bDV S t x‖ ≤ c₀⁻¹ * CDV := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (bΨ_pos S ht x).le)]
      gcongr
      · exact bΨ_lower S ht x
      · exact hDV_bound t ht x
    dsimp only [bHessΨ]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have hdtΨ_bound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      |bDtΨ S t x| ≤ (Q * (m * S.CK) + S.Cg ^ 2 + m * S.CM * S.Cg) / (2 * c₀) := fun t ht x => by
    have hI_nn : 0 ≤ I (heat S.f t x) := (I_pos _).le
    have htr : |∑ i : Fin m, ⟪heat S.K t x (eb i), eb i⟫| ≤ m * S.CK := by
      calc |∑ i : Fin m, ⟪heat S.K t x (eb i), eb i⟫|
          ≤ ∑ i : Fin m, |⟪heat S.K t x (eb i), eb i⟫| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin m, S.CK := Finset.sum_le_sum fun i _ => by
            calc |⟪heat S.K t x (eb i), eb i⟫| ≤ ‖heat S.K t x (eb i)‖ * ‖eb i‖ := abs_real_inner_le_norm _ _
              _ = ‖heat S.K t x (eb i)‖ := by rw [norm_eb, mul_one]
              _ ≤ ‖heat S.K t x‖ * ‖eb i‖ := ContinuousLinearMap.le_opNorm _ _
              _ = ‖heat S.K t x‖ := by rw [norm_eb, mul_one]
              _ ≤ S.CK := hK_bound t x
        _ = m * S.CK := by simp
    have hMsum : |∑ i : Fin m, ⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫| ≤ m * S.CM * S.Cg := by
      calc |∑ i : Fin m, ⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫|
          ≤ ∑ i : Fin m, |⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin m, S.CM * S.Cg := Finset.sum_le_sum fun i _ => by
            calc |⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫|
                ≤ ‖heat S.M t x (eb i) (heat S.g t x)‖ * ‖eb i‖ := abs_real_inner_le_norm _ _
              _ = ‖heat S.M t x (eb i) (heat S.g t x)‖ := by rw [norm_eb, mul_one]
              _ ≤ ‖heat S.M t x (eb i)‖ * ‖heat S.g t x‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ (‖heat S.M t x‖ * ‖eb i‖) * ‖heat S.g t x‖ := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
              _ = ‖heat S.M t x‖ * ‖heat S.g t x‖ := by rw [norm_eb, mul_one]
              _ ≤ S.CM * S.Cg := by gcongr; exact hM_bound t x; exact hg_bound t x
        _ = m * S.CM * S.Cg := by simp [mul_assoc]
    have hdtA_abs : |bDtA S t x| ≤ Q * (m * S.CK) + S.Cg ^ 2 + m * S.CM * S.Cg := by
      dsimp only [bDtA]
      calc |-(q (heat S.f t x) * I (heat S.f t x)) * (∑ i, ⟪heat S.K t x (eb i), eb i⟫) -
            ‖heat S.g t x‖ ^ 2 + (1 - t) * (∑ i, ⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫)|
          ≤ |-(q (heat S.f t x) * I (heat S.f t x)) * (∑ i, ⟪heat S.K t x (eb i), eb i⟫) -
            ‖heat S.g t x‖ ^ 2| + |(1 - t) * (∑ i, ⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫)| :=
              abs_add_le _ _
        _ ≤ |-(q (heat S.f t x) * I (heat S.f t x)) * (∑ i, ⟪heat S.K t x (eb i), eb i⟫)| +
            |‖heat S.g t x‖ ^ 2| + |(1 - t) * (∑ i, ⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫)| := by
              gcongr; exact abs_sub _ _
        _ = |q (heat S.f t x)| * I (heat S.f t x) * |∑ i, ⟪heat S.K t x (eb i), eb i⟫| +
            ‖heat S.g t x‖ ^ 2 + (1 - t) * |∑ i, ⟪heat S.M t x (eb i) (heat S.g t x), eb i⟫| := by
            rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hI_nn,
              abs_of_nonneg (sq_nonneg ‖heat S.g t x‖), abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
        _ ≤ Q * 1 * (m * S.CK) + S.Cg ^ 2 + 1 * (m * S.CM * S.Cg) := by
            gcongr
            · exact hq_bound t x
            · exact hI_upper t x
            · exact hg_bound t x
            · linarith [ht.1]
        _ = Q * (m * S.CK) + S.Cg ^ 2 + m * S.CM * S.Cg := by ring
    dsimp only [bDtΨ]
    rw [abs_div, abs_of_pos (mul_pos zero_lt_two (bΨ_pos S ht x))]
    gcongr
    exact bΨ_lower S ht x
  exact ⟨c₀⁻¹ * CV, (c₀ ^ 3)⁻¹ * CV ^ 2 + c₀⁻¹ * CDV,
    (Q * (m * S.CK) + S.Cg ^ 2 + m * S.CM * S.Cg) / (2 * c₀),
    hgradΨ_bound, hhessΨ_bound, hdtΨ_bound⟩

/-- Joint continuity of `bΨ` and `bDtA`. -/
private lemma bobkov_Ψ_dtA_cont (S : SmoothC3Bounded m) :
    Continuous (fun p : ℝ × E => bΨ S p.1 p.2) ∧
    Continuous (fun p : ℝ × E => bDtA S p.1 p.2) := by
  have hu_Ioo : ∀ t x, heat S.f t x ∈ Ioo (0 : ℝ) 1 := fun t x => by
    have hm := heat_mem_Icc S.hf_cont S.hf_mem t x
    exact ⟨lt_of_lt_of_le S.hη_pos hm.1, lt_of_le_of_lt hm.2 (by linarith [S.hη_pos])⟩
  have hu_cont : Continuous (fun p : ℝ × E => heat S.f p.1 p.2) := continuous_heat S.hf_cont S.hf_bound
  have hg_cont' : Continuous (fun p : ℝ × E => heat S.g p.1 p.2) := continuous_heat S.hg_cont S.hg_bound
  have hK_cont' : Continuous (fun p : ℝ × E => heat S.K p.1 p.2) := continuous_heat S.hK_cont S.hK_bound
  have hqu_cont : Continuous (fun p : ℝ × E => q (heat S.f p.1 p.2)) :=
    continuousOn_q.comp_continuous hu_cont fun p => hu_Ioo p.1 p.2
  have hIu_cont : Continuous (fun p : ℝ × E => I (heat S.f p.1 p.2)) := continuous_φ.comp hqu_cont
  have hA_cont : Continuous (fun p : ℝ × E => bA S p.1 p.2) :=
    (hIu_cont.pow 2).add (((continuous_const (y := (1 : ℝ))).sub continuous_fst).mul (hg_cont'.norm.pow 2))
  have hΨ_cont : Continuous (fun p : ℝ × E => bΨ S p.1 p.2) := Real.continuous_sqrt.comp hA_cont
  have hdtA_cont : Continuous (fun p : ℝ × E => bDtA S p.1 p.2) := by
    have hc1 : Continuous (fun p : ℝ × E => ∑ i : Fin m, ⟪heat S.K p.1 p.2 (eb i), eb i⟫) :=
      continuous_finsetSum _ fun i _ =>
        (hK_cont'.clm_apply continuous_const).inner continuous_const
    have hc2 : Continuous (fun p : ℝ × E => ∑ i : Fin m, ⟪heat S.M p.1 p.2 (eb i) (heat S.g p.1 p.2), eb i⟫) := by
      refine continuous_finsetSum _ fun i _ => ?_
      have hMi_eq : (fun p : ℝ × E => heat S.M p.1 p.2 (eb i)) =
          fun p => heat (fun y => S.M y (eb i)) p.1 p.2 :=
        funext fun p => heat_clm_eval S.hM_cont S.hM_bound (eb i) p.1 p.2
      have hMi_c : Continuous (fun p : ℝ × E => heat S.M p.1 p.2 (eb i)) := by
        rw [hMi_eq]
        exact continuous_heat (S.hM_cont.clm_apply continuous_const) (fun y =>
          (ContinuousLinearMap.le_opNorm _ _).trans (by rw [norm_eb, mul_one]; exact S.hM_bound y))
      exact (hMi_c.clm_apply hg_cont').inner continuous_const
    exact ((hqu_cont.mul hIu_cont).neg.mul hc1).sub (hg_cont'.norm.pow 2)
      |>.add (((continuous_const (y := (1 : ℝ))).sub continuous_fst).mul hc2)
  exact ⟨hΨ_cont, hdtA_cont⟩

/-- Continuity properties for `bΨ` and `bDtΨ`. -/
private lemma bobkov_cont (S : SmoothC3Bounded m) :
    Continuous (fun p : ℝ × E => bΨ S p.1 p.2) ∧
    ContinuousOn (fun p : ℝ × E => bDtΨ S p.1 p.2) (Ioo 0 1 ×ˢ univ) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, Continuous (fun x => bDtΨ S t x)) := by
  obtain ⟨hΨ_cont, hdtA_cont⟩ := bobkov_Ψ_dtA_cont S
  have hdtΨ_cont : ContinuousOn (fun p : ℝ × E => bDtΨ S p.1 p.2) (Ioo 0 1 ×ˢ univ) := by
    refine hdtA_cont.continuousOn.div (hΨ_cont.const_mul 2).continuousOn fun p hp => ?_
    exact (mul_pos zero_lt_two (bΨ_pos S ⟨hp.1.1.le, hp.1.2.le⟩ p.2)).ne'
  have hdtΨ_cont_x : ∀ t ∈ Ioo (0 : ℝ) 1, Continuous (fun x => bDtΨ S t x) := fun t ht => by
    have hslice : Continuous (fun x : E => (t, x)) := continuous_const.prodMk continuous_id
    have hdtA_t : Continuous (fun x => bDtA S t x) := by
      simpa only [Function.comp_def] using hdtA_cont.comp hslice
    have hΨ_t : Continuous (fun x => bΨ S t x) := by
      simpa only [Function.comp_def] using hΨ_cont.comp hslice
    exact hdtA_t.div (hΨ_t.const_mul 2) fun x =>
      (mul_pos zero_lt_two (bΨ_pos S ⟨ht.1.le, ht.2.le⟩ x)).ne'
  exact ⟨hΨ_cont, hdtΨ_cont, hdtΨ_cont_x⟩

/-- Spatial continuity of `bHessΨ S t` for `t ∈ [0, 1]`. -/
private lemma bobkov_hess_cont (S : SmoothC3Bounded m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Continuous (bHessΨ S t) := by
  have hu_Ioo : ∀ x, heat S.f t x ∈ Ioo (0 : ℝ) 1 := fun x => by
    have hm := heat_mem_Icc S.hf_cont S.hf_mem t x
    exact ⟨lt_of_lt_of_le S.hη_pos hm.1, lt_of_le_of_lt hm.2 (by linarith [S.hη_pos])⟩
  have hslice : Continuous (fun x : E => (t, x)) := continuous_const.prodMk continuous_id
  have hu_t : Continuous (heat S.f t) := (continuous_heat S.hf_cont S.hf_bound).comp hslice
  have hg_t : Continuous (heat S.g t) := (continuous_heat S.hg_cont S.hg_bound).comp hslice
  have hK_t : Continuous (heat S.K t) := (continuous_heat S.hK_cont S.hK_bound).comp hslice
  have hM_t : Continuous (heat S.M t) := (continuous_heat S.hM_cont S.hM_bound).comp hslice
  have hqu_t : Continuous (fun x => q (heat S.f t x)) :=
    continuousOn_q.comp_continuous hu_t hu_Ioo
  have hIu_t : Continuous (fun x => I (heat S.f t x)) := continuous_φ.comp hqu_t
  have hA_t : Continuous (bA S t) :=
    (hIu_t.pow 2).add ((hg_t.norm.pow 2).const_mul (1 - t))
  have hΨ_t : Continuous (bΨ S t) := Real.continuous_sqrt.comp hA_t
  have hV_t : Continuous (bV S t) :=
    ((hqu_t.mul hIu_t).neg.smul hg_t).add ((hK_t.clm_apply hg_t).const_smul (1 - t))
  have hDV_t : Continuous (bDV S t) := by
    have h1 : Continuous (fun x => ((q (heat S.f t x) ^ 2 - 1) • innerSL ℝ (heat S.g t x)).smulRight (heat S.g t x)) :=
      ((ContinuousLinearMap.smulRightL ℝ E E).continuous.comp
        (((hqu_t.pow 2).sub (continuous_const (y := (1 : ℝ)))).smul
          ((innerSL ℝ).continuous.comp hg_t))).clm_apply hg_t
    have h2 : Continuous (fun x => (-(q (heat S.f t x) * I (heat S.f t x))) • heat S.K t x) :=
      (hqu_t.mul hIu_t).neg.smul hK_t
    have h3 : Continuous (fun x => (heat S.M t x).flip (heat S.g t x)) :=
      ((ContinuousLinearMap.flipₗᵢ ℝ E E E).continuous.comp hM_t).clm_apply hg_t
    have h4 : Continuous (fun x => (heat S.K t x).comp (heat S.K t x)) :=
      hK_t.clm_comp hK_t
    exact (h1.add h2).add ((h3.add h4).const_smul (1 - t))
  have h1 : Continuous (fun x => (-(bA S t x * bΨ S t x)⁻¹ • innerSL ℝ (bV S t x)).smulRight (bV S t x)) :=
    ((ContinuousLinearMap.smulRightL ℝ E E).continuous.comp
      ((((hA_t.mul hΨ_t).inv₀ fun x => (mul_pos (bA_pos S ht x) (bΨ_pos S ht x)).ne').neg).smul
        ((innerSL ℝ).continuous.comp hV_t))).clm_apply hV_t
  have h2 : Continuous (fun x => (bΨ S t x)⁻¹ • bDV S t x) :=
    (hΨ_t.inv₀ fun x => (bΨ_pos S ht x).ne').smul hDV_t
  exact h1.add h2

/-- Upper bound on `‖bΨ S t x‖` for `t ∈ [0, 1]`. -/
private lemma bΨ_norm_le (S : SmoothC3Bounded m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
    ‖bΨ S t x‖ ≤ Real.sqrt (1 + S.Cg ^ 2) := by
  dsimp only [bΨ]
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  have h1 : I (heat S.f t x) ^ 2 ≤ 1 := by
    have hI1 : I (heat S.f t x) ≤ 1 := φ_le_one _
    nlinarith [I_pos (heat S.f t x)]
  have h2 : (1 - t) * ‖heat S.g t x‖ ^ 2 ≤ S.Cg ^ 2 := by
    have hg2 : ‖heat S.g t x‖ ^ 2 ≤ S.Cg ^ 2 := by
      nlinarith [norm_heat_le S.hCg_nn S.hg_bound t x, norm_nonneg (heat S.g t x)]
    nlinarith [ht.1, ht.2, sq_nonneg S.Cg]
  dsimp only [bA]; linarith

/-- Nonpositivity of the derivative of the Bakry–Ledoux functional `Λ` on `(0, 1)`. -/
private lemma bobkov_Λ_deriv (S : SmoothC3Bounded m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ d ≤ (0 : ℝ), HasDerivAt (fun s => ∫ z, bΨ S s (Real.sqrt (1 - s) • z) ∂γ) d t := by
  obtain ⟨hΨ_fderiv, hgradΨ_fderiv, hΨ_tderiv, hpde⟩ := bobkov_derivs_and_pde S
  obtain ⟨Cgrad, Chess, Cdt, hgradΨ_bound, hhessΨ_bound, hdtΨ_bound⟩ := bobkov_bounds S
  obtain ⟨hΨ_cont, hdtΨ_cont, hdtΨ_cont_x⟩ := bobkov_cont S
  have hhessΨ_cont_t : Continuous (bHessΨ S t) := bobkov_hess_cont S ⟨ht.1.le, ht.2.le⟩
  have hCgrad_nn : 0 ≤ Cgrad := le_trans (norm_nonneg _) (hgradΨ_bound 0 ⟨le_rfl, zero_le_one⟩ 0)
  have hChess_nn : 0 ≤ Chess := le_trans (norm_nonneg (bHessΨ S 0 0)) (hhessΨ_bound 0 ⟨le_rfl, zero_le_one⟩ 0)
  set a := t / 2 with ha_def
  set b := (t + 1) / 2 with hb_def
  have ha0 : 0 < a := by rw [ha_def]; linarith [ht.1]
  have hab : a < t ∧ t < b := ⟨by rw [ha_def]; linarith [ht.1], by rw [hb_def]; linarith [ht.2]⟩
  have hb1 : b < 1 := by rw [hb_def]; linarith [ht.2]
  have hIoo_sub : Ioo a b ⊆ Ioo 0 1 := fun s hs => ⟨lt_trans ha0 hs.1, lt_trans hs.2 hb1⟩
  set r : ℝ → ℝ := fun s => Real.sqrt (1 - s)
  have hpair : ∀ s : ℝ, Continuous (fun z : E => (s, r s • z)) := fun s =>
    continuous_const.prodMk (continuous_id.const_smul (r s))
  have hr_deriv : ∀ s ∈ Ioo a b, HasDerivAt r (-(2 * r s)⁻¹) s := fun s hs => by
    have h1s : 0 < 1 - s := by linarith [(hIoo_sub hs).2]
    have h := (Real.hasDerivAt_sqrt h1s.ne').comp s
      ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))
    refine h.congr_deriv ?_
    dsimp only [r]; ring
  let F' : ℝ → E → ℝ := fun s z =>
    bDtΨ S s (r s • z) - (2 * r s)⁻¹ * ⟪bGradΨ S s (r s • z), z⟫
  have hpt_deriv : ∀ z : E, ∀ s ∈ Ioo a b,
      HasDerivAt (fun τ => bΨ S τ (r τ • z)) (F' s z) s := fun z s hs => by
    have hsIoo : s ∈ Ioo 0 1 := hIoo_sub hs
    have h := hasDerivAt_time_space (F := bΨ S) (Ft := bDtΨ S) (Fx := bGradΨ S s)
      hsIoo (hr_deriv s hs) z hΨ_tderiv (hΨ_fderiv s ⟨hsIoo.1.le, hsIoo.2.le⟩ _) hdtΨ_cont
    refine h.congr_deriv ?_
    dsimp only [F']; ring
  set rmin : ℝ := Real.sqrt (1 - b)
  have hrmin_pos : 0 < rmin := Real.sqrt_pos.mpr (by linarith)
  have hbound : ∀ z : E, ∀ s ∈ Ioo a b,
      ‖F' s z‖ ≤ Cdt + (2 * rmin)⁻¹ * Cgrad * ‖z‖ := fun z s hs => by
    have hsIcc : s ∈ Icc (0 : ℝ) 1 := ⟨(hIoo_sub hs).1.le, (hIoo_sub hs).2.le⟩
    have hrs_ge : rmin ≤ r s := Real.sqrt_le_sqrt (by linarith [hs.2])
    have hrs_pos : 0 < r s := lt_of_lt_of_le hrmin_pos hrs_ge
    dsimp only [F']
    rw [Real.norm_eq_abs]
    calc |bDtΨ S s (r s • z) - (2 * r s)⁻¹ * ⟪bGradΨ S s (r s • z), z⟫|
        ≤ |bDtΨ S s (r s • z)| + |(2 * r s)⁻¹ * ⟪bGradΨ S s (r s • z), z⟫| := abs_sub _ _
      _ = |bDtΨ S s (r s • z)| + (2 * r s)⁻¹ * |⟪bGradΨ S s (r s • z), z⟫| := by
          rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos zero_lt_two hrs_pos))]
      _ ≤ Cdt + (2 * rmin)⁻¹ * (Cgrad * ‖z‖) := by
          gcongr
          · exact hdtΨ_bound s hsIcc _
          · exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact hgradΨ_bound s hsIcc _)
      _ = Cdt + (2 * rmin)⁻¹ * Cgrad * ‖z‖ := by ring
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun z => bΨ S s (r s • z)) γ :=
    Filter.Eventually.of_forall fun s => (hΨ_cont.comp (hpair s)).aestronglyMeasurable
  have hF_int : Integrable (fun z => bΨ S t (r t • z)) γ :=
    Integrable.of_bound (hΨ_cont.comp (hpair t)).aestronglyMeasurable
      (Real.sqrt (1 + S.Cg ^ 2)) (ae_of_all _ fun z => bΨ_norm_le S ⟨ht.1.le, ht.2.le⟩ _)
  have hdt_cont_t : Continuous (fun z => bDtΨ S t (r t • z)) :=
    (hdtΨ_cont_x t ht).comp (continuous_id.const_smul (r t))
  have hF'_meas : AEStronglyMeasurable (F' t) γ := by
    have hc2 : Continuous (fun z => bGradΨ S t (r t • z)) :=
      (continuous_iff_continuousAt.mpr fun x => (hgradΨ_fderiv t ⟨ht.1.le, ht.2.le⟩ x).continuousAt).comp
        (continuous_id.const_smul (r t))
    exact (hdt_cont_t.sub ((hc2.inner continuous_id).const_mul _)).aestronglyMeasurable
  have hdom_int : Integrable (fun z : E => Cdt + (2 * rmin)⁻¹ * Cgrad * ‖z‖) γ :=
    (integrable_const Cdt).add (integrable_norm_stdGaussian.const_mul _)
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds hab.1 hab.2) hF_meas hF_int hF'_meas
    (ae_of_all _ hbound) hdom_int (ae_of_all _ hpt_deriv)
  have hstein := stein_trace (hgradΨ_fderiv t ⟨ht.1.le, ht.2.le⟩)
    hhessΨ_cont_t
    (hgradΨ_bound t ⟨ht.1.le, ht.2.le⟩)
    (hhessΨ_bound t ⟨ht.1.le, ht.2.le⟩) (r t) 0
  simp only [zero_add] at hstein
  have hint_dt : Integrable (fun z => bDtΨ S t (r t • z)) γ :=
    Integrable.of_bound hdt_cont_t.aestronglyMeasurable
      Cdt (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]; exact hdtΨ_bound t ⟨ht.1.le, ht.2.le⟩ _)
  have hint_grad : Integrable (fun z => ⟪bGradΨ S t (r t • z), z⟫) γ := by
    have hc : Continuous (fun z => ⟪bGradΨ S t (r t • z), z⟫) :=
      ((continuous_iff_continuousAt.mpr fun x =>
        (hgradΨ_fderiv t ⟨ht.1.le, ht.2.le⟩ x).continuousAt).comp
        (continuous_id.const_smul (r t))).inner continuous_id
    exact (integrable_norm_stdGaussian.const_mul Cgrad).mono'
      hc.aestronglyMeasurable (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact hgradΨ_bound t ⟨ht.1.le, ht.2.le⟩ _))
  have hint_lap : Integrable (fun z => ∑ i : Fin m, ⟪bHessΨ S t (r t • z) (eb i), eb i⟫) γ := by
    have hc : Continuous (fun z => ∑ i : Fin m, ⟪bHessΨ S t (r t • z) (eb i), eb i⟫) :=
      continuous_finsetSum _ fun i _ =>
        ((hhessΨ_cont_t.comp
          (continuous_id.const_smul (r t))).clm_apply continuous_const).inner continuous_const
    refine Integrable.of_bound hc.aestronglyMeasurable (m * Chess) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    calc |∑ i : Fin m, ⟪bHessΨ S t (r t • z) (eb i), eb i⟫|
        ≤ ∑ i : Fin m, |⟪bHessΨ S t (r t • z) (eb i), eb i⟫| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, Chess := Finset.sum_le_sum fun i _ => by
          calc |⟪bHessΨ S t (r t • z) (eb i), eb i⟫|
              ≤ ‖bHessΨ S t (r t • z) (eb i)‖ * ‖eb i‖ := abs_real_inner_le_norm _ _
            _ = ‖bHessΨ S t (r t • z) (eb i)‖ := by rw [norm_eb, mul_one]
            _ ≤ ‖bHessΨ S t (r t • z)‖ * ‖eb i‖ := ContinuousLinearMap.le_opNorm _ _
            _ = ‖bHessΨ S t (r t • z)‖ := by rw [norm_eb, mul_one]
            _ ≤ Chess := hhessΨ_bound t ⟨ht.1.le, ht.2.le⟩ _
      _ = m * Chess := by simp
  have hrt_pos : 0 < r t := Real.sqrt_pos.mpr (by linarith [ht.2])
  have hint_eq : ∫ z, F' t z ∂γ =
      ∫ z, (bDtΨ S t (r t • z) - (∑ i : Fin m, ⟪bHessΨ S t (r t • z) (eb i), eb i⟫) / 2) ∂γ := by
    dsimp only [F']
    rw [integral_sub hint_dt (hint_grad.const_mul _), integral_const_mul, hstein,
      integral_sub hint_dt (hint_lap.div_const 2), integral_div]
    field_simp [hrt_pos.ne']
  have hle : ∫ z, F' t z ∂γ ≤ 0 := by
    rw [hint_eq]
    exact integral_nonpos fun z => hpde t ht (r t • z)
  exact ⟨∫ z, F' t z ∂γ, hle, hderiv⟩

/-- Bobkov's Gaussian functional isoperimetric inequality for smooth `C³_b` functions
valued in `[η, 1 - η]`. -/
private theorem bobkov_smooth (S : SmoothC3Bounded m) :
    I (∫ z, S.f z ∂γ) ≤ ∫ z, Real.sqrt (I (S.f z) ^ 2 + ‖S.g z‖ ^ 2) ∂γ := by
  obtain ⟨hΨ_cont, _, _⟩ := bobkov_cont S
  let Λ : ℝ → ℝ := fun t => ∫ z, bΨ S t (Real.sqrt (1 - t) • z) ∂γ
  have hΛ_cont : ContinuousOn Λ (Icc 0 1) := by
    refine continuousOn_of_dominated (bound := fun _ => Real.sqrt (1 + S.Cg ^ 2)) ?_ ?_
      (integrable_const _) ?_
    · intro t _
      have hpair_t : Continuous (fun z : E => (t, Real.sqrt (1 - t) • z)) :=
        continuous_const.prodMk (continuous_id.const_smul (Real.sqrt (1 - t)))
      exact (hΨ_cont.comp hpair_t).aestronglyMeasurable
    · intro t ht
      exact ae_of_all _ fun z => bΨ_norm_le S ht _
    · refine ae_of_all _ fun z => ?_
      exact (hΨ_cont.comp (continuous_id.prodMk
        ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).smul continuous_const))).continuousOn
  have hanti : AntitoneOn Λ (Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hΛ_cont ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d, _, hd⟩ := bobkov_Λ_deriv S ht
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d, hd0, hd⟩ := bobkov_Λ_deriv S ht
      rw [hd.deriv]
      exact hd0
  have h10 : Λ 1 ≤ Λ 0 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have hΛ1 : Λ 1 = I (∫ z, S.f z ∂γ) := by
    simp only [Λ, bΨ, bA, sub_self, Real.sqrt_zero, zero_smul, zero_mul, add_zero,
      heat_one_zero, Real.sqrt_sq (I_pos _).le, integral_const, probReal_univ, one_smul]
  have hΛ0 : Λ 0 = ∫ z, Real.sqrt (I (S.f z) ^ 2 + ‖S.g z‖ ^ 2) ∂γ := by
    simp only [Λ, bΨ, bA, sub_zero, Real.sqrt_one, one_smul, one_mul, heat_zero]
  rwa [hΛ1, hΛ0] at h10

end BakryLedoux

end BorellBobkov

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian (EuclideanSpace ℝ (Fin m))

theorem solution
    (f : E → ℝ) (g : E → E) (K : E → E →L[ℝ] E) (M : E → E →L[ℝ] (E →L[ℝ] E))
    (η Cg CK CM : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1 - η)
    (hf_mem : ∀ x, f x ∈ Icc η (1 - η)) (hf_deriv : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg_deriv : ∀ x, HasFDerivAt g (K x) x) (hK_deriv : ∀ x, HasFDerivAt K (M x) x)
    (hM_cont : Continuous M) (hK_symm : ∀ x v w, ⟪K x v, w⟫ = ⟪v, K x w⟫)
    (hCg_nn : 0 ≤ Cg) (hCK_nn : 0 ≤ CK) (hCM_nn : 0 ≤ CM)
    (hg_bound : ∀ x, ‖g x‖ ≤ Cg) (hK_bound : ∀ x, ‖K x‖ ≤ CK) (hM_bound : ∀ x, ‖M x‖ ≤ CM) :
    I (∫ z, f z ∂γ) ≤ ∫ z, Real.sqrt (I (f z) ^ 2 + ‖g z‖ ^ 2) ∂γ :=
  BorellBobkov.bobkov_smooth
    ⟨f, g, K, M, η, hη_pos, hη_le, hf_mem, hf_deriv, hg_deriv, hK_deriv, hM_cont, hK_symm,
      Cg, CK, CM, hCg_nn, hCK_nn, hCM_nn, hg_bound, hK_bound, hM_bound⟩
