-- Prove2me | solution 1 for RetirePartialInfo.Duality.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T06:41:48.330495+00:00
-- url     : https://prove2.me/submissions/b6aee8ee-166f-432e-90a9-fd64c5cd3cae

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal
import Definitions.Def_RetirePartialInfo_Duality_Dual
import Theorems.Thm_RetirePartialInfo_Duality_eq_11
import Theorems.Thm_RetirePartialInfo_Duality_optional_sampling_Zv

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
open RetirePartialInfo.Duality

namespace RetirePI13

variable {Ω : Type*} [MeasurableSpace Ω]

lemma Iθ_zero (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ)
    (hIto : IsItoIntegral p st (θ p st) Iθ) : Iθ 0 =ᵐ[st.P] 0 := by
  obtain ⟨a, -, -, -, hconv⟩ := hIto.2.2.2.2 0 (by simpa using p.T_pos.le)
  have hzero : (fun n ω => EthierKurtz.itoStepSum st.W 0 n (a n) ω) = fun _ _ => 0 := by
    funext n ω
    simp [EthierKurtz.itoStepSum]
  rw [hzero] at hconv
  obtain ⟨ns, -, hae⟩ := hconv.exists_seq_tendsto_ae
  filter_upwards [hae] with ω hω
  exact (tendsto_nhds_unique tendsto_const_nhds hω).symm

lemma measurable_Z (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ)
    (hIto : IsItoIntegral p st (θ p st) Iθ) (t : ℝ≥0) : Measurable (Z p st Iθ t) := by
  have h1 : Measurable (fun ω => ∫ s in Icc (0 : ℝ) t, θ p st s.toNNReal ω ^ 2) := by
    have h : Measurable (fun q : Ω × ℝ => θ p st q.2.toNNReal q.1 ^ 2) := by
      have hμ : Measurable (fun q : Ω × ℝ => st.μ q.2.toNNReal q.1) :=
        st.measurable_μ.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
      unfold θ
      fun_prop
    exact (h.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Icc (0 : ℝ) t))).measurable
  have h2 : Measurable (Iθ t) := (hIto.2.2.1 t).mono (st.𝓕.le t) le_rfl
  unfold Z
  fun_prop

lemma Z_pos (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    0 < Z p st Iθ t ω := Real.exp_pos _

lemma integrable_ZT (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ)
    (h21 : Assumption21 p st Iθ) : Integrable (Z p st Iθ p.Tn) st.P := by
  simpa only [min_self] using h21.2.integrable p.Tn

lemma integral_ZT (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ) (hst : st.Standing p)
    (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ) :
    ∫ ω, Z p st Iθ p.Tn ω ∂st.P = 1 := by
  have : IsProbabilityMeasure st.P := hst.1
  have hmart := h21.2
  have hce := hmart.condExp_ae_eq (zero_le (a := p.Tn))
  simp only [min_self, zero_min] at hce
  rw [← integral_condExp (st.𝓕.le 0)]
  rw [integral_congr_ae hce]
  have h0 : (fun ω => Z p st Iθ 0 ω) =ᵐ[st.P] fun _ => (1 : ℝ) := by
    filter_upwards [Iθ_zero p st Iθ hIto] with ω hω
    simp [Z, hω]
  rw [integral_congr_ae h0]
  simp

lemma Pt_prob (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ) (hst : st.Standing p)
    (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ) :
    IsProbabilityMeasure (Pt p st Iθ) := by
  constructor
  unfold Pt
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_ZT p st Iθ h21)
      (Eventually.of_forall fun ω => (Z_pos p st Iθ _ ω).le),
    integral_ZT p st Iθ hst hIto h21]
  simp

lemma lintegral_com (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (hst : st.Standing p)
    (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (t : ℝ≥0) (ht : (t : ℝ) ≤ p.T) (M : Ω → ℝ)
    (hM : Measurable[FS p st t] M) (hM0 : ∀ᵐ ω ∂st.P, 0 ≤ M ω)
    (hfin : ∫⁻ ω, ENNReal.ofReal (Z p st Iθ p.Tn ω * M ω) ∂st.P < ⊤) :
    ∫⁻ ω, ENNReal.ofReal (Z p st Iθ p.Tn ω * M ω) ∂st.P =
      ∫⁻ ω, ENNReal.ofReal (Zv t ω * M ω) ∂st.P := by
  have : IsProbabilityMeasure st.P := hst.1
  have hMm : Measurable M := hM.mono ((FS p st).le t) le_rfl
  have hZm := measurable_Z p st Iθ hIto p.Tn
  have hnn : 0 ≤ᵐ[st.P] fun ω => Z p st Iθ p.Tn ω * M ω := by
    filter_upwards [hM0] with ω hω
    exact mul_nonneg (Z_pos p st Iθ _ ω).le hω
  have hint : Integrable (fun ω => Z p st Iθ p.Tn ω * M ω) st.P :=
    ⟨(hZm.mul hMm).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hfin⟩
  have hpull := condExp_mul_of_stronglyMeasurable_right (m := FS p st t) (μ := st.P)
    (f := Z p st Iθ p.Tn) hM.stronglyMeasurable hint (integrable_ZT p st Iθ h21)
  have hg : (fun ω => Zv t ω * M ω) =ᵐ[st.P] st.P[Z p st Iθ p.Tn * M | FS p st t] := by
    filter_upwards [hpull, hZv.1 t ht] with ω h1 h2
    rw [h1]
    simp only [Pi.mul_apply]
    rw [h2]
    rfl
  have hgint : Integrable (fun ω => Zv t ω * M ω) st.P :=
    integrable_condExp.congr hg.symm
  have hgnn : 0 ≤ᵐ[st.P] fun ω => Zv t ω * M ω := by
    filter_upwards [hM0] with ω hω
    exact mul_nonneg (hZv.2.2.2 t ω).le hω
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← ofReal_integral_eq_lintegral_ofReal hgint hgnn, integral_congr_ae hg,
    integral_condExp ((FS p st).le t)]
  rfl

lemma measurable_cm (p : Params) (c : ℝ≥0 → Ω → ℝ)
    (hc : Measurable (fun z : ℝ≥0 × Ω => c (min z.1 p.Tn) z.2)) :
    Measurable (fun z : ℝ × Ω => c (min z.1.toNNReal p.Tn) z.2) :=
  hc.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

lemma measurable_zm (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ)
    (hZv : IsZVersion p st Iθ Zv) :
    Measurable (fun z : ℝ × Ω => Zv (min z.1.toNNReal p.Tn) z.2) := by
  refine measurable_uncurry_of_continuous_of_measurable (m := ‹MeasurableSpace Ω›)
    (u := fun (u : ℝ) (ω : Ω) => Zv (min u.toNNReal p.Tn) ω) ?_ ?_
  · intro ω
    have hc : Continuous (fun u : ℝ => min u.toNNReal p.Tn) :=
      continuous_real_toNNReal.min continuous_const
    exact (hZv.2.2.1 ω).comp_continuous hc (fun u => show min u.toNNReal p.Tn ≤ p.Tn from min_le_right _ _)
  · intro u
    exact (hZv.2.1 _).mono ((FS p st).le _) le_rfl

lemma toNNReal_le_Tn (p : Params) {u : ℝ} (hu : u ≤ p.T) : u.toNNReal ≤ p.Tn :=
  Real.toNNReal_le_toNNReal hu

lemma coe_toNNReal_le (p : Params) {u : ℝ} (hu : u ≤ p.T) : ((u.toNNReal : ℝ≥0) : ℝ) ≤ p.T := by
  rw [Real.coe_toNNReal']
  exact max_le hu p.T_pos.le

lemma Bt_pos (p : Params) (u : ℝ) : 0 < Bt p u := Real.exp_pos _

lemma Tn_pos (p : Params) : 0 < p.Tn := Real.toNNReal_pos.2 p.T_pos

lemma coe_Tn (p : Params) : ((p.Tn : ℝ≥0) : ℝ) = p.T := Real.coe_toNNReal _ p.T_pos.le

lemma budget_Pt (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (x : ℝ) (c H : ℝ≥0 → Ω → ℝ)
    (hq : (⟨c, H, fun _ => 0⟩ : Plan Ω) ∈ Bclass p st Iθ U1 U2 x) :
    ∫⁻ ω, (ENNReal.ofReal (Z p st Iθ p.Tn ω * (H p.Tn ω / Bt p p.T)) +
      ∫⁻ u in Ioc (0 : ℝ) p.T, ENNReal.ofReal (Z p st Iθ p.Tn ω * (c u.toNNReal ω / Bt p u)))
      ∂st.P ≤ ENNReal.ofReal x := by
  have hP : IsProbabilityMeasure st.P := hst.1
  have hPt : IsProbabilityMeasure (Pt p st Iθ) := Pt_prob p st Iθ hst hIto h21
  obtain ⟨-, ⟨-, -, hcpos, hcint⟩, -, hH0, -, hbud, hHT, -, -⟩ := hq
  obtain ⟨hNint, hNle⟩ := hbud 0 p.Tn (Tn_pos p) (le_of_eq (coe_Tn p))
  set N : Ω → ℝ := fun ω => H p.Tn ω / Bt p p.T +
    ∫ u in Ioc (0 : ℝ) p.T, c u.toNNReal ω / Bt p u with hNdef
  have hNeq : budgetLHS p ⟨c, H, fun _ => 0⟩ 0 p.Tn = N := by
    funext ω
    simp [budgetLHS, Rind, dRatom, coe_Tn, N]
  rw [hNeq] at hNint hNle
  have hac : Pt p st Iθ ≪ st.P := withDensity_absolutelyContinuous _ _
  have hx : (fun ω => (H 0 ω - b p ((0 : ℝ≥0) : ℝ) * (1 - Rind (fun _ => (0 : ℝ≥0)) 0 ω)) /
      Bt p ((0 : ℝ≥0) : ℝ)) =ᵐ[Pt p st Iθ] fun _ => x := by
    filter_upwards [hac.ae_le hH0] with ω hω
    simp [Rind, Bt, hω]
  have hle : ∫ ω, N ω ∂(Pt p st Iθ) ≤ x := by
    rw [← integral_condExp ((FS p st).le 0)]
    calc ∫ ω, (Pt p st Iθ)[N | FS p st 0] ω ∂(Pt p st Iθ)
        ≤ ∫ _, x ∂(Pt p st Iθ) :=
          integral_mono_ae integrable_condExp (integrable_const x) (hNle.trans_eq hx)
      _ = x := by simp
  -- pointwise decomposition, P-a.e.
  have hdec : ∀ᵐ ω ∂st.P, ENNReal.ofReal (Z p st Iθ p.Tn ω) * ENNReal.ofReal (N ω) =
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (H p.Tn ω / Bt p p.T)) +
      ∫⁻ u in Ioc (0 : ℝ) p.T, ENNReal.ofReal (Z p st Iθ p.Tn ω * (c u.toNNReal ω / Bt p u)) := by
    filter_upwards [hcint, hHT] with ω hci hHpos
    have hint : IntegrableOn (fun u : ℝ => c u.toNNReal ω / Bt p u) (Ioc 0 p.T) := by
      have h1 := hci.mul_continuousOn (g' := fun u : ℝ => (Bt p u)⁻¹)
        (by
          have : Continuous (fun u : ℝ => (Bt p u)⁻¹) := by
            simp only [Bt, ← Real.exp_neg]; fun_prop
          exact this.continuousOn) isCompact_Icc
      exact (h1.mono_set Ioc_subset_Icc_self).congr_fun (fun u _ => by simp [div_eq_mul_inv])
        measurableSet_Ioc
    have hnn : ∀ u ∈ Ioc (0 : ℝ) p.T, 0 ≤ c u.toNNReal ω / Bt p u := fun u hu =>
      div_nonneg (hcpos _ (coe_toNNReal_le p hu.2) ω).le (Bt_pos p u).le
    have hI : ENNReal.ofReal (∫ u in Ioc (0 : ℝ) p.T, c u.toNNReal ω / Bt p u) =
        ∫⁻ u in Ioc (0 : ℝ) p.T, ENNReal.ofReal (c u.toNNReal ω / Bt p u) :=
      ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hnn))
    have hHB : 0 ≤ H p.Tn ω / Bt p p.T := div_nonneg hHpos.le (Bt_pos p _).le
    have hZ0 : 0 ≤ Z p st Iθ p.Tn ω := (Z_pos p st Iθ _ ω).le
    simp only [N]
    rw [ENNReal.ofReal_add hHB (setIntegral_nonneg measurableSet_Ioc hnn), mul_add, hI,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hZ0]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    rw [ENNReal.ofReal_mul hZ0]
  rw [← lintegral_congr_ae hdec]
  have h2 : ∫⁻ ω, ENNReal.ofReal (N ω) ∂(Pt p st Iθ) =
      ∫⁻ ω, ENNReal.ofReal (Z p st Iθ p.Tn ω) * ENNReal.ofReal (N ω) ∂st.P := by
    unfold Pt
    exact lintegral_withDensity_eq_lintegral_mul₀'
      (measurable_Z p st Iθ hIto p.Tn).ennreal_ofReal.aemeasurable
      hNint.aemeasurable.ennreal_ofReal
  rw [← h2]
  have hNnn : 0 ≤ᵐ[Pt p st Iθ] N := by
    refine hac.ae_le ?_
    filter_upwards [hHT] with ω hHpos
    have hnn : ∀ u ∈ Ioc (0 : ℝ) p.T, 0 ≤ c u.toNNReal ω / Bt p u := fun u hu =>
      div_nonneg (hcpos _ (coe_toNNReal_le p hu.2) ω).le (Bt_pos p u).le
    exact add_nonneg (div_nonneg hHpos.le (Bt_pos p _).le)
      (setIntegral_nonneg measurableSet_Ioc hnn)
  rw [← ofReal_integral_eq_lintegral_ofReal hNint hNnn]
  exact ENNReal.ofReal_le_ofReal hle

lemma cons_swap (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (c : ℝ≥0 → Ω → ℝ)
    (hcm : Measurable (fun z : ℝ≥0 × Ω => c (min z.1 p.Tn) z.2))
    (hcad : ∀ t : ℝ≥0, (t : ℝ) ≤ p.T → Measurable[FS p st t] (c t))
    (hcpos : ∀ t : ℝ≥0, (t : ℝ) ≤ p.T → ∀ ω, 0 < c t ω)
    (hfin : ∫⁻ ω, (∫⁻ u in Ioc (0 : ℝ) p.T,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c u.toNNReal ω / Bt p u))) ∂st.P < ⊤) :
    ∫⁻ ω, (∫⁻ u in Ioc (0 : ℝ) p.T,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c u.toNNReal ω / Bt p u))) ∂st.P =
    ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) p.T,
      ENNReal.ofReal (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) ∂st.P := by
  have hP : IsProbabilityMeasure st.P := hst.1
  have hcmm := measurable_cm p c hcm
  have hzmm := measurable_zm p st Iθ Zv hZv
  have hZm := measurable_Z p st Iθ hIto p.Tn
  have hBm : Measurable (fun u : ℝ => Bt p u) := by unfold Bt; fun_prop
  have step1 : ∀ ω, ∫⁻ u in Ioc (0 : ℝ) p.T,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c u.toNNReal ω / Bt p u)) =
      ∫⁻ u in Ioc (0 : ℝ) p.T,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c (min u.toNNReal p.Tn) ω / Bt p u)) := fun ω =>
    setLIntegral_congr_fun measurableSet_Ioc (fun u hu => by
      rw [min_eq_left (toNNReal_le_Tn p hu.2)])
  simp_rw [step1] at hfin ⊢
  have hF : Measurable (Function.uncurry fun (ω : Ω) (u : ℝ) =>
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c (min u.toNNReal p.Tn) ω / Bt p u))) := by
    have h1 : Measurable (fun z : Ω × ℝ => c (min z.2.toNNReal p.Tn) z.1) :=
      hcmm.comp measurable_swap
    have h2 : Measurable (fun z : Ω × ℝ => Bt p z.2) := hBm.comp measurable_snd
    have h3 : Measurable (fun z : Ω × ℝ => Z p st Iθ p.Tn z.1) := hZm.comp measurable_fst
    exact (h3.mul (h1.div h2)).ennreal_ofReal
  rw [lintegral_lintegral_swap hF.aemeasurable] at hfin ⊢
  have hG : Measurable (fun u : ℝ => ∫⁻ ω,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c (min u.toNNReal p.Tn) ω / Bt p u)) ∂st.P) := by
    have : Measurable (fun z : ℝ × Ω =>
        ENNReal.ofReal (Z p st Iθ p.Tn z.2 * (c (min z.1.toNNReal p.Tn) z.2 / Bt p z.1))) :=
      ((hZm.comp measurable_snd).mul (hcmm.div (hBm.comp measurable_fst))).ennreal_ofReal
    exact this.lintegral_prod_right'
  have step3 : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) p.T)),
      ∫⁻ ω, ENNReal.ofReal (Z p st Iθ p.Tn ω * (c (min u.toNNReal p.Tn) ω / Bt p u)) ∂st.P =
      ∫⁻ ω, ENNReal.ofReal (Zv (min u.toNNReal p.Tn) ω *
        (c (min u.toNNReal p.Tn) ω / Bt p u)) ∂st.P := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_lt_top hG hfin.ne] with u hu hlt
    have hmin : min u.toNNReal p.Tn = u.toNNReal := min_eq_left (toNNReal_le_Tn p hu.2)
    rw [hmin] at hlt ⊢
    have hle : ((u.toNNReal : ℝ≥0) : ℝ) ≤ p.T := coe_toNNReal_le p hu.2
    exact lintegral_com p st Iθ Zv hst hIto h21 hZv u.toNNReal hle
      (fun ω => c u.toNNReal ω / Bt p u) ((hcad _ hle).div_const _)
      (Eventually.of_forall fun ω => div_nonneg (hcpos _ hle ω).le (Bt_pos p u).le) hlt
  rw [lintegral_congr_ae step3]
  have hF2 : Measurable (Function.uncurry fun (ω : Ω) (u : ℝ) =>
      ENNReal.ofReal (Zv (min u.toNNReal p.Tn) ω * (c (min u.toNNReal p.Tn) ω / Bt p u))) := by
    have h1 : Measurable (fun z : Ω × ℝ => c (min z.2.toNNReal p.Tn) z.1) :=
      hcmm.comp measurable_swap
    have h2 : Measurable (fun z : Ω × ℝ => Bt p z.2) := hBm.comp measurable_snd
    have h3 : Measurable (fun z : Ω × ℝ => Zv (min z.2.toNNReal p.Tn) z.1) :=
      hzmm.comp measurable_swap
    exact (h3.mul (h1.div h2)).ennreal_ofReal
  rw [← lintegral_lintegral_swap hF2.aemeasurable]
  refine lintegral_congr fun ω => ?_
  rw [setLIntegral_congr Ioc_ae_eq_Icc]
  refine setLIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
  rw [min_eq_left (toNNReal_le_Tn p hu.2)]

lemma static_budget (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (x : ℝ) (c H : ℝ≥0 → Ω → ℝ)
    (hq : (⟨c, H, fun _ => 0⟩ : Plan Ω) ∈ Bclass p st Iθ U1 U2 x) :
    ∫⁻ ω, ENNReal.ofReal (Zv p.Tn ω * (H p.Tn ω / Bt p p.T)) ∂st.P +
      ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) p.T,
        ENNReal.ofReal (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) ∂st.P
      ≤ ENNReal.ofReal x := by
  have hb := budget_Pt p st Iθ Zv U1 U2 hst hIto h21 x c H hq
  obtain ⟨-, ⟨hcm, hcad, hcpos, -⟩, hHad, -, -, -, hHT, -, -⟩ := hq
  have hTle : ((p.Tn : ℝ≥0) : ℝ) ≤ p.T := le_of_eq (coe_Tn p)
  have hHm : Measurable[FS p st p.Tn] (fun ω => H p.Tn ω / Bt p p.T) :=
    (hHad p.Tn hTle).div_const _
  have hm1 : Measurable (fun ω => ENNReal.ofReal (Z p st Iθ p.Tn ω * (H p.Tn ω / Bt p p.T))) :=
    ((measurable_Z p st Iθ hIto p.Tn).mul (hHm.mono ((FS p st).le _) le_rfl)).ennreal_ofReal
  rw [lintegral_add_left hm1] at hb
  have hlt1 := lt_of_le_of_lt (le_add_right le_rfl) (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
  have hlt2 := lt_of_le_of_lt (le_add_left le_rfl) (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
  rw [lintegral_com p st Iθ Zv hst hIto h21 hZv p.Tn hTle _ hHm
    (by filter_upwards [hHT] with ω hω; exact div_nonneg hω.le (Bt_pos p _).le) hlt1] at hb
  rw [cons_swap p st Iθ Zv hst hIto h21 hZv c hcm hcad hcpos hlt2] at hb
  exact hb

lemma U_le (p : Params) (U : ℝ → ℝ → ℝ) (hU : Assumption22 p U) (t : ℝ) (ht : t ∈ Icc 0 p.T)
    (y : ℝ) (hy : 0 < y) (c : ℝ) (hc : 0 < c) : U t c ≤ Utilde U t y + y * c := by
  have h := eq_11 p U hU t ht y hy
  have h1 := h.2.1.2 ⟨c, hc, rfl⟩
  rw [← h.2.2] at h1
  linarith

end RetirePI13

namespace RetirePIveqr

lemma deriv_cont (p : Params) (U : ℝ → ℝ → ℝ) (hU : Assumption22 p U) (a : ℝ) (ha : 0 < a) :
    ContinuousOn (fun s => deriv (U s) a) (Icc 0 p.T) := by
  have hS : UniqueDiffOn ℝ (Icc 0 p.T ×ˢ Ioi (0 : ℝ)) :=
    (uniqueDiffOn_Icc p.T_pos).prod (uniqueDiffOn_Ioi 0)
  have hcont := hU.1.continuousOn_fderivWithin hS (by simp)
  have heq : ∀ s ∈ Icc 0 p.T, deriv (U s) a =
      fderivWithin ℝ (fun q : ℝ × ℝ => U q.1 q.2) (Icc 0 p.T ×ˢ Ioi (0 : ℝ)) (s, a) (0, 1) := by
    intro s hs
    have hd : DifferentiableWithinAt ℝ (fun q : ℝ × ℝ => U q.1 q.2)
        (Icc 0 p.T ×ˢ Ioi (0 : ℝ)) (s, a) :=
      (hU.1.differentiableOn (by simp)) _ ⟨hs, ha⟩
    have hg : HasDerivAt (fun c : ℝ => (s, c)) ((0 : ℝ), (1 : ℝ)) a :=
      (hasDerivAt_const a s).prodMk (hasDerivAt_id a)
    have h2 := hd.hasFDerivWithinAt.comp_hasDerivWithinAt a hg.hasDerivWithinAt
      (s := Ioi 0) (fun c hc => ⟨hs, hc⟩)
    exact (h2.hasDerivAt (Ioi_mem_nhds ha)).deriv
  refine ContinuousOn.congr ?_ heq
  have hpair : ContinuousOn (fun s : ℝ => (s, a)) (Icc 0 p.T) :=
    (continuous_id.prodMk continuous_const).continuousOn
  exact (hcont.comp hpair (fun s hs => ⟨hs, ha⟩)).clm_apply continuousOn_const

/-- `a < I(s, y) ↔ y < ∂_c U(s, a)` for `a, y > 0`. -/
lemma lt_Iinv_iff (p : Params) (U : ℝ → ℝ → ℝ) (hU : Assumption22 p U) (s : ℝ)
    (hs : s ∈ Icc 0 p.T) (y : ℝ) (hy : 0 < y) (a : ℝ) (ha : 0 < a) :
    a < Iinv U s y ↔ y < deriv (U s) a := by
  have hfcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (U s) (Ioi 0) := by
    have hpair : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c : ℝ => (s, c)) (Ioi 0) :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    exact hU.1.comp hpair (fun c hc => ⟨hs, hc⟩)
  have hfdiff : ∀ c ∈ Ioi (0 : ℝ), DifferentiableAt ℝ (U s) c := by
    intro c hc
    exact ((hfcd.differentiableOn (by simp)) c hc).differentiableAt (Ioi_mem_nhds hc)
  have hanti : StrictAntiOn (deriv (U s)) (Ioi 0) := (hU.2.1 s hs).strictAntiOn_deriv hfdiff
  have hDc : ContinuousOn (deriv (U s)) (Ioi 0) :=
    hfcd.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)
  have hSbdd : BddBelow {c | 0 < c ∧ deriv (U s) c ≤ y} := ⟨0, fun c hc => hc.1.le⟩
  constructor
  · intro h
    have : a ∉ {c | 0 < c ∧ deriv (U s) c ≤ y} := notMem_of_lt_csInf h hSbdd
    by_contra h'
    exact this ⟨ha, not_lt.1 h'⟩
  · intro h
    have hev : ∀ᶠ c in 𝓝 a, y < deriv (U s) c :=
      ((hDc a ha).continuousAt (Ioi_mem_nhds ha)).eventually (lt_mem_nhds h)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have hne : ({c | 0 < c ∧ deriv (U s) c ≤ y} : Set ℝ).Nonempty :=
      (eq_11 p U hU s hs y hy).1 |> fun hpos => by
        have h11 := eq_11 p U hU s hs y hy
        -- `Iinv` is positive, so the set is nonempty (sInf ∅ = 0)
        by_contra hemp
        rw [not_nonempty_iff_eq_empty] at hemp
        have : Iinv U s y = 0 := by simp [Iinv, hemp]
        linarith
    have hlow : a + δ / 2 ≤ Iinv U s y := by
      refine le_csInf hne (fun c hc => ?_)
      by_contra hlt
      rw [not_le] at hlt
      rcases le_or_gt c a with hca | hca
      · have h1 : deriv (U s) a ≤ deriv (U s) c := hanti.antitoneOn hc.1 ha hca
        linarith [hc.2]
      · have hdist : dist c a < δ := by
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith
        linarith [hball hdist, hc.2]
    linarith
lemma measurable_Iinv_comp {X : Type*} {mX : MeasurableSpace X} (p : Params) (U : ℝ → ℝ → ℝ)
    (hU : Assumption22 p U) (s : X → ℝ) (hs : Measurable s) (hsI : ∀ x, s x ∈ Icc 0 p.T)
    (yv : X → ℝ) (hyv : Measurable yv) (hyp : ∀ x, 0 < yv x) :
    Measurable (fun x => Iinv U (s x) (yv x)) := by
  refine measurable_of_Ioi fun a => ?_
  by_cases ha : 0 < a
  · set g : ℝ → ℝ := fun t => deriv (U (max 0 (min t p.T))) a with hg
    have hclamp : Continuous (fun t : ℝ => max 0 (min t p.T)) := by fun_prop
    have hgc : Continuous g :=
      (deriv_cont p U hU a ha).comp_continuous hclamp
        (fun t => ⟨le_max_left _ _, max_le p.T_pos.le (min_le_right _ _)⟩)
    have hset : (fun x => Iinv U (s x) (yv x)) ⁻¹' Ioi a = {x | yv x < g (s x)} := by
      ext x
      have hx := hsI x
      have hcl : max 0 (min (s x) p.T) = s x := by
        rw [min_eq_left hx.2, max_eq_right hx.1]
      simp only [mem_preimage, mem_Ioi, mem_setOf_eq, hg, hcl]
      exact lt_Iinv_iff p U hU (s x) hx (yv x) (hyp x) a ha
    rw [hset]
    exact measurableSet_lt hyv (hgc.measurable.comp hs)
  · have hset : (fun x => Iinv U (s x) (yv x)) ⁻¹' Ioi a = univ := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact lt_of_le_of_lt (not_lt.1 ha) (eq_11 p U hU (s x) (hsI x) (yv x) (hyp x)).1
    rw [hset]
    exact MeasurableSet.univ

end RetirePIveqr


namespace RetirePIfr

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The σ-algebra of measurable sets of probability `0` or `1`. -/
def m01 (P : Measure Ω) [IsProbabilityMeasure P] : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet A ∧ (P A = 0 ∨ P A = 1)
  measurableSet_empty := ⟨MeasurableSet.empty, Or.inl measure_empty⟩
  measurableSet_compl A h := by
    refine ⟨h.1.compl, ?_⟩
    rcases h.2 with h0 | h1
    · right; rw [prob_compl_eq_one_sub h.1, h0]; simp
    · left; rw [prob_compl_eq_one_sub h.1, h1]; simp
  measurableSet_iUnion f hf := by
    refine ⟨MeasurableSet.iUnion fun i => (hf i).1, ?_⟩
    by_cases h : ∃ i, P (f i) = 1
    · obtain ⟨i, hi⟩ := h
      right
      exact le_antisymm prob_le_one (hi ▸ measure_mono (subset_iUnion f i))
    · push Not at h
      left
      exact measure_iUnion_null fun i => ((hf i).2.resolve_right (h i))

lemma FS0_zero_one (p : Params) (st : Setting Ω) (hst : st.Standing p) (A : Set Ω)
    (hA : MeasurableSet[FS p st 0] A) : MeasurableSet A ∧ (st.P A = 0 ∨ st.P A = 1) := by
  have : IsProbabilityMeasure st.P := hst.1
  suffices h : FS p st 0 ≤ m01 st.P from h A hA
  refine sup_le (iSup₂_le fun u hu => ?_) (MeasurableSpace.generateFrom_le fun N hN => ?_)
  · have hu0 : u = 0 := le_antisymm hu (zero_le (a := u))
    subst hu0
    intro B hB
    obtain ⟨C, hC, rfl⟩ := hB
    refine ⟨measurable_S p st 0 hC, ?_⟩
    have hW0 := hst.2.2.2.1.1.toIsPreBrownianReal.eval_zero_ae_eq_zero
    have hS : S p st 0 =ᵐ[st.P] fun _ => st.S0 := by
      filter_upwards [hW0] with ω hω
      simp [S, hω]
    have hpre : S p st 0 ⁻¹' C =ᵐ[st.P] (fun _ : Ω => st.S0) ⁻¹' C := by
      filter_upwards [hS] with ω hω
      change (S p st 0 ω ∈ C) = (st.S0 ∈ C)
      rw [hω]
    rw [measure_congr hpre]
    by_cases hc : st.S0 ∈ C
    · right; simp [preimage_const_of_mem hc]
    · left; simp [preimage_const_of_notMem hc]
  · exact ⟨hN.1, Or.inl hN.2⟩

lemma P_ac_Pt (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ)
    (hIto : IsItoIntegral p st (θ p st) Iθ) : st.P ≪ Pt p st Iθ :=
  withDensity_absolutelyContinuous'
    (RetirePI13.measurable_Z p st Iθ hIto p.Tn).ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun ω => (ENNReal.ofReal_pos.2 (RetirePI13.Z_pos p st Iθ _ ω)).ne')

lemma condExp_FS0 (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ) (hst : st.Standing p)
    (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ) (f : Ω → ℝ)
    (hf : Integrable f (Pt p st Iθ)) :
    (Pt p st Iθ)[f | FS p st 0] =ᵐ[Pt p st Iθ] fun _ => ∫ ω, f ω ∂(Pt p st Iθ) := by
  have hPt : IsProbabilityMeasure (Pt p st Iθ) := RetirePI13.Pt_prob p st Iθ hst hIto h21
  have hP : IsProbabilityMeasure st.P := hst.1
  have hac : Pt p st Iθ ≪ st.P := withDensity_absolutelyContinuous _ _
  set g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[Pt p st Iθ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : StronglyMeasurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hind : Indep ‹MeasurableSpace Ω› (FS p st 0) (Pt p st Iθ) := by
    rw [Indep_iff]
    intro t1 t2 h1 h2
    obtain ⟨h2m, h01⟩ := FS0_zero_one p st hst t2 h2
    rcases h01 with h0 | h1'
    · have : Pt p st Iθ t2 = 0 := hac h0
      rw [this, mul_zero]
      exact measure_mono_null inter_subset_right this
    · have hc : st.P t2ᶜ = 0 := by rw [prob_compl_eq_one_sub h2m, h1']; simp
      have hc' : Pt p st Iθ t2ᶜ = 0 := hac hc
      have h1t : Pt p st Iθ t2 = 1 := by
        rw [← prob_compl_eq_zero_iff h2m]; exact hc'
      rw [h1t, mul_one, measure_inter_conull hc']
  have h := condExp_indep_eq (m₁ := ‹MeasurableSpace Ω›) (m₂ := FS p st 0) (μ := Pt p st Iθ)
    le_rfl ((FS p st).le 0) hg hind
  refine (condExp_congr_ae hfg).trans (h.trans ?_)
  filter_upwards with ω
  exact (integral_congr_ae hfg).symm

section cand
variable (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)

lemma yd_pos (hZv : IsZVersion p st Iθ Zv) (y : ℝ) (hy : 0 < y) (s : ℝ) (ω : Ω) :
    0 < ydual p Zv y s ω := by
  unfold ydual
  exact div_pos (mul_pos (mul_pos hy (Real.exp_pos _)) (hZv.2.2.2 _ ω)) (RetirePI13.Bt_pos p s)

lemma cs_pos (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (y : ℝ) (hy : 0 < y)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ p.T) (ω : Ω) : 0 < cstar p Zv U1 y t ω :=
  (eq_11 p U1 hU1 t ⟨t.2, ht⟩ _ (yd_pos p st Iθ Zv hZv y hy _ ω)).1

lemma Hs_pos (hZv : IsZVersion p st Iθ Zv) (hU2 : Assumption22 p U2) (y : ℝ) (hy : 0 < y)
    (ω : Ω) : 0 < Hstar p Zv U2 y ω :=
  (eq_11 p U2 hU2 p.T ⟨p.T_pos.le, le_rfl⟩ _ (yd_pos p st Iθ Zv hZv y hy _ ω)).1

lemma cs_adapted (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (y : ℝ) (hy : 0 < y)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ p.T) : Measurable[FS p st t] (cstar p Zv U1 y t) := by
  have hZt : Measurable[FS p st t] (fun ω => Zv (((t : ℝ)).toNNReal) ω) := by
    simpa [Real.toNNReal_coe] using hZv.2.1 t
  have hyv : Measurable[FS p st t] (fun ω => ydual p Zv y t ω) := by
    unfold ydual
    exact (hZt.const_mul _).div_const _
  exact RetirePIveqr.measurable_Iinv_comp (mX := FS p st t) p U1 hU1 (fun _ => (t : ℝ))
    measurable_const (fun _ => ⟨t.2, ht⟩) _ hyv (fun ω => yd_pos p st Iθ Zv hZv y hy _ ω)

lemma cs_meas (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (y : ℝ) (hy : 0 < y) :
    Measurable (fun z : ℝ≥0 × Ω => cstar p Zv U1 y (min z.1 p.Tn) z.2) := by
  have hzmm := RetirePI13.measurable_zm p st Iθ Zv hZv
  have hBm : Measurable (fun u : ℝ => Bt p u) := by unfold Bt; fun_prop
  have hZ2 : Measurable (fun z : ℝ≥0 × Ω => Zv (min z.1 p.Tn) z.2) := by
    have h1 : Measurable (fun z : ℝ≥0 × Ω => (((z.1 : ℝ≥0) : ℝ), z.2)) :=
      (measurable_coe_nnreal_real.comp measurable_fst).prodMk measurable_snd
    simpa [Real.toNNReal_coe, Function.comp_def] using hzmm.comp h1
  have hsm : Measurable (fun z : ℝ≥0 × Ω => ((min z.1 p.Tn : ℝ≥0) : ℝ)) :=
    measurable_coe_nnreal_real.comp (measurable_fst.min measurable_const)
  have hyv : Measurable (fun z : ℝ≥0 × Ω => ydual p Zv y (min z.1 p.Tn : ℝ≥0) z.2) := by
    unfold ydual
    simp only [Real.toNNReal_coe]
    exact ((measurable_const.mul ((hsm.const_mul _).exp)).mul hZ2).div (hBm.comp hsm)
  exact RetirePIveqr.measurable_Iinv_comp p U1 hU1 _ hsm
    (fun z => ⟨(min z.1 p.Tn).2, by
      have : ((min z.1 p.Tn : ℝ≥0) : ℝ) ≤ (p.Tn : ℝ) := NNReal.coe_le_coe.2 (min_le_right _ _)
      linarith [RetirePI13.coe_Tn p]⟩) _ hyv (fun z => yd_pos p st Iθ Zv hZv y hy _ _)

lemma Hs_meas (hZv : IsZVersion p st Iθ Zv) (hU2 : Assumption22 p U2) (y : ℝ) (hy : 0 < y) :
    Measurable[FS p st p.Tn] (Hstar p Zv U2 y) := by
  have hZt : Measurable[FS p st p.Tn] (fun ω => Zv (p.T.toNNReal) ω) := hZv.2.1 p.Tn
  have hyv : Measurable[FS p st p.Tn] (fun ω => ydual p Zv y p.T ω) := by
    unfold ydual
    exact (hZt.const_mul _).div_const _
  exact RetirePIveqr.measurable_Iinv_comp (mX := FS p st p.Tn) p U2 hU2 (fun _ => p.T)
    measurable_const (fun _ => ⟨p.T_pos.le, le_rfl⟩) _ hyv
    (fun ω => yd_pos p st Iθ Zv hZv y hy _ ω)

end cand

open RetirePI13 RetirePIveqr in
lemma budget_identity (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (x y : ℝ) (hy : 0 < y) (h21eq : X12 p st Iθ Zv U1 U2 y = ENNReal.ofReal x) :
    ∫⁻ ω, ENNReal.ofReal (Zv p.Tn ω * (Hstar p Zv U2 y ω / Bt p p.T)) ∂st.P +
      ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) p.T, ENNReal.ofReal
        (Zv s.toNNReal ω * (cstar p Zv U1 y s.toNNReal ω / Bt p s))) ∂st.P = ENNReal.ofReal x := by
  have hP : IsProbabilityMeasure st.P := hst.1
  have hTle : ((p.Tn : ℝ≥0) : ℝ) ≤ p.T := le_of_eq (coe_Tn p)
  have hZm := measurable_Z p st Iθ hIto p.Tn
  have hBm : Measurable (fun u : ℝ => Bt p u) := by unfold Bt; fun_prop
  have hcpos := cs_pos p st Iθ Zv U1 hZv hU1 y hy
  have hHpos := Hs_pos p st Iθ Zv U2 hZv hU2 y hy
  have hcad := cs_adapted p st Iθ Zv U1 hZv hU1 y hy
  have hcm := cs_meas p st Iθ Zv U1 hZv hU1 y hy
  have hHm := Hs_meas p st Iθ Zv U2 hZv hU2 y hy
  have hHm' : Measurable (Hstar p Zv U2 y) := hHm.mono ((FS p st).le _) le_rfl
  set cs := cstar p Zv U1 y with hcsdef
  set Hs := Hstar p Zv U2 y with hHsdef
  have hcmm := measurable_cm p cs hcm
  have hcongr0 : ∀ ω, ∀ s ∈ Icc (0 : ℝ) p.T, cs s.toNNReal ω = cs (min s.toNNReal p.Tn) ω := by
    intro ω s hs
    rw [min_eq_left (toNNReal_le_Tn p hs.2)]
  -- Step A: the budget identity under `P`
  have hinner_m : Measurable (fun ω => ∫⁻ s in Icc (0 : ℝ) p.T,
      ENNReal.ofReal (cs s.toNNReal ω / Bt p s)) := by
    have : (fun ω => ∫⁻ s in Icc (0 : ℝ) p.T, ENNReal.ofReal (cs s.toNNReal ω / Bt p s)) =
        fun ω => ∫⁻ s in Icc (0 : ℝ) p.T,
          ENNReal.ofReal (cs (min s.toNNReal p.Tn) ω / Bt p s) := by
      funext ω
      exact setLIntegral_congr_fun measurableSet_Icc (fun s hs => by rw [hcongr0 ω s hs])
    rw [this]
    have hm : Measurable (fun q : Ω × ℝ =>
        ENNReal.ofReal (cs (min q.2.toNNReal p.Tn) q.1 / Bt p q.2)) :=
      ((hcmm.comp measurable_swap).div (hBm.comp measurable_snd)).ennreal_ofReal
    exact hm.lintegral_prod_right'
  have hm1 : Measurable (fun ω => ENNReal.ofReal (Z p st Iθ p.Tn ω * (Hs ω / Bt p p.T))) :=
    (hZm.mul (hHm'.div_const _)).ennreal_ofReal
  have hXP : X12 p st Iθ Zv U1 U2 y =
      ∫⁻ ω, ENNReal.ofReal (Z p st Iθ p.Tn ω * (Hs ω / Bt p p.T)) ∂st.P +
      ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) p.T,
        ENNReal.ofReal (Z p st Iθ p.Tn ω * (cs s.toNNReal ω / Bt p s))) ∂st.P := by
    unfold X12 Pt
    rw [← hcsdef, ← hHsdef]
    have hgm : Measurable (fun ω => ENNReal.ofReal (Hs ω / Bt p p.T) +
        ∫⁻ s in Icc (0 : ℝ) p.T, ENNReal.ofReal (cs s.toNNReal ω / Bt p s)) :=
      ((hHm'.div_const _).ennreal_ofReal).add hinner_m
    rw [lintegral_withDensity_eq_lintegral_mul₀ hZm.ennreal_ofReal.aemeasurable hgm.aemeasurable,
      ← lintegral_add_left hm1]
    refine lintegral_congr fun ω => ?_
    have hZ0 : 0 ≤ Z p st Iθ p.Tn ω := (Z_pos p st Iθ _ ω).le
    simp only [Pi.mul_apply]
    rw [mul_add, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hZ0]
    congr 1
    refine lintegral_congr fun s => ?_
    rw [ENNReal.ofReal_mul hZ0]
  rw [h21eq] at hXP
  have hlt1 : ∫⁻ ω, ENNReal.ofReal (Z p st Iθ p.Tn ω * (Hs ω / Bt p p.T)) ∂st.P < ⊤ :=
    lt_of_le_of_lt (le_add_right le_rfl) (hXP ▸ ENNReal.ofReal_lt_top)
  have hlt2' : ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) p.T,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (cs s.toNNReal ω / Bt p s))) ∂st.P < ⊤ :=
    lt_of_le_of_lt (le_add_left le_rfl) (hXP ▸ ENNReal.ofReal_lt_top)
  have hIocIcc : ∀ ω, ∫⁻ s in Icc (0 : ℝ) p.T,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (cs s.toNNReal ω / Bt p s)) =
      ∫⁻ s in Ioc (0 : ℝ) p.T,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (cs s.toNNReal ω / Bt p s)) := fun ω =>
    (setLIntegral_congr Ioc_ae_eq_Icc).symm
  simp_rw [hIocIcc] at hXP hlt2'
  rw [lintegral_com p st Iθ Zv hst hIto h21 hZv p.Tn hTle (fun ω => Hs ω / Bt p p.T)
      (hHm.div_const _)
      (Eventually.of_forall fun ω => div_nonneg (hHpos ω).le (Bt_pos p _).le) hlt1,
    cons_swap p st Iθ Zv hst hIto h21 hZv cs hcm hcad hcpos hlt2'] at hXP
  exact hXP.symm

/-- The discounted remaining budget cost `H*/B_T + ∫_t^T c*_u/B_u du`. -/
noncomputable def Yp (p : Params) (Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ) (y : ℝ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  Hstar p Zv U2 y ω / Bt p p.T + ∫ u in Ioc (t : ℝ) p.T, cstar p Zv U1 y u.toNNReal ω / Bt p u

/-- The candidate wealth process: `H_t = B_t Ẽ[Y_t | F^S_t]` for `t < T`, `H_T = H*`. -/
noncomputable def Hp (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (y : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ) < p.T then Bt p t * (Pt p st Iθ)[Yp p Zv U1 U2 y t | FS p st t] ω
  else Hstar p Zv U2 y ω

omit [MeasurableSpace Ω] in
lemma Y_nonneg' {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (y : ℝ) (hy : 0 < y) (t : ℝ≥0) (ω : Ω) : 0 ≤ Yp p Zv U1 U2 y t ω := by
  refine add_nonneg (div_nonneg (Hs_pos p st Iθ Zv U2 hZv hU2 y hy ω).le
    (RetirePI13.Bt_pos p _).le) ?_
  exact setIntegral_nonneg measurableSet_Ioc fun u hu =>
    div_nonneg (cs_pos p st Iθ Zv U1 hZv hU1 y hy _ (RetirePI13.coe_toNNReal_le p hu.2) ω).le
      (RetirePI13.Bt_pos p u).le

section constr
variable (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
  (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
  (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
  (x y : ℝ) (hy : 0 < y) (h21eq : X12 p st Iθ Zv U1 U2 y = ENNReal.ofReal x)
include hst hIto h21 hZv hU1 hU2 hy h21eq

open RetirePI13 RetirePIveqr

lemma cs_congr (ω : Ω) (s : ℝ) (hs : s ≤ p.T) :
    cstar p Zv U1 y s.toNNReal ω = cstar p Zv U1 y (min s.toNNReal p.Tn) ω := by
  rw [min_eq_left (toNNReal_le_Tn p hs)]

omit hst hIto h21 hZv hU1 hU2 hy h21eq in
lemma cs_congr' (ω : Ω) (s : ℝ) (hs : s ≤ p.T) :
    cstar p Zv U1 y s.toNNReal ω = cstar p Zv U1 y (min s.toNNReal p.Tn) ω := by
  rw [min_eq_left (toNNReal_le_Tn p hs)]

lemma inner_meas (a : ℝ) (ha : 0 ≤ a) :
    Measurable (fun ω => ∫⁻ u in Ioc a p.T,
      ENNReal.ofReal (cstar p Zv U1 y u.toNNReal ω / Bt p u)) := by
  have hcmm := measurable_cm p _ (cs_meas p st Iθ Zv U1 hZv hU1 y hy)
  have hBm : Measurable (fun u : ℝ => Bt p u) := by unfold Bt; fun_prop
  have : (fun ω => ∫⁻ u in Ioc a p.T, ENNReal.ofReal (cstar p Zv U1 y u.toNNReal ω / Bt p u)) =
      fun ω => ∫⁻ u in Ioc a p.T,
        ENNReal.ofReal (cstar p Zv U1 y (min u.toNNReal p.Tn) ω / Bt p u) := by
    funext ω
    exact setLIntegral_congr_fun measurableSet_Ioc (fun u hu => by
      rw [cs_congr' p Zv U1 y ω u hu.2])
  rw [this]
  have hm : Measurable (fun q : Ω × ℝ =>
      ENNReal.ofReal (cstar p Zv U1 y (min q.2.toNNReal p.Tn) q.1 / Bt p q.2)) :=
    ((hcmm.comp measurable_swap).div (hBm.comp measurable_snd)).ennreal_ofReal
  exact hm.lintegral_prod_right'

lemma int_meas (a b : ℝ) (hb : b ≤ p.T) :
    StronglyMeasurable (fun ω => ∫ u in Ioc a b, cstar p Zv U1 y u.toNNReal ω / Bt p u) := by
  have hcmm := measurable_cm p _ (cs_meas p st Iθ Zv U1 hZv hU1 y hy)
  have hBm : Measurable (fun u : ℝ => Bt p u) := by unfold Bt; fun_prop
  have : (fun ω => ∫ u in Ioc a b, cstar p Zv U1 y u.toNNReal ω / Bt p u) =
      fun ω => ∫ u in Ioc a b, cstar p Zv U1 y (min u.toNNReal p.Tn) ω / Bt p u := by
    funext ω
    exact setIntegral_congr_fun measurableSet_Ioc (fun u hu => by
      rw [cs_congr' p Zv U1 y ω u (hu.2.trans hb)])
  rw [this]
  have hm : Measurable (fun q : Ω × ℝ =>
      cstar p Zv U1 y (min q.2.toNNReal p.Tn) q.1 / Bt p q.2) :=
    (hcmm.comp measurable_swap).div (hBm.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'

lemma intPt : ∀ᵐ ω ∂(Pt p st Iθ),
    IntegrableOn (fun u => cstar p Zv U1 y u.toNNReal ω / Bt p u) (Icc (0 : ℝ) p.T) := by
  have hcmm := measurable_cm p _ (cs_meas p st Iθ Zv U1 hZv hU1 y hy)
  have hBm : Measurable (fun u : ℝ => Bt p u) := by unfold Bt; fun_prop
  have hle : ∫⁻ ω, (∫⁻ u in Icc (0 : ℝ) p.T,
      ENNReal.ofReal (cstar p Zv U1 y u.toNNReal ω / Bt p u)) ∂(Pt p st Iθ) ≤ X12 p st Iθ Zv U1 U2 y :=
    lintegral_mono fun ω => le_add_left le_rfl
  have hlt := lt_of_le_of_lt hle (h21eq ▸ ENNReal.ofReal_lt_top)
  have hm : Measurable (fun ω => ∫⁻ u in Icc (0 : ℝ) p.T,
      ENNReal.ofReal (cstar p Zv U1 y u.toNNReal ω / Bt p u)) := by
    have : (fun ω => ∫⁻ u in Icc (0 : ℝ) p.T,
        ENNReal.ofReal (cstar p Zv U1 y u.toNNReal ω / Bt p u)) =
        fun ω => ∫⁻ u in Ioc (0 : ℝ) p.T,
          ENNReal.ofReal (cstar p Zv U1 y u.toNNReal ω / Bt p u) := by
      funext ω; exact (setLIntegral_congr Ioc_ae_eq_Icc).symm
    rw [this]; exact inner_meas p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq 0 le_rfl
  filter_upwards [ae_lt_top hm hlt.ne] with ω hω
  have hae : AEStronglyMeasurable (fun u => cstar p Zv U1 y u.toNNReal ω / Bt p u)
      (volume.restrict (Icc (0 : ℝ) p.T)) := by
    have hm2 : Measurable (fun u : ℝ => cstar p Zv U1 y (min u.toNNReal p.Tn) ω / Bt p u) :=
      (hcmm.comp (measurable_id.prodMk measurable_const)).div hBm
    refine hm2.aestronglyMeasurable.congr ?_
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun u hu => by simp only [cs_congr' p Zv U1 y ω u hu.2])
  refine ⟨hae, (hasFiniteIntegral_iff_ofReal ?_).2 hω⟩
  exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun u hu =>
    div_nonneg (cs_pos p st Iθ Zv U1 hZv hU1 y hy _ (coe_toNNReal_le p hu.2) ω).le (Bt_pos p u).le)

lemma Y_meas (t : ℝ≥0) : StronglyMeasurable (Yp p Zv U1 U2 y t) := by
  have hHm := (Hs_meas p st Iθ Zv U2 hZv hU2 y hy).mono ((FS p st).le _) le_rfl
  have h2 := int_meas p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq t p.T le_rfl
  unfold Yp
  exact ((hHm.div_const _).add h2.measurable).stronglyMeasurable

lemma Y_lint (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Yp p Zv U1 U2 y t ω) ∂(Pt p st Iθ) ≤ X12 p st Iθ Zv U1 U2 y := by
  unfold X12
  refine lintegral_mono_ae ?_
  filter_upwards [intPt p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq] with ω hω
  have hsub : Ioc (t : ℝ) p.T ⊆ Icc 0 p.T := fun u hu => ⟨t.2.trans hu.1.le, hu.2⟩
  have hnn : ∀ u ∈ Ioc (t : ℝ) p.T, 0 ≤ cstar p Zv U1 y u.toNNReal ω / Bt p u := fun u hu =>
    div_nonneg (cs_pos p st Iθ Zv U1 hZv hU1 y hy _ (coe_toNNReal_le p hu.2) ω).le (Bt_pos p u).le
  unfold Yp
  rw [ENNReal.ofReal_add (div_nonneg (Hs_pos p st Iθ Zv U2 hZv hU2 y hy ω).le (Bt_pos p _).le)
    (setIntegral_nonneg measurableSet_Ioc hnn),
    ofReal_integral_eq_lintegral_ofReal (hω.mono_set hsub)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hnn))]
  gcongr

lemma Y_int (t : ℝ≥0) : Integrable (Yp p Zv U1 U2 y t) (Pt p st Iθ) := by
  refine ⟨(Y_meas p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq t).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
      (Y_nonneg' p st Iθ Zv U1 U2 hZv hU1 hU2 y hy t))).2 ?_⟩
  exact lt_of_le_of_lt (Y_lint p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq t)
    (h21eq ▸ ENNReal.ofReal_lt_top)

lemma Y0_integral (hx : 0 ≤ x) : ∫ ω, Yp p Zv U1 U2 y 0 ω ∂(Pt p st Iθ) = x := by
  have hnn := Y_nonneg' p st Iθ Zv U1 U2 hZv hU1 hU2 y hy 0
  have h1 := ofReal_integral_eq_lintegral_ofReal
    (Y_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq 0) (Eventually.of_forall hnn)
  have h2 : ∫⁻ ω, ENNReal.ofReal (Yp p Zv U1 U2 y 0 ω) ∂(Pt p st Iθ) = ENNReal.ofReal x := by
    rw [← h21eq]
    unfold X12
    refine lintegral_congr_ae ?_
    filter_upwards [intPt p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq] with ω hω
    have hnn' : ∀ u ∈ Ioc (0 : ℝ) p.T, 0 ≤ cstar p Zv U1 y u.toNNReal ω / Bt p u := fun u hu =>
      div_nonneg (cs_pos p st Iθ Zv U1 hZv hU1 y hy _ (coe_toNNReal_le p hu.2) ω).le
        (Bt_pos p u).le
    unfold Yp
    simp only [NNReal.coe_zero]
    rw [ENNReal.ofReal_add (div_nonneg (Hs_pos p st Iθ Zv U2 hZv hU2 y hy ω).le
      (Bt_pos p _).le) (setIntegral_nonneg measurableSet_Ioc hnn'),
      ofReal_integral_eq_lintegral_ofReal (hω.mono_set Ioc_subset_Icc_self)
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hnn')),
      setLIntegral_congr Ioc_ae_eq_Icc]
  rw [h2] at h1
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hnn) hx).1 h1

lemma Y_split (s t : ℝ≥0) (hst' : s ≤ t) (ht : (t : ℝ) ≤ p.T) :
    ∀ᵐ ω ∂(Pt p st Iθ), Yp p Zv U1 U2 y s ω =
      Yp p Zv U1 U2 y t ω + ∫ u in Ioc (s : ℝ) t, cstar p Zv U1 y u.toNNReal ω / Bt p u := by
  filter_upwards [intPt p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq] with ω hω
  have h1 : IntegrableOn (fun u => cstar p Zv U1 y u.toNNReal ω / Bt p u) (Ioc (s : ℝ) t) :=
    hω.mono_set fun u hu => ⟨s.2.trans hu.1.le, hu.2.trans ht⟩
  have h2 : IntegrableOn (fun u => cstar p Zv U1 y u.toNNReal ω / Bt p u) (Ioc (t : ℝ) p.T) :=
    hω.mono_set fun u hu => ⟨t.2.trans hu.1.le, hu.2⟩
  unfold Yp
  rw [← Ioc_union_Ioc_eq_Ioc (NNReal.coe_le_coe.2 hst') ht,
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc h1 h2]
  ring

lemma D_int (s t : ℝ≥0) (hst' : s ≤ t) (ht : (t : ℝ) ≤ p.T) :
    Integrable (fun ω => ∫ u in Ioc (s : ℝ) t, cstar p Zv U1 y u.toNNReal ω / Bt p u)
      (Pt p st Iθ) := by
  refine ((Y_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq s).sub
    (Y_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq t)).congr ?_
  filter_upwards [Y_split p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq s t hst' ht]
    with ω hω
  simp only [Pi.sub_apply, hω]
  ring

lemma V_eq (t : ℝ≥0) (ht : (t : ℝ) ≤ p.T) :
    (fun ω => Hp p st Iθ Zv U1 U2 y t ω / Bt p t) =ᵐ[Pt p st Iθ]
      (Pt p st Iθ)[Yp p Zv U1 U2 y t | FS p st t] := by
  have hPt : IsProbabilityMeasure (Pt p st Iθ) := Pt_prob p st Iθ hst hIto h21
  by_cases h : (t : ℝ) < p.T
  · refine Eventually.of_forall fun ω => ?_
    have hB := (Bt_pos p t).ne'
    simp only [Hp, h, if_true]
    field_simp
  · have htT : (t : ℝ) = p.T := le_antisymm ht (not_lt.1 h)
    have htn : t = p.Tn := NNReal.eq (by rw [htT, coe_Tn])
    have hYt : Yp p Zv U1 U2 y t = fun ω => Hstar p Zv U2 y ω / Bt p p.T := by
      funext ω
      simp [Yp, htT]
    have hm : StronglyMeasurable[FS p st t] (Yp p Zv U1 U2 y t) := by
      rw [hYt]
      have := Hs_meas p st Iθ Zv U2 hZv hU2 y hy
      rw [← htn] at this
      exact (this.div_const _).stronglyMeasurable
    rw [condExp_of_stronglyMeasurable ((FS p st).le t) hm
      (Y_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq t)]
    refine Eventually.of_forall fun ω => ?_
    simp only [Hp, hYt, htT, lt_irrefl, if_false]

lemma budget_ok : BudgetConstraint p st Iθ
    ⟨cstar p Zv U1 y, Hp p st Iθ Zv U1 U2 y, fun _ => 0⟩ := by
  have hPt : IsProbabilityMeasure (Pt p st Iθ) := Pt_prob p st Iθ hst hIto h21
  intro s t hst' ht
  have hbl : budgetLHS p ⟨cstar p Zv U1 y, Hp p st Iθ Zv U1 U2 y, fun _ => 0⟩ s t =
      fun ω => Hp p st Iθ Zv U1 U2 y t ω / Bt p t +
        ∫ u in Ioc (s : ℝ) t, cstar p Zv U1 y u.toNNReal ω / Bt p u := by
    funext ω
    simp [budgetLHS, Rind, dRatom]
  have hV := V_eq p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq t ht
  have hVs := V_eq p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq s
    (le_trans (NNReal.coe_le_coe.2 hst'.le) ht)
  have hD := D_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq s t hst'.le ht
  have hYt := Y_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq t
  have hsplit := Y_split p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy h21eq s t hst'.le ht
  have hVint : Integrable (fun ω => Hp p st Iθ Zv U1 U2 y t ω / Bt p t) (Pt p st Iθ) :=
    integrable_condExp.congr hV.symm
  rw [hbl]
  refine ⟨hVint.add hD, ?_⟩
  have hrhs : (fun ω => (Hp p st Iθ Zv U1 U2 y s ω - b p s *
      (1 - Rind (fun _ => (0 : ℝ≥0)) s ω)) / Bt p s) =
      fun ω => Hp p st Iθ Zv U1 U2 y s ω / Bt p s := by
    funext ω; simp [Rind]
  show _ ≤ᵐ[Pt p st Iθ] (fun ω => (Hp p st Iθ Zv U1 U2 y s ω - b p s *
      (1 - Rind (fun _ => (0 : ℝ≥0)) s ω)) / Bt p s)
  rw [hrhs]
  refine EventuallyEq.le ?_
  have hle : FS p st s ≤ FS p st t := (FS p st).mono hst'.le
  have e1 := condExp_add (m := FS p st s) hVint hD
  have e2 := condExp_congr_ae (m := FS p st s) hV
  have e3 := condExp_condExp_of_le (μ := Pt p st Iθ) (f := Yp p Zv U1 U2 y t) hle ((FS p st).le t)
  have e4 := condExp_add (m := FS p st s) hYt hD
  have e5 := condExp_congr_ae (m := FS p st s) hsplit
  filter_upwards [e1, e2, e3, e4, e5, hVs] with ω h1 h2 h3 h4 h5 h6
  have h1' : (Pt p st Iθ)[(fun ω => Hp p st Iθ Zv U1 U2 y t ω / Bt p t +
      ∫ u in Ioc (s : ℝ) t, cstar p Zv U1 y u.toNNReal ω / Bt p u) | FS p st s] ω =
      (Pt p st Iθ)[(fun ω => Hp p st Iθ Zv U1 U2 y t ω / Bt p t) | FS p st s] ω +
      (Pt p st Iθ)[(fun ω => ∫ u in Ioc (s : ℝ) t,
        cstar p Zv U1 y u.toNNReal ω / Bt p u) | FS p st s] ω := h1
  rw [h1', h2, h3, ← Pi.add_apply, ← h4]
  exact h5.symm.trans h6.symm

end constr

end RetirePIfr


namespace RetirePIfw

variable {Ω : Type*} [MeasurableSpace Ω]

open RetirePI13 RetirePIveqr RetirePIfr

lemma b_nonpos (p : Params) (t : ℝ) : b p t ≤ 0 := by
  unfold b
  split_ifs with h
  · have hneg : t - p.T1 < 0 := by linarith
    rcases lt_or_gt_of_ne p.r_ne_zero with hr | hr
    · have he : 1 < Real.exp (p.r * (t - p.T1)) := Real.one_lt_exp_iff.2 (mul_pos_of_neg_of_neg hr hneg)
      have h1 : p.ξ / p.r ≤ 0 := div_nonpos_of_nonneg_of_nonpos p.ξ_nonneg hr.le
      nlinarith
    · have he : Real.exp (p.r * (t - p.T1)) < 1 := Real.exp_lt_one_iff.2 (mul_neg_of_pos_of_neg hr hneg)
      have h1 : 0 ≤ p.ξ / p.r := div_nonneg p.ξ_nonneg hr.le
      nlinarith
  · exact le_rfl

lemma measurable_b (p : Params) : Measurable (b p) := by
  unfold b
  exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

lemma measurable_tau (p : Params) (st : Setting Ω) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ) :
    Measurable τ := by
  refine measurable_of_Iic fun t => ?_
  have h := (hτ.1 t)
  have : τ ⁻¹' Iic t = {ω | (τ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := by
    ext ω; simp only [mem_preimage, mem_Iic, mem_setOf_eq, WithTop.coe_le_coe]
  rw [this]
  exact (FS p st).le t _ h

lemma tau_le_T (p : Params) (st : Setting Ω) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ)
    (ω : Ω) : (τ ω : ℝ) ≤ p.T := (hτ.2 ω).trans p.T1_le_T

/-- The atom `−b(τ)/B_τ ≥ 0`. -/
noncomputable def Aτ (p : Params) (τ : Ω → ℝ≥0) (ω : Ω) : ℝ := -(b p (τ ω)) / Bt p (τ ω)

lemma A_nonneg (p : Params) (τ : Ω → ℝ≥0) (ω : Ω) : 0 ≤ Aτ p τ ω :=
  div_nonneg (neg_nonneg.2 (b_nonpos p _)) (Bt_pos p _).le

lemma measurable_A (p : Params) (st : Setting Ω) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ) :
    Measurable (Aτ p τ) := by
  have hτm := measurable_coe_nnreal_real.comp (measurable_tau p st τ hτ)
  have hBm : Measurable (fun u : ℝ => Bt p u) := by unfold Bt; fun_prop
  unfold Aτ
  exact ((measurable_b p).comp hτm).neg.div (hBm.comp hτm)

/-- The remaining cost with retirement: `Y_t + 1{t < τ} (−b(τ)/B_τ)`. -/
noncomputable def Yw (p : Params) (Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ) (y : ℝ)
    (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Yp p Zv U1 U2 y t ω + if t < τ ω then Aτ p τ ω else 0

/-- The candidate wealth: `H_t = B_t Ẽ[Yw_t | F^S_t] + b(t)(1 − R_t)` for `t < T`, `H_T = H*`. -/
noncomputable def Hw (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (y : ℝ) (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ) < p.T then
    Bt p t * (Pt p st Iθ)[Yw p Zv U1 U2 y τ t | FS p st t] ω + b p t * (1 - Rind τ t ω)
  else Hstar p Zv U2 y ω

section constrw
variable (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
  (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
  (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
  (x y : ℝ) (hy : 0 < y) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ)
  (hXc : Xcal p st Iθ Zv U1 U2 y τ = ENNReal.ofReal (x - b p 0))
include hst hIto h21 hZv hU1 hU2 hy hτ hXc

lemma X12_le_Xcal : X12 p st Iθ Zv U1 U2 y ≤ Xcal p st Iθ Zv U1 U2 y τ := by
  unfold X12 Xcal
  exact lintegral_mono fun ω => le_self_add

lemma X12_eq : X12 p st Iθ Zv U1 U2 y = ENNReal.ofReal (X12 p st Iθ Zv U1 U2 y).toReal := by
  refine (ENNReal.ofReal_toReal ?_).symm
  exact ne_top_of_le_ne_top (hXc ▸ ENNReal.ofReal_ne_top)
    (X12_le_Xcal p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc)

lemma A_int : Integrable (Aτ p τ) (Pt p st Iθ) := by
  refine ⟨(measurable_A p st τ hτ).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (A_nonneg p τ))).2 ?_⟩
  refine lt_of_le_of_lt ?_ (hXc ▸ ENNReal.ofReal_lt_top : Xcal p st Iθ Zv U1 U2 y τ < ⊤)
  unfold Xcal
  exact lintegral_mono fun ω => le_add_left le_rfl

lemma ite_int (t : ℝ≥0) : Integrable (fun ω => if t < τ ω then Aτ p τ ω else 0) (Pt p st Iθ) := by
  refine (A_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc).mono' ?_ ?_
  · exact (Measurable.ite (measurableSet_lt measurable_const (measurable_tau p st τ hτ))
      (measurable_A p st τ hτ) measurable_const).aestronglyMeasurable
  · refine Eventually.of_forall fun ω => ?_
    split_ifs
    · rw [Real.norm_of_nonneg (A_nonneg p τ ω)]
    · simpa using A_nonneg p τ ω

lemma Yw_int (t : ℝ≥0) : Integrable (Yw p Zv U1 U2 y τ t) (Pt p st Iθ) :=
  (Y_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 _ y hy
    (X12_eq p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc) t).add
    (ite_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc t)

lemma dR_int (s t : ℝ≥0) : Integrable (dRatom p τ s t) (Pt p st Iθ) := by
  refine (A_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc).mono' ?_ ?_
  · have hτm := measurable_tau p st τ hτ
    have hBm : Measurable (fun u : ℝ => Bt p u) := by unfold Bt; fun_prop
    unfold dRatom
    refine (Measurable.ite ?_ ?_ measurable_const).aestronglyMeasurable
    · have hτr := measurable_coe_nnreal_real.comp hτm
      exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
        (measurableSet_le (by fun_prop) (by fun_prop))
    · have hτr := measurable_coe_nnreal_real.comp hτm
      exact ((measurable_b p).comp hτr).div (hBm.comp hτr)
  · refine Eventually.of_forall fun ω => ?_
    unfold dRatom Aτ
    split_ifs
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos (Bt_pos p _), abs_of_nonpos (b_nonpos p _)]
    · rw [norm_zero]; exact A_nonneg p τ ω

lemma Yw_split (s t : ℝ≥0) (hst' : s ≤ t) (ht : (t : ℝ) ≤ p.T) :
    ∀ᵐ ω ∂(Pt p st Iθ), Yw p Zv U1 U2 y τ s ω =
      Yw p Zv U1 U2 y τ t ω + ((∫ u in Ioc (s : ℝ) t, cstar p Zv U1 y u.toNNReal ω / Bt p u) -
        dRatom p τ s t ω) := by
  filter_upwards [Y_split p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 _ y hy
    (X12_eq p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc) s t hst' ht] with ω hω
  unfold Yw dRatom Aτ
  rw [hω]
  by_cases h1 : s < τ ω
  · by_cases h2 : τ ω ≤ t
    · have h3 : ¬ t < τ ω := not_lt.2 h2
      simp only [h1, h2, h3, and_self, if_true, if_false]
      ring
    · have h3 : t < τ ω := not_le.1 h2
      simp only [h1, h2, h3, and_false, if_true, if_false]
      ring
  · have h3 : ¬ t < τ ω := fun h => h1 (lt_of_le_of_lt hst' h)
    simp only [h1, h3, false_and, if_false]
    ring

lemma Rind_T (ω : Ω) : Rind τ p.Tn ω = 1 := by
  have : τ ω ≤ p.Tn := by
    rw [← NNReal.coe_le_coe, coe_Tn]; exact tau_le_T p st τ hτ ω
  simp [Rind, this]

lemma V_eqw (t : ℝ≥0) (ht : (t : ℝ) ≤ p.T) :
    (fun ω => (Hw p st Iθ Zv U1 U2 y τ t ω - b p t * (1 - Rind τ t ω)) / Bt p t) =ᵐ[Pt p st Iθ]
      (Pt p st Iθ)[Yw p Zv U1 U2 y τ t | FS p st t] := by
  have hPt : IsProbabilityMeasure (Pt p st Iθ) := Pt_prob p st Iθ hst hIto h21
  by_cases h : (t : ℝ) < p.T
  · refine Eventually.of_forall fun ω => ?_
    have hB := (Bt_pos p t).ne'
    simp only [Hw, h, if_true]
    field_simp
    ring
  · have htT : (t : ℝ) = p.T := le_antisymm ht (not_lt.1 h)
    have htn : t = p.Tn := NNReal.eq (by rw [htT, coe_Tn])
    subst htn
    have hnot : ∀ ω, ¬ p.Tn < τ ω := fun ω => by
      rw [← NNReal.coe_lt_coe, coe_Tn, not_lt]; exact tau_le_T p st τ hτ ω
    have hYt : Yw p Zv U1 U2 y τ p.Tn = fun ω => Hstar p Zv U2 y ω / Bt p p.T := by
      funext ω
      simp [Yw, Yp, coe_Tn, hnot ω]
    have hm : StronglyMeasurable[FS p st p.Tn] (Yw p Zv U1 U2 y τ p.Tn) := by
      rw [hYt]
      exact ((Hs_meas p st Iθ Zv U2 hZv hU2 y hy).div_const _).stronglyMeasurable
    rw [condExp_of_stronglyMeasurable ((FS p st).le _) hm
      (Yw_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc _)]
    refine Eventually.of_forall fun ω => ?_
    simp only [Hw, h, if_false, hYt, Rind_T p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ
      hXc ω, sub_self, mul_zero, sub_zero, coe_Tn, lt_irrefl, if_false]

lemma budget_okw : BudgetConstraint p st Iθ
    ⟨cstar p Zv U1 y, Hw p st Iθ Zv U1 U2 y τ, τ⟩ := by
  have hPt : IsProbabilityMeasure (Pt p st Iθ) := Pt_prob p st Iθ hst hIto h21
  have hX := X12_eq p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc
  intro s t hst' ht
  have hbl : budgetLHS p ⟨cstar p Zv U1 y, Hw p st Iθ Zv U1 U2 y τ, τ⟩ s t =
      fun ω => (Hw p st Iθ Zv U1 U2 y τ t ω - b p t * (1 - Rind τ t ω)) / Bt p t +
        ((∫ u in Ioc (s : ℝ) t, cstar p Zv U1 y u.toNNReal ω / Bt p u) - dRatom p τ s t ω) := by
    funext ω
    simp only [budgetLHS]
    ring
  have hV := V_eqw p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc t ht
  have hVs := V_eqw p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc s
    (le_trans (NNReal.coe_le_coe.2 hst'.le) ht)
  have hD := (D_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 _ y hy hX s t hst'.le ht).sub
    (dR_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc s t)
  have hYt := Yw_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc t
  have hsplit := Yw_split p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc s t
    hst'.le ht
  have hVint : Integrable (fun ω => (Hw p st Iθ Zv U1 U2 y τ t ω - b p t * (1 - Rind τ t ω)) /
      Bt p t) (Pt p st Iθ) :=
    integrable_condExp.congr hV.symm
  rw [hbl]
  refine ⟨hVint.add hD, ?_⟩
  refine EventuallyEq.le ?_
  have hle : FS p st s ≤ FS p st t := (FS p st).mono hst'.le
  have e1 := condExp_add (m := FS p st s) hVint hD
  have e2 := condExp_congr_ae (m := FS p st s) hV
  have e3 := condExp_condExp_of_le (μ := Pt p st Iθ) (f := Yw p Zv U1 U2 y τ t) hle
    ((FS p st).le t)
  have e4 := condExp_add (m := FS p st s) hYt hD
  have e5 := condExp_congr_ae (m := FS p st s) hsplit
  filter_upwards [e1, e2, e3, e4, e5, hVs] with ω h1 h2 h3 h4 h5 h6
  have h1' := h1
  simp only [Pi.add_apply] at h1'
  refine (h1.trans ?_)
  rw [Pi.add_apply, h2, h3, ← Pi.add_apply, ← h4]
  exact h5.symm.trans h6.symm

lemma H0w (hx : b p 0 < x) : ∀ᵐ ω ∂st.P, Hw p st Iθ Zv U1 U2 y τ 0 ω = x := by
  have hP : IsProbabilityMeasure st.P := hst.1
  have hPt : IsProbabilityMeasure (Pt p st Iθ) := Pt_prob p st Iθ hst hIto h21
  have hX := X12_eq p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc
  have hPac := P_ac_Pt p st Iθ hIto
  have hac : Pt p st Iθ ≪ st.P := withDensity_absolutelyContinuous _ _
  set x1 := (X12 p st Iθ Zv U1 U2 y).toReal with hx1
  have hY0 := Y0_integral p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x1 y hy hX
    ENNReal.toReal_nonneg
  have hAint := A_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc
  -- `x − b(0) = x1 + Ẽ[A]`
  have hsum : x - b p 0 = x1 + ∫ ω, Aτ p τ ω ∂(Pt p st Iθ) := by
    have h1 : Xcal p st Iθ Zv U1 U2 y τ = X12 p st Iθ Zv U1 U2 y +
        ∫⁻ ω, ENNReal.ofReal (Aτ p τ ω) ∂(Pt p st Iθ) := by
      unfold Xcal X12
      rw [← lintegral_add_right _ (measurable_A p st τ hτ).ennreal_ofReal]
      rfl
    rw [hXc, hX, ← ofReal_integral_eq_lintegral_ofReal hAint
      (Eventually.of_forall (A_nonneg p τ)),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg (integral_nonneg (A_nonneg p τ))] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff (by linarith) (add_nonneg ENNReal.toReal_nonneg
      (integral_nonneg (A_nonneg p τ)))).1 h1
  have hE0 : MeasurableSet[FS p st 0] {ω | τ ω ≤ 0} := by
    have h := hτ.1 0
    have : {ω | (τ ω : WithTop ℝ≥0) ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)} = {ω | τ ω ≤ 0} := by
      ext ω; simp only [mem_setOf_eq, WithTop.coe_le_coe]
    rw [← this]; exact h
  obtain ⟨hE0m, h01⟩ := FS0_zero_one p st hst _ hE0
  have h0 : ((0 : ℝ≥0) : ℝ) < p.T := by simpa using p.T_pos
  have hc := condExp_FS0 p st Iθ hst hIto h21 _
    (Yw_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc 0)
  have hYw : ∫ ω, Yw p Zv U1 U2 y τ 0 ω ∂(Pt p st Iθ) = x1 +
      ∫ ω, (if (0 : ℝ≥0) < τ ω then Aτ p τ ω else 0) ∂(Pt p st Iθ) := by
    unfold Yw
    rw [integral_add (Y_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 _ y hy hX 0)
      (ite_int p st Iθ Zv U1 U2 hst hIto h21 hZv hU1 hU2 x y hy τ hτ hXc 0), hY0]
  rcases h01 with hz | ho
  · -- `τ > 0` almost surely
    have hpos : ∀ᵐ ω ∂st.P, ¬ τ ω ≤ 0 := measure_eq_zero_iff_ae_notMem.1 hz
    have hite : (fun ω => if (0 : ℝ≥0) < τ ω then Aτ p τ ω else 0) =ᵐ[Pt p st Iθ] Aτ p τ := by
      filter_upwards [hac.ae_le hpos] with ω hω
      simp [pos_iff_ne_zero, (not_le.1 hω).ne']
    rw [integral_congr_ae hite, ← hsum] at hYw
    filter_upwards [hPac.ae_le hc, hpos] with ω hω hτω
    simp only [Hw, h0, if_true, hω, hYw, Rind, hτω, if_false]
    simp [Bt]
  · -- `τ = 0` almost surely
    have hc0 : st.P {ω | τ ω ≤ 0}ᶜ = 0 := by rw [prob_compl_eq_one_sub hE0m, ho]; simp
    have hzero : ∀ᵐ ω ∂st.P, τ ω ≤ 0 := by
      rw [ae_iff]; exact hc0
    have hite : (fun ω => if (0 : ℝ≥0) < τ ω then Aτ p τ ω else 0) =ᵐ[Pt p st Iθ] 0 := by
      filter_upwards [hac.ae_le hzero] with ω hω
      simp [not_lt.2 hω]
    have hA : Aτ p τ =ᵐ[Pt p st Iθ] fun _ => -b p 0 := by
      filter_upwards [hac.ae_le hzero] with ω hω
      have : τ ω = 0 := le_antisymm hω (zero_le (a := τ ω))
      simp [Aτ, this, Bt]
    rw [integral_congr_ae hA] at hsum
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hsum
    rw [integral_congr_ae hite] at hYw
    simp only [Pi.zero_apply, integral_zero, add_zero] at hYw
    filter_upwards [hPac.ae_le hc, hzero] with ω hω hτω
    simp only [Hw, h0, if_true, hω, hYw, Rind, hτω, if_true]
    simp [Bt]
    linarith

end constrw

end RetirePIfw


namespace RetirePIwk

variable {Ω : Type*} [MeasurableSpace Ω]

open RetirePI13 RetirePIveqr RetirePIfr RetirePIfw

lemma b_formula (p : Params) (t : ℝ) :
    b p t = -(p.ξ / p.r) * (1 - Real.exp (p.r * min (t - p.T1) 0)) := by
  unfold b
  split_ifs with h
  · rw [min_eq_left (by linarith)]
  · rw [min_eq_right (by linarith)]; simp

lemma continuous_bB (p : Params) : Continuous (fun t => b p t / Bt p t) := by
  have : (fun t => b p t / Bt p t) =
      fun t => -(p.ξ / p.r) * (1 - Real.exp (p.r * min (t - p.T1) 0)) / Real.exp (p.r * t) := by
    funext t; rw [b_formula]; rfl
  rw [this]
  exact Continuous.div (by fun_prop) (by fun_prop) (fun t => (Real.exp_pos _).ne')

lemma bB_nonpos (p : Params) (t : ℝ) : b p t / Bt p t ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (b_nonpos p t) (Bt_pos p t).le

/-- Integrals over `[0, τ]` and `[τ, T]` of a `ds ⊗ P`-integrable function are integrable. -/
lemma int_lower (p : Params) (st : Setting Ω) (hst : st.Standing p) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ)
    (F : ℝ → Ω → ℝ)
    (hF : Integrable (fun z : ℝ × Ω => F z.1 z.2) ((volume.restrict (Icc (0 : ℝ) p.T)).prod st.P)) :
    Integrable (fun ω => ∫ s in Icc (0 : ℝ) (τ ω), F s ω) st.P := by
  have : IsProbabilityMeasure st.P := hst.1
  have hτm := measurable_coe_nnreal_real.comp (measurable_tau p st τ hτ)
  have hS : MeasurableSet {z : ℝ × Ω | z.1 ∈ Icc (0 : ℝ) (τ z.2)} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (hτm.comp measurable_snd))
  have h := (hF.indicator hS).integral_prod_right
  refine h.congr (Eventually.of_forall fun ω => ?_)
  have hsub : Icc (0 : ℝ) (τ ω) ⊆ Icc 0 p.T := Icc_subset_Icc le_rfl (tau_le_T p st τ hτ ω)
  simp only
  have : (fun s => {z : ℝ × Ω | z.1 ∈ Icc (0 : ℝ) (τ z.2)}.indicator
      (fun z : ℝ × Ω => F z.1 z.2) (s, ω)) = (Icc (0 : ℝ) (τ ω)).indicator (fun s => F s ω) := by
    funext s; simp [indicator]
  rw [this, setIntegral_indicator measurableSet_Icc, inter_eq_right.2 hsub]

lemma int_upper (p : Params) (st : Setting Ω) (hst : st.Standing p) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ)
    (F : ℝ → Ω → ℝ)
    (hF : Integrable (fun z : ℝ × Ω => F z.1 z.2) ((volume.restrict (Icc (0 : ℝ) p.T)).prod st.P)) :
    Integrable (fun ω => ∫ s in Icc (τ ω : ℝ) p.T, F s ω) st.P := by
  have : IsProbabilityMeasure st.P := hst.1
  have hτm := measurable_coe_nnreal_real.comp (measurable_tau p st τ hτ)
  have hS : MeasurableSet {z : ℝ × Ω | z.1 ∈ Icc (τ z.2 : ℝ) p.T} :=
    (measurableSet_le (hτm.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  have h := (hF.indicator hS).integral_prod_right
  refine h.congr (Eventually.of_forall fun ω => ?_)
  have hsub : Icc (τ ω : ℝ) p.T ⊆ Icc 0 p.T := Icc_subset_Icc (τ ω).2 le_rfl
  simp only
  have : (fun s => {z : ℝ × Ω | z.1 ∈ Icc (τ z.2 : ℝ) p.T}.indicator
      (fun z : ℝ × Ω => F z.1 z.2) (s, ω)) = (Icc (τ ω : ℝ) p.T).indicator (fun s => F s ω) := by
    funext s; simp [indicator]
  rw [this, setIntegral_indicator measurableSet_Icc, inter_eq_right.2 hsub]

lemma split_Icc (p : Params) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ p.T) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Icc 0 p.T)) :
    (∫ s in Icc (0 : ℝ) t, f s) + ∫ s in Icc t p.T, f s = ∫ s in Icc (0 : ℝ) p.T, f s := by
  rw [← Icc_union_Icc_eq_Icc ht0 htT, setIntegral_union₀]
  · rw [AEDisjoint, Icc_inter_Icc]
    refine measure_mono_null (fun s hs => ?_) (measure_singleton t)
    simp only [mem_Icc, mem_singleton_iff] at hs ⊢
    rcases hs with ⟨h1, h2⟩
    have : max 0 t = t := max_eq_right ht0
    have : min t p.T = t := min_eq_left htT
    linarith [le_max_right 0 t, min_le_left t p.T]
  · exact measurableSet_Icc.nullMeasurableSet
  · exact hf.mono_set (Icc_subset_Icc le_rfl htT)
  · exact hf.mono_set (Icc_subset_Icc ht0 le_rfl)

lemma bterm_int (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (hst : st.Standing p)
    (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ) :
    Integrable (fun ω => Zv (τ ω) ω * (b p (τ ω) / Bt p (τ ω))) st.P := by
  have hOS := optional_sampling_Zv p st Iθ Zv hst hIto h21 hZv τ hτ _ (continuous_bB p)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_bB p).continuousOn (s := Icc (0 : ℝ) p.T)
  have hτm := measurable_coe_nnreal_real.comp (measurable_tau p st τ hτ)
  refine hOS.1.mul_bdd (c := C) ?_ (Eventually.of_forall fun ω => hC _ ⟨(τ ω).2,
    tau_le_T p st τ hτ ω⟩)
  exact ((continuous_bB p).measurable.comp hτm).aestronglyMeasurable

lemma stopObj_decomp (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hdual : DualIntegrable p st Zv U1 U2) (y : ℝ) (hy : 0 < y)
    (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ) :
    stopObj p st Zv U1 U2 y τ hτ = L1 p st Zv U1 U2 y -
      p.ℓ * ∫ ω, (∫ s in Icc (0 : ℝ) (τ ω), Real.exp (-p.β * s)) ∂st.P +
      y * ∫ ω, Zv (τ ω) ω * (b p (τ ω) / Bt p (τ ω)) ∂st.P := by
  have hP : IsProbabilityMeasure st.P := hst.1
  set M := (volume.restrict (Icc (0 : ℝ) p.T)).prod st.P
  have hF1 := (hdual y hy).1
  have hmem : ∀ᵐ z ∂M, z.1 ∈ Icc (0 : ℝ) p.T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hE : Integrable (fun z : ℝ × Ω => Real.exp (-p.β * z.1)) M := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hmem] with z hz
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.2 (by nlinarith [p.β_pos, hz.1])
  have hIlow := int_lower p st hst τ hτ
    (fun s ω => Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) hF1
  have hIhigh := int_upper p st hst τ hτ
    (fun s ω => Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) hF1
  have hElow := int_lower p st hst τ hτ (fun s _ => Real.exp (-p.β * s)) hE
  have hU2 := ((hdual y hy).2).const_mul (Real.exp (-p.β * p.T))
  have hb := bterm_int p st Iθ Zv hst hIto h21 hZv τ hτ
  have hsec := hF1.prod_left_ae
  -- the three pieces of the stopping objective
  have hA1 : (fun ω => ∫ s in Icc (0 : ℝ) (τ ω),
      Real.exp (-p.β * s) * (Utilde U1 s (ydual p Zv y s ω) - p.ℓ)) =ᵐ[st.P]
      fun ω => (∫ s in Icc (0 : ℝ) (τ ω), Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω))
        - p.ℓ * ∫ s in Icc (0 : ℝ) (τ ω), Real.exp (-p.β * s) := by
    filter_upwards [hsec] with ω hω
    have hsub : Icc (0 : ℝ) (τ ω) ⊆ Icc 0 p.T := Icc_subset_Icc le_rfl (tau_le_T p st τ hτ ω)
    have h1 : IntegrableOn (fun s => Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω))
        (Icc (0 : ℝ) (τ ω)) :=
      (show IntegrableOn (fun s => Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω))
        (Icc 0 p.T) volume from hω).mono_set hsub
    have h2 : IntegrableOn (fun s : ℝ => Real.exp (-p.β * s) * p.ℓ) (Icc (0 : ℝ) (τ ω)) :=
      (by fun_prop : Continuous (fun s : ℝ => Real.exp (-p.β * s) * p.ℓ)).integrableOn_Icc
    simp_rw [mul_sub]
    rw [integral_sub h1 h2, integral_mul_const]
    ring
  have hbt : (fun ω => Real.exp (-p.β * (τ ω : ℝ)) * ydual p Zv y (τ ω) ω * b p (τ ω)) =
      fun ω => y * (Zv (τ ω) ω * (b p (τ ω) / Bt p (τ ω))) := by
    funext ω
    unfold ydual
    rw [Real.toNNReal_coe]
    have hB := (Bt_pos p (τ ω)).ne'
    rw [show -p.β * (τ ω : ℝ) = -(p.β * τ ω) by ring, Real.exp_neg]
    field_simp
  have hL1at : ∫ ω, L1at p st Zv U1 U2 y τ hτ ω ∂st.P =
      ∫ ω, ((∫ s in Icc (τ ω : ℝ) p.T, Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) +
        Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω)) ∂st.P := by
    unfold L1at
    exact integral_condExp hτ.1.measurableSpace_le
  have hsplit : ∀ᵐ ω ∂st.P,
      (∫ s in Icc (0 : ℝ) (τ ω), Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) +
      (∫ s in Icc (τ ω : ℝ) p.T, Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) =
      ∫ s in Icc (0 : ℝ) p.T, Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω) := by
    filter_upwards [hsec] with ω hω
    exact split_Icc p (τ ω) (τ ω).2 (tau_le_T p st τ hτ ω) _ hω
  have hL1 : L1 p st Zv U1 U2 y = (∫ ω, (∫ s in Icc (0 : ℝ) (τ ω),
        Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) ∂st.P) +
      (∫ ω, (∫ s in Icc (τ ω : ℝ) p.T,
        Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) ∂st.P) +
      ∫ ω, Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω) ∂st.P := by
    unfold L1
    rw [integral_add hF1.integral_prod_right hU2, ← integral_add hIlow hIhigh]
    congr 1
    exact (integral_congr_ae hsplit).symm
  have hL1atint : Integrable (L1at p st Zv U1 U2 y τ hτ) st.P := integrable_condExp
  have hA1i : Integrable (fun ω => ∫ s in Icc (0 : ℝ) (τ ω),
      Real.exp (-p.β * s) * (Utilde U1 s (ydual p Zv y s ω) - p.ℓ)) st.P :=
    (hIlow.sub (hElow.const_mul p.ℓ)).congr hA1.symm
  have hbt' : Integrable (fun ω => Real.exp (-p.β * (τ ω : ℝ)) * ydual p Zv y (τ ω) ω *
      b p (τ ω)) st.P := by
    rw [hbt]; exact hb.const_mul y
  have hX : Integrable (fun ω => (∫ s in Icc (0 : ℝ) (τ ω),
      Real.exp (-p.β * s) * (Utilde U1 s (ydual p Zv y s ω) - p.ℓ)) +
      L1at p st Zv U1 U2 y τ hτ ω) st.P := hA1i.add hL1atint
  unfold stopObj
  rw [integral_add hX hbt', integral_add hA1i hL1atint, integral_congr_ae hA1,
    integral_sub hIlow (hElow.const_mul p.ℓ), integral_const_mul,
    hL1at, integral_add hIhigh hU2, hbt, integral_const_mul y, hL1]
  ring

lemma bB_bound (p : Params) : ∃ C, ∀ t ∈ Icc (0 : ℝ) p.T, ‖b p t / Bt p t‖ ≤ C :=
  isCompact_Icc.exists_bound_of_continuousOn (continuous_bB p).continuousOn

lemma bBτ_int (p : Params) (st : Setting Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ) :
    Integrable (fun ω => b p (τ ω) / Bt p (τ ω)) μ := by
  obtain ⟨C, hC⟩ := bB_bound p
  have hτm := measurable_coe_nnreal_real.comp (measurable_tau p st τ hτ)
  refine (integrable_const C).mono' ((continuous_bB p).measurable.comp hτm).aestronglyMeasurable
    (Eventually.of_forall fun ω => hC _ ⟨(τ ω).2, tau_le_T p st τ hτ ω⟩)

lemma budget_gen (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (x : ℝ) (q : Plan Ω) (hq : q ∈ Bclass p st Iθ U1 U2 x) :
    Integrable (fun ω => q.H p.Tn ω / Bt p p.T +
      ∫ u in Ioc (0 : ℝ) p.T, q.c u.toNNReal ω / Bt p u) (Pt p st Iθ) ∧
    ∫ ω, (q.H p.Tn ω / Bt p p.T + ∫ u in Ioc (0 : ℝ) p.T, q.c u.toNNReal ω / Bt p u)
      ∂(Pt p st Iθ) ≤ x - b p 0 + ∫ ω, b p (q.τ ω) / Bt p (q.τ ω) ∂(Pt p st Iθ) := by
  have hPt : IsProbabilityMeasure (Pt p st Iθ) := Pt_prob p st Iθ hst hIto h21
  obtain ⟨hτ, -, -, hH0, -, hbud, -, -, -⟩ := hq
  obtain ⟨hNint, hNle⟩ := hbud 0 p.Tn (Tn_pos p) (le_of_eq (coe_Tn p))
  have hτT : ∀ ω, q.τ ω ≤ p.Tn := fun ω => by
    rw [← NNReal.coe_le_coe, coe_Tn]; exact tau_le_T p st q.τ hτ ω
  set N : Ω → ℝ := fun ω => q.H p.Tn ω / Bt p p.T +
    ∫ u in Ioc (0 : ℝ) p.T, q.c u.toNNReal ω / Bt p u with hNdef
  have hbl : budgetLHS p q 0 p.Tn = fun ω => N ω - dRatom p q.τ 0 p.Tn ω := by
    funext ω
    simp [budgetLHS, Rind, hτT ω, coe_Tn, N]
  rw [hbl] at hNint hNle
  have hdR : Integrable (dRatom p q.τ 0 p.Tn) (Pt p st Iθ) := by
    obtain ⟨C, hC⟩ := bB_bound p
    have hτm := measurable_tau p st q.τ hτ
    have hBm : Measurable (fun u : ℝ => Bt p u) := by unfold Bt; fun_prop
    have hτr := measurable_coe_nnreal_real.comp hτm
    refine (integrable_const C).mono' ?_ ?_
    · unfold dRatom
      refine (Measurable.ite ?_ (((measurable_b p).comp hτr).div (hBm.comp hτr))
        measurable_const).aestronglyMeasurable
      exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
        (measurableSet_le (by fun_prop) (by fun_prop))
    · refine Eventually.of_forall fun ω => ?_
      unfold dRatom
      split_ifs
      · exact hC _ ⟨(q.τ ω).2, tau_le_T p st q.τ hτ ω⟩
      · rw [norm_zero]; exact (norm_nonneg _).trans (hC 0 ⟨le_rfl, p.T_pos.le⟩)
  have hNi : Integrable N (Pt p st Iθ) := (hNint.add hdR).congr
    (Eventually.of_forall fun ω => by simp)
  refine ⟨hNi, ?_⟩
  have hac : Pt p st Iθ ≪ st.P := withDensity_absolutelyContinuous _ _
  have hle : ∫ ω, (N ω - dRatom p q.τ 0 p.Tn ω) ∂(Pt p st Iθ) ≤
      ∫ ω, (x - b p 0 * (1 - Rind q.τ 0 ω)) ∂(Pt p st Iθ) := by
    rw [← integral_condExp ((FS p st).le 0)]
    have hR : Integrable (fun ω => x - b p 0 * (1 - Rind q.τ 0 ω)) (Pt p st Iθ) := by
      refine (integrable_const x).sub ((integrable_const (1 : ℝ)).sub ?_ |>.const_mul _)
      refine (integrable_const (1 : ℝ)).mono' ?_ (Eventually.of_forall fun ω => ?_)
      · unfold Rind
        exact (Measurable.ite (measurableSet_le (measurable_tau p st q.τ hτ) measurable_const)
          measurable_const measurable_const).aestronglyMeasurable
      · unfold Rind; split_ifs <;> simp
    refine integral_mono_ae integrable_condExp hR (hNle.trans_eq ?_)
    filter_upwards [hac.ae_le hH0] with ω hω
    simp [Bt, hω]
  have hpt : ∀ ω, x - b p 0 * (1 - Rind q.τ 0 ω) + dRatom p q.τ 0 p.Tn ω =
      x - b p 0 + b p (q.τ ω) / Bt p (q.τ ω) := by
    intro ω
    unfold Rind dRatom
    by_cases h0 : q.τ ω ≤ 0
    · have hz : q.τ ω = 0 := le_antisymm h0 (zero_le (a := q.τ ω))
      simp [hz, Bt]
    · have hpos : 0 < q.τ ω := lt_of_not_ge h0
      simp [h0, hpos, hτT ω]
  have hRi : Integrable (fun ω => x - b p 0 * (1 - Rind q.τ 0 ω)) (Pt p st Iθ) := by
    have := (((integrable_const (x - b p 0)).add (bBτ_int p st (Pt p st Iθ) q.τ hτ)).sub hdR)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    linarith [hpt ω]
  calc ∫ ω, N ω ∂(Pt p st Iθ)
      = ∫ ω, (N ω - dRatom p q.τ 0 p.Tn ω) ∂(Pt p st Iθ) +
          ∫ ω, dRatom p q.τ 0 p.Tn ω ∂(Pt p st Iθ) := by
        rw [← integral_add hNint hdR]; congr 1; funext ω; ring
    _ ≤ ∫ ω, (x - b p 0 * (1 - Rind q.τ 0 ω)) ∂(Pt p st Iθ) +
          ∫ ω, dRatom p q.τ 0 p.Tn ω ∂(Pt p st Iθ) := by linarith
    _ = ∫ ω, (x - b p 0 + b p (q.τ ω) / Bt p (q.τ ω)) ∂(Pt p st Iθ) := by
        rw [← integral_add hRi hdR]; congr 1; funext ω; exact hpt ω
    _ = x - b p 0 + ∫ ω, b p (q.τ ω) / Bt p (q.τ ω) ∂(Pt p st Iθ) := by
        rw [integral_add (integrable_const _) (bBτ_int p st (Pt p st Iθ) q.τ hτ)]
        simp

lemma budget_Pt_gen (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (x : ℝ) (q : Plan Ω) (hq : q ∈ Bclass p st Iθ U1 U2 x) :
    ∫⁻ ω, (ENNReal.ofReal (Z p st Iθ p.Tn ω * (q.H p.Tn ω / Bt p p.T)) +
      ∫⁻ u in Ioc (0 : ℝ) p.T, ENNReal.ofReal (Z p st Iθ p.Tn ω * (q.c u.toNNReal ω / Bt p u)))
      ∂st.P = ENNReal.ofReal (∫ ω, (q.H p.Tn ω / Bt p p.T +
        ∫ u in Ioc (0 : ℝ) p.T, q.c u.toNNReal ω / Bt p u) ∂(Pt p st Iθ)) := by
  have hP : IsProbabilityMeasure st.P := hst.1
  have hPt : IsProbabilityMeasure (Pt p st Iθ) := Pt_prob p st Iθ hst hIto h21
  have hNint := (budget_gen p st Iθ U1 U2 hst hIto h21 x q hq).1
  obtain ⟨c, H, τ⟩ := q
  obtain ⟨-, ⟨-, -, hcpos, hcint⟩, -, -, -, -, hHT, -, -⟩ := hq
  set N : Ω → ℝ := fun ω => H p.Tn ω / Bt p p.T +
    ∫ u in Ioc (0 : ℝ) p.T, c u.toNNReal ω / Bt p u with hNdef
  have hac : Pt p st Iθ ≪ st.P := withDensity_absolutelyContinuous _ _
  -- pointwise decomposition, P-a.e.
  have hdec : ∀ᵐ ω ∂st.P, ENNReal.ofReal (Z p st Iθ p.Tn ω) * ENNReal.ofReal (N ω) =
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (H p.Tn ω / Bt p p.T)) +
      ∫⁻ u in Ioc (0 : ℝ) p.T, ENNReal.ofReal (Z p st Iθ p.Tn ω * (c u.toNNReal ω / Bt p u)) := by
    filter_upwards [hcint, hHT] with ω hci hHpos
    have hint : IntegrableOn (fun u : ℝ => c u.toNNReal ω / Bt p u) (Ioc 0 p.T) := by
      have h1 := hci.mul_continuousOn (g' := fun u : ℝ => (Bt p u)⁻¹)
        (by
          have : Continuous (fun u : ℝ => (Bt p u)⁻¹) := by
            simp only [Bt, ← Real.exp_neg]; fun_prop
          exact this.continuousOn) isCompact_Icc
      exact (h1.mono_set Ioc_subset_Icc_self).congr_fun (fun u _ => by simp [div_eq_mul_inv])
        measurableSet_Ioc
    have hnn : ∀ u ∈ Ioc (0 : ℝ) p.T, 0 ≤ c u.toNNReal ω / Bt p u := fun u hu =>
      div_nonneg (hcpos _ (coe_toNNReal_le p hu.2) ω).le (Bt_pos p u).le
    have hI : ENNReal.ofReal (∫ u in Ioc (0 : ℝ) p.T, c u.toNNReal ω / Bt p u) =
        ∫⁻ u in Ioc (0 : ℝ) p.T, ENNReal.ofReal (c u.toNNReal ω / Bt p u) :=
      ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hnn))
    have hHB : 0 ≤ H p.Tn ω / Bt p p.T := div_nonneg hHpos.le (Bt_pos p _).le
    have hZ0 : 0 ≤ Z p st Iθ p.Tn ω := (Z_pos p st Iθ _ ω).le
    simp only [N]
    rw [ENNReal.ofReal_add hHB (setIntegral_nonneg measurableSet_Ioc hnn), mul_add, hI,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hZ0]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    rw [ENNReal.ofReal_mul hZ0]
  rw [← lintegral_congr_ae hdec]
  have h2 : ∫⁻ ω, ENNReal.ofReal (N ω) ∂(Pt p st Iθ) =
      ∫⁻ ω, ENNReal.ofReal (Z p st Iθ p.Tn ω) * ENNReal.ofReal (N ω) ∂st.P := by
    unfold Pt
    exact lintegral_withDensity_eq_lintegral_mul₀'
      (measurable_Z p st Iθ hIto p.Tn).ennreal_ofReal.aemeasurable
      hNint.aemeasurable.ennreal_ofReal
  rw [← h2]
  have hNnn : 0 ≤ᵐ[Pt p st Iθ] N := by
    refine hac.ae_le ?_
    filter_upwards [hHT] with ω hHpos
    have hnn : ∀ u ∈ Ioc (0 : ℝ) p.T, 0 ≤ c u.toNNReal ω / Bt p u := fun u hu =>
      div_nonneg (hcpos _ (coe_toNNReal_le p hu.2) ω).le (Bt_pos p u).le
    exact add_nonneg (div_nonneg hHpos.le (Bt_pos p _).le)
      (setIntegral_nonneg measurableSet_Ioc hnn)
  rw [← ofReal_integral_eq_lintegral_ofReal hNint hNnn]

lemma cons_swap (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (c : ℝ≥0 → Ω → ℝ)
    (hcm : Measurable (fun z : ℝ≥0 × Ω => c (min z.1 p.Tn) z.2))
    (hcad : ∀ t : ℝ≥0, (t : ℝ) ≤ p.T → Measurable[FS p st t] (c t))
    (hcpos : ∀ t : ℝ≥0, (t : ℝ) ≤ p.T → ∀ ω, 0 < c t ω)
    (hfin : ∫⁻ ω, (∫⁻ u in Ioc (0 : ℝ) p.T,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c u.toNNReal ω / Bt p u))) ∂st.P < ⊤) :
    ∫⁻ ω, (∫⁻ u in Ioc (0 : ℝ) p.T,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c u.toNNReal ω / Bt p u))) ∂st.P =
    ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) p.T,
      ENNReal.ofReal (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) ∂st.P := by
  have hP : IsProbabilityMeasure st.P := hst.1
  have hcmm := measurable_cm p c hcm
  have hzmm := measurable_zm p st Iθ Zv hZv
  have hZm := measurable_Z p st Iθ hIto p.Tn
  have hBm : Measurable (fun u : ℝ => Bt p u) := by unfold Bt; fun_prop
  have step1 : ∀ ω, ∫⁻ u in Ioc (0 : ℝ) p.T,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c u.toNNReal ω / Bt p u)) =
      ∫⁻ u in Ioc (0 : ℝ) p.T,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c (min u.toNNReal p.Tn) ω / Bt p u)) := fun ω =>
    setLIntegral_congr_fun measurableSet_Ioc (fun u hu => by
      rw [min_eq_left (toNNReal_le_Tn p hu.2)])
  simp_rw [step1] at hfin ⊢
  have hF : Measurable (Function.uncurry fun (ω : Ω) (u : ℝ) =>
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c (min u.toNNReal p.Tn) ω / Bt p u))) := by
    have h1 : Measurable (fun z : Ω × ℝ => c (min z.2.toNNReal p.Tn) z.1) :=
      hcmm.comp measurable_swap
    have h2 : Measurable (fun z : Ω × ℝ => Bt p z.2) := hBm.comp measurable_snd
    have h3 : Measurable (fun z : Ω × ℝ => Z p st Iθ p.Tn z.1) := hZm.comp measurable_fst
    exact (h3.mul (h1.div h2)).ennreal_ofReal
  rw [lintegral_lintegral_swap hF.aemeasurable] at hfin ⊢
  have hG : Measurable (fun u : ℝ => ∫⁻ ω,
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (c (min u.toNNReal p.Tn) ω / Bt p u)) ∂st.P) := by
    have : Measurable (fun z : ℝ × Ω =>
        ENNReal.ofReal (Z p st Iθ p.Tn z.2 * (c (min z.1.toNNReal p.Tn) z.2 / Bt p z.1))) :=
      ((hZm.comp measurable_snd).mul (hcmm.div (hBm.comp measurable_fst))).ennreal_ofReal
    exact this.lintegral_prod_right'
  have step3 : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) p.T)),
      ∫⁻ ω, ENNReal.ofReal (Z p st Iθ p.Tn ω * (c (min u.toNNReal p.Tn) ω / Bt p u)) ∂st.P =
      ∫⁻ ω, ENNReal.ofReal (Zv (min u.toNNReal p.Tn) ω *
        (c (min u.toNNReal p.Tn) ω / Bt p u)) ∂st.P := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_lt_top hG hfin.ne] with u hu hlt
    have hmin : min u.toNNReal p.Tn = u.toNNReal := min_eq_left (toNNReal_le_Tn p hu.2)
    rw [hmin] at hlt ⊢
    have hle : ((u.toNNReal : ℝ≥0) : ℝ) ≤ p.T := coe_toNNReal_le p hu.2
    exact lintegral_com p st Iθ Zv hst hIto h21 hZv u.toNNReal hle
      (fun ω => c u.toNNReal ω / Bt p u) ((hcad _ hle).div_const _)
      (Eventually.of_forall fun ω => div_nonneg (hcpos _ hle ω).le (Bt_pos p u).le) hlt
  rw [lintegral_congr_ae step3]
  have hF2 : Measurable (Function.uncurry fun (ω : Ω) (u : ℝ) =>
      ENNReal.ofReal (Zv (min u.toNNReal p.Tn) ω * (c (min u.toNNReal p.Tn) ω / Bt p u))) := by
    have h1 : Measurable (fun z : Ω × ℝ => c (min z.2.toNNReal p.Tn) z.1) :=
      hcmm.comp measurable_swap
    have h2 : Measurable (fun z : Ω × ℝ => Bt p z.2) := hBm.comp measurable_snd
    have h3 : Measurable (fun z : Ω × ℝ => Zv (min z.2.toNNReal p.Tn) z.1) :=
      hzmm.comp measurable_swap
    exact (h3.mul (h1.div h2)).ennreal_ofReal
  rw [← lintegral_lintegral_swap hF2.aemeasurable]
  refine lintegral_congr fun ω => ?_
  rw [setLIntegral_congr Ioc_ae_eq_Icc]
  refine setLIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
  rw [min_eq_left (toNNReal_le_Tn p hu.2)]


lemma static_budget_gen (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (x : ℝ) (q : Plan Ω) (hq : q ∈ Bclass p st Iθ U1 U2 x) :
    ∫⁻ ω, ENNReal.ofReal (Zv p.Tn ω * (q.H p.Tn ω / Bt p p.T)) ∂st.P +
      ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) p.T,
        ENNReal.ofReal (Zv s.toNNReal ω * (q.c s.toNNReal ω / Bt p s))) ∂st.P
      = ENNReal.ofReal (∫ ω, (q.H p.Tn ω / Bt p p.T +
        ∫ u in Ioc (0 : ℝ) p.T, q.c u.toNNReal ω / Bt p u) ∂(Pt p st Iθ)) := by
  have hb := budget_Pt_gen p st Iθ U1 U2 hst hIto h21 x q hq
  obtain ⟨-, ⟨hcm, hcad, hcpos, -⟩, hHad, -, -, -, hHT, -, -⟩ := hq
  have hTle : ((p.Tn : ℝ≥0) : ℝ) ≤ p.T := le_of_eq (coe_Tn p)
  have hHm : Measurable[FS p st p.Tn] (fun ω => q.H p.Tn ω / Bt p p.T) :=
    (hHad p.Tn hTle).div_const _
  have hm1 : Measurable (fun ω =>
      ENNReal.ofReal (Z p st Iθ p.Tn ω * (q.H p.Tn ω / Bt p p.T))) :=
    ((measurable_Z p st Iθ hIto p.Tn).mul (hHm.mono ((FS p st).le _) le_rfl)).ennreal_ofReal
  rw [lintegral_add_left hm1] at hb
  have hlt1 := lt_of_le_of_lt (le_add_right le_rfl) (hb ▸ ENNReal.ofReal_lt_top)
  have hlt2 := lt_of_le_of_lt (le_add_left le_rfl) (hb ▸ ENNReal.ofReal_lt_top)
  rw [lintegral_com p st Iθ Zv hst hIto h21 hZv p.Tn hTle _ hHm
    (by filter_upwards [hHT] with ω hω; exact div_nonneg hω.le (Bt_pos p _).le) hlt1] at hb
  rw [cons_swap p st Iθ Zv hst hIto h21 hZv q.c hcm hcad hcpos hlt2] at hb
  exact hb

lemma ell_conv (p : Params) (st : Setting Ω) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ)
    (ω : Ω) :
    ∫ s in Icc (0 : ℝ) p.T, Real.exp (-p.β * s) * (1 - Rind τ s.toNNReal ω) =
      ∫ s in Icc (0 : ℝ) (τ ω), Real.exp (-p.β * s) := by
  have h1 : ∀ s ∈ Icc (0 : ℝ) p.T, Real.exp (-p.β * s) * (1 - Rind τ s.toNNReal ω) =
      (Iio (τ ω : ℝ)).indicator (fun s => Real.exp (-p.β * s)) s := by
    intro s hs
    unfold Rind
    by_cases h : τ ω ≤ s.toNNReal
    · have : ¬ s < τ ω := by
        rw [not_lt]; rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1] at h; exact h
      simp [h, this]
    · have : s < τ ω := by
        rw [not_le, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1] at h; exact h
      simp [h, this]
  rw [setIntegral_congr_fun measurableSet_Icc h1, setIntegral_indicator measurableSet_Iio]
  have : Icc (0 : ℝ) p.T ∩ Iio (τ ω : ℝ) = Ico (0 : ℝ) (τ ω) := by
    ext s; simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨⟨h0, -⟩, h2⟩; exact ⟨h0, h2⟩
    · rintro ⟨h0, h2⟩; exact ⟨⟨h0, h2.le.trans (tau_le_T p st τ hτ ω)⟩, h2⟩
  rw [this]
  exact setIntegral_congr_set Ico_ae_eq_Icc

lemma Pt_integral (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ)
    (hIto : IsItoIntegral p st (θ p st) Iθ) (g : Ω → ℝ) :
    ∫ ω, g ω ∂(Pt p st Iθ) = ∫ ω, Z p st Iθ p.Tn ω * g ω ∂st.P := by
  unfold Pt
  have hae : AEMeasurable (fun ω => (Z p st Iθ p.Tn ω).toNNReal) st.P :=
    (measurable_real_toNNReal.comp (measurable_Z p st Iθ hIto p.Tn)).aemeasurable
  have := integral_withDensity_eq_integral_smul₀ hae g
  simp only [ENNReal.ofReal] at *
  rw [this]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (Z_pos p st Iθ _ ω).le]

lemma ell_int (p : Params) (st : Setting Ω) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ)
    (ω : Ω) : IntegrableOn (fun s => Real.exp (-p.β * s) * (1 - Rind τ s.toNNReal ω))
      (Icc (0 : ℝ) p.T) := by
  have h0 : IntegrableOn (fun s : ℝ => Real.exp (-p.β * s)) (Icc (0 : ℝ) p.T) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-p.β * s))).integrableOn_Icc
  refine (h0.indicator (measurableSet_Iio (a := (τ ω : ℝ)))).congr_fun (fun s hs => ?_)
    measurableSet_Icc
  unfold Rind
  by_cases h : τ ω ≤ s.toNNReal
  · have : ¬ s < τ ω := by
      rw [not_lt]; rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1] at h; exact h
    simp [h, this]
  · have : s < τ ω := by
      rw [not_le, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1] at h; exact h
    simp [h, this]

end RetirePIwk

open RetirePI13 RetirePIveqr RetirePIfr RetirePIfw RetirePIwk in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (hdual : DualIntegrable p st Zv U1 U2) (x y : ℝ) (hy : 0 < y)
    (q : Plan Ω) (hq : q ∈ Bclass p st Iθ U1 U2 x) :
    J p st U1 U2 q ≤ L0 p st Zv U1 U2 y + y * (x - b p 0) := by
  have hP : IsProbabilityMeasure st.P := hst.1
  have hPt : IsProbabilityMeasure (Pt p st Iθ) := Pt_prob p st Iθ hst hIto h21
  have hsb := static_budget_gen p st Iθ Zv U1 U2 hst hIto h21 hZv x q hq
  obtain ⟨hNi, hNle⟩ := budget_gen p st Iθ U1 U2 hst hIto h21 x q hq
  obtain ⟨c, H, τ⟩ := q
  obtain ⟨hτ, ⟨hcm, hcad, hcpos, hcint⟩, hHad, hH0, hHb, -, hHT, hrr, hU2i⟩ := hq
  have hTle : ((p.Tn : ℝ≥0) : ℝ) ≤ p.T := le_of_eq (coe_Tn p)
  set NI := ∫ ω, (H p.Tn ω / Bt p p.T + ∫ u in Ioc (0 : ℝ) p.T, c u.toNNReal ω / Bt p u)
    ∂(Pt p st Iθ) with hNIdef
  have hNInn : 0 ≤ NI := by
    have hac : Pt p st Iθ ≪ st.P := withDensity_absolutelyContinuous _ _
    refine integral_nonneg_of_ae (hac.ae_le ?_)
    filter_upwards [hHT] with ω hω
    refine add_nonneg (div_nonneg hω.le (Bt_pos p _).le) (setIntegral_nonneg measurableSet_Ioc
      fun u hu => div_nonneg (hcpos _ (coe_toNNReal_le p hu.2) ω).le (Bt_pos p u).le)
  have hcmm := measurable_cm p c hcm
  have hzmm := measurable_zm p st Iθ Zv hZv
  have hBm : Measurable (fun u : ℝ => Bt p u) := by unfold Bt; fun_prop
  -- the measurable version of the integrand `Zv_s c_s / B_s`
  have hFm : Measurable (fun q : Ω × ℝ =>
      Zv (min q.2.toNNReal p.Tn) q.1 * (c (min q.2.toNNReal p.Tn) q.1 / Bt p q.2)) :=
    (hzmm.comp measurable_swap).mul ((hcmm.comp measurable_swap).div (hBm.comp measurable_snd))
  have hcongr : ∀ ω, ∀ s ∈ Icc (0 : ℝ) p.T,
      Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s) =
      Zv (min s.toNNReal p.Tn) ω * (c (min s.toNNReal p.Tn) ω / Bt p s) := by
    intro ω s hs
    rw [min_eq_left (toNNReal_le_Tn p hs.2)]
  have hfnn : ∀ ω, ∀ s ∈ Icc (0 : ℝ) p.T, 0 ≤ Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s) :=
    fun ω s hs => mul_nonneg (hZv.2.2.2 _ ω).le
      (div_nonneg (hcpos _ (coe_toNNReal_le p hs.2) ω).le (Bt_pos p s).le)
  have hT2 : ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) p.T,
      ENNReal.ofReal (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) ∂st.P < ⊤ :=
    lt_of_le_of_lt (le_add_left le_rfl) (hsb ▸ ENNReal.ofReal_lt_top)
  have hinnerm : Measurable (fun ω => ∫⁻ s in Icc (0 : ℝ) p.T,
      ENNReal.ofReal (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) := by
    have : (fun ω => ∫⁻ s in Icc (0 : ℝ) p.T,
        ENNReal.ofReal (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) =
        fun ω => ∫⁻ s in Icc (0 : ℝ) p.T, ENNReal.ofReal
          (Zv (min s.toNNReal p.Tn) ω * (c (min s.toNNReal p.Tn) ω / Bt p s)) := by
      funext ω
      exact setLIntegral_congr_fun measurableSet_Icc (fun s hs => by rw [hcongr ω s hs])
    rw [this]
    exact hFm.ennreal_ofReal.lintegral_prod_right'
  have hfint : ∀ᵐ ω ∂st.P, IntegrableOn
      (fun s => Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s)) (Icc (0 : ℝ) p.T) := by
    filter_upwards [ae_lt_top hinnerm hT2.ne] with ω hω
    have hae : AEStronglyMeasurable (fun s => Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))
        (volume.restrict (Icc (0 : ℝ) p.T)) := by
      have hm : Measurable (fun s : ℝ =>
          Zv (min s.toNNReal p.Tn) ω * (c (min s.toNNReal p.Tn) ω / Bt p s)) :=
        hFm.comp (measurable_const.prodMk measurable_id)
      refine hm.aestronglyMeasurable.congr ?_
      exact (ae_restrict_iff' measurableSet_Icc).2
        (Eventually.of_forall fun s hs => (hcongr ω s hs).symm)
    refine ⟨hae, (hasFiniteIntegral_iff_ofReal ?_).2 hω⟩
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall (hfnn ω))
  -- the budget term `G`
  set G : Ω → ℝ := fun ω =>
    (∫ s in Icc (0 : ℝ) p.T, y * (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) +
      y * (Zv p.Tn ω * (H p.Tn ω / Bt p p.T)) with hGdef
  have hGnn : 0 ≤ᵐ[st.P] G := by
    filter_upwards [hHT] with ω hω
    refine add_nonneg (setIntegral_nonneg measurableSet_Icc fun s hs =>
      mul_nonneg hy.le (hfnn ω s hs)) ?_
    exact mul_nonneg hy.le (mul_nonneg (hZv.2.2.2 _ ω).le (div_nonneg hω.le (Bt_pos p _).le))
  have hZTm : Measurable (fun ω => Zv p.Tn ω * (H p.Tn ω / Bt p p.T)) :=
    ((hZv.2.1 _).mono ((FS p st).le _) le_rfl).mul
      (((hHad p.Tn hTle).mono ((FS p st).le _) le_rfl).div_const _)
  have hGm : AEStronglyMeasurable G st.P := by
    have hK : (fun ω => ∫ s in Icc (0 : ℝ) p.T,
        y * (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) =
        fun ω => ∫ s in Icc (0 : ℝ) p.T,
          y * (Zv (min s.toNNReal p.Tn) ω * (c (min s.toNNReal p.Tn) ω / Bt p s)) := by
      funext ω
      exact setIntegral_congr_fun measurableSet_Icc (fun s hs => by rw [hcongr ω s hs])
    have h1 : StronglyMeasurable (fun ω => ∫ s in Icc (0 : ℝ) p.T,
        y * (Zv (min s.toNNReal p.Tn) ω * (c (min s.toNNReal p.Tn) ω / Bt p s))) :=
      (measurable_const.mul hFm).stronglyMeasurable.integral_prod_right'
    have hG2 : G = fun ω => (∫ s in Icc (0 : ℝ) p.T,
          y * (Zv (min s.toNNReal p.Tn) ω * (c (min s.toNNReal p.Tn) ω / Bt p s))) +
        y * (Zv p.Tn ω * (H p.Tn ω / Bt p p.T)) := by
      funext ω
      simp only [hGdef]
      rw [congrFun hK ω]
    rw [hG2]
    exact (h1.measurable.add (hZTm.const_mul y)).aestronglyMeasurable
  have hGlint : ∫⁻ ω, ENNReal.ofReal (G ω) ∂st.P ≤ ENNReal.ofReal (y * NI) := by
    calc ∫⁻ ω, ENNReal.ofReal (G ω) ∂st.P
        ≤ ∫⁻ ω, (ENNReal.ofReal y * ∫⁻ s in Icc (0 : ℝ) p.T,
            ENNReal.ofReal (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) +
            ENNReal.ofReal y * ENNReal.ofReal (Zv p.Tn ω * (H p.Tn ω / Bt p p.T)) ∂st.P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hfint] with ω hω
          refine (ENNReal.ofReal_add_le).trans (le_of_eq ?_)
          rw [integral_const_mul, ENNReal.ofReal_mul hy.le, ENNReal.ofReal_mul hy.le,
            ofReal_integral_eq_lintegral_ofReal hω
              ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall (hfnn ω)))]
      _ = ENNReal.ofReal y * (∫⁻ ω, ENNReal.ofReal (Zv p.Tn ω * (H p.Tn ω / Bt p p.T)) ∂st.P +
            ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) p.T,
              ENNReal.ofReal (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) ∂st.P) := by
          rw [lintegral_add_right _ (hZTm.ennreal_ofReal.const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_add, add_comm]
      _ = ENNReal.ofReal y * ENNReal.ofReal NI := by rw [hsb]
      _ = ENNReal.ofReal (y * NI) := (ENNReal.ofReal_mul hy.le).symm
  have hGint : Integrable G st.P :=
    ⟨hGm, (hasFiniteIntegral_iff_ofReal hGnn).2 (lt_of_le_of_lt hGlint ENNReal.ofReal_lt_top)⟩
  have hGle : ∫ ω, G ω ∂st.P ≤ y * NI := by
    rw [integral_eq_lintegral_of_nonneg_ae hGnn hGm]
    calc (∫⁻ ω, ENNReal.ofReal (G ω) ∂st.P).toReal ≤ (ENNReal.ofReal (y * NI)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hGlint
      _ = y * NI := ENNReal.toReal_ofReal (mul_nonneg hy.le hNInn)
  -- pointwise comparison
  have hpt : ∀ᵐ ω ∂st.P,
      (∫ t in Icc (0 : ℝ) p.T, runReward p U1 c τ t ω) +
        Real.exp (-p.β * p.T) * U2 p.T (H p.Tn ω) ≤
      ((∫ s in Icc (0 : ℝ) p.T, Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) +
        Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω)) + G ω -
        p.ℓ * ∫ s in Icc (0 : ℝ) (τ ω), Real.exp (-p.β * s) := by
    filter_upwards [hrr.prod_left_ae, (hdual y hy).1.prod_left_ae, hfint, hHT]
      with ω h1 h2 h3 h4
    have h3' := h3.const_mul y
    have hli := (ell_int p st τ hτ ω).const_mul p.ℓ
    have hA : (∫ t in Icc (0 : ℝ) p.T, runReward p U1 c τ t ω) ≤
        ∫ s in Icc (0 : ℝ) p.T, ((Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω) +
          y * (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) -
          p.ℓ * (Real.exp (-p.β * s) * (1 - Rind τ s.toNNReal ω))) := by
      refine setIntegral_mono_on h1 ((h2.add h3').sub hli) measurableSet_Icc (fun s hs => ?_)
      have hcs := hcpos _ (coe_toNNReal_le p hs.2) ω
      have hyd : 0 < ydual p Zv y s ω := by
        unfold ydual
        exact div_pos (mul_pos (mul_pos hy (Real.exp_pos _)) (hZv.2.2.2 _ ω)) (Bt_pos p s)
      have hle := U_le p U1 hU1 s hs (ydual p Zv y s ω) hyd _ hcs
      have hkey : Real.exp (-p.β * s) * (ydual p Zv y s ω * c s.toNNReal ω) =
          y * (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s)) := by
        unfold ydual
        have hB := (Bt_pos p s).ne'
        rw [show -p.β * s = -(p.β * s) by ring, Real.exp_neg]
        field_simp
      have hR : runReward p U1 c τ s ω =
          Real.exp (-p.β * s) * U1 s (c s.toNNReal ω) -
            p.ℓ * (Real.exp (-p.β * s) * (1 - Rind τ s.toNNReal ω)) := by
        simp only [runReward]; ring
      rw [hR, ← hkey]
      have := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-p.β * s)).le
      linarith
    have h23 : IntegrableOn (fun s => Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω) +
        y * (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) (Icc (0 : ℝ) p.T) := h2.add h3'
    rw [integral_sub h23 hli, integral_add h2 h3', integral_const_mul p.ℓ,
      ell_conv p st τ hτ ω] at hA
    have hT : p.T ∈ Icc 0 p.T := ⟨p.T_pos.le, le_rfl⟩
    have hydT : 0 < ydual p Zv y p.T ω := by
      unfold ydual
      exact div_pos (mul_pos (mul_pos hy (Real.exp_pos _)) (hZv.2.2.2 _ ω)) (Bt_pos p _)
    have hle2 := U_le p U2 hU2 p.T hT (ydual p Zv y p.T ω) hydT _ h4
    have hkey2 : Real.exp (-p.β * p.T) * (ydual p Zv y p.T ω * H p.Tn ω) =
        y * (Zv p.Tn ω * (H p.Tn ω / Bt p p.T)) := by
      unfold ydual
      have hB := (Bt_pos p p.T).ne'
      rw [show -p.β * p.T = -(p.β * p.T) by ring, Real.exp_neg]
      field_simp
      rfl
    have hterm : Real.exp (-p.β * p.T) * U2 p.T (H p.Tn ω) ≤
        Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω) +
          y * (Zv p.Tn ω * (H p.Tn ω / Bt p p.T)) := by
      rw [← hkey2, ← mul_add]
      exact mul_le_mul_of_nonneg_left hle2 (Real.exp_pos _).le
    simp only [hGdef]
    linarith
  -- integrate
  have hLint : Integrable (fun ω => (∫ t in Icc (0 : ℝ) p.T, runReward p U1 c τ t ω) +
      Real.exp (-p.β * p.T) * U2 p.T (H p.Tn ω)) st.P :=
    hrr.integral_prod_right.add (hU2i.const_mul _)
  have hRint : Integrable (fun ω =>
      (∫ s in Icc (0 : ℝ) p.T, Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) +
        Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω)) st.P :=
    (hdual y hy).1.integral_prod_right.add ((hdual y hy).2.const_mul _)
  set M := (volume.restrict (Icc (0 : ℝ) p.T)).prod st.P
  have hmem : ∀ᵐ z ∂M, z.1 ∈ Icc (0 : ℝ) p.T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hE : Integrable (fun z : ℝ × Ω => Real.exp (-p.β * z.1)) M := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hmem] with z hz
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.2 (by nlinarith [p.β_pos, hz.1])
  have hElow := int_lower p st hst τ hτ (fun s _ => Real.exp (-p.β * s)) hE
  have hJ : J p st U1 U2 ⟨c, H, τ⟩ ≤ L1 p st Zv U1 U2 y + y * NI -
      p.ℓ * ∫ ω, (∫ s in Icc (0 : ℝ) (τ ω), Real.exp (-p.β * s)) ∂st.P := by
    unfold J Jobj L1
    calc _ ≤ ∫ ω, (((∫ s in Icc (0 : ℝ) p.T,
            Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) +
            Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω)) + G ω -
            p.ℓ * ∫ s in Icc (0 : ℝ) (τ ω), Real.exp (-p.β * s)) ∂st.P :=
          integral_mono_ae hLint ((hRint.add hGint).sub (hElow.const_mul p.ℓ)) hpt
      _ = _ + ∫ ω, G ω ∂st.P - p.ℓ * ∫ ω, (∫ s in Icc (0 : ℝ) (τ ω),
            Real.exp (-p.β * s)) ∂st.P := by
          have hRG : Integrable (fun ω =>
              ((∫ s in Icc (0 : ℝ) p.T, Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) +
              Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω)) + G ω) st.P :=
            hRint.add hGint
          rw [integral_sub hRG (hElow.const_mul p.ℓ), integral_add hRint hGint,
            integral_const_mul]
      _ ≤ _ := by nlinarith [hGle]
  -- the dual side
  have hdec := stopObj_decomp p st Iθ Zv U1 U2 hst hIto h21 hZv hdual y hy τ hτ
  have hOS := optional_sampling_Zv p st Iθ Zv hst hIto h21 hZv τ hτ _ (continuous_bB p)
  have hPtb : ∫ ω, b p (τ ω) / Bt p (τ ω) ∂(Pt p st Iθ) =
      ∫ ω, Zv (τ ω) ω * (b p (τ ω) / Bt p (τ ω)) ∂st.P := by
    rw [Pt_integral p st Iθ hIto]; exact hOS.2
  have hbdd : BddAbove {v | ∃ τ' : Ω → ℝ≥0, ∃ hτ' : IsRetirementTime p st τ',
      v = stopObj p st Zv U1 U2 y τ' hτ'} := by
    refine ⟨L1 p st Zv U1 U2 y, ?_⟩
    rintro v ⟨τ', hτ', rfl⟩
    rw [stopObj_decomp p st Iθ Zv U1 U2 hst hIto h21 hZv hdual y hy τ' hτ']
    have h1 : 0 ≤ ∫ ω, (∫ s in Icc (0 : ℝ) (τ' ω), Real.exp (-p.β * s)) ∂st.P :=
      integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun s _ => (Real.exp_pos _).le
    have h2 : ∫ ω, Zv (τ' ω) ω * (b p (τ' ω) / Bt p (τ' ω)) ∂st.P ≤ 0 :=
      integral_nonpos fun ω => mul_nonpos_of_nonneg_of_nonpos (hZv.2.2.2 _ ω).le (bB_nonpos p _)
    nlinarith [p.ℓ_pos]
  have hL0 : stopObj p st Zv U1 U2 y τ hτ ≤ L0 p st Zv U1 U2 y :=
    le_csSup hbdd ⟨τ, hτ, rfl⟩
  have hNle' : NI ≤ x - b p 0 + ∫ ω, Zv (τ ω) ω * (b p (τ ω) / Bt p (τ ω)) ∂st.P := by
    rw [← hPtb]; exact hNle
  nlinarith [hJ, hdec, hL0, hNle', mul_le_mul_of_nonneg_left hNle' hy.le]
