-- Prove2me | solution 1 for RetirePartialInfo.Duality.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:57:00.409199+00:00
-- url     : https://prove2.me/submissions/130144b7-1f4b-427d-8138-5493d879377b

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal
import Definitions.Def_RetirePartialInfo_Duality_Dual
import Theorems.Thm_RetirePartialInfo_Duality_eq_11

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

open RetirePI13 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (hdual : DualIntegrable p st Zv U1 U2) (x y : ℝ) (hy : 0 < y)
    (q : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hq : q ∈ B1class p st Iθ U1 U2 x) :
    J1 p st U1 U2 q ≤ L1 p st Zv U1 U2 y + y * x := by
  obtain ⟨c, H⟩ := q
  have hq' : (⟨c, H, fun _ => 0⟩ : Plan Ω) ∈ Bclass p st Iθ U1 U2 x := hq
  have hP : IsProbabilityMeasure st.P := hst.1
  have hsb := static_budget p st Iθ Zv U1 U2 hst hIto h21 hZv x c H hq'
  obtain ⟨-, ⟨hcm, hcad, hcpos, hcint⟩, hHad, hH0, hHb, -, hHT, hrr, hU2i⟩ := hq'
  have hTle : ((p.Tn : ℝ≥0) : ℝ) ≤ p.T := le_of_eq (coe_Tn p)
  have hx : 0 ≤ x := by
    have := (hHb 0 (by simpa using p.T_pos.le)).and hH0
    obtain ⟨ω, h1, h2⟩ := this.exists
    simp [Rind] at h1
    linarith
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
    lt_of_le_of_lt (le_add_left le_rfl) (lt_of_le_of_lt hsb ENNReal.ofReal_lt_top)
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
  have hGlint : ∫⁻ ω, ENNReal.ofReal (G ω) ∂st.P ≤ ENNReal.ofReal (y * x) := by
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
      _ ≤ ENNReal.ofReal y * ENNReal.ofReal x := mul_le_mul_right hsb _
      _ = ENNReal.ofReal (y * x) := (ENNReal.ofReal_mul hy.le).symm
  have hGint : Integrable G st.P :=
    ⟨hGm, (hasFiniteIntegral_iff_ofReal hGnn).2 (lt_of_le_of_lt hGlint ENNReal.ofReal_lt_top)⟩
  have hGle : ∫ ω, G ω ∂st.P ≤ y * x := by
    rw [integral_eq_lintegral_of_nonneg_ae hGnn hGm]
    calc (∫⁻ ω, ENNReal.ofReal (G ω) ∂st.P).toReal ≤ (ENNReal.ofReal (y * x)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hGlint
      _ = y * x := ENNReal.toReal_ofReal (mul_nonneg hy.le hx)
  -- pointwise comparison
  have hpt : ∀ᵐ ω ∂st.P,
      (∫ t in Icc (0 : ℝ) p.T, runReward p U1 c (fun _ => 0) t ω) +
        Real.exp (-p.β * p.T) * U2 p.T (H p.Tn ω) ≤
      ((∫ s in Icc (0 : ℝ) p.T, Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) +
        Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω)) + G ω := by
    filter_upwards [hrr.prod_left_ae, (hdual y hy).1.prod_left_ae, hfint, hHT]
      with ω h1 h2 h3 h4
    have h3' := h3.const_mul y
    have hA : (∫ t in Icc (0 : ℝ) p.T, runReward p U1 c (fun _ => 0) t ω) ≤
        ∫ s in Icc (0 : ℝ) p.T, (Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω) +
          y * (Zv s.toNNReal ω * (c s.toNNReal ω / Bt p s))) := by
      refine setIntegral_mono_on h1 (h2.add h3') measurableSet_Icc (fun s hs => ?_)
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
      have hR : runReward p U1 c (fun _ => 0) s ω =
          Real.exp (-p.β * s) * U1 s (c s.toNNReal ω) := by
        simp [runReward, Rind]
      rw [hR, ← hkey, ← mul_add]
      exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    rw [integral_add h2 h3'] at hA
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
  have hLint : Integrable (fun ω => (∫ t in Icc (0 : ℝ) p.T, runReward p U1 c (fun _ => 0) t ω) +
      Real.exp (-p.β * p.T) * U2 p.T (H p.Tn ω)) st.P :=
    hrr.integral_prod_right.add (hU2i.const_mul _)
  have hRint : Integrable (fun ω =>
      (∫ s in Icc (0 : ℝ) p.T, Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) +
        Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω)) st.P :=
    (hdual y hy).1.integral_prod_right.add ((hdual y hy).2.const_mul _)
  unfold J1 L1 Jobj
  calc _ ≤ ∫ ω, (((∫ s in Icc (0 : ℝ) p.T,
          Real.exp (-p.β * s) * Utilde U1 s (ydual p Zv y s ω)) +
          Real.exp (-p.β * p.T) * Utilde U2 p.T (ydual p Zv y p.T ω)) + G ω) ∂st.P :=
        integral_mono_ae hLint (hRint.add hGint) hpt
    _ = _ + ∫ ω, G ω ∂st.P := integral_add hRint hGint
    _ ≤ _ := by linarith
