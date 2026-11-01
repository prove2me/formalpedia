-- Prove2me | solution 1 for RiskPostpone.Threshold.proposition_4_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T10:45:32.44238+00:00
-- url     : https://prove2.me/submissions/cf6f86c2-47e7-4a0e-a5dd-e4f5f69014f0

import Mathlib
import Definitions.Def_RiskPostpone_Threshold_Setting

open MeasureTheory Set

namespace RPSolA
open RiskPostpone.Threshold

variable (M : Model)

lemma ae_mem (hM : M.YieldLaw) : ∀ᵐ ξ ∂M.ν, ξ ∈ Icc M.l M.u := by
  rw [ae_iff]
  exact hM.support

lemma ae_unit (hM : M.YieldLaw) : ∀ᵐ ξ ∂M.ν, 0 ≤ ξ ∧ ξ ≤ 1 := by
  filter_upwards [ae_mem M hM] with ξ hξ
  exact ⟨hM.l_nonneg.trans hξ.1, hξ.2.trans hM.u_le_one⟩

lemma int_id (hM : M.YieldLaw) : Integrable (fun ξ : ℝ => ξ) M.ν := by
  haveI := hM.prob
  refine Integrable.of_bound measurable_id.aestronglyMeasurable 1 ?_
  filter_upwards [ae_unit M hM] with ξ hξ
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hξ.1, hξ.2]

lemma quantile_spec (hM : M.YieldLaw) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    (M.ν (Iic (M.quantile η))).toReal = η := by
  haveI := hM.prob
  haveI := hM.noAtoms
  set T : Set ℝ := {y | ENNReal.ofReal η ≤ M.ν (Iic y)} with hT
  have hQ : M.quantile η = sInf T := rfl
  have hfull : M.ν (Icc M.l M.u) = 1 :=
    (prob_compl_eq_zero_iff measurableSet_Icc).1 hM.support
  have huT : M.u ∈ T := by
    show ENNReal.ofReal η ≤ M.ν (Iic M.u)
    calc ENNReal.ofReal η ≤ 1 := ENNReal.ofReal_le_one.2 h1
      _ = M.ν (Icc M.l M.u) := hfull.symm
      _ ≤ M.ν (Iic M.u) := measure_mono Icc_subset_Iic_self
  have hlow : ∀ y ∈ T, M.l ≤ y := by
    intro y hy
    by_contra hlt
    push_neg at hlt
    have hsub : Iic y ⊆ (Icc M.l M.u)ᶜ := by
      intro x hx hx'
      exact absurd (lt_of_le_of_lt (mem_Iic.1 hx) hlt) (not_lt.2 hx'.1)
    have h00 : M.ν (Iic y) = 0 := measure_mono_null hsub hM.support
    have : ENNReal.ofReal η ≤ 0 := by
      have := hy; simp only [hT, mem_setOf_eq] at this; rw [h00] at this; exact this
    have := ENNReal.ofReal_pos.2 h0
    exact absurd this (not_lt.2 (le_of_le_of_eq ‹_› rfl))
  have hne : T.Nonempty := ⟨M.u, huT⟩
  have hbdd : BddBelow T := ⟨M.l, hlow⟩
  set F := ProbabilityTheory.cdf M.ν with hF
  have hFeq : ∀ x, F x = (M.ν (Iic x)).toReal := fun x => by
    rw [hF, ProbabilityTheory.cdf_eq_real]; rfl
  have hTiff : ∀ y, y ∈ T ↔ η ≤ F y := by
    intro y
    rw [hFeq]
    simp only [hT, mem_setOf_eq]
    exact ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)
  set a := sInf T with ha
  -- lower bound: right continuity
  have hge : η ≤ F a := by
    have hc := (F.right_continuous a).mono (Ioi_subset_Ici_self (a := a))
    refine ge_of_tendsto hc ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨t, htT, hty⟩ := exists_lt_of_csInf_lt hne (show sInf T < y from hy)
    exact ((hTiff t).1 htT).trans (F.mono hty.le)
  have hle : F a ≤ η := by
    have hsing : M.ν {a} = 0 := measure_singleton a
    have hm : F.measure {a} = 0 := by
      rw [hF, ProbabilityTheory.measure_cdf]; exact hsing
    rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hm
    have hlim : Function.leftLim F a ≤ η := by
      refine le_of_tendsto (F.mono.tendsto_leftLim a) ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hyT : y ∉ T := fun hyT => absurd (csInf_le hbdd hyT) (not_le.2 hy)
      rw [hTiff] at hyT
      exact (not_le.1 hyT).le
    linarith
  rw [hQ, ← hFeq]
  exact le_antisymm hle hge

lemma quantile_mono (hM : M.YieldLaw) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    M.quantile x ≤ M.quantile y := by
  haveI := hM.prob
  have hfull : M.ν (Icc M.l M.u) = 1 :=
    (prob_compl_eq_zero_iff measurableSet_Icc).1 hM.support
  have huT : ENNReal.ofReal y ≤ M.ν (Iic M.u) :=
    calc ENNReal.ofReal y ≤ 1 := ENNReal.ofReal_le_one.2 hy
      _ = M.ν (Icc M.l M.u) := hfull.symm
      _ ≤ M.ν (Iic M.u) := measure_mono Icc_subset_Iic_self
  have hlow : ∀ z, ENNReal.ofReal x ≤ M.ν (Iic z) → M.l ≤ z := by
    intro z hz
    by_contra hlt
    push_neg at hlt
    have hsub : Iic z ⊆ (Icc M.l M.u)ᶜ := by
      intro t ht ht'
      exact absurd (lt_of_le_of_lt (mem_Iic.1 ht) hlt) (not_lt.2 ht'.1)
    have h00 : M.ν (Iic z) = 0 := measure_mono_null hsub hM.support
    rw [h00] at hz
    exact absurd (ENNReal.ofReal_pos.2 hx) (not_lt.2 hz)
  unfold Model.quantile MultistageStochastic.valueAtRisk
  apply csInf_le_csInf
  · exact ⟨M.l, fun z hz => hlow z hz⟩
  · exact ⟨M.u, huT⟩
  · intro z hz
    exact le_trans (ENNReal.ofReal_le_ofReal hxy) hz


noncomputable def brk (η : ℝ) (X : ℝ → ℝ) (v : ℝ) : ℝ :=
  v + (1 / η) * ∫ ξ, min (X ξ - v) 0 ∂M.ν

lemma int_min (hM : M.YieldLaw) (X : ℝ → ℝ) (hX : Integrable X M.ν) (v : ℝ) :
    Integrable (fun ξ => min (X ξ - v) 0) M.ν := by
  haveI := hM.prob
  exact (hX.sub (integrable_const v)).inf (integrable_const 0)

lemma int_aff (hM : M.YieldLaw) (α β : ℝ) : Integrable (fun ξ : ℝ => α * ξ - β) M.ν := by
  haveI := hM.prob
  exact ((int_id M hM).const_mul α).sub (integrable_const β)

lemma Icc_ae (hM : M.YieldLaw) (a : ℝ) : (Icc M.l a : Set ℝ) =ᵐ[M.ν] (Iic a : Set ℝ) := by
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [ae_mem M hM] with ξ hξ
  exact ⟨fun h => h.2, fun h => ⟨hξ.1, h⟩⟩

lemma tailMean_eq (hM : M.YieldLaw) (η : ℝ) :
    M.tailMean η = (1 / η) * ∫ ξ in Iic (M.quantile η), ξ ∂M.ν := by
  unfold Model.tailMean
  rw [setIntegral_congr_set (Icc_ae M hM _)]

lemma ind_int (hM : M.YieldLaw) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) (α w : ℝ) :
    ∫ ξ, (Iic (M.quantile η)).indicator (fun ξ => α * ξ - w) ξ ∂M.ν =
      α * ∫ ξ in Iic (M.quantile η), ξ ∂M.ν - w * η := by
  haveI := hM.prob
  rw [integral_indicator measurableSet_Iic, integral_sub ((int_id M hM).const_mul α).integrableOn
    (integrable_const w), integral_const_mul, setIntegral_const, smul_eq_mul]
  have := quantile_spec M hM h0 h1
  rw [Measure.real, this]
  ring

lemma brk_affine (hM : M.YieldLaw) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) {α : ℝ} (hα : 0 ≤ α)
    (β v : ℝ) : brk M η (fun ξ => α * ξ - β) v ≤ α * M.tailMean η - β := by
  haveI := hM.prob
  have key : ∫ ξ, min (α * ξ - β - v) 0 ∂M.ν ≤
      ∫ ξ, (Iic (M.quantile η)).indicator (fun ξ => α * ξ - (β + v)) ξ ∂M.ν := by
    apply integral_mono_ae (int_min M hM _ (int_aff M hM α β) v)
      ((int_aff M hM α (β + v)).indicator measurableSet_Iic)
    refine Filter.Eventually.of_forall (fun ξ => ?_)
    by_cases h : ξ ∈ Iic (M.quantile η)
    · rw [indicator_of_mem h]; exact (min_le_left _ _).trans (le_of_eq (by ring))
    · rw [indicator_of_notMem h]; exact min_le_right _ _
  rw [ind_int M hM h0 h1] at key
  show v + (1 / η) * ∫ ξ, min (α * ξ - β - v) 0 ∂M.ν ≤ _
  rw [tailMean_eq M hM]
  set I := ∫ ξ in Iic (M.quantile η), ξ ∂M.ν
  have h2 := mul_le_mul_of_nonneg_left key (show (0:ℝ) ≤ 1 / η by positivity)
  have e : (1 / η) * (α * I - (β + v) * η) = α * ((1 / η) * I) - β - v := by
    field_simp; ring
  linarith

lemma brk_affine_eq (hM : M.YieldLaw) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) {α : ℝ} (hα : 0 ≤ α)
    (β : ℝ) : brk M η (fun ξ => α * ξ - β) (α * M.quantile η - β) = α * M.tailMean η - β := by
  haveI := hM.prob
  have key : ∫ ξ, min (α * ξ - β - (α * M.quantile η - β)) 0 ∂M.ν =
      ∫ ξ, (Iic (M.quantile η)).indicator
        (fun ξ => α * ξ - (β + (α * M.quantile η - β))) ξ ∂M.ν := by
    congr 1; funext ξ
    by_cases h : ξ ∈ Iic (M.quantile η)
    · rw [indicator_of_mem h]
      have : α * ξ ≤ α * M.quantile η := mul_le_mul_of_nonneg_left (mem_Iic.1 h) hα
      rw [min_eq_left (by linarith)]; ring
    · rw [indicator_of_notMem h]
      have : α * M.quantile η ≤ α * ξ :=
        mul_le_mul_of_nonneg_left (le_of_lt (not_le.1 h)) hα
      rw [min_eq_right (by linarith)]
  rw [ind_int M hM h0 h1] at key
  show _ + (1 / η) * ∫ ξ, min (α * ξ - β - _) 0 ∂M.ν = _
  rw [key, tailMean_eq M hM]
  field_simp; ring

lemma brk_mono_X (hM : M.YieldLaw) {η : ℝ} (h0 : 0 < η) {X Y : ℝ → ℝ} (hX : Integrable X M.ν)
    (hY : Integrable Y M.ν) (hXY : X ≤ᵐ[M.ν] Y) (v : ℝ) : brk M η X v ≤ brk M η Y v := by
  unfold brk
  have := integral_mono_ae (int_min M hM X hX v) (int_min M hM Y hY v)
    (hXY.mono fun ξ h => min_le_min (sub_le_sub_right h v) le_rfl)
  have h2 := mul_le_mul_of_nonneg_left this (show (0:ℝ) ≤ 1 / η by positivity)
  linarith

lemma brk_le_int (hM : M.YieldLaw) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) {X : ℝ → ℝ}
    (hX : Integrable X M.ν) (v : ℝ) : brk M η X v ≤ ∫ ξ, X ξ ∂M.ν := by
  haveI := hM.prob
  have hm : ∫ ξ, min (X ξ - v) 0 ∂M.ν ≤ 0 := integral_nonpos (fun ξ => min_le_right _ _)
  have hm2 : ∫ ξ, min (X ξ - v) 0 ∂M.ν ≤ ∫ ξ, (X ξ - v) ∂M.ν :=
    integral_mono (int_min M hM X hX v) (hX.sub (integrable_const v)) (fun ξ => min_le_left _ _)
  rw [integral_sub hX (integrable_const v), integral_const, probReal_univ, one_smul] at hm2
  have h3 : 1 ≤ 1 / η := by rw [le_div_iff₀ h0]; linarith
  unfold brk
  nlinarith

lemma cvar_le_affine (hM : M.YieldLaw) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) {α : ℝ} (hα : 0 ≤ α)
    (β : ℝ) {X : ℝ → ℝ} (hX : Integrable X M.ν) (hXY : X ≤ᵐ[M.ν] fun ξ => α * ξ - β) :
    cvar M.ν η X ≤ α * M.tailMean η - β :=
  ciSup_le fun v => (brk_mono_X M hM h0 hX (int_aff M hM α β) hXY v).trans
    (brk_affine M hM h0 h1 hα β v)

lemma affine_le_cvar (hM : M.YieldLaw) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) {α : ℝ} (hα : 0 ≤ α)
    (β : ℝ) {X : ℝ → ℝ} (hX : Integrable X M.ν) (hYX : (fun ξ => α * ξ - β) ≤ᵐ[M.ν] X) :
    α * M.tailMean η - β ≤ cvar M.ν η X := by
  rw [← brk_affine_eq M hM h0 h1 hα β]
  refine le_ciSup_of_le ⟨∫ ξ, X ξ ∂M.ν, ?_⟩ (α * M.quantile η - β)
    (brk_mono_X M hM h0 (int_aff M hM α β) hX hYX _)
  rintro _ ⟨v, rfl⟩
  exact brk_le_int M hM h0 h1 hX v

lemma tailMean_mono (hM : M.YieldLaw) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    M.tailMean x ≤ M.tailMean y := by
  have e1 := brk_affine_eq M hM hx (hxy.trans hy) zero_le_one 0
  have e2 := brk_affine M hM (hx.trans_le hxy) hy zero_le_one 0 (1 * M.quantile x - 0)
  have e3 : brk M x (fun ξ => 1 * ξ - 0) (1 * M.quantile x - 0) ≤
      brk M y (fun ξ => 1 * ξ - 0) (1 * M.quantile x - 0) := by
    unfold brk
    have hm : ∫ ξ, min (1 * ξ - 0 - (1 * M.quantile x - 0)) 0 ∂M.ν ≤ 0 :=
      integral_nonpos (fun ξ => min_le_right _ _)
    have : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx hxy
    nlinarith
  linarith

lemma H_incr (hM : M.YieldLaw) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    0 ≤ y * M.tailMean y - x * M.tailMean x ∧ y * M.tailMean y - x * M.tailMean x ≤ y - x := by
  haveI := hM.prob
  have hy0 : 0 < y := hx.trans_le hxy
  rw [tailMean_eq M hM, tailMean_eq M hM]
  have ex : x * (1 / x * ∫ ξ in Iic (M.quantile x), ξ ∂M.ν) = ∫ ξ in Iic (M.quantile x), ξ ∂M.ν := by
    field_simp
  have ey : y * (1 / y * ∫ ξ in Iic (M.quantile y), ξ ∂M.ν) = ∫ ξ in Iic (M.quantile y), ξ ∂M.ν := by
    field_simp
  rw [ex, ey]
  set a := M.quantile x
  set b := M.quantile y
  have hab : a ≤ b := quantile_mono M hM hx hxy hy
  have hU : Iic b = Iic a ∪ Ioc a b := (Iic_union_Ioc_eq_Iic hab).symm
  have hD : Disjoint (Iic a) (Ioc a b) := Iic_disjoint_Ioc le_rfl
  have hint := int_id M hM
  have hsplit : ∫ ξ in Iic b, ξ ∂M.ν = ∫ ξ in Iic a, ξ ∂M.ν + ∫ ξ in Ioc a b, ξ ∂M.ν := by
    rw [hU, setIntegral_union hD measurableSet_Ioc hint.integrableOn hint.integrableOn]
  have hmeas : M.ν.real (Iic b) = M.ν.real (Iic a) + M.ν.real (Ioc a b) := by
    rw [hU, measureReal_union hD measurableSet_Ioc]
  have qa := quantile_spec M hM hx (hxy.trans hy)
  have qb := quantile_spec M hM hy0 hy
  have hra : M.ν.real (Iic a) = x := qa
  have hrb : M.ν.real (Iic b) = y := qb
  have hun := ae_unit M hM
  have hnn : 0 ≤ ∫ ξ in Ioc a b, ξ ∂M.ν :=
    integral_nonneg_of_ae (ae_restrict_of_ae (hun.mono fun ξ h => h.1))
  have hle : ∫ ξ in Ioc a b, ξ ∂M.ν ≤ ∫ ξ in Ioc a b, (1 : ℝ) ∂M.ν :=
    integral_mono_ae hint.integrableOn (integrable_const 1)
      (ae_restrict_of_ae (hun.mono fun ξ h => h.2))
  rw [setIntegral_const, smul_eq_mul, mul_one] at hle
  constructor <;> linarith

lemma tailMean_one (hM : M.YieldLaw) : M.tailMean 1 = M.mean := by
  haveI := hM.prob
  have q := quantile_spec M hM one_pos le_rfl
  have h1 : M.ν (Iic (M.quantile 1)) = 1 := by
    rw [ENNReal.toReal_eq_one_iff] at q; exact q
  have hc : M.ν (Iic (M.quantile 1))ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Iic).2 h1
  rw [tailMean_eq M hM, Measure.restrict_eq_self_of_ae_mem]
  · unfold Model.mean; ring
  · rw [ae_iff]; exact hc


lemma threshold (hM : M.Standing) :
    ∃ ηs ∈ Icc (0 : ℝ) 1, (ηs = 0 ∨ M.p0 * M.tailMean ηs = M.c) ∧
      ∀ η ∈ Ioc (0 : ℝ) 1, (M.c < M.p0 * M.tailMean η ↔ ηs < η) := by
  have Y := hM.toYieldLaw
  have hp0 := hM.p0_pos
  have hc0 := hM.c_nonneg
  set S := {η ∈ Ioc (0 : ℝ) 1 | M.p0 * M.tailMean η ≤ M.c} with hS
  by_cases hne : S = ∅
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, Or.inl rfl, fun η hη => ⟨fun _ => hη.1, fun _ => ?_⟩⟩
    by_contra h
    have hmem : η ∈ S := ⟨hη, not_lt.1 h⟩
    rw [hne] at hmem; exact hmem
  · obtain ⟨s, hs⟩ := nonempty_iff_ne_empty.2 hne
    have hbdd : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
    set e := sSup S with he_def
    have hse : s ≤ e := le_csSup hbdd hs
    have he0 : 0 < e := hs.1.1.trans_le hse
    have he1 : e ≤ 1 := csSup_le ⟨s, hs⟩ fun x hx => hx.1.2
    have hA : M.p0 * M.tailMean e ≤ M.c := by
      by_contra hcon
      push_neg at hcon
      set δ := e * (M.p0 * M.tailMean e - M.c) / M.p0 with hδ
      have hδpos : 0 < δ := div_pos (mul_pos he0 (by linarith)) hp0
      have hδe : δ * M.p0 = e * (M.p0 * M.tailMean e - M.c) := by
        rw [hδ]; field_simp
      obtain ⟨t, ht, hlt⟩ := exists_lt_of_lt_csSup ⟨s, hs⟩ (show e - δ < e by linarith)
      have hte : t ≤ e := le_csSup hbdd ht
      have hinc := H_incr M Y ht.1.1 hte he1
      have h1 := mul_le_mul_of_nonneg_left hinc.2 hp0.le
      have h2 : 0 < M.p0 * (δ - (e - t)) := mul_pos hp0 (by linarith)
      have h3 : 0 ≤ M.c * (e - t) := mul_nonneg hc0 (by linarith)
      have hpos : 0 < t * (M.p0 * M.tailMean t - M.c) := by nlinarith
      have hneg : t * (M.p0 * M.tailMean t - M.c) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht.1.1.le (by linarith [ht.2])
      linarith
    have hB : M.c ≤ M.p0 * M.tailMean e := by
      by_cases he : e = 1
      · rw [he, tailMean_one M Y]; exact hM.c_le
      have he1' : e < 1 := lt_of_le_of_ne he1 he
      by_contra hcon
      push_neg at hcon
      set δ := e * (M.c - M.p0 * M.tailMean e) / (2 * M.p0) with hδ
      have hδpos : 0 < δ := div_pos (mul_pos he0 (by linarith)) (by linarith)
      have hδe : δ * (2 * M.p0) = e * (M.c - M.p0 * M.tailMean e) := by
        rw [hδ]; field_simp
      set η := min 1 (e + δ) with hη
      have hηe : e < η := lt_min he1' (by linarith)
      have hη1 : η ≤ 1 := min_le_left _ _
      have hηd : η ≤ e + δ := min_le_right _ _
      have hnot : η ∉ S := fun hm => absurd (le_csSup hbdd hm) (not_le.2 hηe)
      have hgt : M.c < M.p0 * M.tailMean η := by
        by_contra h
        exact hnot ⟨⟨he0.trans hηe, hη1⟩, not_lt.1 h⟩
      have hinc := H_incr M Y he0 hηe.le hη1
      have h1 := mul_le_mul_of_nonneg_left hinc.2 hp0.le
      have hpos : 0 < η * (M.p0 * M.tailMean η - M.c) :=
        mul_pos (he0.trans hηe) (by linarith)
      have h4 : M.p0 * (η - e) ≤ M.p0 * δ := mul_le_mul_of_nonneg_left (by linarith) hp0.le
      have h5 : 0 ≤ M.c * (η - e) := mul_nonneg hc0 (by linarith)
      nlinarith
    refine ⟨e, ⟨he0.le, he1⟩, Or.inr (le_antisymm hA hB), fun η hη => ⟨fun h => ?_, fun h => ?_⟩⟩
    · by_contra hle
      push_neg at hle
      have := tailMean_mono M Y hη.1 hle he1
      have := mul_le_mul_of_nonneg_left this hp0.le
      linarith
    · by_contra hle
      have hm : η ∈ S := ⟨hη, not_lt.1 hle⟩
      exact absurd (le_csSup hbdd hm) (not_le.2 h)

noncomputable def rev (x : ℝ) : ℝ := sSup ((fun p => p * min (M.d p) x) '' Icc 0 M.p0)

lemma rev_bdd (hM : M.Standing) (x : ℝ) :
    BddAbove ((fun p => p * min (M.d p) x) '' Icc 0 M.p0) := by
  refine ⟨M.p0 * |x|, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have h1 : p * min (M.d p) x ≤ p * x := mul_le_mul_of_nonneg_left (min_le_right _ _) hp.1
  have h2 : p * x ≤ p * |x| := mul_le_mul_of_nonneg_left (le_abs_self x) hp.1
  have h3 : p * |x| ≤ M.p0 * |x| := mul_le_mul_of_nonneg_right hp.2 (abs_nonneg x)
  linarith

lemma rev_ne (hM : M.Standing) (x : ℝ) :
    ((fun p => p * min (M.d p) x) '' Icc 0 M.p0).Nonempty :=
  ⟨_, ⟨0, ⟨le_rfl, hM.p0_pos.le⟩, rfl⟩⟩

lemma rev_ge (hM : M.Standing) {p : ℝ} (hp : p ∈ Icc 0 M.p0) (x : ℝ) :
    p * min (M.d p) x ≤ rev M x :=
  le_csSup (rev_bdd M hM x) ⟨p, hp, rfl⟩

lemma rev_nonneg (hM : M.Standing) (x : ℝ) : 0 ≤ rev M x := by
  have := rev_ge M hM (p := 0) ⟨le_rfl, hM.p0_pos.le⟩ x
  simpa using this

lemma rev_le (hM : M.Standing) (x : ℝ) : rev M x ≤ M.p0 * |x| := by
  apply csSup_le (rev_ne M hM x)
  rintro _ ⟨p, hp, rfl⟩
  have h1 : p * min (M.d p) x ≤ p * x := mul_le_mul_of_nonneg_left (min_le_right _ _) hp.1
  have h2 : p * x ≤ p * |x| := mul_le_mul_of_nonneg_left (le_abs_self x) hp.1
  have h3 : p * |x| ≤ M.p0 * |x| := mul_le_mul_of_nonneg_right hp.2 (abs_nonneg x)
  linarith

lemma rev_mono (hM : M.Standing) : Monotone (rev M) := by
  intro x y hxy
  apply csSup_le (rev_ne M hM x)
  rintro _ ⟨p, hp, rfl⟩
  exact le_trans (mul_le_mul_of_nonneg_left (min_le_min le_rfl hxy) hp.1) (rev_ge M hM hp y)

lemma int_profitA (hM : M.Standing) (p q : ℝ) : Integrable (M.profitA p q) M.ν := by
  haveI := hM.prob
  unfold Model.profitA
  refine Integrable.sub (Integrable.const_mul ?_ p) (integrable_const _)
  exact (integrable_const (M.d p)).inf ((int_id M hM.toYieldLaw).const_mul q)

lemma profitR_eq (q : ℝ) : M.profitR q = fun ξ => rev M (q * ξ) - M.c * q := rfl

lemma int_profitR (hM : M.Standing) {q : ℝ} (hq : 0 ≤ q) : Integrable (M.profitR q) M.ν := by
  haveI := hM.prob
  rw [profitR_eq]
  refine Integrable.sub ?_ (integrable_const _)
  have hmono : Monotone fun ξ => rev M (q * ξ) :=
    (rev_mono M hM).comp fun a b h => mul_le_mul_of_nonneg_left h hq
  refine Integrable.mono' (((int_id M hM.toYieldLaw).const_mul q).abs.const_mul M.p0)
    hmono.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (rev_nonneg M hM _)]
  exact rev_le M hM _

lemma good_price (hM : M.Standing) {η : ℝ} (h : M.c < M.p0 * M.tailMean η) :
    ∃ p, 0 ≤ p ∧ p < M.p0 ∧ M.c < p * M.tailMean η ∧ 0 < M.d p := by
  have hp0 := hM.p0_pos
  have hc0 := hM.c_nonneg
  have hg : 0 < M.tailMean η := by
    by_contra hg; push_neg at hg
    have := mul_nonpos_of_nonneg_of_nonpos hp0.le hg
    linarith
  set p := (M.c / M.tailMean η + M.p0) / 2 with hp
  have hcg : M.c / M.tailMean η < M.p0 := by rw [div_lt_iff₀ hg]; linarith
  have hcg0 : 0 ≤ M.c / M.tailMean η := div_nonneg hc0 hg.le
  have hpl : p < M.p0 := by rw [hp]; linarith
  have hpn : 0 ≤ p := by rw [hp]; linarith
  refine ⟨p, hpn, hpl, ?_, ?_⟩
  · have : M.c / M.tailMean η < p := by rw [hp]; linarith
    rwa [div_lt_iff₀ hg] at this
  · have := hM.d_strictAnti ⟨hpn, hpl.le⟩ ⟨hp0.le, le_rfl⟩ hpl
    rw [hM.d_p0] at this; exact this

lemma exante_iff (hM : M.Standing) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    M.ProducesExAnte η ↔ M.c < M.p0 * M.tailMean η := by
  have Y := hM.toYieldLaw
  constructor
  · rintro ⟨p, hp, q, hq, hpos⟩
    by_contra hle
    push_neg at hle
    have hb := cvar_le_affine M Y h0 h1 (mul_nonneg hq hM.p0_pos.le) (q * M.c)
      (int_profitA M hM p q) (X := M.profitA p q) (by
        filter_upwards [ae_unit M Y] with ξ hξ
        unfold Model.profitA
        have hqx : 0 ≤ q * ξ := mul_nonneg hq hξ.1
        have e1 : p * min (M.d p) (q * ξ) ≤ p * (q * ξ) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hp.1
        have e2 : p * (q * ξ) ≤ M.p0 * (q * ξ) := mul_le_mul_of_nonneg_right hp.2 hqx
        nlinarith)
    have : q * M.p0 * M.tailMean η - q * M.c ≤ 0 := by
      have := mul_nonneg hq (sub_nonneg.2 hle); nlinarith
    exact absurd hpos (not_lt.2 (le_trans hb this))
  · intro h
    obtain ⟨p, hp0, hpl, hpg, hd⟩ := good_price M hM h
    refine ⟨p, ⟨hp0, hpl.le⟩, M.d p, hd.le, ?_⟩
    have hb := affine_le_cvar M Y h0 h1 (mul_nonneg hd.le hp0) (M.d p * M.c)
      (int_profitA M hM p (M.d p)) (X := M.profitA p (M.d p)) (by
        filter_upwards [ae_unit M Y] with ξ hξ
        unfold Model.profitA
        have : M.d p * ξ ≤ M.d p := by nlinarith
        rw [min_eq_right this]
        nlinarith)
    have : 0 < M.d p * p * M.tailMean η - M.d p * M.c := by
      have := mul_pos hd (sub_pos.2 hpg); nlinarith
    exact lt_of_lt_of_le this hb

lemma resp_iff (hM : M.Standing) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    M.ProducesResponsive η ↔ M.c < M.p0 * M.tailMean η := by
  have Y := hM.toYieldLaw
  constructor
  · rintro ⟨q, hq, hpos⟩
    by_contra hle
    push_neg at hle
    have hb := cvar_le_affine M Y h0 h1 (mul_nonneg hq hM.p0_pos.le) (q * M.c)
      (int_profitR M hM hq) (X := M.profitR q) (by
        filter_upwards [ae_unit M Y] with ξ hξ
        rw [profitR_eq]
        have hqx : 0 ≤ q * ξ := mul_nonneg hq hξ.1
        have e1 := rev_le M hM (q * ξ)
        rw [abs_of_nonneg hqx] at e1
        show rev M (q * ξ) - M.c * q ≤ q * M.p0 * ξ - q * M.c
        nlinarith)
    have : q * M.p0 * M.tailMean η - q * M.c ≤ 0 := by
      have := mul_nonneg hq (sub_nonneg.2 hle); nlinarith
    exact absurd hpos (not_lt.2 (le_trans hb this))
  · intro h
    obtain ⟨p, hp0, hpl, hpg, hd⟩ := good_price M hM h
    refine ⟨M.d p, hd.le, ?_⟩
    have hb := affine_le_cvar M Y h0 h1 (mul_nonneg hd.le hp0) (M.d p * M.c)
      (int_profitR M hM hd.le) (X := M.profitR (M.d p)) (by
        filter_upwards [ae_unit M Y] with ξ hξ
        rw [profitR_eq]
        have e1 := rev_ge M hM ⟨hp0, hpl.le⟩ (M.d p * ξ)
        have : M.d p * ξ ≤ M.d p := by nlinarith
        rw [min_eq_right this] at e1
        show M.d p * p * ξ - M.d p * M.c ≤ rev M (M.d p * ξ) - M.c * M.d p
        nlinarith)
    have : 0 < M.d p * p * M.tailMean η - M.d p * M.c := by
      have := mul_pos hd (sub_pos.2 hpg); nlinarith
    exact lt_of_lt_of_le this hb

end RPSolA

open RiskPostpone.Threshold in
theorem solution (M : Model) (hM : M.Standing) (hA2 : M.Assumption2) :
    ∃ ηs ∈ Icc (0 : ℝ) 1, (ηs = 0 ∨ M.p0 * M.tailMean ηs = M.c) ∧
      ∀ η ∈ Ioc (0 : ℝ) 1,
        (M.ProducesExAnte η ↔ ηs < η) ∧ (M.ProducesResponsive η ↔ ηs < η) := by
  obtain ⟨ηs, hs, hor, hiff⟩ := RPSolA.threshold M hM
  exact ⟨ηs, hs, hor, fun η hη =>
    ⟨(RPSolA.exante_iff M hM hη.1 hη.2).trans (hiff η hη),
     (RPSolA.resp_iff M hM hη.1 hη.2).trans (hiff η hη)⟩⟩
