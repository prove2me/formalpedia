-- Prove2me | solution 1 for SurgeSpatial.Attraction.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:10:53.623301+00:00
-- url     : https://prove2.me/submissions/8e067f82-8f0b-4051-a632-8605527ad36c

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeAuxL1
open SurgeSpatial.Attraction Filter

lemma Fbar_nonneg (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) (q : ℝ) :
    0 ≤ M.Fbar y q := by
  unfold Market.Fbar; linarith [hM.F_le_one y hy q]

lemma Fbar_eq_zero (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) {q : ℝ}
    (hq : M.Vbar ≤ q) : M.Fbar y q = 0 := by
  unfold Market.Fbar
  have h1 := hM.F_mono y hy hq
  have h2 := hM.F_le_one y hy q
  rw [hM.F_Vbar y hy] at h1
  linarith

lemma lam_nonneg (M : Market) (y : E) : 0 ≤ M.lam y := ENNReal.toReal_nonneg

lemma R_le_one (M : Market) (y : E) (q s : ℝ) : M.R y q s ≤ 1 := by
  unfold Market.R
  split_ifs <;> simp

lemma R_nonneg (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) (q s : ℝ) :
    0 ≤ M.R y q s := by
  unfold Market.R
  split_ifs with h
  · exact le_min zero_le_one
      (div_nonneg (mul_nonneg (lam_nonneg M y) (Fbar_nonneg M hM hy q)) h.le)
  · exact zero_le_one
  · exact le_rfl

lemma R_eq_zero (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) {q : ℝ}
    (hq : M.Vbar ≤ q) (s : ℝ) : M.R y q s = 0 := by
  unfold Market.R
  rw [Fbar_eq_zero M hM hy hq]
  simp

lemma Ufun_nonneg (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) {q : ℝ}
    (hq : 0 ≤ q) (s : ℝ) : 0 ≤ M.Ufun y q s := by
  unfold Market.Ufun
  exact mul_nonneg (mul_nonneg hM.α_pos.le hq) (R_nonneg M hM hy q s)

lemma Ufun_le (M : Market) (hM : M.Standing) {y : E} (hy : y ∈ M.C) (q s : ℝ) :
    M.Ufun y q s ≤ M.α * M.Vbar := by
  unfold Market.Ufun
  rcases le_or_gt M.Vbar q with h | h
  · rw [R_eq_zero M hM hy h]; simp; exact mul_nonneg hM.α_pos.le hM.Vbar_pos.le
  · rcases le_or_gt q 0 with h0 | h0
    · have := R_nonneg M hM hy q s
      have : M.α * q * M.R y q s ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hM.α_pos.le h0) this
      nlinarith [hM.α_pos, hM.Vbar_pos]
    · have h1 := R_le_one M y q s
      have h2 := R_nonneg M hM hy q s
      calc M.α * q * M.R y q s ≤ M.α * q * 1 :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hM.α_pos.le h0.le)
        _ ≤ M.α * M.Vbar := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left h.le hM.α_pos.le

/-- generic essSup comparison in `ℝ`. -/
lemma essSup_le_add {α : Type*} [MeasurableSpace α] {μ : Measure α} (hμ : μ ≠ 0)
    {f g : α → ℝ} {a b c : ℝ} (hfa : ∀ᵐ y ∂μ, a ≤ f y) (hgb : ∀ᵐ y ∂μ, g y ≤ b)
    (h : ∀ᵐ y ∂μ, f y ≤ g y + c) : essSup f μ ≤ essSup g μ + c := by
  have : (ae μ).NeBot := ae_neBot.mpr hμ
  have hg : ∀ᵐ y ∂μ, g y ≤ essSup g μ := ae_le_essSup (isBoundedUnder_of_eventually_le hgb)
  refine essSup_le_of_ae_le _ ?_ (isCoboundedUnder_le_of_eventually_le _ hfa)
  filter_upwards [hg, h] with y h1 h2
  linarith

lemma le_essSup_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} (hμ : μ ≠ 0)
    {f : α → ℝ} {b c : ℝ} (hfb : ∀ᵐ y ∂μ, f y ≤ b) (h : ∀ᵐ y ∂μ, c ≤ f y) :
    c ≤ essSup f μ := by
  have : (ae μ).NeBot := ae_neBot.mpr hμ
  calc c = essSup (fun _ => c) μ := (essSup_const c hμ).symm
    _ ≤ essSup f μ := essSup_mono_ae h
        (isCoboundedUnder_le_of_eventually_le _ (Eventually.of_forall fun _ => le_rfl))
        (isBoundedUnder_of_eventually_le hfb)

lemma essSup_le_of_ae' {α : Type*} [MeasurableSpace α] {μ : Measure α} (hμ : μ ≠ 0)
    {f : α → ℝ} {a c : ℝ} (hfa : ∀ᵐ y ∂μ, a ≤ f y) (h : ∀ᵐ y ∂μ, f y ≤ c) :
    essSup f μ ≤ c := by
  have : (ae μ).NeBot := ae_neBot.mpr hμ
  exact essSup_le_of_ae_le _ h (isCoboundedUnder_le_of_eventually_le _ hfa)

/-- Bounds on `Π` for destinations in `C`. -/
lemma Pi_bounds (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E)) {K : ℝ}
    (hK : ∀ y ∈ M.C, ‖y‖ ≤ K) (x : E) {y : E} (hy : y ∈ M.C) (hp : 0 ≤ p y) :
    -(K + ‖x‖) ≤ M.Pi p T x y ∧ M.Pi p T x y ≤ M.α * M.Vbar := by
  unfold Market.Pi Market.U
  have h1 := Ufun_nonneg M hM hy hp (M.sT T y)
  have h2 := Ufun_le M hM hy (p y) (M.sT T y)
  have h3 : ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le y x
  have h4 := hK y hy
  constructor <;> nlinarith [norm_nonneg (y - x)]

lemma VB_le_add (M : Market) (hM : M.Standing) (B : Set E) (hB : MeasurableSet B)
    (hBC : B ⊆ M.C) (hΓB : 0 < M.Γ B) (p : E → ℝ) (hp0 : ∀ y ∈ B, 0 ≤ p y)
    (T : Measure (E × E)) (x x' : E) :
    M.VB B p T x ≤ M.VB B p T x' + ‖x - x'‖ := by
  obtain ⟨K, hK⟩ : ∃ K, ∀ y ∈ M.C, ‖y‖ ≤ K := by
    obtain ⟨K, hK⟩ := hM.compact_C.isBounded.exists_norm_le
    exact ⟨K, hK⟩
  have hμ : M.Γ.restrict B ≠ 0 := by
    intro h
    have := congrArg (fun μ : Measure E => μ B) h
    simp [Measure.restrict_apply hB] at this
    exact hΓB.ne' this
  have hmem : ∀ᵐ y ∂(M.Γ.restrict B), y ∈ B := ae_restrict_mem hB
  unfold Market.VB
  refine essSup_le_add hμ (a := -(K + ‖x‖)) (b := M.α * M.Vbar) ?_ ?_ ?_
  · filter_upwards [hmem] with y hy
    exact (Pi_bounds M hM p T hK x (hBC hy) (hp0 y hy)).1
  · filter_upwards [hmem] with y hy
    exact (Pi_bounds M hM p T hK x' (hBC hy) (hp0 y hy)).2
  · filter_upwards with y
    unfold Market.Pi
    have : ‖y - x'‖ ≤ ‖y - x‖ + ‖x - x'‖ := by
      calc ‖y - x'‖ = ‖(y - x) + (x - x')‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith


lemma V_le_add (M : Market) (hM : M.Standing) (p : E → ℝ) (hp0 : ∀ y ∈ M.C, 0 ≤ p y)
    (T : Measure (E × E)) (x x' : E) :
    M.V p T x ≤ M.V p T x' + ‖x - x'‖ := by
  have hCm : MeasurableSet M.C := hM.compact_C.isClosed.measurableSet
  rcases eq_or_ne (M.Γ M.C) 0 with h0 | h0
  · have hz : M.Γ.restrict M.C = 0 := by
      rw [Measure.restrict_eq_zero]; exact h0
    have : M.V p T x = M.V p T x' := by
      unfold Market.V Market.VB; rw [hz]
      exact essSup_congr_ae (by simp [Filter.EventuallyEq])
    rw [this]; linarith [norm_nonneg (x - x')]
  · exact VB_le_add M hM M.C hCm subset_rfl (pos_iff_ne_zero.mpr h0) p hp0 T x x'

lemma V_lip (M : Market) (hM : M.Standing) (p : E → ℝ) (hp0 : ∀ y ∈ M.C, 0 ≤ p y)
    (T : Measure (E × E)) : LipschitzWith 1 (M.V p T) := by
  refine LipschitzWith.of_le_add_mul 1 ?_
  intro x y
  have := V_le_add M hM p hp0 T x y
  rw [dist_eq_norm]; simpa using this

/-- Lemma B-2 core: indifference propagates along segments. -/
lemma IR_segment (M : Market) (hM : M.Standing) (p : E → ℝ) (hp0 : ∀ y ∈ M.C, 0 ≤ p y)
    (T : Measure (E × E)) (x y : E) (hx : x ∈ M.C) (hy : y ∈ M.IR p T x) :
    ∀ w ∈ segment ℝ x y, y ∈ M.IR p T w := by
  intro w hw
  obtain ⟨hyC, hyx⟩ := hy
  refine ⟨hyC, ?_⟩
  have hd : dist x w + dist w y = dist x y := dist_add_dist_of_mem_segment hw
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at hd
  have h1 := V_le_add M hM p hp0 T y w
  have h2 := V_le_add M hM p hp0 T w x
  have e1 : ‖x - w‖ = ‖w - x‖ := norm_sub_rev _ _
  have e2 : ‖w - y‖ = ‖y - w‖ := norm_sub_rev _ _
  have e3 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev _ _
  linarith

end SurgeAuxL1

namespace SurgeAuxA2
open SurgeSpatial.Attraction

lemma U_meas (M : Market) (hM : M.Standing) (p : E → ℝ) (hp : Measurable p)
    (T : Measure (E × E)) : Measurable (M.U p T) := by
  have hl : Measurable M.lam := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hs : Measurable (M.sT T) := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hF : Measurable (fun y => M.F y (p y)) := hM.F_meas.comp (measurable_id.prodMk hp)
  have hFb : Measurable (fun y => M.lam y * M.Fbar y (p y)) := by
    unfold Market.Fbar; exact hl.mul (measurable_const.sub hF)
  unfold Market.U Market.Ufun Market.R
  refine (measurable_const.mul hp).mul ?_
  exact Measurable.ite (measurableSet_lt measurable_const hs)
    (measurable_const.min (hFb.div hs))
    (Measurable.ite (measurableSet_lt measurable_const hFb) measurable_const measurable_const)

lemma C_meas (M : Market) (hM : M.Standing) : MeasurableSet M.C :=
  hM.compact_C.isClosed.measurableSet

lemma restrict_ne_zero (M : Market) {B : Set E} (hB : MeasurableSet B) (hΓB : 0 < M.Γ B) :
    M.Γ.restrict B ≠ 0 := by
  intro h
  have := congrArg (fun μ : Measure E => μ B) h
  simp [Measure.restrict_apply hB] at this
  exact hΓB.ne' this

/-- `Π(c, ·) ≤ V_B(c)` a.e. on `B`. -/
lemma Pi_le_VB (M : Market) (hM : M.Standing) {B : Set E} (hB : MeasurableSet B)
    (hBC : B ⊆ M.C) (p : E → ℝ) (hp0 : ∀ y ∈ B, 0 ≤ p y) (T : Measure (E × E)) (c : E) :
    ∀ᵐ y ∂(M.Γ.restrict B), M.Pi p T c y ≤ M.VB B p T c := by
  have hbd : ∀ᵐ y ∂(M.Γ.restrict B), M.Pi p T c y ≤ M.α * M.Vbar := by
    filter_upwards [ae_restrict_mem hB] with y hy
    have h1 := SurgeAuxL1.Ufun_le M hM (hBC hy) (p y) (M.sT T y)
    unfold Market.Pi Market.U; linarith [norm_nonneg (y - c)]
  exact ae_le_essSup (Filter.isBoundedUnder_of_eventually_le hbd)

/-- Lemma A-2, second part: `U ≤ V_B` `Γ`-a.e. on `B` (no equilibrium needed). -/
lemma U_le_VB (M : Market) (hM : M.Standing) (B : Set E) (hB : MeasurableSet B)
    (hBC : B ⊆ M.C) (hΓB : 0 < M.Γ B) (p : E → ℝ) (hp0 : ∀ y ∈ B, 0 ≤ p y)
    (T : Measure (E × E)) : ∀ᵐ y ∂M.Γ, y ∈ B → M.U p T y ≤ M.VB B p T y := by
  rw [ae_iff]
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq E
  have key : ∀ n m : ℕ, M.Γ ({y | y ∈ B ∧ M.VB B p T y + 1 / ((n : ℝ) + 1) < M.U p T y} ∩
      Metric.ball (u m) (1 / (3 * ((n : ℝ) + 1)))) = 0 := by
    intro n m
    have h0 := Pi_le_VB M hM hB hBC p hp0 T (u m)
    rw [ae_iff, Measure.restrict_apply' hB] at h0
    refine measure_mono_null ?_ h0
    rintro y ⟨⟨hyB, hlt⟩, hball⟩
    refine ⟨?_, hyB⟩
    simp only [Set.mem_setOf_eq, not_le]
    have hd : ‖y - u m‖ < 1 / (3 * ((n : ℝ) + 1)) := by rw [← dist_eq_norm]; exact hball
    have hlip := SurgeAuxL1.VB_le_add M hM B hB hBC hΓB p hp0 T (u m) y
    have e : ‖u m - y‖ = ‖y - u m‖ := norm_sub_rev _ _
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have e2 : 1 / ((n : ℝ) + 1) = 3 * (1 / (3 * ((n : ℝ) + 1))) := by field_simp
    have hr : (0 : ℝ) < 1 / (3 * ((n : ℝ) + 1)) := by positivity
    unfold Market.Pi
    linarith
  refine measure_mono_null ?_ (measure_iUnion_null fun n => measure_iUnion_null fun m => key n m)
  intro y hy
  simp only [Set.mem_setOf_eq, Classical.not_imp, not_le] at hy
  obtain ⟨hyB, hlt⟩ := hy
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
  have hr : (0 : ℝ) < 1 / (3 * ((n : ℝ) + 1)) := by positivity
  obtain ⟨m, hm⟩ := hu.exists_dist_lt y hr
  simp only [Set.mem_iUnion]
  refine ⟨n, m, ⟨hyB, by linarith⟩, ?_⟩
  rw [Metric.mem_ball]; exact hm

lemma VB_le_V (M : Market) (hM : M.Standing) (B : Set E) (hB : MeasurableSet B)
    (hBC : B ⊆ M.C) (hΓB : 0 < M.Γ B) (p : E → ℝ) (hp0 : ∀ y ∈ M.C, 0 ≤ p y)
    (T : Measure (E × E)) (x : E) : M.VB B p T x ≤ M.V p T x := by
  obtain ⟨K, hK⟩ := hM.compact_C.isBounded.exists_norm_le
  have hC := C_meas M hM
  have hle : ∀ᵐ y ∂(M.Γ.restrict M.C), M.Pi p T x y ≤ M.V p T x :=
    Pi_le_VB M hM hC subset_rfl p hp0 T x
  have hac : M.Γ.restrict B ≪ M.Γ.restrict M.C :=
    Measure.absolutelyContinuous_of_le (Measure.restrict_mono hBC le_rfl)
  unfold Market.VB
  refine SurgeAuxL1.essSup_le_of_ae' (restrict_ne_zero M hB hΓB) (a := -(K + ‖x‖)) ?_
    (hac.ae_le hle)
  filter_upwards [ae_restrict_mem hB] with y hy
  exact (SurgeAuxL1.Pi_bounds M hM p T hK x (hBC hy) (hp0 y (hBC hy))).1

/-- Equilibrium: `T`-a.e. pair is in `C × C` and indifferent. -/
lemma eq_ae (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) :
    ∀ᵐ q ∂T, q ∈ M.C ×ˢ M.C ∧ M.Pi p T q.1 q.2 = M.V p T q.1 := by
  obtain ⟨hp, hpr, ⟨hTf, _, hT1, _⟩, heq⟩ := hpT
  have hp0 : ∀ y ∈ M.C, 0 ≤ p y := fun y hy => (hpr y hy).1
  have hC := C_meas M hM
  have hU := U_meas M hM p hp T
  have hV : Measurable (M.V p T) := (SurgeAuxL1.V_lip M hM p hp0 T).continuous.measurable
  have hG : MeasurableSet {q : E × E | q ∈ M.C ×ˢ M.C ∧ M.Pi p T q.1 q.2 = M.V p T q.1} := by
    refine (hC.prod hC).inter ?_
    unfold Market.Pi
    exact measurableSet_eq_fun ((hU.comp measurable_snd).sub
      (measurable_snd.sub measurable_fst).norm) (hV.comp measurable_fst)
  unfold Market.IsEquilibrium at heq
  have htot : T Set.univ = M.Θ M.C := by
    have h1 : T Set.univ = M.Θ Set.univ := by
      rw [← hT1, Measure.map_apply measurable_fst MeasurableSet.univ]; rfl
    rw [h1, ← measure_add_measure_compl hC, hM.Θ_conc, add_zero]
  rw [ae_iff]
  have : {q : E × E | ¬ (q ∈ M.C ×ˢ M.C ∧ M.Pi p T q.1 q.2 = M.V p T q.1)} =
      {q : E × E | q ∈ M.C ×ˢ M.C ∧ M.Pi p T q.1 q.2 = M.V p T q.1}ᶜ := rfl
  rw [this, measure_compl hG (measure_ne_top _ _), heq, htot, tsub_self]

end SurgeAuxA2

namespace SurgeAuxA2b
open SurgeSpatial.Attraction

lemma V_le_U_T (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) :
    ∀ᵐ q ∂T, q ∈ M.C ×ˢ M.C ∧ M.Pi p T q.1 q.2 = M.V p T q.1 ∧
      M.V p T q.2 ≤ M.U p T q.2 := by
  have hp0 : ∀ y ∈ M.C, 0 ≤ p y := fun y hy => (hpT.2.1 y hy).1
  filter_upwards [SurgeAuxA2.eq_ae M hM p T hpT] with q hq
  obtain ⟨hqC, hpi⟩ := hq
  refine ⟨hqC, hpi, ?_⟩
  have := SurgeAuxL1.V_le_add M hM p hp0 T q.2 q.1
  unfold Market.Pi at hpi
  have e : ‖q.2 - q.1‖ = ‖q.1 - q.2‖ := norm_sub_rev _ _
  linarith

lemma V_le_U_T2 (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) :
    ∀ᵐ y ∂(T.map Prod.snd), y ∈ M.C ∧ M.V p T y ≤ M.U p T y := by
  have hp0 : ∀ y ∈ M.C, 0 ≤ p y := fun y hy => (hpT.2.1 y hy).1
  have hC := SurgeAuxA2.C_meas M hM
  have hU := SurgeAuxA2.U_meas M hM p hpT.1 T
  have hV : Measurable (M.V p T) := (SurgeAuxL1.V_lip M hM p hp0 T).continuous.measurable
  have hmeas : MeasurableSet {y | y ∈ M.C ∧ M.V p T y ≤ M.U p T y} :=
    hC.inter (measurableSet_le hV hU)
  refine (ae_map_iff measurable_snd.aemeasurable hmeas).mpr ?_
  filter_upwards [V_le_U_T M hM p T hpT] with q hq
  exact ⟨hq.1.2, hq.2.2⟩

lemma Γ_eq_zero (M : Market) (hM : M.Standing) (h : M.Γ M.C = 0) : M.Γ = 0 := by
  rw [← Measure.measure_univ_eq_zero, ← measure_add_measure_compl (SurgeAuxA2.C_meas M hM),
    h, hM.Γ_conc, add_zero]

end SurgeAuxA2b

namespace SurgeAuxA3
open SurgeSpatial.Attraction Set

lemma g_le (M : Market) {x : E} {s q : ℝ} (hs : 0 ≤ s) (hq : q ∈ Icc 0 M.Vbar) :
    q * min s (M.lam x * M.Fbar x q) ≤ M.Vbar * s :=
  calc _ ≤ q * s := mul_le_mul_of_nonneg_left (min_le_left _ _) hq.1
    _ ≤ _ := mul_le_mul_of_nonneg_right hq.2 hs

lemma bdd (M : Market) {x : E} {s : ℝ} (hs : 0 ≤ s) :
    BddAbove ((fun q => q * min s (M.lam x * M.Fbar x q)) '' Icc 0 M.Vbar) :=
  ⟨M.Vbar * s, by rintro _ ⟨q, hq, rfl⟩; exact g_le M hs hq⟩

lemma le_Rloc (M : Market) {x : E} {s q : ℝ} (hs : 0 ≤ s) (hq : q ∈ Icc 0 M.Vbar) :
    q * min s (M.lam x * M.Fbar x q) ≤ M.Rloc x s :=
  le_csSup (bdd M hs) ⟨q, hq, rfl⟩

lemma Rloc_attained (M : Market) (hM : M.Standing) {x : E} (hx : x ∈ M.C) {s : ℝ}
    (hs : 0 < s) : ∃ q ∈ Icc 0 M.Vbar, M.Rloc x s = q * min s (M.lam x * M.Fbar x q) := by
  have hcont : ContinuousOn (fun q => q * min s (M.lam x * M.Fbar x q)) (Icc 0 M.Vbar) := by
    have h1 := hM.revenue_cont x hx
    have ha : ContinuousOn (fun q : ℝ => q * s) (Icc 0 M.Vbar) := by fun_prop
    have hb : ContinuousOn (fun q => M.lam x * (q * M.Fbar x q)) (Icc 0 M.Vbar) :=
      continuousOn_const.mul h1
    have h2 : ContinuousOn (fun q => min (q * s) (M.lam x * (q * M.Fbar x q)))
        (Icc 0 M.Vbar) := ha.inf hb
    refine h2.congr ?_
    intro q hq
    simp only
    rw [mul_min_of_nonneg _ _ hq.1]
    congr 1; ring
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hM.Vbar_pos.le) hcont
  refine ⟨q, hq, ?_⟩
  unfold Market.Rloc
  apply le_antisymm
  · apply csSup_le ((nonempty_Icc.2 hM.Vbar_pos.le).image _)
    rintro _ ⟨q'', hq'', rfl⟩
    exact hmax hq''
  · exact le_csSup (bdd M hs.le) ⟨q, hq, rfl⟩

lemma Fbar_pos (M : Market) (hM : M.Standing) {x : E} (hx : x ∈ M.C) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q < M.Vbar) : 0 < M.Fbar x q := by
  have := hM.F_strictMono x hx ⟨hq0, hq.le⟩ ⟨hM.Vbar_pos.le, le_rfl⟩ hq
  rw [hM.F_Vbar x hx] at this
  unfold Market.Fbar; linarith

theorem psi_anti (M : Market) (hM : M.Standing) {x : E} (hx : x ∈ M.C)
    (hl : 0 < M.lam x) : StrictAntiOn (M.psi x) (Ici 0) := by
  intro s hs s' _ hss'
  have hs0 : (0 : ℝ) ≤ s := hs
  have hs'pos : 0 < s' := lt_of_le_of_lt hs0 hss'
  have hα := hM.α_pos
  have hV := hM.Vbar_pos
  obtain ⟨q', hq', hR'⟩ := Rloc_attained M hM hx hs'pos
  show M.psi x s' < M.psi x s
  unfold Market.psi
  rw [if_pos hs'pos]
  set v' := M.lam x * M.Fbar x q' with hv'
  rcases eq_or_lt_of_le hs0 with h0 | hspos
  · rw [if_neg (by rw [← h0]; exact lt_irrefl 0)]
    rw [mul_div_assoc]
    apply mul_lt_mul_of_pos_left _ hα
    rw [div_lt_iff₀ hs'pos, hR']
    rcases lt_or_eq_of_le hq'.2 with hlt | heq
    · calc q' * min s' v' ≤ q' * s' := mul_le_mul_of_nonneg_left (min_le_left _ _) hq'.1
        _ < M.Vbar * s' := mul_lt_mul_of_pos_right hlt hs'pos
    · have : v' = 0 := by
        rw [hv', heq, SurgeAuxL1.Fbar_eq_zero M hM hx le_rfl, mul_zero]
      rw [this, min_eq_right hs'pos.le, mul_zero]
      exact mul_pos hV hs'pos
  · rw [if_pos hspos, mul_div_assoc, mul_div_assoc]
    apply mul_lt_mul_of_pos_left _ hα
    rw [hR']
    by_cases hg : 0 < q' * min s' v'
    · have hq'pos : 0 < q' := by
        by_contra h
        push Not at h
        have : q' = 0 := le_antisymm h hq'.1
        rw [this, zero_mul] at hg; exact lt_irrefl 0 hg
      have hmin : 0 < min s' v' := pos_of_mul_pos_right hg hq'pos.le
      have hv'pos : 0 < v' := lt_of_lt_of_le hmin (min_le_right _ _)
      rcases lt_or_ge v' s' with hvs | hvs
      · rw [min_eq_right hvs.le]
        have hle := le_Rloc M (x := x) hspos.le hq'
        rw [← hv'] at hle
        refine lt_of_lt_of_le ?_ (div_le_div_of_nonneg_right hle hspos.le)
        rcases le_or_gt v' s with hvs2 | hvs2
        · rw [min_eq_right hvs2]
          exact div_lt_div_of_pos_left (mul_pos hq'pos hv'pos) hspos hss'
        · rw [min_eq_left hvs2.le, show q' * s / s = q' by field_simp,
            show q' * v' / s' = q' * (v' / s') by ring]
          have : v' / s' < 1 := (div_lt_one hs'pos).mpr hvs
          nlinarith
      · rw [min_eq_left hvs, mul_div_assoc, div_self hs'pos.ne', mul_one]
        have hq'lt : q' < M.Vbar := by
          rcases lt_or_eq_of_le hq'.2 with h | h
          · exact h
          · exfalso
            have : v' = 0 := by
              rw [hv', h, SurgeAuxL1.Fbar_eq_zero M hM hx le_rfl, mul_zero]
            linarith
        -- continuity of `h q = λ q F̄(q) - s q` at `q'`
        have hc : ContinuousOn (fun q => M.lam x * (q * M.Fbar x q) - s * q) (Icc 0 M.Vbar) :=
          (continuousOn_const.mul (hM.revenue_cont x hx)).sub
            (continuousOn_const.mul continuousOn_id)
        have hhq' : 0 < M.lam x * (q' * M.Fbar x q') - s * q' := by
          have : M.lam x * (q' * M.Fbar x q') = q' * v' := by rw [hv']; ring
          rw [this]; nlinarith
        obtain ⟨δ, hδ, hδc⟩ := Metric.continuousOn_iff.mp hc q' hq' _ hhq'
        set q'' := q' + min (δ / 2) ((M.Vbar - q') / 2) with hq''
        have hm1 : 0 < min (δ / 2) ((M.Vbar - q') / 2) := lt_min (by linarith) (by linarith)
        have hm2 : min (δ / 2) ((M.Vbar - q') / 2) ≤ δ / 2 := min_le_left _ _
        have hm3 : min (δ / 2) ((M.Vbar - q') / 2) ≤ (M.Vbar - q') / 2 := min_le_right _ _
        have hq''I : q'' ∈ Icc 0 M.Vbar := ⟨by linarith [hq'.1], by linarith⟩
        have hdist : dist q'' q' < δ := by
          rw [Real.dist_eq, hq'', add_sub_cancel_left, abs_of_pos hm1]; linarith
        have hh := hδc q'' hq''I hdist
        rw [Real.dist_eq] at hh
        have hpos'' : 0 < M.lam x * (q'' * M.Fbar x q'') - s * q'' := by
          have := neg_abs_le (M.lam x * (q'' * M.Fbar x q'') - s * q'' -
            (M.lam x * (q' * M.Fbar x q') - s * q'))
          linarith
        have hq''pos : 0 < q'' := by linarith
        have hbig : s < M.lam x * M.Fbar x q'' := by
          by_contra hc'
          push Not at hc'
          have : M.lam x * (q'' * M.Fbar x q'') ≤ s * q'' := by
            have := mul_le_mul_of_nonneg_left hc' hq''pos.le
            linarith [this]
          linarith
        have hle := le_Rloc M (x := x) hspos.le hq''I
        rw [min_eq_left hbig.le] at hle
        calc q' < q'' := by linarith
          _ = q'' * s / s := by rw [mul_div_assoc, div_self hspos.ne', mul_one]
          _ ≤ M.Rloc x s / s := div_le_div_of_nonneg_right hle hspos.le
    · push Not at hg
      have hq0 : M.Vbar / 2 ∈ Icc 0 M.Vbar := ⟨by linarith, by linarith⟩
      have hle := le_Rloc M (x := x) hspos.le hq0
      have hF := Fbar_pos M hM hx (q := M.Vbar / 2) (by linarith) (by linarith)
      have hpos : 0 < M.Vbar / 2 * min s (M.lam x * M.Fbar x (M.Vbar / 2)) :=
        mul_pos (by linarith) (lt_min hspos (mul_pos hl hF))
      calc q' * min s' v' / s' ≤ 0 := div_nonpos_of_nonpos_of_nonneg hg hs'pos.le
        _ < M.Rloc x s / s := div_pos (lt_of_lt_of_le hpos hle) hspos

end SurgeAuxA3

namespace SurgeAuxP2
open SurgeSpatial.Attraction

lemma U_le_psi (M : Market) (hM : M.Standing) {x : E} (hx : x ∈ M.C) {q s : ℝ}
    (hq : q ∈ Set.Icc 0 M.Vbar) (hs : 0 < s) : M.Ufun x q s ≤ M.psi x s := by
  unfold Market.Ufun Market.psi Market.R
  rw [if_pos hs, if_pos hs]
  have h1 := SurgeAuxA3.le_Rloc M (x := x) hs.le hq
  have e : min 1 (M.lam x * M.Fbar x q / s) = min s (M.lam x * M.Fbar x q) / s := by
    rw [← min_div_div_right hs.le, div_self hs.ne']
  rw [e, mul_assoc, ← mul_div_assoc, mul_div_assoc M.α (M.Rloc x s)]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 hs.le) hM.α_pos.le

end SurgeAuxP2

open SurgeSpatial.Attraction in
theorem solution (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) :
    ∀ᵐ x ∂M.Γ, x ∈ M.C → M.V p T x ≤ M.psi x (M.sT T x) := by
  have hp0 : ∀ y ∈ M.C, 0 ≤ p y := fun y hy => (hpT.2.1 y hy).1
  haveI : IsFiniteMeasure T := hpT.2.2.1.1
  haveI : IsFiniteMeasure M.Γ := hM.finite_Γ
  have hC := SurgeAuxA2.C_meas M hM
  rcases eq_or_ne (M.Γ M.C) 0 with h0 | h0
  · rw [SurgeAuxA2b.Γ_eq_zero M hM h0]; simp
  have hμ : M.Γ.restrict M.C ≠ 0 := SurgeAuxA2.restrict_ne_zero M hC (pos_iff_ne_zero.mpr h0)
  obtain ⟨K, hK⟩ := hM.compact_C.isBounded.exists_norm_le
  -- `V ≤ αV̄` on `C`
  have hVle : ∀ x, M.V p T x ≤ M.α * M.Vbar := by
    intro x
    unfold Market.V Market.VB
    refine SurgeAuxL1.essSup_le_of_ae' hμ (a := -(K + ‖x‖)) ?_ ?_
    · filter_upwards [ae_restrict_mem hC] with y hy
      exact (SurgeAuxL1.Pi_bounds M hM p T hK x hy (hp0 y hy)).1
    · filter_upwards [ae_restrict_mem hC] with y hy
      exact (SurgeAuxL1.Pi_bounds M hM p T hK x hy (hp0 y hy)).2
  have h1 := Measure.ae_rnDeriv_ne_zero_imp_of_ae M.Γ (SurgeAuxA2b.V_le_U_T2 M hM p T hpT)
  filter_upwards [h1] with x hx hxC
  rcases lt_or_ge 0 (M.sT T x) with hs | hs
  · have hne : (T.map Prod.snd).rnDeriv M.Γ x ≠ 0 := by
      intro h; unfold Market.sT at hs; rw [h] at hs; simp at hs
    have hVU := (hx hne).2
    have := SurgeAuxP2.U_le_psi M hM hxC (hpT.2.1 x hxC) hs
    unfold Market.U at hVU
    linarith
  · unfold Market.psi
    rw [if_neg (not_lt.mpr hs)]
    exact hVle x
