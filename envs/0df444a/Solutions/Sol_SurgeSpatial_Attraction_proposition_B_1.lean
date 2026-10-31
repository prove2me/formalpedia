-- Prove2me | solution 1 for SurgeSpatial.Attraction.proposition_B_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:15:56.113011+00:00
-- url     : https://prove2.me/submissions/592c257f-4706-4d89-9daa-d7427664dc10

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

namespace SurgeAuxB3
open SurgeSpatial.Attraction
theorem B3 (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) (L : Set (E × E)) (hL : L ⊆ M.C ×ˢ M.C) (hTL : 0 < T L) :
    ∃ q ∈ L, q.2 ∈ M.IR p T q.1 := by
  have hp0 : ∀ y ∈ M.C, 0 ≤ p y := fun y hy => (hpT.2.1 y hy).1
  haveI : IsFiniteMeasure T := hpT.2.2.1.1
  haveI : IsFiniteMeasure M.Γ := hM.finite_Γ
  have hac : T.map Prod.snd ≪ M.Γ := hpT.2.2.1.2.2.2
  rcases eq_or_ne (M.Γ M.C) 0 with h0 | h0
  · exfalso
    have hΓ := SurgeAuxA2b.Γ_eq_zero M hM h0
    rw [hΓ] at hac
    have hT2 : T.map Prod.snd = 0 := Measure.absolutelyContinuous_zero_iff.mp hac
    have : T Set.univ = 0 := by
      have := congrArg (fun μ : Measure E => μ Set.univ) hT2
      simpa [Measure.map_apply measurable_snd MeasurableSet.univ] using this
    have := measure_mono_null (Set.subset_univ L) this
    exact hTL.ne' this
  · have hC := SurgeAuxA2.C_meas M hM
    have h2 := SurgeAuxA2.U_le_VB M hM M.C hC subset_rfl (pos_iff_ne_zero.mpr h0) p hp0 T
    have h2T : ∀ᵐ q ∂T, q.2 ∈ M.C → M.U p T q.2 ≤ M.V p T q.2 :=
      ae_of_ae_map measurable_snd.aemeasurable (hac.ae_le h2)
    have hgood : ∀ᵐ q ∂T, q.2 ∈ M.IR p T q.1 := by
      filter_upwards [SurgeAuxA2b.V_le_U_T M hM p T hpT, h2T] with q hq hq2
      obtain ⟨⟨_, hq2C⟩, hpi, hle⟩ := hq
      have := hq2 hq2C
      refine ⟨hq2C, ?_⟩
      unfold Market.Pi at hpi
      linarith
    by_contra hne
    push Not at hne
    have : T L = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp hgood)
      intro q hq; exact hne q hq
    exact hTL.ne' this

end SurgeAuxB3
namespace SurgeAuxB1
open SurgeSpatial.Attraction

lemma attr_eq (M : Market) (p : E → ℝ) (T : Measure (E × E)) (z : E) (hz : z ∈ M.C) :
    M.attr p T z = M.C ∩ {x | M.V p T z - ‖z - x‖ = M.V p T x} := by
  ext x; simp [Market.attr, Market.IR, hz]

lemma attr_closed (M : Market) (hM : M.Standing) (p : E → ℝ) (hp0 : ∀ y ∈ M.C, 0 ≤ p y)
    (T : Measure (E × E)) (z : E) (hz : z ∈ M.C) : IsClosed (M.attr p T z) := by
  rw [attr_eq M p T z hz]
  have hc := (SurgeAuxL1.V_lip M hM p hp0 T).continuous
  exact hM.compact_C.isClosed.inter (isClosed_eq (by fun_prop) hc)

lemma attr_segment (M : Market) (hM : M.Standing) (p : E → ℝ) (hp0 : ∀ y ∈ M.C, 0 ≤ p y)
    (T : Measure (E × E)) (z : E) (hz : z ∈ M.C) (x : E) (hx : x ∈ M.attr p T z) :
    ∀ w ∈ segment ℝ x z, w ∈ M.attr p T z := by
  intro w hw
  refine ⟨hM.convex_C.segment_subset hx.1 hz hw, ?_⟩
  exact SurgeAuxL1.IR_segment M hM p hp0 T x z hx.1 hx.2 w hw

end SurgeAuxB1

namespace SurgeAuxRay
open SurgeSpatial.Attraction

lemma ray (M : Market) (hM : M.Standing) (p : E → ℝ) (hp0 : ∀ y ∈ M.C, 0 ≤ p y)
    (T : Measure (E × E)) (z : E) (hz : z ∈ M.C) (a : S1) :
    ∃ t : ℝ, 0 ≤ t ∧ M.Xend p T z a = z + t • (a : E) ∧
      ∀ s : ℝ, 0 ≤ s → (z + s • (a : E) ∈ M.attr p T z ↔ s ≤ t) := by
  have hzA : z ∈ M.attr p T z := ⟨hz, hz, by simp⟩
  have hcl := SurgeAuxB1.attr_closed M hM p hp0 T z hz
  obtain ⟨K, hK⟩ := hM.compact_C.isBounded.exists_norm_le
  have ha : ‖(a : E)‖ = 1 := by simp
  set S := {t : ℝ | 0 ≤ t ∧ z + t • (a : E) ∈ M.attr p T z} with hS
  have hS0 : (0 : ℝ) ∈ S := ⟨le_rfl, by simpa using hzA⟩
  have hSbdd : BddAbove S := by
    refine ⟨K + ‖z‖, fun t ht => ?_⟩
    have h1 := hK _ ht.2.1
    have h2 : ‖t • (a : E)‖ ≤ ‖z + t • (a : E)‖ + ‖z‖ := by
      calc ‖t • (a : E)‖ = ‖(z + t • (a : E)) - z‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    rw [norm_smul, ha, mul_one, Real.norm_of_nonneg ht.1] at h2
    linarith
  have hScl : IsClosed S := by
    have : S = Set.Ici 0 ∩ (fun t : ℝ => z + t • (a : E)) ⁻¹' M.attr p T z := rfl
    rw [this]
    exact isClosed_Ici.inter (hcl.preimage (by fun_prop))
  have hmemS : sSup S ∈ S := hScl.csSup_mem ⟨0, hS0⟩ hSbdd
  set t0 := sSup S with ht0
  refine ⟨t0, hmemS.1, rfl, fun s hs => ⟨fun h => le_csSup hSbdd ⟨hs, h⟩, fun htt => ?_⟩⟩
  rcases eq_or_lt_of_le hmemS.1 with h | h
  · have : s = 0 := by linarith
    subst this; simpa using hzA
  · apply SurgeAuxB1.attr_segment M hM p hp0 T z hz _ hmemS.2
    rw [segment_eq_image']
    refine ⟨1 - s / t0, ⟨by rw [sub_nonneg, div_le_one h]; exact htt,
      by linarith [div_nonneg hs h.le]⟩, ?_⟩
    simp only
    rw [show z - (z + t0 • (a : E)) = (-t0) • (a : E) by simp [neg_smul],
      smul_smul, add_assoc, ← add_smul]
    congr 2
    field_simp
    ring

lemma unit_eq {a b : S1} {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d)
    (h : c • (a : E) = d • (b : E)) : a = b ∧ c = d := by
  have hn := congrArg norm h
  simp only [norm_smul, Real.norm_of_nonneg hc.le, Real.norm_of_nonneg hd] at hn
  have ha : ‖(a : E)‖ = 1 := by simp
  have hb : ‖(b : E)‖ = 1 := by simp
  rw [ha, hb, mul_one, mul_one] at hn
  subst hn
  exact ⟨Subtype.ext (smul_right_injective E hc.ne' h), rfl⟩

lemma mem_seg {z : E} {a : E} {t : ℝ} {x : E} (hx : x ∈ segment ℝ z (z + t • a)) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1, x = z + (θ * t) • a := by
  rw [segment_eq_image'] at hx
  obtain ⟨θ, hθ, rfl⟩ := hx
  exact ⟨θ, hθ, by simp [smul_smul]⟩

end SurgeAuxRay

namespace SurgeAuxPB1
open SurgeSpatial.Attraction

lemma norm_ray (z : E) (e : E) (he : ‖e‖ = 1) (u v : ℝ) :
    ‖(z + u • e) - (z + v • e)‖ = |u - v| := by
  rw [show (z + u • e) - (z + v • e) = (u - v) • e by rw [sub_smul]; abel]
  rw [norm_smul, Real.norm_eq_abs, he, mul_one]

end SurgeAuxPB1

open SurgeSpatial.Attraction in
theorem solution (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) (z : E) (hz : z ∈ M.C) (hsink : M.IsSink p T z) :
    (T ((M.C \ M.attr p T z) ×ˢ M.attr p T z) = 0 ∧
      T (({z} ∪ ⋃ a : S1, (segment ℝ z (M.Xend p T z a) \ {M.Xend p T z a})) ×ˢ
          (((M.C \ M.attr p T z) ∪ Set.range (M.Xend p T z)) \ {z})) = 0) ∧
    (∀ R₁ R₂ : Set S1, Disjoint R₁ R₂ →
      T ((⋃ a ∈ R₁, (segment ℝ z (M.Xend p T z a) \ {z})) ×ˢ
          (⋃ a ∈ R₂, (segment ℝ z (M.Xend p T z a) \ {z}))) = 0) := by
  have hp0 : ∀ y ∈ M.C, 0 ≤ p y := fun y hy => (hpT.2.1 y hy).1
  have hlip := SurgeAuxL1.V_le_add M hM p hp0 T
  have hAC : ∀ x ∈ M.attr p T z, x ∈ M.C := fun x hx => hx.1
  have hAeq : ∀ x ∈ M.attr p T z, M.V p T z - ‖z - x‖ = M.V p T x := fun x hx => hx.2.2
  have hAmk : ∀ x ∈ M.C, M.V p T z - ‖z - x‖ = M.V p T x → x ∈ M.attr p T z :=
    fun x hx h => ⟨hx, hz, h⟩
  have hsk : ∀ y ∈ M.C, y ≠ z → ¬ (M.V p T y - ‖y - z‖ = M.V p T z) := by
    intro y hy hyz h
    exact hsink.2 y hy hyz ⟨hz, hy, h⟩
  have hray := fun a => SurgeAuxRay.ray M hM p hp0 T z hz a
  have hsegA : ∀ a x, x ∈ segment ℝ z (M.Xend p T z a) → x ∈ M.attr p T z := by
    intro a x hx
    obtain ⟨t, ht0, hX, hiff⟩ := hray a
    rw [hX] at hx
    obtain ⟨θ, hθ, rfl⟩ := SurgeAuxRay.mem_seg hx
    exact (hiff _ (mul_nonneg hθ.1 ht0)).2 (by nlinarith [hθ.2, hθ.1])
  have hXA : ∀ a, M.Xend p T z a ∈ M.attr p T z := fun a => hsegA a _ (right_mem_segment _ _ _)
  have key : ∀ L : Set (E × E), L ⊆ M.C ×ˢ M.C →
      (∀ q ∈ L, q.2 ∈ M.IR p T q.1 → False) → T L = 0 := by
    intro L hL h
    by_contra hne
    obtain ⟨q, hq, hIR⟩ := SurgeAuxB3.B3 M hM p T hpT L hL (pos_iff_ne_zero.mpr hne)
    exact h q hq hIR
  have hunit : ∀ a : S1, ‖(a : E)‖ = 1 := fun a => by simp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply key
    · rintro ⟨x, y⟩ ⟨⟨hxC, _⟩, hyA⟩; exact ⟨hxC, hAC y hyA⟩
    · rintro ⟨x, y⟩ ⟨⟨hxC, hxA⟩, hyA⟩ ⟨_, hIR⟩
      apply hxA
      apply hAmk x hxC
      have h1 := hAeq y hyA
      have h2 := hlip z x
      have h3 : ‖z - x‖ ≤ ‖z - y‖ + ‖y - x‖ := norm_sub_le_norm_sub_add_norm_sub z y x
      simp only at hIR
      linarith
  · apply key
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      refine ⟨?_, ?_⟩
      · rcases hx with hx | hx
        · rw [Set.mem_singleton_iff.mp hx]; exact hz
        · obtain ⟨a, ha, _⟩ := Set.mem_iUnion.mp hx; exact hAC _ (hsegA a _ ha)
      · rcases hy.1 with hy | ⟨a, rfl⟩
        · exact hy.1
        · exact hAC _ (hXA a)
    · rintro ⟨x, y⟩ ⟨hx, hy⟩ hIR
      simp only at hIR hx hy
      obtain ⟨hyC, hyeq⟩ := hIR
      have hyz : y ≠ z := hy.2
      have hcase_z : x = z → False := by
        intro hxz; rw [hxz] at hyeq; exact hsk y hyC hyz hyeq
      rcases hx with hx | hx
      · exact hcase_z (Set.mem_singleton_iff.mp hx)
      obtain ⟨a, hxseg, hxne⟩ := Set.mem_iUnion.mp hx
      have hxA := hsegA a x hxseg
      obtain ⟨t, ht0, hX, hiff⟩ := hray a
      rw [hX] at hxseg hxne
      obtain ⟨θ, hθ, hxdef⟩ := SurgeAuxRay.mem_seg hxseg
      set e : E := (a : E) with he_def
      have he : ‖e‖ = 1 := hunit a
      set s := θ * t with hs_def
      have hs0 : 0 ≤ s := mul_nonneg hθ.1 ht0
      have hst : s ≤ t := by nlinarith [hθ.2]
      rcases eq_or_lt_of_le hs0 with hs00 | hspos
      · apply hcase_z; rw [hxdef, ← hs00]; simp
      have hslt : s < t := by
        rcases eq_or_lt_of_le hst with h | h
        · exfalso; apply hxne; rw [hxdef, h]; simp
        · exact h
      set x' := z + t • e with hx'
      have hx'A : x' ∈ M.attr p T z := (hiff t ht0).2 le_rfl
      have n1 : ‖z - x‖ = s := by
        rw [hxdef, show z - (z + s • e) = -(s • e) by abel, norm_neg, norm_smul, he, mul_one,
          Real.norm_of_nonneg hs0]
      have n2 : ‖z - x'‖ = t := by
        rw [hx', show z - (z + t • e) = -(t • e) by abel, norm_neg, norm_smul, he, mul_one,
          Real.norm_of_nonneg ht0]
      have n3 : ‖x - x'‖ = t - s := by
        rw [hxdef, hx', SurgeAuxPB1.norm_ray z e he, abs_of_neg (by linarith)]; ring
      have h1 := hAeq x hxA
      have h2 := hAeq x' hx'A
      have h4 := hlip y x'
      have h5 : ‖y - x'‖ ≤ ‖y - x‖ + ‖x - x'‖ := norm_sub_le_norm_sub_add_norm_sub y x x'
      have hd : dist y x + dist x x' = dist y x' := by
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]; linarith
      have hseg : x ∈ segment ℝ y x' := mem_segment_iff_wbtw.2 (dist_add_dist_eq_iff.1 hd)
      rw [segment_eq_image'] at hseg
      obtain ⟨l, ⟨hl0, hl1⟩, hlx⟩ := hseg
      simp only at hlx
      have hl1' : l < 1 := by
        rcases eq_or_lt_of_le hl1 with h | h
        · exfalso
          rw [h, one_smul, add_sub_cancel] at hlx
          rw [← hlx] at n3; rw [sub_self, norm_zero] at n3; linarith
        · exact h
      have h1l : (0 : ℝ) < 1 - l := by linarith
      set c := (s - l * t) / (1 - l) with hc
      have hyc : y = z + c • e := by
        apply smul_right_injective E h1l.ne'
        simp only
        have hlx' : y + l • (z + t • e - y) = z + s • e := by rw [hlx, hxdef]
        have e1 : (1 - l) • (z + c • e) = (1 - l) • z + (s - l * t) • e := by
          rw [smul_add, smul_smul, hc, mul_div_cancel₀ _ h1l.ne']
        rw [e1]
        linear_combination (norm := module) hlx'
      rcases le_or_gt c 0 with hc0 | hcpos
      · -- `z` lies between `x` and `y`
        have hsc : 0 < s - c := by linarith
        have hzseg : z ∈ segment ℝ x y := by
          rw [segment_eq_image']
          refine ⟨s / (s - c), ⟨div_nonneg hs0 hsc.le, by rw [div_le_one hsc]; linarith⟩, ?_⟩
          have hk : s + s / (s - c) * (c - s) = 0 := by
            rw [div_mul_eq_mul_div, show c - s = -(s - c) by ring, mul_neg, neg_div,
              mul_div_assoc, div_self hsc.ne', mul_one]; ring
          simp only
          rw [hxdef, hyc]
          linear_combination (norm := module) hk • e
        have := SurgeAuxL1.IR_segment M hM p hp0 T x y (hAC x hxA) ⟨hyC, hyeq⟩ z hzseg
        exact hsk y hyC hyz this.2
      · have hcs : c ≤ s := by
          rw [hc, div_le_iff₀ h1l]; nlinarith
        have hyA : y ∈ M.attr p T z := by
          rw [hyc]; exact (hiff c hcpos.le).2 (by linarith)
        rcases hy.1 with hy1 | ⟨b, hb⟩
        · exact hy1.2 hyA
        · obtain ⟨tb, htb0, hXb, _⟩ := hray b
          rw [hXb, hyc] at hb
          have hb' : c • e = tb • (b : E) := by
            exact (add_left_cancel hb).symm
          obtain ⟨hab, hctb⟩ := SurgeAuxRay.unit_eq hcpos htb0 hb'
          subst hab
          rw [hX] at hXb
          have := (SurgeAuxRay.unit_eq (by linarith) htb0 (add_left_cancel hXb)).2
          linarith
  · intro R₁ R₂ hdisj
    apply key
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      obtain ⟨a, _, hxs, _⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨b, _, hys, _⟩ := Set.mem_iUnion₂.mp hy
      exact ⟨hAC _ (hsegA a _ hxs), hAC _ (hsegA b _ hys)⟩
    · rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨_, hIR⟩
      simp only at hIR hx hy
      obtain ⟨a, ha1, hxs, hxz⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨b, hb2, hys, hyz⟩ := Set.mem_iUnion₂.mp hy
      have hxA := hsegA a x hxs
      have hyA := hsegA b y hys
      have h1 := hAeq x hxA
      have h2 := hAeq y hyA
      have hd : dist z y + dist y x = dist z x := by
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]; linarith
      have hyzx : y ∈ segment ℝ z x := mem_segment_iff_wbtw.2 (dist_add_dist_eq_iff.1 hd)
      obtain ⟨ta, hta0, hXa, _⟩ := hray a
      obtain ⟨tb, htb0, hXb, _⟩ := hray b
      rw [hXa] at hxs
      rw [hXb] at hys
      obtain ⟨θ, hθ, hxdef⟩ := SurgeAuxRay.mem_seg hxs
      obtain ⟨φ, hφ, hydef⟩ := SurgeAuxRay.mem_seg hys
      rw [hxdef] at hyzx
      obtain ⟨θ', hθ', hydef'⟩ := SurgeAuxRay.mem_seg hyzx
      have hpos : 0 < θ' * (θ * ta) := by
        rcases eq_or_lt_of_le (mul_nonneg hθ'.1 (mul_nonneg hθ.1 hta0)) with h | h
        · exfalso; apply hyz; simp only [Set.mem_singleton_iff]; rw [hydef', ← h]; simp
        · exact h
      have heq : (θ' * (θ * ta)) • (a : E) = (φ * tb) • (b : E) := by
        have := hydef'.symm.trans hydef
        simpa using this
      obtain ⟨hab, _⟩ := SurgeAuxRay.unit_eq hpos (mul_nonneg hφ.1 htb0) heq
      subst hab
      exact Set.disjoint_left.mp hdisj ha1 hb2
