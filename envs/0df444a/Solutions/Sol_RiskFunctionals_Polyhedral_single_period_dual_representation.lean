-- Prove2me | solution 1 for RiskFunctionals.Polyhedral.single_period_dual_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:44:38.344697+00:00
-- url     : https://prove2.me/submissions/25c092e0-cd5e-4c8c-892e-7a55563424cf

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_SinglePeriod

namespace S202PD

open RiskFunctionals.Polyhedral MeasureTheory Set Filter Topology

/-- The one-dimensional dual feasibility set `{u | c - u w ∈ V*}`. -/
def DS {k : ℕ} (c w : Fin k → ℝ) (V : Set (Fin k → ℝ)) : Set ℝ :=
  {u | ∀ v ∈ V, c ⬝ᵥ v ≤ u * (w ⬝ᵥ v)}

lemma mem_polar_iff {k : ℕ} (c w : Fin k → ℝ) (V : Set (Fin k → ℝ)) (u : ℝ) :
    c - u • w ∈ polarCone V ↔ u ∈ DS c w V := by
  simp only [polarCone, DS, Set.mem_setOf_eq, sub_dotProduct, smul_dotProduct, smul_eq_mul,
    sub_nonpos]

lemma DS_closed {k : ℕ} (c w : Fin k → ℝ) (V : Set (Fin k → ℝ)) : IsClosed (DS c w V) := by
  have : DS c w V = ⋂ v ∈ V, {u : ℝ | c ⬝ᵥ v ≤ u * (w ⬝ᵥ v)} := by ext; simp [DS]
  rw [this]
  exact isClosed_biInter fun v _ => isClosed_le continuous_const
    (continuous_id.mul continuous_const)

lemma DS_convex {k : ℕ} {c w : Fin k → ℝ} {V : Set (Fin k → ℝ)} {u₁ u₂ u : ℝ}
    (h1 : u₁ ∈ DS c w V) (h2 : u₂ ∈ DS c w V) (hu1 : u₁ ≤ u) (hu2 : u ≤ u₂) :
    u ∈ DS c w V := by
  intro v hv
  rcases le_total 0 (w ⬝ᵥ v) with h | h
  · exact (h1 v hv).trans (mul_le_mul_of_nonneg_right hu1 h)
  · exact (h2 v hv).trans (mul_le_mul_of_nonpos_right hu2 h)

/-- cone properties -/
def IsCone' {k : ℕ} (V : Set (Fin k → ℝ)) : Prop :=
  (0 ∈ V) ∧ (∀ v ∈ V, ∀ r : ℝ, 0 ≤ r → r • v ∈ V) ∧ ∀ v ∈ V, ∀ v' ∈ V, v + v' ∈ V

lemma cone_of_poly {k : ℕ} {V : Set (Fin k → ℝ)} (h : IsPolyhedralCone V) : IsCone' V := by
  obtain ⟨m, a, rfl⟩ := h
  refine ⟨fun j => by simp, fun v hv r hr j => ?_, fun v hv v' hv' j => ?_⟩
  · rw [dotProduct_smul, smul_eq_mul]; exact mul_nonpos_of_nonneg_of_nonpos hr (hv j)
  · rw [dotProduct_add]; exact add_nonpos (hv j) (hv' j)

lemma exists_of_inf {k : ℕ} {c w : Fin k → ℝ} {V : Set (Fin k → ℝ)}
    (hV : ∀ v ∈ V, ∀ r : ℝ, 0 ≤ r → r • v ∈ V) {α t δ : ℝ}
    (hα : α ∈ DS c w V) (hlb : ∀ u ∈ DS c w V, α ≤ u) (ht : 0 < t) (hδ : 0 < δ) :
    ∃ v ∈ V, w ⬝ᵥ v = t ∧ α * t - δ ≤ c ⬝ᵥ v := by
  have hd : 0 < δ / t := div_pos hδ ht
  have hnot : α - δ / t ∉ DS c w V := fun h => by
    have := hlb _ h; linarith
  simp only [DS, Set.mem_setOf_eq, not_forall, not_le] at hnot
  obtain ⟨v, hv, hlt⟩ := hnot
  have hwpos : 0 < w ⬝ᵥ v := by
    by_contra hle; push Not at hle
    have h1 := hα v hv
    have : 0 ≤ δ / t * -(w ⬝ᵥ v) := mul_nonneg hd.le (by linarith)
    nlinarith
  refine ⟨(t / (w ⬝ᵥ v)) • v, hV v hv _ (div_pos ht hwpos).le, ?_, ?_⟩
  · rw [dotProduct_smul, smul_eq_mul]; field_simp
  · rw [dotProduct_smul, smul_eq_mul]
    have key : (α - δ / t) * (w ⬝ᵥ v) * (t / (w ⬝ᵥ v)) = α * t - δ := by
      field_simp
    have : (α - δ / t) * (w ⬝ᵥ v) * (t / (w ⬝ᵥ v)) ≤ c ⬝ᵥ v * (t / (w ⬝ᵥ v)) :=
      mul_le_mul_of_nonneg_right hlt.le (div_pos ht hwpos).le
    linarith [mul_comm (t / (w ⬝ᵥ v)) (c ⬝ᵥ v)]

lemma exists_of_sup {k : ℕ} {c w : Fin k → ℝ} {V : Set (Fin k → ℝ)}
    (hV : ∀ v ∈ V, ∀ r : ℝ, 0 ≤ r → r • v ∈ V) {β t δ : ℝ}
    (hβ : β ∈ DS c w V) (hub : ∀ u ∈ DS c w V, u ≤ β) (ht : t < 0) (hδ : 0 < δ) :
    ∃ v ∈ V, w ⬝ᵥ v = t ∧ β * t - δ ≤ c ⬝ᵥ v := by
  have hd : 0 < δ / (-t) := div_pos hδ (by linarith)
  have hnot : β + δ / (-t) ∉ DS c w V := fun h => by
    have := hub _ h; linarith
  simp only [DS, Set.mem_setOf_eq, not_forall, not_le] at hnot
  obtain ⟨v, hv, hlt⟩ := hnot
  have hwneg : w ⬝ᵥ v < 0 := by
    by_contra hle; push Not at hle
    have h1 := hβ v hv
    have : 0 ≤ δ / (-t) * (w ⬝ᵥ v) := mul_nonneg hd.le hle
    nlinarith
  have hpos : 0 < t / (w ⬝ᵥ v) := div_pos_of_neg_of_neg ht hwneg
  refine ⟨(t / (w ⬝ᵥ v)) • v, hV v hv _ hpos.le, ?_, ?_⟩
  · rw [dotProduct_smul, smul_eq_mul]; exact div_mul_cancel₀ t hwneg.ne
  · rw [dotProduct_smul, smul_eq_mul]
    have key : (β + δ / (-t)) * (w ⬝ᵥ v) * (t / (w ⬝ᵥ v)) = β * t - δ := by
      have : t ≠ 0 := ht.ne
      have : w ⬝ᵥ v ≠ 0 := hwneg.ne
      field_simp
      ring
    have : (β + δ / (-t)) * (w ⬝ᵥ v) * (t / (w ⬝ᵥ v)) ≤ c ⬝ᵥ v * (t / (w ⬝ᵥ v)) :=
      mul_le_mul_of_nonneg_right hlt.le hpos.le
    linarith [mul_comm (t / (w ⬝ᵥ v)) (c ⬝ᵥ v)]

lemma ereal_le_of_forall {X : ℝ} {F : EReal}
    (h : ∀ δ : ℝ, 0 < δ → ((X - δ : ℝ) : EReal) ≤ F) : (X : EReal) ≤ F := by
  refine EReal.ge_of_forall_gt_iff_ge.1 fun z hz => ?_
  have hz' : z < X := by exact_mod_cast hz
  have := h (X - z) (by linarith)
  simpa using this

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma plpe {Ym : Ω → ℝ} (hYm : Measurable Ym) (t : ℝ) :
    P.real (Ym ⁻¹' Iio t) + P.real (Ym ⁻¹' {t}) = P.real (Ym ⁻¹' Iic t) := by
  have : Ym ⁻¹' Iic t = Ym ⁻¹' Iio t ∪ Ym ⁻¹' {t} := by rw [← preimage_union, Iio_union_right]
  rw [this, measureReal_union
    ((Set.disjoint_singleton_right.2 (show t ∉ Iio t from lt_irrefl t)).preimage Ym) (hYm (measurableSet_singleton t))]

lemma quantile {Ym : Ω → ℝ} (hYm : Measurable Ym) {γ : ℝ} (h0 : 0 < γ) (h1 : γ < 1) :
    ∃ t, P.real (Ym ⁻¹' Iio t) ≤ γ ∧ γ ≤ P.real (Ym ⁻¹' Iio t) + P.real (Ym ⁻¹' {t}) := by
  set μ : Measure ℝ := P.map Ym with hμ
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hYm.aemeasurable
  set F := ProbabilityTheory.cdf μ with hF
  have hFeq : ∀ s, F s = P.real (Ym ⁻¹' Iic s) := fun s => by
    rw [hF, ProbabilityTheory.cdf_eq_real, hμ, map_measureReal_apply hYm measurableSet_Iic]
  set S := {s : ℝ | γ ≤ F s} with hS
  have hne : S.Nonempty := by
    obtain ⟨s, hs⟩ := ((ProbabilityTheory.tendsto_cdf_atTop μ).eventually (lt_mem_nhds h1)).exists
    exact ⟨s, hs.le⟩
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atBot.1
    ((ProbabilityTheory.tendsto_cdf_atBot μ).eventually (gt_mem_nhds h0))
  have hbdd : BddBelow S := ⟨s₀, fun s hs => by
    by_contra h; push Not at h
    have := hs₀ s h.le
    simp only [hS, Set.mem_setOf_eq] at hs
    linarith⟩
  set t := sInf S with ht
  have hmono : Monotone F := ProbabilityTheory.monotone_cdf μ
  have hFt : γ ≤ F t := by
    have hc : ContinuousWithinAt F (Ioi t) t :=
      (F.right_continuous t).mono Ioi_subset_Ici_self
    refine ge_of_tendsto hc (eventually_nhdsWithin_of_forall fun s hs => ?_)
    obtain ⟨s', hs'S, hs's⟩ := exists_lt_of_csInf_lt hne (show sInf S < s from hs)
    exact le_trans hs'S (hmono hs's.le)
  have hlt : ∀ s < t, F s < γ := fun s hs => by
    by_contra h; push Not at h
    have := csInf_le hbdd (show s ∈ S from h)
    linarith
  have hleft : Function.leftLim F t ≤ γ := by
    rw [hmono.leftLim_eq_sSup]
    refine csSup_le (nonempty_Iio.image _) ?_
    rintro _ ⟨s, hs, rfl⟩
    exact (hlt s hs).le
  have hsing : P.real (Ym ⁻¹' {t}) = F t - Function.leftLim F t := by
    rw [← map_measureReal_apply hYm (measurableSet_singleton t), ← hμ, Measure.real,
      ← ProbabilityTheory.measure_cdf μ, StieltjesFunction.measure_singleton, ← hF,
      ENNReal.toReal_ofReal (sub_nonneg.2 (hmono.leftLim_le le_rfl))]
  have hsum := plpe (P := P) hYm t
  rw [← hFeq] at hsum
  refine ⟨t, ?_, ?_⟩ <;> linarith

lemma tail {Y : Ω → ℝ} (hY : Integrable Y P) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∫ ω, max (Y ω - t) 0 ∂P < ε := by
  have hT : Tendsto (fun n : ℕ => ∫ ω, max (Y ω - ((n : ℝ) + 1)) 0 ∂P) atTop (𝓝 (∫ _ω, (0:ℝ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => |Y ω|) (fun n => ?_) hY.abs
      (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · exact ((hY.sub (integrable_const _)).pos_part).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (abs_nonneg _)
      have := le_abs_self (Y ω); have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
    · obtain ⟨N, hN⟩ := exists_nat_ge (Y ω)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      rw [max_eq_right (by linarith)]
  rw [integral_zero] at hT
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hT).2 ε hε).exists
  exact ⟨(n : ℝ) + 1, by positivity, hn⟩

lemma int_split {Y : Ω → ℝ} (hY : Integrable Y P) (t : ℝ) :
    ∫ ω, Y ω ∂P = t + ∫ ω, max (Y ω - t) 0 ∂P - ∫ ω, max (t - Y ω) 0 ∂P := by
  have h1 : Integrable (fun ω => max (Y ω - t) 0) P := (hY.sub (integrable_const t)).pos_part
  have h2 : Integrable (fun ω => max (t - Y ω) 0) P := ((integrable_const t).sub hY).pos_part
  have : ∀ ω, Y ω = t + max (Y ω - t) 0 - max (t - Y ω) 0 := fun ω => by
    rcases le_total (Y ω) t with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  conv_lhs => rw [show (fun ω => Y ω) = fun ω => t + max (Y ω - t) 0 - max (t - Y ω) 0 from
    funext this]
  rw [integral_sub (by exact (integrable_const t).add h1 :
    Integrable (fun ω => t + max (Y ω - t) 0) P) h2, integral_add (integrable_const t) h1]
  simp

open RiskFunctionals.Polyhedral.SinglePeriodData in
lemma primal_lb (D : SinglePeriodData) (hV₁ : IsCone' D.V₁) {p : ENNReal} (hp : 1 ≤ p)
    {Y : Ω → ℝ} (hY : MemLp Y p P) {a b t u : ℝ}
    (ha : ∀ δ > 0, ∃ v ∈ D.V₁, D.w₁ ⬝ᵥ v = 1 ∧ a - δ ≤ D.c₁ ⬝ᵥ v)
    (hb : ∀ δ > 0, ∃ v ∈ D.V₁, D.w₁ ⬝ᵥ v = -1 ∧ -b - δ ≤ D.c₁ ⬝ᵥ v)
    (hu : ∀ δ > 0, ∃ v ∈ D.V₀, D.w₀ ⬝ᵥ v = t ∧ u * t - δ ≤ D.c₀ ⬝ᵥ v) :
    ((u * t + a * ∫ ω, max (Y ω - t) 0 ∂P - b * ∫ ω, max (t - Y ω) 0 ∂P : ℝ) : EReal) ≤
      D.functional P p Y := by
  set f := fun ω => max (Y ω - t) 0 with hfdef
  set g := fun ω => max (t - Y ω) 0 with hgdef
  have hf : MemLp f p P := (hY.sub (memLp_const t)).pos_part
  have hg : MemLp g p P := ((memLp_const t).sub hY).pos_part
  have hfi : Integrable f P := hf.integrable hp
  have hgi : Integrable g P := hg.integrable hp
  have If : 0 ≤ ∫ ω, f ω ∂P := integral_nonneg fun ω => le_max_right _ _
  have Ig : 0 ≤ ∫ ω, g ω ∂P := integral_nonneg fun ω => le_max_right _ _
  refine ereal_le_of_forall fun δ hδ => ?_
  set K := 1 + ∫ ω, f ω ∂P + ∫ ω, g ω ∂P with hK
  have hKp : 0 < K := by linarith
  have hd : 0 < δ / K := div_pos hδ hKp
  obtain ⟨v₀, hv₀, hw₀, hc₀⟩ := hu (δ / K) hd
  obtain ⟨vp, hvp, hwp, hcp⟩ := ha (δ / K) hd
  obtain ⟨vm, hvm, hwm, hcm⟩ := hb (δ / K) hd
  let v₁ : Ω → Fin D.k₁ → ℝ := fun ω => f ω • vp + g ω • vm
  have hfeas : D.Feasible P p Y v₀ v₁ := by
    refine ⟨?_, hv₀, ?_, ?_⟩
    · refine MemLp.of_eval fun i => ?_
      simp only [v₁, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (hf.mul_const _).add (hg.mul_const _)
    · exact Eventually.of_forall fun ω => hV₁.2.2 _ (hV₁.2.1 _ hvp _ (le_max_right _ _)) _
        (hV₁.2.1 _ hvm _ (le_max_right _ _))
    · refine Eventually.of_forall fun ω => ?_
      simp only [v₁, dotProduct_add, dotProduct_smul, smul_eq_mul, hwp, hw₀, hwm, f, g]
      rcases le_total (Y ω) t with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hint : ∫ ω, D.c₁ ⬝ᵥ v₁ ω ∂P =
      (D.c₁ ⬝ᵥ vp) * ∫ ω, f ω ∂P + (D.c₁ ⬝ᵥ vm) * ∫ ω, g ω ∂P := by
    simp only [v₁, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [integral_add (hfi.mul_const _) (hgi.mul_const _), integral_mul_const, integral_mul_const]
    ring
  have hle : ((D.c₀ ⬝ᵥ v₀ + ∫ ω, D.c₁ ⬝ᵥ v₁ ω ∂P : ℝ) : EReal) ≤ D.functional P p Y :=
    le_sSup ⟨v₀, v₁, hfeas, rfl⟩
  refine le_trans ?_ hle
  rw [hint, EReal.coe_le_coe_iff]
  have e1 : (a - δ / K) * ∫ ω, f ω ∂P ≤ (D.c₁ ⬝ᵥ vp) * ∫ ω, f ω ∂P :=
    mul_le_mul_of_nonneg_right hcp If
  have e2 : (-b - δ / K) * ∫ ω, g ω ∂P ≤ (D.c₁ ⬝ᵥ vm) * ∫ ω, g ω ∂P :=
    mul_le_mul_of_nonneg_right hcm Ig
  have e3 : δ / K * K = δ := div_mul_cancel₀ _ hKp.ne'
  rw [hK] at e3
  nlinarith

open RiskFunctionals.Polyhedral.SinglePeriodData in
lemma dual_bdd (D : SinglePeriodData) {q : ENNReal} {Z : Ω → ℝ} (hZ : Z ∈ D.dualSet P q)
    {M : ℝ} (hM : ∀ u ∈ DS D.c₁ D.w₁ D.V₁, |u| ≤ M) :
    AEStronglyMeasurable Z P ∧ (∀ᵐ ω ∂P, ‖Z ω‖ ≤ M) ∧ Integrable Z P ∧
      (∫ ω, Z ω ∂P) ∈ DS D.c₀ D.w₀ D.V₀ ∧ ∀ᵐ ω ∂P, Z ω ∈ DS D.c₁ D.w₁ D.V₁ := by
  obtain ⟨hZm, hZ0, hZ1⟩ := hZ
  have hZ1' : ∀ᵐ ω ∂P, Z ω ∈ DS D.c₁ D.w₁ D.V₁ :=
    hZ1.mono fun ω h => (mem_polar_iff _ _ _ _).1 h
  have hZb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ M := hZ1'.mono fun ω h => by
    rw [Real.norm_eq_abs]; exact hM _ h
  refine ⟨hZm.1, hZb, ?_, (mem_polar_iff _ _ _ _).1 hZ0, hZ1'⟩
  exact (MemLp.of_bound hZm.1 M hZb : MemLp Z 1 P).integrable le_rfl

open RiskFunctionals.Polyhedral.SinglePeriodData in
lemma weak (D : SinglePeriodData) {p : ENNReal} (hp : 1 ≤ p) {q : ENNReal}
    {Y : Ω → ℝ} (hY : MemLp Y p P) {Z : Ω → ℝ} (hZ : Z ∈ D.dualSet P q)
    {M : ℝ} (hM : ∀ u ∈ DS D.c₁ D.w₁ D.V₁, |u| ≤ M) :
    D.functional P p Y ≤ ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal) := by
  obtain ⟨hZae, hZb, hZi, hZ0, hZ1⟩ := dual_bdd D hZ hM
  apply sSup_le
  rintro x ⟨v₀, v₁, ⟨hv₁, hv₀, hV, hEq⟩, rfl⟩
  rw [EReal.coe_le_coe_iff]
  set s := D.w₀ ⬝ᵥ v₀
  have hv₁i : Integrable v₁ P := hv₁.integrable hp
  have hci : Integrable (fun ω => D.c₁ ⬝ᵥ v₁ ω) P := by
    simp only [dotProduct]
    exact integrable_finset_sum _ fun i _ => (hv₁i.eval i).const_mul _
  have hYi : Integrable Y P := hY.integrable hp
  have hYZ : Integrable (fun ω => Y ω * Z ω) P := hYi.mul_bdd hZae hZb
  have h1 : ∫ ω, D.c₁ ⬝ᵥ v₁ ω ∂P ≤ ∫ ω, (Y ω * Z ω - s * Z ω) ∂P := by
    apply integral_mono_ae hci (hYZ.sub (hZi.const_mul s))
    filter_upwards [hV, hEq, hZ1] with ω h1 h2 h3
    have h4 := h3 _ h1
    have h5 : D.w₁ ⬝ᵥ v₁ ω = Y ω - s := by linarith
    rw [h5] at h4
    show D.c₁ ⬝ᵥ v₁ ω ≤ Y ω * Z ω - s * Z ω
    have : Z ω * (Y ω - s) = Y ω * Z ω - s * Z ω := by ring
    linarith
  rw [integral_sub hYZ (hZi.const_mul s), integral_const_mul] at h1
  have h2 := hZ0 v₀ hv₀
  have : (∫ ω, Z ω ∂P) * s = s * ∫ ω, Z ω ∂P := mul_comm _ _
  linarith

open RiskFunctionals.Polyhedral.SinglePeriodData in
lemma core (D : SinglePeriodData) (q : ENNReal) {Y Ym : Ω → ℝ} (hYm : Measurable Ym)
    (hYY : Y =ᵐ[P] Ym) (hYi : Integrable Y P) {a b t u : ℝ} (hab : a ≤ b)
    (ha : a ∈ DS D.c₁ D.w₁ D.V₁) (hb : b ∈ DS D.c₁ D.w₁ D.V₁) (hu0 : u ∈ DS D.c₀ D.w₀ D.V₀)
    (hlo : a + (b - a) * P.real (Ym ⁻¹' Iio t) ≤ u)
    (hhi : u ≤ a + (b - a) * (P.real (Ym ⁻¹' Iio t) + P.real (Ym ⁻¹' {t}))) :
    ∃ Z ∈ D.dualSet P q, ∫ ω, Y ω * Z ω ∂P =
      u * t + a * ∫ ω, max (Y ω - t) 0 ∂P - b * ∫ ω, max (t - Y ω) 0 ∂P := by
  set pl := P.real (Ym ⁻¹' Iio t) with hpl
  set pe := P.real (Ym ⁻¹' {t}) with hpe
  have hpe0 : 0 ≤ pe := measureReal_nonneg
  set lam : ℝ := if (b - a) * pe = 0 then 0 else (u - a - (b - a) * pl) / ((b - a) * pe)
    with hlam
  have hpos : 0 ≤ (b - a) * pe := mul_nonneg (by linarith) hpe0
  have hlam01 : 0 ≤ lam ∧ lam ≤ 1 := by
    rw [hlam]; split_ifs with h
    · exact ⟨le_rfl, zero_le_one⟩
    · have hp' : 0 < (b - a) * pe := lt_of_le_of_ne hpos (Ne.symm h)
      refine ⟨div_nonneg (by linarith) hp'.le, (div_le_one hp').2 (by linarith)⟩
  have hlamE : a + (b - a) * (pl + lam * pe) = u := by
    rw [hlam]; split_ifs with h
    · have : (b - a) * pl + (b - a) * pe = (b - a) * pl := by rw [h]; ring
      nlinarith
    · have e : (b - a) * ((u - a - (b - a) * pl) / ((b - a) * pe) * pe) =
          (u - a - (b - a) * pl) * (((b - a) * pe) / ((b - a) * pe)) := by ring
      rw [div_self h, mul_one] at e
      rw [mul_add, e]; ring
  have hS1 : MeasurableSet (Ym ⁻¹' Iio t) := hYm measurableSet_Iio
  have hS2 : MeasurableSet (Ym ⁻¹' {t}) := hYm (measurableSet_singleton t)
  set W : Ω → ℝ := fun ω => (Ym ⁻¹' Iio t).indicator 1 ω + lam * (Ym ⁻¹' {t}).indicator 1 ω
    with hW
  set Z : Ω → ℝ := fun ω => a + (b - a) * W ω with hZ
  have hWm : Measurable W :=
    (measurable_one.indicator hS1).add (measurable_const.mul (measurable_one.indicator hS2))
  have hZm : Measurable Z := measurable_const.add (measurable_const.mul hWm)
  have hW01 : ∀ ω, 0 ≤ W ω ∧ W ω ≤ 1 := fun ω => by
    rcases lt_trichotomy (Ym ω) t with h | h | h
    · have h' : Ym ω ≠ t := h.ne
      simp [hW, Set.indicator, h, h']
    · simp [hW, Set.indicator, h, hlam01.1, hlam01.2]
    · have h' : Ym ω ≠ t := h.ne'
      have h'' : ¬ Ym ω < t := not_lt.2 h.le
      simp [hW, Set.indicator, h', h'']
  have hZab : ∀ ω, a ≤ Z ω ∧ Z ω ≤ b := fun ω => by
    obtain ⟨h0, h1⟩ := hW01 ω
    constructor
    · have := mul_nonneg (by linarith : (0:ℝ) ≤ b - a) h0
      simp only [hZ]; linarith
    · have := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ b - a)
      simp only [hZ]; linarith
  have hZbd : ∀ ω, ‖Z ω‖ ≤ |a| + |b| := fun ω => by
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨h0, h1⟩ := hZab ω
    constructor
    · linarith [neg_abs_le a, abs_nonneg b]
    · linarith [le_abs_self b, abs_nonneg a]
  have hZi : Integrable Z P :=
    (MemLp.of_bound hZm.aestronglyMeasurable _ (Eventually.of_forall hZbd) :
      MemLp Z 1 P).integrable le_rfl
  have hWint : ∫ ω, W ω ∂P = pl + lam * pe := by
    have i1 : Integrable (fun ω => (Ym ⁻¹' Iio t).indicator (1 : Ω → ℝ) ω) P :=
      (integrable_const (1:ℝ)).indicator hS1
    have i2 : Integrable (fun ω => lam * (Ym ⁻¹' {t}).indicator (1 : Ω → ℝ) ω) P :=
      ((integrable_const (1:ℝ)).indicator hS2).const_mul lam
    simp only [hW]
    rw [integral_add i1 i2, integral_const_mul,
      integral_indicator_one hS1, integral_indicator_one hS2]
  have hWi : Integrable W P := by
    refine (MemLp.of_bound hWm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_) :
      MemLp W 1 P).integrable le_rfl
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hW01 ω]
  have hZint : ∫ ω, Z ω ∂P = u := by
    simp only [hZ]
    rw [integral_add (integrable_const a) (hWi.const_mul _), integral_const_mul, hWint]
    simp [hlamE]
  refine ⟨Z, ⟨MemLp.of_bound hZm.aestronglyMeasurable _ (Eventually.of_forall hZbd),
    (mem_polar_iff _ _ _ _).2 (hZint ▸ hu0),
    Eventually.of_forall fun ω => (mem_polar_iff _ _ _ _).2
      (DS_convex ha hb (hZab ω).1 (hZab ω).2)⟩, ?_⟩
  have hf : Integrable (fun ω => max (Y ω - t) 0) P := (hYi.sub (integrable_const t)).pos_part
  have hg : Integrable (fun ω => max (t - Y ω) 0) P := ((integrable_const t).sub hYi).pos_part
  have hpt : ∀ᵐ ω ∂P, Y ω * Z ω =
      a * max (Y ω - t) 0 - b * max (t - Y ω) 0 + t * Z ω := by
    filter_upwards [hYY] with ω hω
    rw [hω]
    rcases lt_trichotomy (Ym ω) t with h | h | h
    · have h' : Ym ω ≠ t := h.ne
      simp only [hZ, hW, Set.indicator, Set.mem_preimage, Set.mem_Iio, Set.mem_singleton_iff,
        h, h', if_true, if_false, Pi.one_apply]
      rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [h]; simp
    · have h' : Ym ω ≠ t := h.ne'
      have h'' : ¬ Ym ω < t := not_lt.2 h.le
      simp only [hZ, hW, Set.indicator, Set.mem_preimage, Set.mem_Iio, Set.mem_singleton_iff,
        h', h'', if_false]
      rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have i3 : Integrable (fun ω => a * max (Y ω - t) 0 - b * max (t - Y ω) 0) P :=
    (hf.const_mul a).sub (hg.const_mul b)
  rw [integral_congr_ae hpt, integral_add i3 (hZi.const_mul t), integral_sub (hf.const_mul a) (hg.const_mul b), integral_const_mul,
    integral_const_mul, integral_const_mul, hZint]
  ring

open RiskFunctionals.Polyhedral.SinglePeriodData in
lemma strong (D : SinglePeriodData) (hV₀ : IsCone' D.V₀) (hV₁ : IsCone' D.V₁)
    (hi : D.CompleteRecourse) (hii : D.dualFeasibleSet.Nonempty) {p : ENNReal} (hp : 1 ≤ p)
    (q : ENNReal) {Y : Ω → ℝ} (hY : MemLp Y p P) :
    ∃ Z ∈ D.dualSet P q, ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal) ≤ D.functional P p Y := by
  set D₁ := DS D.c₁ D.w₁ D.V₁ with hD₁
  set D₀ := DS D.c₀ D.w₀ D.V₀ with hD₀
  obtain ⟨vp, hvp, hwp⟩ : (1:ℝ) ∈ (fun v => D.w₁ ⬝ᵥ v) '' D.V₁ := hi ▸ trivial
  obtain ⟨vm, hvm, hwm⟩ : (-1:ℝ) ∈ (fun v => D.w₁ ⬝ᵥ v) '' D.V₁ := hi ▸ trivial
  simp only at hwp hwm
  have hlow : ∀ u ∈ D₁, D.c₁ ⬝ᵥ vp ≤ u := fun u hu => by
    have := hu vp hvp; rw [hwp, mul_one] at this; exact this
  have hup : ∀ u ∈ D₁, u ≤ -(D.c₁ ⬝ᵥ vm) := fun u hu => by
    have := hu vm hvm; rw [hwm] at this; linarith
  obtain ⟨u₀, hu₀0, hu₀1⟩ := hii
  rw [mem_polar_iff] at hu₀0 hu₀1
  have hD₁ne : D₁.Nonempty := ⟨u₀, hu₀1⟩
  have hD₁bb : BddBelow D₁ := ⟨_, hlow⟩
  have hD₁ba : BddAbove D₁ := ⟨_, hup⟩
  set a := sInf D₁ with ha_def
  set b := sSup D₁ with hb_def
  have ha : a ∈ D₁ := (DS_closed _ _ _).csInf_mem hD₁ne hD₁bb
  have hb : b ∈ D₁ := (DS_closed _ _ _).csSup_mem hD₁ne hD₁ba
  have hau : ∀ u ∈ D₁, a ≤ u := fun u hu => csInf_le hD₁bb hu
  have hub : ∀ u ∈ D₁, u ≤ b := fun u hu => le_csSup hD₁ba hu
  have hab : a ≤ b := hau b hb
  have hA : ∀ δ > 0, ∃ v ∈ D.V₁, D.w₁ ⬝ᵥ v = 1 ∧ a - δ ≤ D.c₁ ⬝ᵥ v := fun δ hδ => by
    obtain ⟨v, hv, h1, h2⟩ := exists_of_inf hV₁.2.1 ha hau one_pos hδ
    exact ⟨v, hv, h1, by linarith [h2]⟩
  have hB : ∀ δ > 0, ∃ v ∈ D.V₁, D.w₁ ⬝ᵥ v = -1 ∧ -b - δ ≤ D.c₁ ⬝ᵥ v := fun δ hδ => by
    obtain ⟨v, hv, h1, h2⟩ := exists_of_sup hV₁.2.1 hb hub (by norm_num : (-1:ℝ) < 0) hδ
    exact ⟨v, hv, h1, by linarith [h2]⟩
  have hYi : Integrable Y P := hY.integrable hp
  have hm : AEMeasurable Y P := hY.1.aemeasurable
  set Ym := hm.mk Y with hYmdef
  have hYm : Measurable Ym := hm.measurable_mk
  have hYY : Y =ᵐ[P] Ym := hm.ae_eq_mk
  have fin : ∀ t u : ℝ, u ∈ D₀ →
      (∀ δ > 0, ∃ v ∈ D.V₀, D.w₀ ⬝ᵥ v = t ∧ u * t - δ ≤ D.c₀ ⬝ᵥ v) →
      a + (b - a) * P.real (Ym ⁻¹' Iio t) ≤ u →
      u ≤ a + (b - a) * (P.real (Ym ⁻¹' Iio t) + P.real (Ym ⁻¹' {t})) →
      ∃ Z ∈ D.dualSet P q, ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal) ≤ D.functional P p Y := by
    intro t u hu hψ hlo hhi
    obtain ⟨Z, hZ, hZeq⟩ := core D q hYm hYY hYi hab ha hb hu hlo hhi
    exact ⟨Z, hZ, hZeq ▸ primal_lb D hV₁ hp hY hA hB hψ⟩
  have const_mem : ∀ c : ℝ, c ∈ D₀ → c ∈ D₁ → (fun _ : Ω => c) ∈ D.dualSet P q :=
    fun c h0 h1 => ⟨memLp_const c, (mem_polar_iff _ _ _ _).2 (by simpa using h0),
      Eventually.of_forall fun _ => (mem_polar_iff _ _ _ _).2 h1⟩
  set pl0 := P.real (Ym ⁻¹' Iio 0) with hpl0d
  set pe0 := P.real (Ym ⁻¹' {0}) with hpe0d
  have hpl0 : 0 ≤ pl0 := measureReal_nonneg
  have hpe0 : 0 ≤ pe0 := measureReal_nonneg
  have hple1 : pl0 + pe0 ≤ 1 := by rw [plpe hYm]; exact measureReal_le_one
  set mlo := a + (b - a) * pl0 with hmlo
  set mhi := a + (b - a) * (pl0 + pe0) with hmhi
  have hmlohi : mlo ≤ mhi := by
    have := mul_nonneg (sub_nonneg.2 hab) hpe0; rw [hmlo, hmhi]; nlinarith
  have hamhi : a ≤ mhi := by
    have := mul_nonneg (sub_nonneg.2 hab) (add_nonneg hpl0 hpe0); rw [hmhi]; linarith
  have hψ0 : ∀ u : ℝ, ∀ δ > 0, ∃ v ∈ D.V₀, D.w₀ ⬝ᵥ v = 0 ∧ u * 0 - δ ≤ D.c₀ ⬝ᵥ v :=
    fun u δ hδ => ⟨0, hV₀.1, by simp, by simp; linarith⟩
  by_cases hcase : ∃ u ∈ D₀, mlo ≤ u ∧ u ≤ mhi
  · obtain ⟨u, hu, h1, h2⟩ := hcase
    exact fin 0 u hu (hψ0 u) h1 h2
  push Not at hcase
  have hD₀ne : D₀.Nonempty := ⟨u₀, hu₀0⟩
  have hIinteg : ∀ t, 0 ≤ ∫ ω, max (Y ω - t) 0 ∂P ∧ 0 ≤ ∫ ω, max (t - Y ω) 0 ∂P := fun t =>
    ⟨integral_nonneg fun ω => le_max_right _ _, integral_nonneg fun ω => le_max_right _ _⟩
  rcases lt_or_ge mhi u₀ with hB1 | hB2
  · have hall : ∀ u ∈ D₀, mhi < u := fun u hu => by
      by_contra hle; push Not at hle
      have hm : mhi ∈ D₀ := DS_convex hu hu₀0 hle hB1.le
      exact lt_irrefl _ (hcase mhi hm hmlohi)
    have hbb : BddBelow D₀ := ⟨mhi, fun u hu => (hall u hu).le⟩
    set α := sInf D₀ with hαd
    have hα : α ∈ D₀ := (DS_closed _ _ _).csInf_mem hD₀ne hbb
    have hαlb : ∀ u ∈ D₀, α ≤ u := fun u hu => csInf_le hbb hu
    have hαgt : mhi < α := hall α hα
    have hαb : α ≤ b := (hαlb u₀ hu₀0).trans (hub u₀ hu₀1)
    have hψ : ∀ t > 0, ∀ δ > 0, ∃ v ∈ D.V₀, D.w₀ ⬝ᵥ v = t ∧ α * t - δ ≤ D.c₀ ⬝ᵥ v :=
      fun t ht δ hδ => exists_of_inf hV₀.2.1 hα hαlb ht hδ
    rcases lt_or_eq_of_le hαb with hlt | heq
    · have hba : 0 < b - a := by linarith
      set γ := (α - a) / (b - a) with hγd
      have hγe : (b - a) * γ = α - a := mul_div_cancel₀ _ hba.ne'
      have hγ1 : γ < 1 := (div_lt_one hba).2 (by linarith)
      have hγ0 : pl0 + pe0 < γ := by
        by_contra h; push Not at h
        have := mul_le_mul_of_nonneg_left h hba.le
        linarith
      obtain ⟨t, h1, h2⟩ := quantile (P := P) hYm (by linarith : 0 < γ) hγ1
      have ht : 0 < t := by
        by_contra hle; push Not at hle
        have := measureReal_mono (μ := P)
          (preimage_mono (Iic_subset_Iic.2 hle) : Ym ⁻¹' Iic t ⊆ Ym ⁻¹' Iic 0)
        rw [← plpe hYm, ← plpe hYm] at this
        linarith
      refine fin t α hα (hψ t ht) ?_ ?_
      · have := mul_le_mul_of_nonneg_left h1 hba.le; linarith
      · have := mul_le_mul_of_nonneg_left h2 hba.le; linarith
    · refine ⟨fun _ => b, const_mem b (heq ▸ hα) hb, ?_⟩
      rw [integral_mul_const]
      refine ereal_le_of_forall fun δ hδ => ?_
      have hK : 0 < b - a + 1 := by linarith
      obtain ⟨t, ht, htail⟩ := tail hYi (div_pos hδ hK)
      have hlb := primal_lb D hV₁ hp hY hA hB (hψ t ht)
      refine le_trans ?_ hlb
      rw [EReal.coe_le_coe_iff, heq, int_split hYi t]
      have h3 := (lt_div_iff₀ hK).1 htail
      have h4 := (hIinteg t).1
      nlinarith
  · have hu₀lt : u₀ < mlo := by
      by_contra hle; push Not at hle
      have := hcase u₀ hu₀0 hle; linarith
    have hall : ∀ u ∈ D₀, u < mlo := fun u hu => by
      by_contra hle; push Not at hle
      have hm : mlo ∈ D₀ := DS_convex hu₀0 hu hu₀lt.le hle
      have := hcase mlo hm le_rfl; linarith
    have hba : BddAbove D₀ := ⟨mlo, fun u hu => (hall u hu).le⟩
    set β := sSup D₀ with hβd
    have hβ : β ∈ D₀ := (DS_closed _ _ _).csSup_mem hD₀ne hba
    have hβub : ∀ u ∈ D₀, u ≤ β := fun u hu => le_csSup hba hu
    have hβlt : β < mlo := hall β hβ
    have haβ : a ≤ β := (hau u₀ hu₀1).trans (hβub u₀ hu₀0)
    have hψ : ∀ t < 0, ∀ δ > 0, ∃ v ∈ D.V₀, D.w₀ ⬝ᵥ v = t ∧ β * t - δ ≤ D.c₀ ⬝ᵥ v :=
      fun t ht δ hδ => exists_of_sup hV₀.2.1 hβ hβub ht hδ
    rcases lt_or_eq_of_le haβ with hlt | heq
    · have hba' : 0 < b - a := by
        by_contra h; push Not at h
        have : (b - a) * pl0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hpl0
        linarith
      set γ := (β - a) / (b - a) with hγd
      have hγe : (b - a) * γ = β - a := mul_div_cancel₀ _ hba'.ne'
      have hγ0 : 0 < γ := div_pos (by linarith) hba'
      have hγpl : γ < pl0 := by
        by_contra h; push Not at h
        have := mul_le_mul_of_nonneg_left h hba'.le
        linarith
      obtain ⟨t, h1, h2⟩ := quantile (P := P) hYm hγ0 (by linarith)
      have ht : t < 0 := by
        by_contra hle; push Not at hle
        have := measureReal_mono (μ := P)
          (preimage_mono (Iio_subset_Iio hle) : Ym ⁻¹' Iio 0 ⊆ Ym ⁻¹' Iio t)
        linarith
      refine fin t β hβ (hψ t ht) ?_ ?_
      · have := mul_le_mul_of_nonneg_left h1 hba'.le; linarith
      · have := mul_le_mul_of_nonneg_left h2 hba'.le; linarith
    · refine ⟨fun _ => a, const_mem a (heq ▸ hβ) ha, ?_⟩
      rw [integral_mul_const]
      refine ereal_le_of_forall fun δ hδ => ?_
      have hK : 0 < b - a + 1 := by linarith
      obtain ⟨s, hs, htail⟩ := tail hYi.neg (div_pos hδ hK)
      have e : ∀ ω, (-Y) ω - s = -s - Y ω := fun ω => by simp only [Pi.neg_apply]; ring
      simp_rw [e] at htail
      have hlb := primal_lb D hV₁ hp hY hA hB (hψ (-s) (by linarith))
      refine le_trans ?_ hlb
      rw [EReal.coe_le_coe_iff, ← heq, int_split hYi (-s)]
      have h3 := (lt_div_iff₀ hK).1 htail
      have h4 := (hIinteg (-s)).2
      nlinarith

open RiskFunctionals.Polyhedral.SinglePeriodData in
lemma bound_exists (D : SinglePeriodData) (hi : D.CompleteRecourse) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ DS D.c₁ D.w₁ D.V₁, |u| ≤ M := by
  obtain ⟨vp, hvp, hwp⟩ : (1:ℝ) ∈ (fun v => D.w₁ ⬝ᵥ v) '' D.V₁ := hi ▸ trivial
  obtain ⟨vm, hvm, hwm⟩ : (-1:ℝ) ∈ (fun v => D.w₁ ⬝ᵥ v) '' D.V₁ := hi ▸ trivial
  simp only at hwp hwm
  refine ⟨|D.c₁ ⬝ᵥ vp| + |D.c₁ ⬝ᵥ vm|, by positivity, fun u hu => ?_⟩
  have h1 := hu vp hvp; rw [hwp, mul_one] at h1
  have h2 := hu vm hvm; rw [hwm] at h2
  rw [abs_le]; constructor
  · linarith [neg_abs_le (D.c₁ ⬝ᵥ vp), abs_nonneg (D.c₁ ⬝ᵥ vm)]
  · linarith [neg_abs_le (D.c₁ ⬝ᵥ vm), abs_nonneg (D.c₁ ⬝ᵥ vp)]

open RiskFunctionals.Polyhedral.SinglePeriodData in
lemma package (D : SinglePeriodData) (hV₀ : IsCone' D.V₀) (hV₁ : IsCone' D.V₁)
    (hi : D.CompleteRecourse) (hii : D.dualFeasibleSet.Nonempty) {p : ENNReal} (hp : 1 ≤ p)
    (q : ENNReal) {M : ℝ} (hM : ∀ u ∈ DS D.c₁ D.w₁ D.V₁, |u| ≤ M) {Y : Ω → ℝ}
    (hY : MemLp Y p P) :
    ∃ Z ∈ D.dualSet P q, (D.functional P p Y).toReal = ∫ ω, Y ω * Z ω ∂P ∧
      D.functional P p Y = ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal) ∧
      ∀ Z' ∈ D.dualSet P q, ∫ ω, Y ω * Z ω ∂P ≤ ∫ ω, Y ω * Z' ω ∂P := by
  obtain ⟨Z, hZ, hle⟩ := strong D hV₀ hV₁ hi hii hp q hY
  have heq : D.functional P p Y = ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal) :=
    le_antisymm (weak D hp hY hZ hM) hle
  refine ⟨Z, hZ, by rw [heq]; rfl, heq, fun Z' hZ' => ?_⟩
  have := weak D hp hY hZ' hM
  rw [heq] at this
  exact EReal.coe_le_coe_iff.1 this

end S202PD

open RiskFunctionals.Polyhedral MeasureTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (D : SinglePeriodData) (hD : D.IsPolyhedral)
    (hV₀ : IsPolyhedralCone D.V₀) (hV₁ : IsPolyhedralCone D.V₁)
    (hi : D.CompleteRecourse) (hii : D.dualFeasibleSet.Nonempty) :
    (∀ Y : Ω → ℝ, MemLp Y p P → D.functional P p Y ≠ ⊥ ∧ D.functional P p Y ≠ ⊤) ∧
    ConcaveOnLp P p (fun Y => (D.functional P p Y).toReal) ∧
    ContinuousOnLp P p (fun Y => (D.functional P p Y).toReal) ∧
    (∀ Y : Ω → ℝ, MemLp Y p P →
      D.functional P p Y =
        sInf {x : EReal | ∃ Z ∈ D.dualSet P q, x = ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal)}) ∧
    (D.dualSet P q ⊆ {Z : Ω → ℝ | (∀ᵐ ω ∂P, 0 ≤ Z ω) ∧ ∫ ω, Z ω ∂P = 1} →
      IsAcceptabilityFunctional P p (fun Y => (D.functional P p Y).toReal)) := by
  have c0 := S202PD.cone_of_poly hV₀
  have c1 := S202PD.cone_of_poly hV₁
  obtain ⟨M, hM0, hM⟩ := S202PD.bound_exists D hi
  have pk : ∀ Y : Ω → ℝ, MemLp Y p P → _ := fun Y hY =>
    S202PD.package (P := P) D c0 c1 hi hii hp q hM hY
  have hint : ∀ Y : Ω → ℝ, MemLp Y p P → ∀ Z ∈ D.dualSet P q,
      Integrable (fun ω => Y ω * Z ω) P := fun Y hY Z hZ => by
    obtain ⟨h1, h2, -⟩ := S202PD.dual_bdd D hZ hM
    exact (hY.integrable hp).mul_bdd h1 h2
  have conc : ConcaveOnLp P p (fun Y => (D.functional P p Y).toReal) := by
    intro Y₁ Y₂ h1 h2 lam hl0 hl1
    have h3 : MemLp (lam • Y₁ + (1 - lam) • Y₂) p P := (h1.const_smul lam).add (h2.const_smul _)
    obtain ⟨Z, hZ, e3, -, -⟩ := pk _ h3
    obtain ⟨Z1, hZ1, e1, -, m1⟩ := pk _ h1
    obtain ⟨Z2, hZ2, e2, -, m2⟩ := pk _ h2
    simp only
    rw [e1, e2, e3]
    have i1 := m1 Z hZ
    have i2 := m2 Z hZ
    have hsplit : ∫ ω, (lam • Y₁ + (1 - lam) • Y₂) ω * Z ω ∂P =
        lam * ∫ ω, Y₁ ω * Z ω ∂P + (1 - lam) * ∫ ω, Y₂ ω * Z ω ∂P := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
      rw [integral_add ((hint _ h1 Z hZ).const_mul lam) ((hint _ h2 Z hZ).const_mul _),
        integral_const_mul, integral_const_mul]
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left i1 hl0
    have := mul_le_mul_of_nonneg_left i2 (by linarith : (0:ℝ) ≤ 1 - lam)
    linarith
  refine ⟨fun Y hY => ?_, conc, ?_, fun Y hY => ?_, fun hsub => ⟨?_, conc, ?_⟩⟩
  · obtain ⟨Z, hZ, -, e, -⟩ := pk _ hY
    rw [e]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  · intro Y hY ε hε
    refine ⟨ε / (M + 1), div_pos hε (by linarith), fun Y' hY' hd => ?_⟩
    obtain ⟨Z, hZ, e, -, m⟩ := pk _ hY
    obtain ⟨Z', hZ', e', -, m'⟩ := pk _ hY'
    simp only
    rw [e, e']
    have hD : MemLp (Y' - Y) p P := hY'.sub hY
    have hL1 : ∫ ω, |(Y' - Y) ω| ∂P < ε / (M + 1) := by
      have h1 : eLpNorm (Y' - Y) 1 P ≤ eLpNorm (Y' - Y) p P :=
        eLpNorm_le_eLpNorm_of_exponent_le hp hD.1
      have h2 : ∫ ω, |(Y' - Y) ω| ∂P = (eLpNorm (Y' - Y) 1 P).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hD.1]
        simp only [Real.norm_eq_abs]
      rw [h2]
      exact ENNReal.toReal_lt_of_lt_ofReal (h1.trans_lt hd)
    have hb : ∀ Z ∈ D.dualSet P q, |∫ ω, Y' ω * Z ω ∂P - ∫ ω, Y ω * Z ω ∂P| ≤
        M * ∫ ω, |(Y' - Y) ω| ∂P := by
      intro Z hZ
      obtain ⟨hZae, hZb, -⟩ := S202PD.dual_bdd D hZ hM
      rw [← integral_sub (hint _ hY' Z hZ) (hint _ hY Z hZ), ← integral_const_mul,
        ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hD.integrable hp).abs.const_mul M) ?_
      filter_upwards [hZb] with ω hω
      rw [Real.norm_eq_abs] at hω ⊢
      rw [← sub_mul, abs_mul, Pi.sub_apply, mul_comm]
      exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
    have h1 := hb Z hZ
    have h2 := hb Z' hZ'
    have i1 := m Z' hZ'
    have i2 := m' Z hZ
    have hL0 : 0 ≤ ∫ ω, |(Y' - Y) ω| ∂P := integral_nonneg fun _ => abs_nonneg _
    have hML : M * ∫ ω, |(Y' - Y) ω| ∂P < ε := by
      have := (lt_div_iff₀ (by linarith : (0:ℝ) < M + 1)).1 hL1
      nlinarith
    rw [abs_le] at h1 h2
    rw [abs_sub_lt_iff]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · obtain ⟨Z, hZ, -, e, m⟩ := pk _ hY
    rw [e]
    apply le_antisymm
    · exact le_sInf (by rintro x ⟨Z', hZ', rfl⟩; exact EReal.coe_le_coe_iff.2 (m Z' hZ'))
    · exact sInf_le ⟨Z, hZ, rfl⟩
  · intro Y hY c
    have hYc : MemLp (fun ω => Y ω + c) p P := hY.add (memLp_const c)
    obtain ⟨Z, hZ, e, -, m⟩ := pk _ hY
    obtain ⟨Zc, hZc, ec, -, mc⟩ := pk _ hYc
    rw [e, ec]
    have hZ1 : ∀ Z ∈ D.dualSet P q,
        ∫ ω, (Y ω + c) * Z ω ∂P = ∫ ω, Y ω * Z ω ∂P + c := fun Z hZ => by
      have hZi := (S202PD.dual_bdd D hZ hM).2.2.1
      simp only [add_mul]
      rw [integral_add (hint _ hY Z hZ) (hZi.const_mul c), integral_const_mul, (hsub hZ).2,
        mul_one]
    have i1 := mc Z hZ
    have i2 := m Zc hZc
    rw [hZ1 Z hZ] at i1
    rw [hZ1 Zc hZc] at i1 ⊢
    linarith
  · intro Y₁ Y₂ h1 h2 hle
    obtain ⟨Z1, hZ1, e1, -, m1⟩ := pk _ h1
    obtain ⟨Z2, hZ2, e2, -, m2⟩ := pk _ h2
    rw [e1, e2]
    refine (m1 Z2 hZ2).trans (integral_mono_ae (hint _ h1 _ hZ2) (hint _ h2 _ hZ2) ?_)
    filter_upwards [hle, (hsub hZ2).1] with ω h h'
    exact mul_le_mul_of_nonneg_right h h'
