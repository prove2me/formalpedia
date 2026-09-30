-- Prove2me | solution 1 for RevenueManagement.base_stock_posted_price
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T23:49:45.995018+00:00
-- url     : https://prove2.me/submissions/acafb740-0865-4a9d-bfdc-d55131e1ecf3

import Definitions.Def_RevenueManagement_dynamicPricing

open MeasureTheory Set

namespace RevenueManagement

variable {Ω : Type*} [MeasurableSpace Ω]

lemma rp_cont {W : ℝ → ℝ} (hW : ConcaveOn ℝ univ W) : Continuous W := by
  have := hW.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.mp this

lemma rp_cont_cvx {W : ℝ → ℝ} (hW : ConvexOn ℝ univ W) : Continuous W := by
  have := hW.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.mp this

lemma rp_U_concave (M : ReplPricing Ω) (hM : M.IsModel) {W : ℝ → ℝ}
    (hW : ConcaveOn ℝ univ W) (t : ℕ) : ConcaveOn ℝ univ (fun u => W u - M.h t u) :=
  hW.sub (hM.2.2.2.2.2 t).1

/-- The continuation value `E[W(y − D(t, d, ξ)) − h_t(y − D(t, d, ξ))]` for a value `W`. -/
noncomputable def rpG (M : ReplPricing Ω) (W : ℝ → ℝ) (t : ℕ) (y d : ℝ) : ℝ :=
  ∫ ω, (W (y - M.D t d ω) - M.h t (y - M.D t d ω)) ∂M.P

lemma rp_integrable (M : ReplPricing Ω) (hM : M.IsModel) {W : ℝ → ℝ}
    (hW : ConcaveOn ℝ univ W) (t : ℕ) (y d : ℝ) :
    Integrable (fun ω => W (y - M.D t d ω) - M.h t (y - M.D t d ω)) M.P := by
  have := hM.1
  obtain ⟨ha, hb, K, hK⟩ := hM.2.2.1 t
  have hUc : Continuous (fun u => W u - M.h t u) :=
    (rp_cont hW).sub (rp_cont_cvx (hM.2.2.2.2.2 t).1)
  have hmeas : Measurable (fun ω => y - M.D t d ω) := by
    show Measurable (fun ω => y - (M.a t ω * d + M.b t ω))
    exact measurable_const.sub ((ha.mul_const d).add hb)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := y - (K * |d| + K)) (b := y + (K * |d| + K))).exists_bound_of_continuousOn hUc.continuousOn
  have hu : ∀ ω, y - M.D t d ω ∈ Icc (y - (K * |d| + K)) (y + (K * |d| + K)) := by
    intro ω
    obtain ⟨h0, h1, h2⟩ := hK ω
    have e1 : |M.a t ω * d| ≤ K * |d| := by
      rw [abs_mul, abs_of_nonneg h0]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg d)
    have e2 := abs_le.mp e1
    have e3 := abs_le.mp h2
    simp only [ReplPricing.D, mem_Icc]
    constructor <;> linarith [e2.1, e2.2, e3.1, e3.2]
  exact Integrable.of_bound (hUc.measurable.comp hmeas).aestronglyMeasurable C
    (ae_of_all _ fun ω => hC _ (hu ω))

lemma rp_G_concave (M : ReplPricing Ω) (hM : M.IsModel) {W : ℝ → ℝ}
    (hW : ConcaveOn ℝ univ W) (t : ℕ) :
    ConcaveOn ℝ univ (fun yd : ℝ × ℝ => rpG M W t yd.1 yd.2) := by
  refine ⟨convex_univ, fun p _ q _ α β hα hβ hαβ => ?_⟩
  have hU := rp_U_concave M hM hW t
  have h1 := rp_integrable M hM hW t p.1 p.2
  have h2 := rp_integrable M hM hW t q.1 q.2
  have h3 := rp_integrable M hM hW t (α * p.1 + β * q.1) (α * p.2 + β * q.2)
  simp only [smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  calc α * rpG M W t p.1 p.2 + β * rpG M W t q.1 q.2
      = ∫ ω, (α * (W (p.1 - M.D t p.2 ω) - M.h t (p.1 - M.D t p.2 ω)) +
          β * (W (q.1 - M.D t q.2 ω) - M.h t (q.1 - M.D t q.2 ω))) ∂M.P := by
        unfold rpG
        rw [integral_add (h1.const_mul α) (h2.const_mul β), integral_const_mul,
          integral_const_mul]
    _ ≤ ∫ ω, (W ((α * p.1 + β * q.1) - M.D t (α * p.2 + β * q.2) ω) -
          M.h t ((α * p.1 + β * q.1) - M.D t (α * p.2 + β * q.2) ω)) ∂M.P := by
        refine integral_mono ((h1.const_mul α).add (h2.const_mul β)) h3 fun ω => ?_
        have := hU.2 (mem_univ (p.1 - M.D t p.2 ω)) (mem_univ (q.1 - M.D t q.2 ω)) hα hβ hαβ
        have e : α • (p.1 - M.D t p.2 ω) + β • (q.1 - M.D t q.2 ω) =
            (α * p.1 + β * q.1) - M.D t (α * p.2 + β * q.2) ω := by
          simp only [smul_eq_mul, ReplPricing.D]
          linear_combination (-(M.b t ω)) * hαβ
        rw [e] at this
        simpa only [smul_eq_mul] using this
    _ = rpG M W t (α * p.1 + β * q.1) (α * p.2 + β * q.2) := rfl

lemma rp_G_le (M : ReplPricing Ω) (hM : M.IsModel) {W : ℝ → ℝ} (hW : ConcaveOn ℝ univ W)
    {B : ℝ} (hB : ∀ x, W x ≤ B) (t : ℕ) (y d : ℝ) : rpG M W t y d ≤ B := by
  have := hM.1
  unfold rpG
  calc ∫ ω, (W (y - M.D t d ω) - M.h t (y - M.D t d ω)) ∂M.P ≤ ∫ _ω, B ∂M.P :=
        integral_mono (rp_integrable M hM hW t y d) (integrable_const B) fun ω => by
          have := (hM.2.2.2.2.2 t).2 (y - M.D t d ω)
          have := hB (y - M.D t d ω)
          show W (y - M.D t d ω) - M.h t (y - M.D t d ω) ≤ B
          linarith
    _ = B := by simp

/-- Increments of a concave function over intervals of equal length decrease. -/
lemma rp_U_incr {U : ℝ → ℝ} (hU : ConcaveOn ℝ univ U) (u δ s : ℝ) (hδ : 0 ≤ δ) (hs : 0 ≤ s) :
    U (u - δ) + U (u + s) ≤ U u + U (u + s - δ) := by
  rcases hδ.lt_or_eq with hδ | hδ
  · rcases hs.lt_or_eq with hs | hs
    · have hL : 0 < s + δ := by linarith
      have hsum : s / (s + δ) + δ / (s + δ) = 1 := by field_simp
      have hsum' : δ / (s + δ) + s / (s + δ) = 1 := by rw [add_comm]; exact hsum
      have c1 := hU.2 (mem_univ (u - δ)) (mem_univ (u + s)) (div_nonneg hs.le hL.le)
        (div_nonneg hδ.le hL.le) hsum
      have c2 := hU.2 (mem_univ (u - δ)) (mem_univ (u + s)) (div_nonneg hδ.le hL.le)
        (div_nonneg hs.le hL.le) hsum'
      have e1 : (s / (s + δ)) • (u - δ) + (δ / (s + δ)) • (u + s) = u := by
        simp only [smul_eq_mul]; field_simp; ring
      have e2 : (δ / (s + δ)) • (u - δ) + (s / (s + δ)) • (u + s) = u + s - δ := by
        simp only [smul_eq_mul]; field_simp; ring
      rw [e1] at c1
      rw [e2] at c2
      simp only [smul_eq_mul] at c1 c2
      have hβ : δ / (s + δ) = 1 - s / (s + δ) := by linarith
      rw [hβ] at c1 c2
      linarith
    · subst hs; simp only [add_zero]; linarith
  · subst hδ; simp only [sub_zero]; linarith

lemma rp_G_super (M : ReplPricing Ω) (hM : M.IsModel) {W : ℝ → ℝ} (hW : ConcaveOn ℝ univ W)
    (t : ℕ) {y y' d d' : ℝ} (hy : y ≤ y') (hd : d ≤ d') :
    rpG M W t y d' - rpG M W t y d ≤ rpG M W t y' d' - rpG M W t y' d := by
  have hU := rp_U_concave M hM hW t
  obtain ⟨-, -, K, hK⟩ := hM.2.2.1 t
  have i1 := rp_integrable M hM hW t y d'
  have i2 := rp_integrable M hM hW t y d
  have i3 := rp_integrable M hM hW t y' d'
  have i4 := rp_integrable M hM hW t y' d
  unfold rpG
  rw [← integral_sub i1 i2, ← integral_sub i3 i4]
  refine integral_mono (i1.sub i2) (i3.sub i4) fun ω => ?_
  have h0 := (hK ω).1
  have := rp_U_incr hU (y - M.D t d ω) (M.a t ω * (d' - d)) (y' - y)
    (mul_nonneg h0 (sub_nonneg.mpr hd)) (sub_nonneg.mpr hy)
  have e1 : y - M.D t d ω - M.a t ω * (d' - d) = y - M.D t d' ω := by
    simp only [ReplPricing.D]; ring
  have e2 : y - M.D t d ω + (y' - y) = y' - M.D t d ω := by ring
  have e3 : y - M.D t d ω + (y' - y) - M.a t ω * (d' - d) = y' - M.D t d' ω := by
    simp only [ReplPricing.D]; ring
  rw [e3, e1, e2] at this
  show W (y - M.D t d' ω) - M.h t (y - M.D t d' ω) - (W (y - M.D t d ω) - M.h t (y - M.D t d ω))
    ≤ W (y' - M.D t d' ω) - M.h t (y' - M.D t d' ω) - (W (y' - M.D t d ω) - M.h t (y' - M.D t d ω))
  linarith

lemma rp_sup_comb {S1 S2 : Set ℝ} (h1 : S1.Nonempty) (h2 : S2.Nonempty) {a b M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ∀ u ∈ S1, ∀ v ∈ S2, a * u + b * v ≤ M) :
    a * sSup S1 + b * sSup S2 ≤ M := by
  have step : ∀ (S : Set ℝ), S.Nonempty → ∀ c N : ℝ, 0 ≤ c → (∀ u ∈ S, c * u ≤ N) →
      c * sSup S ≤ N := by
    intro S hS c N hc hu
    rcases hc.lt_or_eq with hc | hc
    · have hle : sSup S ≤ N / c := csSup_le hS fun u hu' => by
        rw [le_div_iff₀ hc, mul_comm]; exact hu u hu'
      calc c * sSup S ≤ c * (N / c) := mul_le_mul_of_nonneg_left hle hc.le
        _ = N := by field_simp
    · obtain ⟨u, hu'⟩ := hS
      have := hu u hu'
      rw [← hc] at this ⊢
      linarith
  have hv : ∀ v ∈ S2, b * v ≤ M - a * sSup S1 := fun v hv => by
    have := step S1 h1 a (M - b * v) ha fun u hu => by linarith [h u hu v hv]
    linarith
  have := step S2 h2 b (M - a * sSup S1) hb hv
  linarith

/-- The value function with any number of periods to go is concave and bounded above. -/
lemma rp_good (M : ReplPricing Ω) (hM : M.IsModel) :
    ∀ k, ConcaveOn ℝ univ (M.valueGo k) ∧ ∃ B, ∀ x, M.valueGo k x ≤ B := by
  intro k
  induction k with
  | zero =>
    have e : M.valueGo 0 = fun _ => 0 := funext fun x => ReplPricing.valueGo.eq_1 M x
    rw [e]
    exact ⟨concaveOn_const 0 convex_univ, 0, fun _ => le_rfl⟩
  | succ k ih =>
    obtain ⟨hW, B, hB⟩ := ih
    obtain ⟨hrc, hrcont⟩ := hM.2.2.2.1 (M.T - k)
    obtain ⟨R, hR⟩ : ∃ R, ∀ d ∈ Icc 0 M.dbar, M.r (M.T - k) d ≤ R := by
      obtain ⟨R, hR⟩ := isCompact_Icc.bddAbove_image hrcont
      exact ⟨R, fun d hd => hR (mem_image_of_mem _ hd)⟩
    have hc := hM.2.2.2.2.1 (M.T - k)
    let φ : ℝ → ℝ × ℝ → ℝ := fun x yd => M.r (M.T - k) yd.2 - M.c (M.T - k) * (yd.1 - x) +
      rpG M (M.valueGo k) (M.T - k) yd.1 yd.2
    have hval : ∀ x, M.valueGo (k + 1) x =
        sSup (φ x '' {yd : ℝ × ℝ | x ≤ yd.1 ∧ yd.2 ∈ Icc 0 M.dbar}) := fun x => rfl
    have hne : ∀ x, (φ x '' {yd : ℝ × ℝ | x ≤ yd.1 ∧ yd.2 ∈ Icc 0 M.dbar}).Nonempty :=
      fun x => ⟨_, mem_image_of_mem _ (show (x, (0 : ℝ)) ∈ {yd : ℝ × ℝ | x ≤ yd.1 ∧
        yd.2 ∈ Icc 0 M.dbar} from ⟨le_rfl, le_rfl, hM.2.1⟩)⟩
    have hbdd : ∀ x, ∀ z ∈ φ x '' {yd : ℝ × ℝ | x ≤ yd.1 ∧ yd.2 ∈ Icc 0 M.dbar}, z ≤ R + B := by
      rintro x z ⟨yd, ⟨hy, hd⟩, rfl⟩
      have h1 := hR yd.2 hd
      have h2 := rp_G_le M hM hW hB (M.T - k) yd.1 yd.2
      have h3 : 0 ≤ M.c (M.T - k) * (yd.1 - x) := mul_nonneg hc (by linarith)
      show M.r (M.T - k) yd.2 - M.c (M.T - k) * (yd.1 - x) +
        rpG M (M.valueGo k) (M.T - k) yd.1 yd.2 ≤ R + B
      linarith
    refine ⟨⟨convex_univ, fun x1 _ x2 _ α β hα hβ hαβ => ?_⟩, R + B, fun x => ?_⟩
    · rw [smul_eq_mul, smul_eq_mul, hval, hval, hval]
      apply rp_sup_comb (hne x1) (hne x2) hα hβ
      rintro u ⟨p, ⟨hp1, hp2⟩, rfl⟩ v ⟨q, ⟨hq1, hq2⟩, rfl⟩
      have hmem : (α * p.1 + β * q.1, α * p.2 + β * q.2) ∈
          {yd : ℝ × ℝ | α * x1 + β * x2 ≤ yd.1 ∧ yd.2 ∈ Icc 0 M.dbar} := by
        refine ⟨by nlinarith, ?_⟩
        have := (convex_Icc (0 : ℝ) M.dbar) hp2 hq2 hα hβ hαβ
        simpa only [smul_eq_mul] using this
      refine le_trans ?_ (le_csSup ⟨R + B, hbdd _⟩ (mem_image_of_mem _ hmem))
      have hr := hrc.2 hp2 hq2 hα hβ hαβ
      have hG := (rp_G_concave M hM hW (M.T - k)).2 (mem_univ p) (mem_univ q) hα hβ hαβ
      simp only [smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at hr hG
      show α * (M.r (M.T - k) p.2 - M.c (M.T - k) * (p.1 - x1) +
          rpG M (M.valueGo k) (M.T - k) p.1 p.2) +
        β * (M.r (M.T - k) q.2 - M.c (M.T - k) * (q.1 - x2) +
          rpG M (M.valueGo k) (M.T - k) q.1 q.2) ≤
        M.r (M.T - k) (α * p.2 + β * q.2) -
          M.c (M.T - k) * ((α * p.1 + β * q.1) - (α * x1 + β * x2)) +
          rpG M (M.valueGo k) (M.T - k) (α * p.1 + β * q.1) (α * p.2 + β * q.2)
      have hc' : M.c (M.T - k) * ((α * p.1 + β * q.1) - (α * x1 + β * x2)) =
          α * (M.c (M.T - k) * (p.1 - x1)) + β * (M.c (M.T - k) * (q.1 - x2)) := by ring
      rw [hc']
      linarith
    · rw [hval]
      exact csSup_le (hne x) (hbdd x)

end RevenueManagement

open RevenueManagement Set

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : ReplPricing Ω) (hM : M.IsModel) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ M.T) (y0 d0 : ℝ) (hd0 : d0 ∈ Set.Icc 0 M.dbar)
    (h0 : ∀ y d, d ∈ Set.Icc 0 M.dbar → M.objective t y d ≤ M.objective t y0 d0) :
    (∀ x, x ≤ y0 → M.IsOptimal t x y0 d0) ∧
    (∀ x, y0 ≤ x → ∃ d, d0 ≤ d ∧ M.IsOptimal t x x d) ∧
    (∀ x x' d, y0 ≤ x → x ≤ x' → M.IsOptimal t x x d →
      ∃ d', d ≤ d' ∧ M.IsOptimal t x' x' d') := by
  have hW := (rp_good M hM (M.T + 1 - (t + 1))).1
  have hobj : ∀ y d, M.objective t y d =
      M.r t d - M.c t * y + rpG M (M.valueGo (M.T + 1 - (t + 1))) t y d := fun y d => rfl
  obtain ⟨hrc, hrcont⟩ := hM.2.2.2.1 t
  -- increasing differences of the objective
  have hsup : ∀ {y y' d d' : ℝ}, y ≤ y' → d ≤ d' →
      M.objective t y d' - M.objective t y d ≤ M.objective t y' d' - M.objective t y' d := by
    intro y y' d d' hy hd
    rw [hobj, hobj, hobj, hobj]
    have := rp_G_super M hM hW t hy hd
    linarith
  -- joint concavity of the objective on `ℝ × [0, dbar]`
  have hconc : ∀ y1 y2 d1 d2 α β : ℝ, d1 ∈ Icc 0 M.dbar → d2 ∈ Icc 0 M.dbar → 0 ≤ α → 0 ≤ β →
      α + β = 1 → α * M.objective t y1 d1 + β * M.objective t y2 d2 ≤
        M.objective t (α * y1 + β * y2) (α * d1 + β * d2) := by
    intro y1 y2 d1 d2 α β hd1 hd2 hα hβ hαβ
    have hr := hrc.2 hd1 hd2 hα hβ hαβ
    have hG := (rp_G_concave M hM hW t).2 (mem_univ (y1, d1)) (mem_univ (y2, d2)) hα hβ hαβ
    simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at hr hG
    rw [hobj, hobj, hobj]
    have hc : M.c t * (α * y1 + β * y2) = α * (M.c t * y1) + β * (M.c t * y2) := by ring
    rw [hc]
    linarith
  -- continuity of the objective in the demand rate
  have hcontd : ∀ y, ContinuousOn (fun d => M.objective t y d) (Icc 0 M.dbar) := by
    intro y
    have hGd : ConcaveOn ℝ univ (fun d => rpG M (M.valueGo (M.T + 1 - (t + 1))) t y d) := by
      refine ⟨convex_univ, fun d1 _ d2 _ α β hα hβ hαβ => ?_⟩
      have := (rp_G_concave M hM hW t).2 (mem_univ (y, d1)) (mem_univ (y, d2)) hα hβ hαβ
      simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at this
      have hy : α * y + β * y = y := by rw [← add_mul, hαβ, one_mul]
      rw [hy] at this
      simpa only [smul_eq_mul] using this
    have hc := (rp_cont hGd).continuousOn (s := Icc 0 M.dbar)
    simp only [hobj]
    exact (hrcont.sub continuousOn_const).add hc
  have part2 : ∀ x, y0 ≤ x → ∃ d, d0 ≤ d ∧ M.IsOptimal t x x d := by
    intro x hx
    obtain ⟨dh, hdh, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hM.2.1) (hcontd x)
    have hmax' : ∀ d ∈ Icc 0 M.dbar, M.objective t x d ≤ M.objective t x dh :=
      fun d hd => isMaxOn_iff.mp hmax d hd
    obtain ⟨ds, hds0, hdsI, hdsmax⟩ : ∃ ds, d0 ≤ ds ∧ ds ∈ Icc 0 M.dbar ∧
        ∀ d ∈ Icc 0 M.dbar, M.objective t x d ≤ M.objective t x ds := by
      rcases le_total d0 dh with h | h
      · exact ⟨dh, h, hdh, hmax'⟩
      · refine ⟨d0, le_rfl, hd0, fun d hd => ?_⟩
        have h1 := hsup hx h
        have h2 := h0 y0 dh hdh
        have h3 := hmax' d hd
        linarith
    refine ⟨ds, hds0, le_rfl, hdsI, fun y' d' hy' hd' => ?_⟩
    rcases hy'.lt_or_eq with hlt | heq
    · have hpos : 0 < y' - y0 := by linarith
      have hα0 : 0 ≤ (y' - x) / (y' - y0) := div_nonneg (by linarith) hpos.le
      have hβ0 : 0 ≤ (x - y0) / (y' - y0) := div_nonneg (by linarith) hpos.le
      have hαβ : (y' - x) / (y' - y0) + (x - y0) / (y' - y0) = 1 := by
        field_simp; ring
      have hxcomb : (y' - x) / (y' - y0) * y0 + (x - y0) / (y' - y0) * y' = x := by
        field_simp; ring
      have hc := hconc y0 y' d0 d' _ _ hd0 hd' hα0 hβ0 hαβ
      rw [hxcomb] at hc
      have hdm : (y' - x) / (y' - y0) * d0 + (x - y0) / (y' - y0) * d' ∈ Icc 0 M.dbar := by
        have := (convex_Icc (0 : ℝ) M.dbar) hd0 hd' hα0 hβ0 hαβ
        simpa only [smul_eq_mul] using this
      have h1 := hdsmax _ hdm
      have h2 := h0 y' d' hd'
      have e : M.objective t y' d' = (y' - x) / (y' - y0) * M.objective t y' d' +
          (x - y0) / (y' - y0) * M.objective t y' d' := by rw [← add_mul, hαβ, one_mul]
      have := mul_le_mul_of_nonneg_left h2 hα0
      linarith
    · rw [← heq]
      exact hdsmax d' hd'
  refine ⟨fun x hx => ⟨hx, hd0, fun y' d' _ hd' => h0 y' d' hd'⟩, part2,
    fun x x' d hx hxx' hopt => ?_⟩
  obtain ⟨dt, -, hopt'⟩ := part2 x' (hx.trans hxx')
  obtain ⟨-, hdI, hoptd⟩ := hopt
  obtain ⟨-, hdtI, hoptdt⟩ := hopt'
  rcases le_total d dt with h | h
  · exact ⟨dt, h, le_rfl, hdtI, hoptdt⟩
  · refine ⟨d, le_rfl, le_rfl, hdI, fun y'' d'' hy'' hd'' => ?_⟩
    have h1 := hsup hxx' h
    have h2 := hoptd x dt le_rfl hdtI
    have h3 := hoptdt y'' d'' hy'' hd''
    linarith
