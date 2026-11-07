-- Prove2me | solution 1 for ProxADMMLC.Conv.theorem_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T18:53:50.908972+00:00
-- url     : https://prove2.me/submissions/cd5259e8-432f-42b4-8c76-92934ae62aee

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting
import Theorems.Thm_ProxADMMLC_Conv_eq_3_37
import Theorems.Thm_ProxADMMLC_Conv_eq_3_5
import Theorems.Thm_ProxADMMLC_Conv_lemma_3_4
import Theorems.Thm_ProxADMMLC_Conv_lemma_3_10_primal
import Theorems.Thm_ProxADMMLC_Conv_cor_3_7
import Theorems.Thm_ProxADMMLC_Conv_lemma_3_6

set_option autoImplicit false

open Filter Topology

namespace T24Aux

open ProxADMMLC.Conv

theorem boxProj_mem {n : ℕ} {ℓ u : Fin n → ℝ} (h : ∀ i, ℓ i < u i) (v : E n) :
    boxProj ℓ u v ∈ box ℓ u := by
  intro i
  simp only [boxProj, PiLp.toLp_apply]
  have := h i
  split_ifs <;> constructor <;> linarith

theorem box_comb {n : ℕ} {ℓ u : Fin n → ℝ} {z x : E n} {β : ℝ} (hz : z ∈ box ℓ u)
    (hx : x ∈ box ℓ u) (h0 : 0 ≤ β) (h1 : β ≤ 1) : z + β • (x - z) ∈ box ℓ u := by
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  obtain ⟨hz1, hz2⟩ := hz i
  obtain ⟨hx1, hx2⟩ := hx i
  have e1 := mul_le_mul_of_nonneg_left hx1 h0
  have e2 := mul_le_mul_of_nonneg_left hz1 (sub_nonneg.2 h1)
  have e3 := mul_le_mul_of_nonneg_left hx2 h0
  have e4 := mul_le_mul_of_nonneg_left hz2 (sub_nonneg.2 h1)
  constructor <;> nlinarith

theorem box_closed {n : ℕ} (ℓ u : Fin n → ℝ) : IsClosed (box ℓ u) := by
  have : box ℓ u = ⋂ i, ({x : E n | ℓ i ≤ x i} ∩ {x | x i ≤ u i}) := by
    ext x; simp [box]
  rw [this]
  refine isClosed_iInter fun i => ?_
  have hc : Continuous fun x : E n => x i := by fun_prop
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

theorem box_bounded {n : ℕ} (ℓ u : Fin n → ℝ) : Bornology.IsBounded (box ℓ u) := by
  have hc : Continuous (WithLp.toLp 2 : (Fin n → ℝ) → E n) := by fun_prop
  have hK : IsCompact ((WithLp.toLp 2 : (Fin n → ℝ) → E n) ''
      Set.univ.pi fun i => Set.Icc (ℓ i) (u i)) :=
    (isCompact_univ_pi fun i => isCompact_Icc).image hc
  refine hK.isBounded.subset fun x hx => ⟨WithLp.ofLp x, fun i _ => hx i, rfl⟩

theorem boxProj_eq {n : ℕ} {ℓ u : Fin n → ℝ} (h : ∀ i, ℓ i < u i) (v : E n) :
    boxProj ℓ u v = WithLp.toLp 2 (fun i => max (ℓ i) (min (v i) (u i))) := by
  simp only [boxProj]
  congr 1
  funext i
  have := h i
  split_ifs with h1 h2 <;> simp only [max_def, min_def] <;> split_ifs <;> linarith

theorem boxProj_cont {n : ℕ} {ℓ u : Fin n → ℝ} (h : ∀ i, ℓ i < u i) :
    Continuous (boxProj ℓ u) := by
  have : boxProj ℓ u = fun v : E n => WithLp.toLp 2 (fun i => max (ℓ i) (min (v i) (u i))) :=
    funext (boxProj_eq h)
  rw [this]
  have hc : Continuous (WithLp.toLp 2 : (Fin n → ℝ) → E n) := by fun_prop
  refine hc.comp (continuous_pi fun i => continuous_const.max (Continuous.min ?_ continuous_const))
  fun_prop

theorem K_cont {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (Γ p : ℝ)
    (hf : Continuous f) (z : E n) (y : E m) : Continuous fun x => K f A b Γ p x z y := by
  unfold K
  fun_prop

theorem tend_of_sq {a D : ℕ → ℝ} {w : ℝ} (hw : 0 < w) (ha : ∀ t, 0 ≤ a t)
    (h : ∀ t, w * a t ^ 2 ≤ D t) (hD : Tendsto D atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  have h2 : Tendsto (fun t => Real.sqrt (D t / w)) atTop (𝓝 0) := by
    have hDw : Tendsto (fun t => D t / w) atTop (𝓝 0) := by simpa using hD.div_const w
    have := (Real.continuous_sqrt.tendsto 0).comp hDw
    rw [Real.sqrt_zero] at this
    exact this
  refine squeeze_zero ha (fun t => ?_) h2
  rw [← Real.sqrt_sq (ha t)]
  exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hw]; linarith [h t])

theorem tend_of_eps {g : ℕ → ℝ} (h0 : ∀ t, 0 ≤ g t) (h : ∀ ε > 0, ∀ᶠ t in atTop, g t < ε) :
    Tendsto g atTop (𝓝 0) :=
  tendsto_order.2 ⟨fun _ ha => Eventually.of_forall fun t => lt_of_lt_of_le ha (h0 t), h⟩

end T24Aux

open ProxADMMLC.Conv in
theorem solution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hA : Assumption22 f A b ℓ u L) (γ : ℝ)
    (hγ : MonoConst f ℓ u γ) (Γ p c : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hc : 0 < c)
    (hcL : c * (L + p + Γ * ‖A‖ ^ 2) < 1) (hpγ : -γ < p) :
    ∃ α₀ > 0, ∀ α, 0 < α → α < α₀ → ∀ y0 : E m, ∃ β₀ > 0, ∀ β, 0 < β → β ≤ 1 → β ≤ β₀ →
      ∀ (x z : ℕ → E n) (y : ℕ → E m), IsRun f A b ℓ u Γ p c α β x y z → y 0 = y0 →
        Bornology.IsBounded (Set.range y) ∧
        Tendsto (fun t => ‖x (t + 1) - x t‖) atTop (𝓝 0) ∧
        Tendsto (fun t => Metric.infDist (x t) (Xstar f A b ℓ u)) atTop (𝓝 0) ∧
        Tendsto (fun t => Metric.infDist (z t) (Xstar f A b ℓ u)) atTop (𝓝 0) ∧
        Tendsto (fun t => Metric.infDist (x t, y t) (Wset f A b ℓ u)) atTop (𝓝 0) ∧
        ∀ q : E n × E m, MapClusterPt q atTop (fun t => (x t, y t)) → q ∈ Wset f A b ℓ u := by
  classical
  obtain ⟨ha, hsc, hf⟩ := hA
  have hdiff : Differentiable ℝ f := hf.1
  have hLip := hf.2.2
  have hboxC : IsClosed (box ℓ u) := T24Aux.box_closed ℓ u
  have hboxB : Bornology.IsBounded (box ℓ u) := T24Aux.box_bounded ℓ u
  have hboxK : IsCompact (box ℓ u) := Metric.isCompact_of_isClosed_isBounded hboxC hboxB
  obtain ⟨xb, hxb, hAxb⟩ : ∃ xb ∈ box ℓ u, A xb = b := by
    obtain ⟨xb, hxb, h⟩ := intrinsicInterior_subset ha
    exact ⟨xb, hxb, sub_eq_zero.1 h⟩
  have hxs_ex : ∀ (yy : E m) (zz : E n), ∃ xm, xm ∈ box ℓ u ∧
      ∀ x ∈ box ℓ u, K f A b Γ p xm zz yy ≤ K f A b Γ p x zz yy := by
    intro yy zz
    obtain ⟨xm, hxm, hmin⟩ := hboxK.exists_isMinOn ⟨xb, hxb⟩
      (T24Aux.K_cont f A b Γ p hdiff.continuous zz yy).continuousOn
    exact ⟨xm, hxm, fun x hx => isMinOn_iff.1 hmin x hx⟩
  choose xs hxs using hxs_ex
  have hxst_ex : ∀ zz : E n, ∃ xm, xm ∈ feas A b ℓ u ∧
      ∀ x ∈ feas A b ℓ u, f xm + p / 2 * ‖xm - zz‖ ^ 2 ≤ f x + p / 2 * ‖x - zz‖ ^ 2 := by
    intro zz
    have hK : IsCompact (feas A b ℓ u) :=
      hboxK.inter_right (isClosed_eq A.continuous continuous_const)
    have hcont : Continuous fun x => f x + p / 2 * ‖x - zz‖ ^ 2 := by
      have := hdiff.continuous
      fun_prop
    obtain ⟨xm, hxm, hmin⟩ := hK.exists_isMinOn ⟨xb, hxb, hAxb⟩ hcont.continuousOn
    exact ⟨xm, hxm, fun x hx => isMinOn_iff.1 hmin x hx⟩
  choose xst hxst using hxst_ex
  have hIX : IsXSel f A b ℓ u Γ p xs := hxs
  have hIXst : IsXStarSel f A b ℓ u p xst := hxst
  have hpγ' : 0 < c * (p + γ) := mul_pos hc (by linarith)
  have hden : 0 < 4 * c * ‖A‖ ^ 2 + 1 := by positivity
  refine ⟨(c * (p + γ)) ^ 2 / (4 * c * ‖A‖ ^ 2 + 1), div_pos (pow_pos hpγ' 2) hden, ?_⟩
  intro α hα hαlt y0
  have hα' : 4 * c * ‖A‖ ^ 2 * α < (c * (p + γ)) ^ 2 := by
    rw [lt_div_iff₀ hden] at hαlt
    nlinarith
  obtain ⟨β₀, hβ₀, H⟩ := ProxADMMLC.Conv.eq_3_37 f A b ℓ u hℓu L ⟨ha, hsc, hf⟩ γ hγ Γ p c hΓ hp
    hc hcL hpγ xs hIX xst hIXst α hα hα' y0
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ hβ1 hββ₀ x z y hrun hy0
  have hdec := H β hβ hβ1 hββ₀ x z y hrun hy0
  obtain ⟨hx0, hz0, hstep⟩ := hrun
  have hrun' : IsRun f A b ℓ u Γ p c α β x y z := ⟨hx0, hz0, hstep⟩
  -- invariants
  have hbox : ∀ t, x t ∈ box ℓ u ∧ z t ∈ box ℓ u := by
    intro t
    induction t with
    | zero => exact ⟨hx0, hz0⟩
    | succ t ih =>
      have hx1 : x (t + 1) ∈ box ℓ u := by
        rw [(hstep t).2.1]; exact T24Aux.boxProj_mem hℓu _
      exact ⟨hx1, by rw [(hstep t).2.2]; exact T24Aux.box_comb ih.2 hx1 hβ.le hβ1⟩
  have hyR : ∀ t, y t - y0 ∈ LinearMap.range (A : E n →ₗ[ℝ] E m) := by
    intro t
    induction t with
    | zero => rw [hy0, sub_self]; exact Submodule.zero_mem _
    | succ t ih =>
      have : y (t + 1) - y0 = (y t - y0) + (A : E n →ₗ[ℝ] E m) (α • (x t - xb)) := by
        rw [(hstep t).1]
        simp only [ContinuousLinearMap.coe_coe, map_smul, map_sub, hAxb]
        abel
      rw [this]
      exact Submodule.add_mem _ ih (LinearMap.mem_range_self _ _)
  -- the potential decreases and is bounded below
  have h35 := ProxADMMLC.Conv.eq_3_5 f A b ℓ u hℓu hdiff Γ p c α β hp xs hIX xst hIXst x z y hrun'
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℝ, Φ = fun t => phi f A b Γ p xs xst (x t) (z t) (y t) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℝ, D = fun t => 1 / (8 * c) * ‖x t - x (t + 1)‖ ^ 2 +
      α / 2 * ‖A (xs (y (t + 1)) (z t)) - b‖ ^ 2 + p / (6 * β) * ‖z t - z (t + 1)‖ ^ 2 :=
    ⟨_, rfl⟩
  have hdecΦ : ∀ t, D t ≤ Φ t - Φ (t + 1) := by
    intro t; rw [hΦ, hDdef]; exact hdec t
  have hlowΦ : ∀ t, sInf (f '' feas A b ℓ u) ≤ Φ t := by
    intro t; rw [hΦ]; exact ((h35.2 t).2).trans (h35.2 t).1
  have hD0 : ∀ t, 0 ≤ D t := by
    intro t; rw [hDdef]; positivity
  have hsumle : ∀ T, ∑ t ∈ Finset.range T, D t ≤ Φ 0 - Φ T := by
    intro T
    induction T with
    | zero => simp
    | succ T ih => rw [Finset.sum_range_succ]; linarith [hdecΦ T]
  have hDs : Summable D :=
    summable_of_sum_range_le hD0
      (c := Φ 0 - sInf (f '' feas A b ℓ u)) (fun T => (hsumle T).trans (by linarith [hlowΦ T]))
  have hDt : Tendsto D atTop (𝓝 0) := hDs.tendsto_atTop_zero
  have ha1 : Tendsto (fun t => ‖x t - x (t + 1)‖) atTop (𝓝 0) := by
    refine T24Aux.tend_of_sq (w := 1 / (8 * c)) (by positivity) (fun t => norm_nonneg _)
      (fun t => ?_) hDt
    rw [hDdef]
    have h2 : 0 ≤ α / 2 * ‖A (xs (y (t + 1)) (z t)) - b‖ ^ 2 := by positivity
    have h3 : 0 ≤ p / (6 * β) * ‖z t - z (t + 1)‖ ^ 2 := by positivity
    dsimp only
    linarith
  have ha2 : Tendsto (fun t => ‖A (xs (y (t + 1)) (z t)) - b‖) atTop (𝓝 0) := by
    refine T24Aux.tend_of_sq (w := α / 2) (by positivity) (fun t => norm_nonneg _)
      (fun t => ?_) hDt
    rw [hDdef]
    have h2 : 0 ≤ 1 / (8 * c) * ‖x t - x (t + 1)‖ ^ 2 := by positivity
    have h3 : 0 ≤ p / (6 * β) * ‖z t - z (t + 1)‖ ^ 2 := by positivity
    dsimp only
    linarith
  have ha3 : Tendsto (fun t => ‖z t - z (t + 1)‖) atTop (𝓝 0) := by
    refine T24Aux.tend_of_sq (w := p / (6 * β)) (by positivity) (fun t => norm_nonneg _)
      (fun t => ?_) hDt
    rw [hDdef]
    have h2 : 0 ≤ 1 / (8 * c) * ‖x t - x (t + 1)‖ ^ 2 := by positivity
    have h3 : 0 ≤ α / 2 * ‖A (xs (y (t + 1)) (z t)) - b‖ ^ 2 := by positivity
    dsimp only
    linarith
  -- part 2
  have hp2 : Tendsto (fun t => ‖x (t + 1) - x t‖) atTop (𝓝 0) := by
    simpa only [norm_sub_rev] using ha1
  have hzx : ∀ t, ‖z t - x (t + 1)‖ = ‖z t - z (t + 1)‖ / β := by
    intro t
    rw [eq_div_iff hβ.ne', (hstep t).2.2]
    have : z t - (z t + β • (x (t + 1) - z t)) = β • (z t - x (t + 1)) := by
      rw [smul_sub, smul_sub]; abel
    rw [this, norm_smul, Real.norm_of_nonneg hβ.le]; ring
  have ha4 : Tendsto (fun t => ‖z t - x (t + 1)‖) atTop (𝓝 0) := by
    simp_rw [hzx]; simpa using ha3.div_const β
  -- primal error bound: x t - x(y^{t+1}, z t) → 0, hence A x t - b → 0
  have hpe := ProxADMMLC.Conv.lemma_3_10_primal f A b ℓ u hℓu L hf γ hγ Γ p c α β hΓ hp hc hcL
    hpγ hβ hβ1 xs hIX x z y hrun'
  have ha5 : Tendsto (fun t => ‖x t - xs (y (t + 1)) (z t)‖) atTop (𝓝 0) := by
    have := hp2.div_const (c * (p + γ))
    rw [zero_div] at this
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) this
    rw [le_div_iff₀ hpγ', mul_comm]
    exact (hpe t).1
  have hAx : Tendsto (fun t => ‖A (x t) - b‖) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t => ‖A‖ * ‖x t - xs (y (t + 1)) (z t)‖ +
        ‖A (xs (y (t + 1)) (z t)) - b‖) atTop (𝓝 0) := by
      simpa using (ha5.const_mul ‖A‖).add ha2
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hlim
    have : A (x t) - b = A (x t - xs (y (t + 1)) (z t)) + (A (xs (y (t + 1)) (z t)) - b) := by
      rw [map_sub]; abel
    rw [this]
    exact (norm_add_le _ _).trans (by linarith [A.le_opNorm (x t - xs (y (t + 1)) (z t))])
  -- part 1
  have hyB : Bornology.IsBounded (Set.range y) := by
    have h := ProxADMMLC.Conv.lemma_3_4 f A b ℓ u hℓu ha hdiff Γ p xs hIX y0 (fun i => y (i + 1)) z
      (fun i => hyR (i + 1)) (fun i => (hbox i).2) ha2
    refine (h.insert (y 0)).subset ?_
    rintro _ ⟨t, rfl⟩
    cases t with
    | zero => exact Set.mem_insert _ _
    | succ t => exact Set.mem_insert_of_mem _ ⟨t, rfl⟩
  -- part 3
  have hc37 := ProxADMMLC.Conv.cor_3_7 f A b ℓ u hℓu ha L hf γ hγ Γ p c α hΓ hp hc hcL hpγ hα
    xs hIX y0
  have hyP : ∀ t, yPlus A b α (x t) (y t) = y (t + 1) := fun t => ((hstep t).1).symm
  have hxP : ∀ t, xPlus f A b ℓ u Γ p c α (x t) (z t) (y t) = x (t + 1) := by
    intro t
    rw [(hstep t).2.1, (hstep t).1]
    rfl
  have hmax : Tendsto (fun t => max (max ‖x t - xPlus f A b ℓ u Γ p c α (x t) (z t) (y t)‖
      ‖z t - xPlus f A b ℓ u Γ p c α (x t) (z t) (y t)‖)
      ‖A (xs (yPlus A b α (x t) (y t)) (z t)) - b‖) atTop (𝓝 0) := by
    simp only [hxP, hyP]
    simpa using (ha1.max ha4).max ha2
  have hX : ∀ ε > 0, ∀ᶠ t in atTop, max (Metric.infDist (x t) (Xstar f A b ℓ u))
      (Metric.infDist (z t) (Xstar f A b ℓ u)) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδH⟩ := hc37 ε hε
    filter_upwards [(tendsto_order.1 hmax).2 δ hδ] with t ht
    exact hδH (x t) (hbox t).1 (z t) (hbox t).2 (y t) (hyR t) ht
  have hp3x : Tendsto (fun t => Metric.infDist (x t) (Xstar f A b ℓ u)) atTop (𝓝 0) :=
    T24Aux.tend_of_eps (fun t => Metric.infDist_nonneg)
      (fun ε hε => (hX ε hε).mono fun t ht => lt_of_le_of_lt (le_max_left _ _) ht)
  have hp3z : Tendsto (fun t => Metric.infDist (z t) (Xstar f A b ℓ u)) atTop (𝓝 0) :=
    T24Aux.tend_of_eps (fun t => Metric.infDist_nonneg)
      (fun ε hε => (hX ε hε).mono fun t ht => lt_of_le_of_lt (le_max_right _ _) ht)
  -- part 5: limit points are KKT pairs
  have h5 : ∀ q : E n × E m, MapClusterPt q atTop (fun t => (x t, y t)) →
      q ∈ Wset f A b ℓ u := by
    intro q hq
    obtain ⟨ψ, hψ, hlim⟩ := subseq_tendsto_of_neBot hq
    have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
    have hxl : Tendsto (fun k => x (ψ k)) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hlim
    have hyl : Tendsto (fun k => y (ψ k)) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hlim
    have hq1 : q.1 ∈ box ℓ u :=
      hboxC.mem_of_tendsto hxl (Eventually.of_forall fun k => (hbox _).1)
    have hA0 : Tendsto (fun k => A (x (ψ k)) - b) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.2 (hAx.comp hψt)
    have hAq : A q.1 - b = 0 := by
      have h1 : Tendsto (fun k => A (x (ψ k)) - b) atTop (𝓝 (A q.1 - b)) :=
        ((A.continuous.tendsto _).comp hxl).sub_const b
      exact tendsto_nhds_unique h1 hA0
    have hx1 : Tendsto (fun k => x (ψ k + 1)) atTop (𝓝 q.1) := by
      have h0 : Tendsto (fun k => x (ψ k + 1) - x (ψ k)) atTop (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.2 (hp2.comp hψt)
      simpa using h0.add hxl
    have hzl : Tendsto (fun k => z (ψ k)) atTop (𝓝 q.1) := by
      have h0 : Tendsto (fun k => z (ψ k) - x (ψ k + 1)) atTop (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.2 (ha4.comp hψt)
      simpa using h0.add hx1
    have hy1 : Tendsto (fun k => y (ψ k + 1)) atTop (𝓝 q.2) := by
      have := hyl.add (hA0.const_smul α)
      simp only [smul_zero, add_zero] at this
      exact this.congr (fun k => ((hstep (ψ k)).1).symm)
    have hgr : Tendsto (fun k => gradient f (x (ψ k))) atTop (𝓝 (gradient f q.1)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 : Tendsto (fun k => ‖x (ψ k) - q.1‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.1 hxl
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => hLip _ (hbox _).1 _ hq1) ?_
      simpa using h0.const_mul L
    have hG : Tendsto (fun k => gradK f A b Γ p (x (ψ k)) (z (ψ k)) (y (ψ k + 1))) atTop
        (𝓝 (gradK f A b Γ p q.1 q.1 q.2)) := by
      unfold gradK
      have hAd := (ContinuousLinearMap.adjoint A).continuous
      exact ((hgr.add ((hAd.tendsto _).comp hy1)).add
        (((hAd.tendsto _).comp (((A.continuous.tendsto _).comp hxl).sub_const b)).const_smul Γ)).add
        ((hxl.sub hzl).const_smul p)
    have hbp : Continuous (boxProj ℓ u) := T24Aux.boxProj_cont hℓu
    have hx1' : Tendsto (fun k => x (ψ k + 1)) atTop
        (𝓝 (boxProj ℓ u (q.1 - c • gradK f A b Γ p q.1 q.1 q.2))) := by
      have := (hbp.tendsto _).comp (hxl.sub (hG.const_smul c))
      exact this.congr (fun k => ((hstep (ψ k)).2.1).symm)
    have hfix := tendsto_nhds_unique hx1' hx1
    have hyP' : yPlus A b α q.1 q.2 = q.2 := by
      simp only [yPlus, hAq, smul_zero, add_zero]
    have hxP' : xPlus f A b ℓ u Γ p c α q.1 q.1 q.2 = q.1 := by
      simp only [xPlus, hyP']
      exact hfix
    have hzP' : zPlus f A b ℓ u Γ p c α β q.1 q.1 q.2 = q.1 := by
      simp only [zPlus, hxP', sub_self, smul_zero, add_zero]
    exact ProxADMMLC.Conv.lemma_3_6 f A b ℓ u hℓu Γ p c α β hα hβ hc q.1 q.1 q.2 hyP' hxP' hzP'
  -- part 4: distance to W tends to zero (bounded sequence, all limit points in W)
  have h4 : Tendsto (fun t => Metric.infDist (x t, y t) (Wset f A b ℓ u)) atTop (𝓝 0) := by
    by_contra hne
    rw [Metric.tendsto_atTop] at hne
    push Not at hne
    obtain ⟨ε, hε, hN⟩ := hne
    have hfr : ∃ᶠ t in atTop, ε ≤ Metric.infDist (x t, y t) (Wset f A b ℓ u) := by
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨t, ht, h⟩ := hN N
      refine ⟨t, ht, ?_⟩
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg] at h
    obtain ⟨φ, hφ, hφε⟩ := Filter.extraction_of_frequently_atTop hfr
    obtain ⟨a, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded (hboxB.prod hyB)
      (x := fun k => (x (φ k), y (φ k))) (fun k => ⟨(hbox _).1, ⟨_, rfl⟩⟩)
    have hcl : MapClusterPt a atTop (fun t => (x t, y t)) :=
      MapClusterPt.of_comp (φ := φ ∘ ψ) (hφ.comp hψ).tendsto_atTop hlim.mapClusterPt
    have haW := h5 a hcl
    have h1 : Tendsto (fun k => Metric.infDist (x (φ (ψ k)), y (φ (ψ k))) (Wset f A b ℓ u))
        atTop (𝓝 (Metric.infDist a (Wset f A b ℓ u))) :=
      ((Metric.continuous_infDist_pt _).tendsto a).comp hlim
    rw [Metric.infDist_zero_of_mem haW] at h1
    have := ge_of_tendsto h1 (Eventually.of_forall fun k => hφε (ψ k))
    linarith
  exact ⟨hyB, hp2, hp3x, hp3z, h4, h5⟩
