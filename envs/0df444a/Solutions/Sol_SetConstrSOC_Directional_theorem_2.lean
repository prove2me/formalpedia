-- Prove2me | solution 1 for SetConstrSOC.Directional.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:47:22.819084+00:00
-- url     : https://prove2.me/submissions/b4515a2d-b75d-42e1-a939-a36ecef181d8

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model
import Theorems.Thm_SetConstrSOC_Directional_proposition_5_10
import Theorems.Thm_SetConstrSOC_Directional_proposition_5_11
import Theorems.Thm_SetConstrSOC_Directional_proposition_5_12
import Theorems.Thm_SetConstrSOC_Directional_corollary_1
import Theorems.Thm_SetConstrSOC_Directional_theorem_1
import Theorems.Thm_SetConstrSOC_Directional_lemma_4
import Theorems.Thm_SetConstrSOC_Directional_lemma_3_14

open Filter
open scoped Topology

namespace SetConstrSOC.Directional
namespace T2Aux

theorem one_div_succ_tendsto : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem one_div_succ_pos (k : ℕ) : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity

/-- squeeze: a real sequence in `(0, 1/(k+1))` tends to `0`. -/
theorem tendsto_of_lt_one_div {t : ℕ → ℝ} (h0 : ∀ k, 0 < t k)
    (h1 : ∀ k, t k < 1 / ((k : ℝ) + 1)) : Tendsto t atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds one_div_succ_tendsto
    (fun k => (h0 k).le) (fun k => (h1 k).le)

theorem tendsto_of_dist_lt_one_div {α : Type*} [PseudoMetricSpace α] {w : ℕ → α} {v : α}
    (h1 : ∀ k, dist (w k) v < 1 / ((k : ℝ) + 1)) : Tendsto w atTop (𝓝 v) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds one_div_succ_tendsto
    (fun k => dist_nonneg) (fun k => (h1 k).le)

theorem sots_approx {n : ℕ} {S : Set (E n)} {x d v : E n}
    (hv : v ∈ secondOrderTangentSet S x d) {η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, ∃ w : E n, 0 < t ∧ t < η ∧ dist w v < η ∧
      x + t • d + ((1 / 2 : ℝ) * t ^ 2) • w ∈ S := by
  obtain ⟨-, t, wk, ht, htt, hw, hmem⟩ := hv
  have e1 := htt.eventually (gt_mem_nhds hη)
  have e2 := hw.eventually (Metric.ball_mem_nhds v hη)
  obtain ⟨k, hk1, hk2⟩ := (e1.and e2).exists
  exact ⟨t k, wk k, ht k, hk1, hk2, hmem k⟩

theorem sots_closed {n : ℕ} (S : Set (E n)) (x d : E n) :
    IsClosed (secondOrderTangentSet S x d) := by
  refine isClosed_of_closure_subset fun v hv => ?_
  rw [Metric.mem_closure_iff] at hv
  have hx : x ∈ S := by
    obtain ⟨b, hb, -⟩ := hv 1 one_pos
    exact hb.1
  have key : ∀ k : ℕ, ∃ t : ℝ, ∃ w : E n, 0 < t ∧ t < 1 / ((k : ℝ) + 1) ∧
      dist w v < 1 / ((k : ℝ) + 1) ∧ x + t • d + ((1 / 2 : ℝ) * t ^ 2) • w ∈ S := by
    intro k
    have hk := one_div_succ_pos k
    obtain ⟨b, hb, hvb⟩ := hv (1 / ((k : ℝ) + 1) / 2) (by positivity)
    obtain ⟨t, w, ht, htk, hwb, hmem⟩ := sots_approx hb (η := 1 / ((k : ℝ) + 1) / 2)
      (by positivity)
    refine ⟨t, w, ht, by linarith, ?_, hmem⟩
    calc dist w v ≤ dist w b + dist b v := dist_triangle _ _ _
      _ < 1 / ((k : ℝ) + 1) / 2 + 1 / ((k : ℝ) + 1) / 2 := by
          rw [dist_comm b v]; exact add_lt_add hwb hvb
      _ = 1 / ((k : ℝ) + 1) := by ring
  choose t w ht htk hwk hmem using key
  exact ⟨hx, t, w, ht, tendsto_of_lt_one_div ht htk, tendsto_of_dist_lt_one_div hwk, hmem⟩

theorem dln_approx {n : ℕ} {S : Set (E n)} {x d v : E n}
    (hv : v ∈ dirLimNormal S x d) {η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, ∃ dd vv : E n, 0 < t ∧ t < η ∧ dist dd d < η ∧ dist vv v < η ∧
      vv ∈ regNormal S (x + t • dd) := by
  obtain ⟨-, t, dk, vk, ht, htt, hd, hvk, hmem⟩ := hv
  have e1 := htt.eventually (gt_mem_nhds hη)
  have e2 := hd.eventually (Metric.ball_mem_nhds d hη)
  have e3 := hvk.eventually (Metric.ball_mem_nhds v hη)
  obtain ⟨k, hk1, hk2, hk3⟩ := (e1.and (e2.and e3)).exists
  exact ⟨t k, dk k, vk k, ht k, hk1, hk2, hk3, hmem k⟩

/-- The directional limiting normal cone is sequentially closed. -/
theorem dln_seq_closed {n : ℕ} {S : Set (E n)} {x d : E n} {lam : ℕ → E n} {l : E n}
    (hmem : ∀ k, lam k ∈ dirLimNormal S x d) (hl : Tendsto lam atTop (𝓝 l)) :
    l ∈ dirLimNormal S x d := by
  have hx : x ∈ S := (hmem 0).1
  have key : ∀ k : ℕ, ∃ t : ℝ, ∃ dd vv : E n, 0 < t ∧ t < 1 / ((k : ℝ) + 1) ∧
      dist dd d < 1 / ((k : ℝ) + 1) ∧ dist vv l < 1 / ((k : ℝ) + 1) ∧
      vv ∈ regNormal S (x + t • dd) := by
    intro k
    have hk := one_div_succ_pos k
    obtain ⟨j, hj⟩ := (hl.eventually (Metric.ball_mem_nhds l (ε := 1 / ((k : ℝ) + 1) / 2)
      (by positivity))).exists
    obtain ⟨t, dd, vv, ht, htk, hdd, hvv, hm⟩ := dln_approx (hmem j)
      (η := 1 / ((k : ℝ) + 1) / 2) (by positivity)
    refine ⟨t, dd, vv, ht, by linarith, by linarith, ?_, hm⟩
    calc dist vv l ≤ dist vv (lam j) + dist (lam j) l := dist_triangle _ _ _
      _ < 1 / ((k : ℝ) + 1) / 2 + 1 / ((k : ℝ) + 1) / 2 := add_lt_add hvv hj
      _ = 1 / ((k : ℝ) + 1) := by ring
  choose t dd vv ht htk hdd hvv hm using key
  exact ⟨hx, t, dd, vv, ht, tendsto_of_lt_one_div ht htk, tendsto_of_dist_lt_one_div hdd,
    tendsto_of_dist_lt_one_div hvv, hm⟩

/-- First-order condition: minus the gradient at a local minimizer on `D` is a
regular normal. -/
theorem regNormal_of_localMin {m : ℕ} (D : Set (E m)) (y₀ : E m) (hy : y₀ ∈ D)
    (h : E m → ℝ) (h' : E m →L[ℝ] ℝ) (hd : HasFDerivAt h h' y₀)
    (hmin : ∀ᶠ y in 𝓝[D] y₀, h y₀ ≤ h y) (v : E m)
    (hv : ∀ u, inner ℝ v u = - h' u) : v ∈ regNormal D y₀ := by
  refine ⟨hy, fun ε hε => ?_⟩
  have h1 := hd.isLittleO.bound hε
  filter_upwards [hmin, nhdsWithin_le_nhds h1] with y hy1 hy2
  rw [hv]
  rw [Real.norm_eq_abs] at hy2
  have := le_abs_self (h y - h y₀ - h' (y - y₀))
  linarith

theorem norm_le_sqrt_aux (a δ : ℝ) (ha : 0 ≤ a) : a ≤ Real.sqrt (a ^ 2 + δ ^ 2) := by
  have := Real.abs_le_sqrt (x := a) (y := a ^ 2 + δ ^ 2) (by nlinarith [sq_nonneg δ])
  rwa [abs_of_nonneg ha] at this

/-- One smoothing step of the exact-penalty argument. -/
theorem penalty_step {n m : ℕ} (G : E n →L[ℝ] E m) (b : E m) (D : Set (E m))
    (hD : IsClosed D) (ψ : E n → ℝ) (ψ' : E n → (E n →L[ℝ] ℝ))
    (hψ : ∀ w, HasFDerivAt ψ (ψ' w) w)
    (w₀ : E n) (hy₀ : G w₀ + b ∈ D) (ρ r : ℝ) (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hpen : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ y ∈ D, ψ w₀ ≤ ψ w + r * ‖G w + b - y‖)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : r * δ < ρ ^ 2) :
    ∃ w : E n, ∃ y : E m, ∃ l : E m,
      ‖w - w₀‖ ^ 2 + ‖y - (G w₀ + b)‖ ^ 2 ≤ r * δ ∧ y ∈ D ∧ ‖l‖ ≤ r ∧
      l - (2 : ℝ) • (y - (G w₀ + b)) ∈ regNormal D y ∧
      ∀ v, ψ' w v + inner ℝ l (G v) + 2 * inner ℝ (w - w₀) v = 0 := by
  set yb := G w₀ + b with hyb
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun w => (hψ w).continuousAt
  let Φ : E n × E m → ℝ := fun p => ψ p.1 + r * Real.sqrt (‖G p.1 + b - p.2‖ ^ 2 + δ ^ 2) +
    ‖p.1 - w₀‖ ^ 2 + ‖p.2 - yb‖ ^ 2
  have hΦc : Continuous Φ := by
    have : Continuous fun p : E n × E m => G p.1 + b - p.2 := by fun_prop
    exact (((hψc.comp continuous_fst).add (continuous_const.mul
      (((this.norm.pow 2).add continuous_const).sqrt))).add
      (((continuous_fst.sub continuous_const).norm).pow 2)).add
      (((continuous_snd.sub continuous_const).norm).pow 2)
  set K : Set (E n × E m) := Metric.closedBall w₀ ρ ×ˢ (D ∩ Metric.closedBall yb ρ) with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).inter_left hD)
  have hKne : (w₀, yb) ∈ K := ⟨Metric.mem_closedBall_self hρ.le,
    hy₀, Metric.mem_closedBall_self hρ.le⟩
  obtain ⟨⟨w, y⟩, hpK, hpmin⟩ := hKc.exists_isMinOn ⟨_, hKne⟩ hΦc.continuousOn
  obtain ⟨hw, hyD, hy⟩ := hpK
  set z := G w + b - y with hz
  have hq : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
  set s := Real.sqrt (‖z‖ ^ 2 + δ ^ 2) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hq
  have hzs : ‖z‖ ≤ s := norm_le_sqrt_aux _ _ (norm_nonneg _)
  -- the value bound
  have hval : Φ (w, y) ≤ Φ (w₀, yb) := hpmin hKne
  have hbound : ‖w - w₀‖ ^ 2 + ‖y - yb‖ ^ 2 ≤ r * δ := by
    have h1 := hpen w hw y hyD
    have h2 : Φ (w₀, yb) = ψ w₀ + r * δ := by
      simp only [Φ, sub_self, norm_zero, hyb]
      rw [show (0 : ℝ) ^ 2 + δ ^ 2 = δ ^ 2 by ring, Real.sqrt_sq hδ.le]
      ring
    have h3 : r * ‖z‖ ≤ r * s := mul_le_mul_of_nonneg_left hzs hr
    have hval' := hval.trans_eq h2
    simp only [Φ] at hval'
    linarith
  have hlt : ∀ a b' : ℝ, 0 ≤ a → 0 ≤ b' → a ^ 2 + b' ^ 2 ≤ r * δ → a < ρ := by
    intro a b' ha hb' hab
    nlinarith
  have hwlt : ‖w - w₀‖ < ρ := hlt _ _ (norm_nonneg _) (norm_nonneg _) hbound
  have hylt : ‖y - yb‖ < ρ := by
    have := hlt (‖y - yb‖) (‖w - w₀‖) (norm_nonneg _) (norm_nonneg _) (by linarith)
    exact this
  refine ⟨w, y, (r / s) • z, hbound, hyD, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc r / s * ‖z‖ ≤ r / s * s := mul_le_mul_of_nonneg_left hzs (by positivity)
      _ = r := by field_simp
  · -- y-part: regular normal
    have e1 : HasFDerivAt (fun y' : E m => G w + b - y') (-ContinuousLinearMap.id ℝ (E m)) y :=
      (hasFDerivAt_id y).const_sub (G w + b)
    have e2 := ((e1.norm_sq).add_const (δ ^ 2)).sqrt (ne_of_gt hq)
    have e3 := e2.const_mul r
    have e4 := ((hasFDerivAt_id y).sub_const yb).norm_sq
    have hder := e3.add e4
    refine regNormal_of_localMin D y hyD _ _ hder ?_ _ ?_
    · have hball : Metric.ball yb ρ ∈ 𝓝 y := Metric.isOpen_ball.mem_nhds (by
        rw [Metric.mem_ball, dist_eq_norm]; exact hylt)
      filter_upwards [inter_mem_nhdsWithin D hball] with y' hy'
      have hm : (w, y') ∈ K := ⟨hw, hy'.1, Metric.ball_subset_closedBall hy'.2⟩
      have := isMinOn_iff.mp hpmin _ hm
      simp only [Φ, Pi.add_apply, id] at this ⊢
      linarith
    · intro u
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, inner_neg_right,
        real_inner_smul_left, nsmul_eq_mul, Nat.cast_ofNat, id]
      rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hz, hs]
      field_simp
      ring
  · -- w-part: stationarity
    have e1 : HasFDerivAt (fun w' : E n => G w' + b - y) G w :=
      ((G.hasFDerivAt).add_const b).sub_const y
    have e2 := ((e1.norm_sq).add_const (δ ^ 2)).sqrt (ne_of_gt hq)
    have e3 := e2.const_mul r
    have e4 := ((hasFDerivAt_id w).sub_const w₀).norm_sq
    have hder := ((hψ w).add e3).add e4
    have hloc : IsLocalMin ((fun w' => ψ w') + (fun w' => r * Real.sqrt (‖G w' + b - y‖ ^ 2 + δ ^ 2)) +
        (fun w' => ‖id w' - w₀‖ ^ 2)) w := by
      have hball : Metric.ball w₀ ρ ∈ 𝓝 w := Metric.isOpen_ball.mem_nhds (by
        rw [Metric.mem_ball, dist_eq_norm]; exact hwlt)
      filter_upwards [hball] with w' hw'
      have hm : (w', y) ∈ K := ⟨Metric.ball_subset_closedBall hw', hyD, hy⟩
      have := isMinOn_iff.mp hpmin _ hm
      simp only [Φ, Pi.add_apply, id] at this ⊢
      linarith
    have h0 := hloc.hasFDerivAt_eq_zero hder
    intro v
    have h1 := congrArg (fun L => L v) h0
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
      smul_eq_mul, ContinuousLinearMap.zero_apply, nsmul_eq_mul, Nat.cast_ofNat, id] at h1
    rw [real_inner_smul_left]
    field_simp at h1
    field_simp
    linarith

theorem tendsto_norm_of_sq_le {α : Type*} [SeminormedAddCommGroup α] {u : ℕ → α} {a : α}
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) (h : ∀ k, ‖u k - a‖ ^ 2 ≤ e k) :
    Tendsto u atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Tendsto (fun k => Real.sqrt (e k)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp he
    simpa [Function.comp_def] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun k => norm_nonneg _) (fun k => ?_)
  rw [← Real.sqrt_sq (norm_nonneg (u k - a))]
  exact Real.sqrt_le_sqrt (h k)

/-- Exact penalty yields a limiting-normal multiplier (paper: [19, Theorem 3] in the
special case needed for (21)–(22)). -/
theorem penalty_multiplier {n m : ℕ} (G : E n →L[ℝ] E m) (b : E m) (D : Set (E m))
    (hD : IsClosed D) (ψ : E n → ℝ) (ψ' : E n → (E n →L[ℝ] ℝ))
    (hψ : ∀ w, HasFDerivAt ψ (ψ' w) w) (hψ'c : Continuous ψ')
    (w₀ : E n) (hy₀ : G w₀ + b ∈ D) (ρ r : ℝ) (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hpen : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ y ∈ D, ψ w₀ ≤ ψ w + r * ‖G w + b - y‖) :
    ∃ l ∈ limNormal D (G w₀ + b), ‖l‖ ≤ r ∧ ∀ v, ψ' w₀ v + inner ℝ l (G v) = 0 := by
  set c : ℝ := ρ ^ 2 / (r + 1) with hc
  have hcpos : 0 < c := by positivity
  have hδ : ∀ k : ℕ, 0 < c / ((k : ℝ) + 1) := fun k => by positivity
  have hδρ : ∀ k : ℕ, r * (c / ((k : ℝ) + 1)) < ρ ^ 2 := by
    intro k
    have h1 : c / ((k : ℝ) + 1) ≤ c := div_le_self hcpos.le (by linarith [k.cast_nonneg (α := ℝ)])
    have h2 : r * c < ρ ^ 2 := by
      rw [hc, mul_div_assoc']
      rw [div_lt_iff₀ (by linarith)]
      nlinarith [sq_pos_of_pos hρ]
    calc r * (c / ((k : ℝ) + 1)) ≤ r * c := mul_le_mul_of_nonneg_left h1 hr
      _ < ρ ^ 2 := h2
  have step := fun k : ℕ => penalty_step G b D hD ψ ψ' hψ w₀ hy₀ ρ r hρ hr hpen _ (hδ k) (hδρ k)
  choose w y l hb hyD hl hreg hstat using step
  have he : Tendsto (fun k : ℕ => r * (c / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have := (one_div_succ_tendsto.const_mul (r * c))
    simp only [mul_zero] at this
    refine this.congr fun k => ?_
    ring
  have hw : Tendsto w atTop (𝓝 w₀) := tendsto_norm_of_sq_le he fun k => by
    nlinarith [hb k, sq_nonneg ‖y k - (G w₀ + b)‖]
  have hy : Tendsto y atTop (𝓝 (G w₀ + b)) := tendsto_norm_of_sq_le he fun k => by
    nlinarith [hb k, sq_nonneg ‖w k - w₀‖]
  obtain ⟨a, ha, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall
    (x := (0 : E m)) (r := r)) (x := l) (fun k => by simpa using hl k)
  rw [Metric.isClosed_closedBall.closure_eq] at ha
  have hyφ : Tendsto (y ∘ φ) atTop (𝓝 (G w₀ + b)) := hy.comp hφ.tendsto_atTop
  have hwφ : Tendsto (w ∘ φ) atTop (𝓝 w₀) := hw.comp hφ.tendsto_atTop
  refine ⟨a, ⟨hy₀, y ∘ φ, fun k => l (φ k) - (2 : ℝ) • (y (φ k) - (G w₀ + b)), hyφ, ?_,
    fun k => hreg (φ k)⟩, by simpa using ha, fun v => ?_⟩
  · have : Tendsto (fun k => l (φ k) - (2 : ℝ) • (y (φ k) - (G w₀ + b))) atTop
        (𝓝 (a - (2 : ℝ) • ((G w₀ + b) - (G w₀ + b)))) :=
      hlim.sub ((hyφ.sub tendsto_const_nhds).const_smul _)
    simpa using this
  · have h1 : Tendsto (fun k => ψ' (w (φ k)) v + inner ℝ (l (φ k)) (G v) +
        2 * inner ℝ (w (φ k) - w₀) v) atTop
        (𝓝 (ψ' w₀ v + inner ℝ a (G v) + 2 * inner ℝ (w₀ - w₀) v)) := by
      have t1 : Tendsto (fun k => ψ' (w (φ k)) v) atTop (𝓝 (ψ' w₀ v)) :=
        (((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp hψ'c).tendsto w₀).comp hwφ
      have t2 : Tendsto (fun k => inner ℝ (l (φ k)) (G v)) atTop (𝓝 (inner ℝ a (G v))) :=
        hlim.inner tendsto_const_nhds
      have t3 : Tendsto (fun k => inner ℝ (w (φ k) - w₀) v) atTop
          (𝓝 (inner ℝ (w₀ - w₀) v)) :=
        (hwφ.sub tendsto_const_nhds).inner tendsto_const_nhds
      exact (t1.add t2).add (t3.const_mul 2)
    have h2 : (fun k => ψ' (w (φ k)) v + inner ℝ (l (φ k)) (G v) +
        2 * inner ℝ (w (φ k) - w₀) v) = fun _ => 0 := funext fun k => hstat (φ k) v
    rw [h2] at h1
    have := tendsto_nhds_unique h1 tendsto_const_nhds
    simpa using this

/-- Existence of a minimizer of the coercive quadratic (19) over a closed nonempty set. -/
theorem quad_min {n : ℕ} (S : Set (E n)) (hS : IsClosed S) (hne : S.Nonempty)
    (c : E n →L[ℝ] ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ w ∈ S, ∀ s ∈ S, c w + ε / 2 * ‖w‖ ^ 2 ≤ c s + ε / 2 * ‖s‖ ^ 2 := by
  obtain ⟨w₀, hw₀⟩ := hne
  set φ : E n → ℝ := fun s => c s + ε / 2 * ‖s‖ ^ 2 with hφ
  set M := |φ w₀| + 1 with hM
  set R := max ‖w₀‖ (max 1 (2 * (‖c‖ + M) / ε)) with hR
  have hK : IsCompact (S ∩ Metric.closedBall 0 R) := (isCompact_closedBall _ _).inter_left hS
  have hw₀K : w₀ ∈ S ∩ Metric.closedBall 0 R :=
    ⟨hw₀, by rw [mem_closedBall_zero_iff]; exact le_max_left _ _⟩
  have hφc : Continuous φ := by fun_prop
  obtain ⟨w, hwK, hmin⟩ := hK.exists_isMinOn ⟨w₀, hw₀K⟩ hφc.continuousOn
  refine ⟨w, hwK.1, fun s hs => ?_⟩
  show φ w ≤ φ s
  by_cases hsR : ‖s‖ ≤ R
  · exact hmin ⟨hs, by rw [mem_closedBall_zero_iff]; exact hsR⟩
  · push_neg at hsR
    have h1 : φ w ≤ φ w₀ := hmin hw₀K
    have hcs : -(‖c‖ * ‖s‖) ≤ c s := by
      have := c.le_opNorm s
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (c s)]
    have ht1 : 1 ≤ ‖s‖ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hsR.le
    have ht2 : 2 * (‖c‖ + M) / ε ≤ ‖s‖ :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hsR.le
    have ht3 : 2 * (‖c‖ + M) ≤ ε * ‖s‖ := by
      rw [div_le_iff₀ hε] at ht2; linarith
    have hMpos : 0 < M := by positivity
    have hφw₀ : φ w₀ ≤ |φ w₀| := le_abs_self _
    have h4 : (‖c‖ + M) * ‖s‖ ≤ ε / 2 * ‖s‖ ^ 2 := by nlinarith [norm_nonneg s]
    have h5 : φ s = c s + ε / 2 * ‖s‖ ^ 2 := rfl
    nlinarith [norm_nonneg s]

/-- The exact-penalty estimate derived from the error bound (12). -/
theorem exact_penalty {n m : ℕ} (S : Set (E n)) (hne : S.Nonempty) (G : E n →L[ℝ] E m)
    (b : E m) (D : Set (E m)) (κ : ℝ) (hκ : 0 ≤ κ)
    (hEB : ∀ w, Metric.infDist w S ≤ κ * Metric.infDist (G w + b) D)
    (c : E n →L[ℝ] ℝ) (ε : ℝ) (hε : 0 ≤ ε) (w₀ : E n) (hw₀ : w₀ ∈ S)
    (hmin : ∀ s ∈ S, c w₀ + ε / 2 * ‖w₀‖ ^ 2 ≤ c s + ε / 2 * ‖s‖ ^ 2) :
    ∀ w ∈ Metric.closedBall w₀ 1, ∀ y ∈ D,
      c w₀ + ε / 2 * ‖w₀‖ ^ 2 ≤ (c w + ε / 2 * ‖w‖ ^ 2) +
        κ * (‖c‖ + ε * (‖w₀‖ + 3)) * ‖G w + b - y‖ := by
  intro w hw y hy
  set L := ‖c‖ + ε * (‖w₀‖ + 3) with hL
  have hL0 : 0 ≤ L := by positivity
  have hdy : Metric.infDist (G w + b) D ≤ ‖G w + b - y‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hy
  have hdw : Metric.infDist w S ≤ 1 := by
    have := Metric.infDist_le_dist_of_mem (x := w) hw₀
    rw [Metric.mem_closedBall] at hw
    linarith
  have key : ∀ η : ℝ, 0 < η → η ≤ 1 →
      c w₀ + ε / 2 * ‖w₀‖ ^ 2 ≤ (c w + ε / 2 * ‖w‖ ^ 2) + L * (κ * ‖G w + b - y‖ + η) := by
    intro η hη hη1
    obtain ⟨s, hs, hws⟩ := (Metric.infDist_lt_iff hne).1
      (lt_add_of_pos_right (Metric.infDist w S) hη)
    rw [dist_eq_norm] at hws
    have hws1 : ‖w - s‖ ≤ κ * ‖G w + b - y‖ + η := by
      have := hEB w
      have : κ * Metric.infDist (G w + b) D ≤ κ * ‖G w + b - y‖ :=
        mul_le_mul_of_nonneg_left hdy hκ
      linarith
    have hws2 : ‖w - s‖ ≤ 2 := by linarith
    have hsn : ‖s‖ ≤ ‖w₀‖ + 3 := by
      have h1 : ‖s‖ ≤ ‖w₀‖ + ‖w - w₀‖ + ‖w - s‖ := by
        calc ‖s‖ = ‖w₀ + (w - w₀) - (w - s)‖ := by congr 1; abel
          _ ≤ ‖w₀ + (w - w₀)‖ + ‖w - s‖ := norm_sub_le _ _
          _ ≤ ‖w₀‖ + ‖w - w₀‖ + ‖w - s‖ := by gcongr; exact norm_add_le _ _
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      linarith
    -- convexity identity
    have hid : ‖w‖ ^ 2 = ‖s‖ ^ 2 + 2 * inner ℝ s (w - s) + ‖w - s‖ ^ 2 := by
      have := norm_add_sq_real s (w - s)
      rw [show s + (w - s) = w by abel] at this
      exact this
    have hcl : c w = c s + c (w - s) := by rw [map_sub]; ring
    have hc1 : -(‖c‖ * ‖w - s‖) ≤ c (w - s) := by
      have := c.le_opNorm (w - s)
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (c (w - s))]
    have hi1 : -(‖s‖ * ‖w - s‖) ≤ inner ℝ s (w - s) := by
      have := abs_real_inner_le_norm s (w - s)
      linarith [neg_abs_le (inner ℝ s (w - s))]
    have hms := hmin s hs
    have hA : ε * (‖s‖ * ‖w - s‖) ≤ ε * ((‖w₀‖ + 3) * ‖w - s‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsn (norm_nonneg _)) hε
    have hB : L * ‖w - s‖ ≤ L * (κ * ‖G w + b - y‖ + η) := mul_le_mul_of_nonneg_left hws1 hL0
    have hC : 0 ≤ ε / 2 * ‖w - s‖ ^ 2 := by positivity
    have hD' : ε * -(‖s‖ * ‖w - s‖) ≤ ε * inner ℝ s (w - s) := mul_le_mul_of_nonneg_left hi1 hε
    rw [hcl, hid]
    nlinarith
  have hlim : Tendsto (fun k : ℕ => (c w + ε / 2 * ‖w‖ ^ 2) +
      L * (κ * ‖G w + b - y‖ + 1 / ((k : ℝ) + 1))) atTop
      (𝓝 ((c w + ε / 2 * ‖w‖ ^ 2) + L * (κ * ‖G w + b - y‖ + 0))) :=
    tendsto_const_nhds.add ((tendsto_const_nhds.add one_div_succ_tendsto).const_mul L)
  have := ge_of_tendsto' hlim fun k => key _ (one_div_succ_pos k)
    (by rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)])
  rw [add_zero] at this
  linarith [show L * (κ * ‖G w + b - y‖) = κ * L * ‖G w + b - y‖ by ring]

/-- Liminf over the neighbourhood filter is bounded by a limit along a sequence. -/
theorem liminf_nhds_le {m : ℕ} (F : E m → EReal) (hfun : E m → EReal) (hc : Continuous hfun)
    (v : ℕ → E m) (l : E m) (hv : Tendsto v atTop (𝓝 l)) (hle : ∀ k, F (v k) ≤ hfun (v k)) :
    Filter.liminf F (𝓝 l) ≤ hfun l := by
  have h1 : Filter.liminf F (𝓝 l) ≤ Filter.liminf F (Filter.map v atTop) :=
    Filter.liminf_le_liminf_of_le hv
  have h2 : Filter.liminf F (Filter.map v atTop) ≤ Filter.liminf hfun (Filter.map v atTop) :=
    Filter.liminf_le_liminf (Filter.eventually_map.2 (Filter.Eventually.of_forall hle))
  have h3 : Tendsto hfun (Filter.map v atTop) (𝓝 (hfun l)) :=
    (hc.tendsto l).comp hv
  rw [h3.liminf_eq] at h2
  exact h1.trans h2

end T2Aux
end SetConstrSOC.Directional

open SetConstrSOC.Directional

theorem solution {n m : ℕ} (P : Problem n m) (hP : P.Standing)
    (x d : E n) (hmin : IsLocalMinOn P.f P.feasible x) (hx : x ∈ P.feasible)
    (hMS : MetricSubregularDirAt P.g P.Λ x d) (hd : d ∈ P.criticalCone x)
    (hD : (secondOrderTangentSet P.Λ (P.g x) ((fderiv ℝ P.g x) d)).Nonempty) :
    ∃ lam ∈ P.dirMMultipliers x d,
      (∀ A : Set (E m),
        ((fun w => (fderiv ℝ P.g x) w + ((fderiv ℝ (fderiv ℝ P.g) x) d) d) ''
          secondOrderTangentSet P.feasible x d) ⊆ A →
        lowerGenSupport
          (secondOrderTangentSet P.Λ (P.g x) ((fderiv ℝ P.g x) d)) A lam ≤
          (P.hessLag x lam d : EReal)) ∧
      lowerGenSupport₀
        (secondOrderTangentSet P.Λ (P.g x) ((fderiv ℝ P.g x) d)) lam ≤
        (P.hessLag x lam d : EReal) := by
  obtain ⟨κ, hκ⟩ := hMS
  have hκpos : 0 < κ := hκ.2.1
  set c := fderiv ℝ P.f x with hcdef
  set G := fderiv ℝ P.g x with hGdef
  set b := ((fderiv ℝ (fderiv ℝ P.g) x) d) d with hbdef
  set H := ((fderiv ℝ (fderiv ℝ P.f) x) d) d with hHdef
  set D := secondOrderTangentSet P.Λ (P.g x) (G d) with hDdef
  set S := secondOrderTangentSet P.feasible x d with hSdef
  have hdT : G d ∈ tangentCone P.Λ (P.g x) := hd.1
  have hSeq : S = {w | G w + b ∈ D} := proposition_5_11 P hP x d hx κ hκ hdT
  have hEB := proposition_5_12 P hP x d hx κ hκ hdT
  have hDcl : IsClosed D := T2Aux.sots_closed _ _ _
  have hScl : IsClosed S := T2Aux.sots_closed _ _ _
  have hSne : S.Nonempty := (corollary_1 P hP x d hx ⟨κ, hκ⟩ hdT).2 hD
  have hc0 : c d = 0 := lemma_4 P hP x hmin hx d hd ⟨κ, hκ⟩
  have hdF : d ∈ tangentCone P.feasible x := (proposition_5_10 P hP x d hx κ hκ).2 hdT
  have hT1 : ∀ w ∈ S, 0 ≤ c w + H := theorem_1 P hP x hmin hx d hdF hc0
  have hSD : ∀ w ∈ S, G w + b ∈ D := fun w hw => by rw [hSeq] at hw; exact hw
  have hEBr : ∀ w, Metric.infDist w S ≤ κ * Metric.infDist (G w + b) D := by
    intro w
    have h1 := hEB w
    have hne : EMetric.infEdist (G w + b) D ≠ ⊤ := Metric.infEdist_ne_top hD
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hκpos.le] at h2
    exact h2
  -- the regularized problems (19)
  have hmins := fun k : ℕ => T2Aux.quad_min S hScl hSne c (1 / ((k : ℝ) + 1))
    (T2Aux.one_div_succ_pos k)
  choose w hwS hwmin using hmins
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hεpos : ∀ k, 0 < ε k := T2Aux.one_div_succ_pos
  have hεle : ∀ k, ε k ≤ 1 := fun k => by
    simp only [hεdef]; rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
  -- multipliers for the regularized problems, (21)–(22)
  have hmult : ∀ k, ∃ l ∈ limNormal D (G (w k) + b),
      ‖l‖ ≤ κ * (‖c‖ + ε k * (‖w k‖ + 3)) ∧
      ∀ v, c v + ε k * inner ℝ (w k) v + inner ℝ l (G v) = 0 := by
    intro k
    have hpen := T2Aux.exact_penalty S hSne G b D κ hκpos.le hEBr c (ε k) (hεpos k).le (w k)
      (hwS k) (hwmin k)
    have hψ : ∀ u, HasFDerivAt (fun u => c u + ε k / 2 * ‖u‖ ^ 2)
        (c + (ε k) • innerSL ℝ u) u := by
      intro u
      have := (c.hasFDerivAt).add (((hasFDerivAt_id u).norm_sq).const_mul (ε k / 2))
      refine this.congr_fderiv ?_
      ext v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
        smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, id]
      ring
    have hψc : Continuous fun u : E n => c + (ε k) • innerSL ℝ u :=
      continuous_const.add ((innerSL ℝ).continuous.const_smul (ε k))
    obtain ⟨l, hl, hln, hls⟩ := T2Aux.penalty_multiplier G b D hDcl _ _ hψ hψc (w k)
      (hSD _ (hwS k)) 1 (κ * (‖c‖ + ε k * (‖w k‖ + 3))) one_pos
      (by have := hεpos k; positivity) (fun u hu y hy => by
        have := hpen u hu y hy
        simpa using this)
    refine ⟨l, hl, hln, fun v => ?_⟩
    have := hls v
    simpa [innerSL_apply_apply] using this
  choose l hlN hlnorm hlstat using hmult
  -- fix a reference point of S
  obtain ⟨w₀, hw₀⟩ := hSne
  set K₀ := c w₀ + H with hK₀
  have hK₀nn : 0 ≤ K₀ := hT1 w₀ hw₀
  have hsq : ∀ k, (ε k * ‖w k‖) ^ 2 ≤ 2 * ε k * K₀ + ε k ^ 2 * ‖w₀‖ ^ 2 := by
    intro k
    have h1 := hT1 (w k) (hwS k)
    have h2 := hwmin k w₀ hw₀
    have he := hεpos k
    have h3 : ε k / 2 * ‖w k‖ ^ 2 ≤ K₀ + ε k / 2 * ‖w₀‖ ^ 2 := by
      simp only [hK₀]; change c (w k) + ε k / 2 * ‖w k‖ ^ 2 ≤ c w₀ + ε k / 2 * ‖w₀‖ ^ 2 at h2
      linarith
    have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * ε k)
    nlinarith
  -- ε‖w_ε‖ → 0
  have hεw : Tendsto (fun k => ε k • w k) atTop (𝓝 0) := by
    refine T2Aux.tendsto_norm_of_sq_le (e := fun k => 2 * ε k * K₀ + ε k ^ 2 * ‖w₀‖ ^ 2)
      ?_ fun k => ?_
    · have := ((T2Aux.one_div_succ_tendsto.const_mul 2).mul_const K₀).add
        ((T2Aux.one_div_succ_tendsto.pow 2).mul_const (‖w₀‖ ^ 2))
      simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] at this
      exact this
    · rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (hεpos k)]
      exact hsq k
  -- the multipliers are bounded
  set B₂ := 2 * K₀ + ‖w₀‖ ^ 2 with hB₂
  have hεwb : ∀ k, ε k * ‖w k‖ ≤ B₂ + 1 := by
    intro k
    have h1 := hsq k
    have he := hεpos k
    have he1 := hεle k
    have h2 : 2 * ε k * K₀ + ε k ^ 2 * ‖w₀‖ ^ 2 ≤ B₂ := by
      have : ε k ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg ‖w₀‖]
    have h0 : 0 ≤ ε k * ‖w k‖ := by positivity
    nlinarith
  have hlb : ∀ k, l k ∈ Metric.closedBall (0 : E m) (κ * (‖c‖ + (B₂ + 1) + 3)) := by
    intro k
    rw [mem_closedBall_zero_iff]
    refine (hlnorm k).trans (mul_le_mul_of_nonneg_left ?_ hκpos.le)
    have := hεwb k
    have := hεle k
    nlinarith [hεpos k]
  obtain ⟨lam, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hlb
  -- directional normals
  have hdir : ∀ k, l k ∈ dirLimNormal P.Λ (P.g x) (G d) := by
    intro k
    exact lemma_3_14 P.Λ hP.2.2 (P.g x) (G d) (G (w k) + b) hx hdT (hSD _ (hwS k)) (hlN k)
  have hlamdir : lam ∈ dirLimNormal P.Λ (P.g x) (G d) :=
    T2Aux.dln_seq_closed (fun k => hdir (φ k)) hlim
  -- stationarity in the limit
  have hεwφ : Tendsto (fun k => ε (φ k) • w (φ k)) atTop (𝓝 0) := hεw.comp hφ.tendsto_atTop
  have hstat : P.IsStationary x lam := by
    intro v
    have h1 : Tendsto (fun k => c v + inner ℝ (ε (φ k) • w (φ k)) v + inner ℝ (l (φ k)) (G v))
        atTop (𝓝 (c v + inner ℝ (0 : E n) v + inner ℝ lam (G v))) :=
      (tendsto_const_nhds.add (hεwφ.inner tendsto_const_nhds)).add
        (hlim.inner tendsto_const_nhds)
    have h2 : (fun k => c v + inner ℝ (ε (φ k) • w (φ k)) v + inner ℝ (l (φ k)) (G v)) =
        fun _ => 0 := by
      funext k
      rw [real_inner_smul_left]
      exact hlstat (φ k) v
    rw [h2] at h1
    have := tendsto_nhds_unique h1 tendsto_const_nhds
    simpa using this
  -- the key inequality ⟪λ_k, u_k⟫ ≤ ∇²L(x̄, λ_k)(d,d)
  have hkey : ∀ k, inner ℝ (l k) (G (w k) + b) ≤ P.hessLag x (l k) d := by
    intro k
    have h1 := hlstat k (w k)
    have h2 := hT1 (w k) (hwS k)
    have h3 : 0 ≤ ε k * inner ℝ (w k) (w k) :=
      mul_nonneg (hεpos k).le real_inner_self_nonneg
    simp only [Problem.hessLag]
    rw [inner_add_right]
    change inner ℝ (l k) (G (w k)) + inner ℝ (l k) b ≤ H + inner ℝ (l k) b
    linarith
  have hcont : Continuous fun l' : E m => ((P.hessLag x l' d : ℝ) : EReal) := by
    simp only [Problem.hessLag]
    exact continuous_coe_real_ereal.comp (continuous_const.add
      (continuous_id.inner continuous_const))
  have h17 : ∀ A : Set (E m), ((fun w => G w + b) '' S) ⊆ A →
      lowerGenSupport D A lam ≤ (P.hessLag x lam d : EReal) := by
    intro A hA
    refine T2Aux.liminf_nhds_le _ _ hcont (l ∘ φ) lam hlim fun k => ?_
    have hu : G (w (φ k)) + b ∈ A := hA ⟨w (φ k), hwS (φ k), rfl⟩
    calc (⨅ u ∈ {u | u ∈ A ∧ (l ∘ φ) k ∈ limNormal D u}, ((inner ℝ ((l ∘ φ) k) u : ℝ) : EReal))
        ≤ ((inner ℝ ((l ∘ φ) k) (G (w (φ k)) + b) : ℝ) : EReal) :=
          iInf₂_le (G (w (φ k)) + b) ⟨hu, hlN (φ k)⟩
      _ ≤ (P.hessLag x ((l ∘ φ) k) d : EReal) := EReal.coe_le_coe_iff.2 (hkey (φ k))
  refine ⟨lam, ⟨hstat, hlamdir⟩, h17, ?_⟩
  exact h17 Set.univ (Set.subset_univ _)
