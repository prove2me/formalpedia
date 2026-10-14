-- Prove2me | solution 1 for Plasticity.Ext.BishopPhelps
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:10:37.459986+00:00
-- url     : https://prove2.me/submissions/539fe654-fc6d-4d0b-b287-fd13a5bb7785

import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.LocallyConvex.Separation
import Theorems.Thm_EkelandVP_General_ekeland_variational_principle

namespace Sol_Plasticity_Ext_BishopPhelps

open Metric

/-- If `c + t * d < u` for every `t > 0`, then `c ≤ u`. -/
lemma le_of_forall_pos_add_lt {c d u : ℝ} (h : ∀ t : ℝ, 0 < t → c + t * d < u) : c ≤ u := by
  by_contra hc
  rw [not_le] at hc
  have hd : 0 < |d| + 1 := by positivity
  have ht : 0 < (c - u) / (|d| + 1) := div_pos (by linarith) hd
  have h1 := h _ ht
  have h2 : -((c - u) / (|d| + 1) * |d|) ≤ (c - u) / (|d| + 1) * d := by
    have := neg_abs_le d
    nlinarith
  have h3 : (c - u) / (|d| + 1) * |d| < c - u := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    nlinarith [abs_nonneg d]
  linarith

/-- A functional that is maximized over the unit ball at `v` attains its norm at `v`. -/
lemma attains_of_max {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (ψ : StrongDual ℝ Y) (v : Y) (hv : ‖v‖ ≤ 1)
    (hmax : ∀ b : Y, ‖b‖ ≤ 1 → ψ b ≤ ψ v) : ψ v = ‖ψ‖ := by
  have h0 : 0 ≤ ψ v := by simpa using hmax 0 (by simp)
  apply le_antisymm
  · calc ψ v ≤ ‖ψ v‖ := Real.le_norm_self _
      _ ≤ ‖ψ‖ * ‖v‖ := ψ.le_opNorm v
      _ ≤ ‖ψ‖ := mul_le_of_le_one_right (norm_nonneg ψ) hv
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm h0
    intro x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := hmax (-x) (by rw [norm_neg, hx])
      rw [map_neg] at this
      linarith
    · exact hmax x hx.le

/-- Step 1 (Ekeland): a point of the unit ball beyond which `φ` grows slower than `δ‖·‖`. -/
lemma ekeland_step {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (φ : StrongDual ℝ Y) (hφ : ‖φ‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v : Y, ‖v‖ ≤ 1 ∧ ∀ w : Y, ‖w‖ ≤ 1 → w ≠ v → φ w - φ v < δ * ‖w - v‖ := by
  let V := closedBall (0 : Y) 1
  have : CompleteSpace V := isClosed_closedBall.isComplete.completeSpace_coe
  let F : V → EReal := fun w => ((-φ (w : Y) : ℝ) : EReal)
  have hFb : ∀ w : V, ((-1 : ℝ) : EReal) ≤ F w := by
    intro w
    simp only [F]
    rw [EReal.coe_le_coe_iff]
    have hw : ‖(w : Y)‖ ≤ 1 := mem_closedBall_zero_iff.mp w.2
    have h1 := φ.le_opNorm (w : Y)
    rw [Real.norm_eq_abs] at h1
    have h2 : ‖φ‖ * ‖(w : Y)‖ ≤ 1 := by
      nlinarith [norm_nonneg φ, norm_nonneg (w : Y)]
    linarith [le_abs_self (φ w)]
  have hcont : Continuous F :=
    continuous_coe_real_ereal.comp ((φ.continuous.comp continuous_subtype_val).neg)
  have hinf : ((-1 : ℝ) : EReal) ≤ ⨅ v, F v := le_iInf hFb
  let u0 : V := ⟨0, by simp [V]⟩
  have hu : F u0 ≤ (⨅ v, F v) + ((1 : ℝ) : EReal) := by
    have h1 : F u0 = ((-1 : ℝ) : EReal) + ((1 : ℝ) : EReal) := by
      simp only [F, u0, map_zero, neg_zero]
      rw [← EReal.coe_add]
      norm_num
    rw [h1]
    exact add_le_add hinf le_rfl
  obtain ⟨v, -, -, hv⟩ := EkelandVP.General.ekeland_variational_principle F
    hcont.lowerSemicontinuous ⟨u0, EReal.coe_ne_top _⟩
    (lt_of_lt_of_le (EReal.bot_lt_coe _) hinf) 1 one_pos u0 hu (1 / δ) (by positivity)
  refine ⟨v, mem_closedBall_zero_iff.mp v.2, fun w hw hne => ?_⟩
  let w' : V := ⟨w, mem_closedBall_zero_iff.mpr hw⟩
  have hne' : w' ≠ v := by
    intro h
    apply hne
    rw [← h]
  have := hv w' hne'
  simp only [F] at this
  rw [← EReal.coe_sub, EReal.coe_lt_coe_iff, one_div_one_div, Subtype.dist_eq,
    dist_eq_norm, norm_sub_rev] at this
  simp only [w'] at this
  linarith

/-- The theorem for a functional of norm one, with an explicit closeness bound `4δ`. -/
lemma main_unit {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (φ : StrongDual ℝ Y) (hφ : ‖φ‖ = 1) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    ∃ ψ : StrongDual ℝ Y, ‖ψ - φ‖ ≤ 4 * δ ∧ ∃ y : Y, ‖y‖ ≤ 1 ∧ ψ y = ‖ψ‖ := by
  -- Step 1: the Ekeland point `v`.
  obtain ⟨v, hv, hvE⟩ := ekeland_step φ hφ.le δ hδ
  -- Step 2: a point `w₀` of the unit ball where `φ` is nearly maximal.
  obtain ⟨w₀, hw₀, hφw₀⟩ : ∃ w₀ : Y, ‖w₀‖ ≤ 1 ∧ 1 - δ < φ w₀ := by
    obtain ⟨x, hx, hfx⟩ := φ.exists_lt_apply_of_lt_opNorm (show 1 - δ < ‖φ‖ by rw [hφ]; linarith)
    rw [Real.norm_eq_abs] at hfx
    rcases le_or_gt 0 (φ x) with h | h
    · exact ⟨x, hx.le, by rwa [abs_of_nonneg h] at hfx⟩
    · refine ⟨-x, by rw [norm_neg]; exact hx.le, ?_⟩
      rw [map_neg]
      rw [abs_of_neg h] at hfx
      exact hfx
  have hφy : ∀ y : Y, |φ y| ≤ ‖y‖ := by
    intro y
    have := φ.le_opNorm y
    rwa [Real.norm_eq_abs, hφ, one_mul] at this
  have hφw₀1 : φ w₀ ≤ 1 := le_trans (le_abs_self _) ((hφy w₀).trans hw₀)
  -- Step 3: the open convex set `A = v + C`, disjoint from the unit ball, and separation.
  let A : Set Y := {w | δ * ‖w - v‖ < φ w - φ v}
  have hAopen : IsOpen A :=
    isOpen_lt (continuous_const.mul ((continuous_id.sub continuous_const).norm))
      (φ.continuous.sub continuous_const)
  have hAconv : Convex ℝ A := by
    intro x hx y hy a b ha hb hab
    simp only [A, Set.mem_ofPred_eq] at hx hy ⊢
    have e1 : a • x + b • y - v = a • (x - v) + b • (y - v) := by
      calc a • x + b • y - v = a • x + b • y - (a + b) • v := by rw [hab, one_smul]
        _ = a • (x - v) + b • (y - v) := by rw [add_smul, smul_sub, smul_sub]; abel
    have hN : ‖a • x + b • y - v‖ ≤ a * ‖x - v‖ + b * ‖y - v‖ := by
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have hφab : φ (a • x + b • y) = a * φ x + b * φ y := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hφab]
    have h3 : δ * ‖a • x + b • y - v‖ ≤ δ * (a * ‖x - v‖ + b * ‖y - v‖) :=
      mul_le_mul_of_nonneg_left hN hδ.le
    have h4 : φ v = a * φ v + b * φ v := by rw [← add_mul, hab, one_mul]
    rcases ha.eq_or_lt with ha0 | hapos
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      nlinarith
    · have h1 : 0 < a * ((φ x - φ v) - δ * ‖x - v‖) := mul_pos hapos (by linarith)
      have h2 : 0 ≤ b * ((φ y - φ v) - δ * ‖y - v‖) := mul_nonneg hb (by linarith)
      nlinarith
  have hdisj : Disjoint A (closedBall (0 : Y) 1) := by
    rw [Set.disjoint_left]
    intro w hwA hwB
    simp only [A, Set.mem_ofPred_eq] at hwA
    rw [mem_closedBall_zero_iff] at hwB
    by_cases hwv : w = v
    · subst hwv
      simp at hwA
    · have := hvE w hwB hwv
      linarith
  obtain ⟨f, u, hfA, hfB⟩ := geometric_hahn_banach_open hAconv hAopen (convex_closedBall 0 1) hdisj
  -- Step 4: cone positivity.
  have hδw₀ : δ * ‖w₀‖ < φ w₀ := by
    have : δ * ‖w₀‖ ≤ δ := mul_le_of_le_one_right hδ.le hw₀
    linarith
  have hC : ∀ z : Y, δ * ‖z‖ < φ z → f v + f z < u := by
    intro z hz
    have hmem : v + z ∈ A := by
      simp only [A, Set.mem_ofPred_eq, add_sub_cancel_left, map_add]
      linarith
    have := hfA _ hmem
    rwa [map_add] at this
  have hfv : f v = u := by
    refine le_antisymm (le_of_forall_pos_add_lt (d := f w₀) fun t ht => ?_)
      (hfB v (mem_closedBall_zero_iff.mpr hv))
    have := hC (t • w₀) (by
      rw [norm_smul, Real.norm_of_nonneg ht.le, map_smul, smul_eq_mul]
      nlinarith)
    rwa [map_smul, smul_eq_mul] at this
  have hCs : ∀ z : Y, δ * ‖z‖ < φ z → f z < 0 := by
    intro z hz
    have := hC z hz
    linarith
  have hCw : ∀ z : Y, δ * ‖z‖ ≤ φ z → f z ≤ 0 := by
    intro z hz
    refine le_of_forall_pos_add_lt (d := f w₀) fun t ht => ?_
    have hlt : δ * ‖z + t • w₀‖ < φ (z + t • w₀) := by
      have hn : ‖z + t • w₀‖ ≤ ‖z‖ + t * ‖w₀‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_of_nonneg ht.le]
      rw [map_add, map_smul, smul_eq_mul]
      have := mul_le_mul_of_nonneg_left hn hδ.le
      nlinarith
    have := hCs _ hlt
    rwa [map_add, map_smul, smul_eq_mul] at this
  -- Pass to `g = -f`.
  let g : StrongDual ℝ Y := -f
  have hg : ∀ y, g y = -f y := fun y => rfl
  have hgmax : ∀ b : Y, ‖b‖ ≤ 1 → g b ≤ g v := by
    intro b hb
    rw [hg, hg, hfv]
    have := hfB b (mem_closedBall_zero_iff.mpr hb)
    linarith
  have hgw₀ : 0 < g w₀ := by
    rw [hg]
    have := hCs w₀ hδw₀
    linarith
  -- Step 5: on `ker φ`, `|g z| ≤ 2δ‖z‖ g w₀`.
  have hker : ∀ z : Y, φ z = 0 → |g z| ≤ 2 * δ * ‖z‖ * g w₀ := by
    intro z hz
    have hcone : ∀ z' : Y, φ z' = 0 → ‖z'‖ = ‖z‖ →
        0 ≤ g z' + 2 * δ * ‖z‖ * g w₀ := by
      intro z' hz' hnz'
      set t := 2 * δ * ‖z‖ with ht
      have ht0 : 0 ≤ t := by positivity
      have hle : δ * ‖z' + t • w₀‖ ≤ φ (z' + t • w₀) := by
        have hn : ‖z' + t • w₀‖ ≤ ‖z‖ + t := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg ht0, hnz']
          nlinarith
        rw [map_add, map_smul, smul_eq_mul, hz', zero_add]
        have h1 := mul_le_mul_of_nonneg_left hn hδ.le
        have h2 : 0 ≤ δ * ‖z‖ * (2 * φ w₀ - 1 - 2 * δ) :=
          mul_nonneg (mul_nonneg hδ.le (norm_nonneg z)) (by linarith)
        nlinarith
      have := hCw _ hle
      rw [map_add, map_smul, smul_eq_mul] at this
      rw [hg, hg]
      linarith
    have hp := hcone z hz rfl
    have hm := hcone (-z) (by rw [map_neg, hz, neg_zero]) (norm_neg z)
    rw [map_neg] at hm
    rw [abs_le]
    constructor <;> linarith
  -- The rescaled functional `ψ`.
  let c : ℝ := φ w₀ / g w₀
  have hc : 0 < c := div_pos (by linarith) hgw₀
  let ψ : StrongDual ℝ Y := c • g
  have hψ : ∀ y, ψ y = c * g y := fun y => rfl
  refine ⟨ψ, ?_, v, hv, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
    have ha : 0 < φ w₀ := by linarith
    have key : (ψ - φ) y = c * g (y - (φ y / φ w₀) • w₀) := by
      rw [sub_apply, hψ, map_sub, map_smul, smul_eq_mul]
      simp only [c]
      field_simp
    have hz : φ (y - (φ y / φ w₀) • w₀) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul]
      field_simp
      ring
    have hgz := hker _ hz
    have hnz : ‖y - (φ y / φ w₀) • w₀‖ ≤ ‖y‖ + |φ y| / φ w₀ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos ha]
      have : |φ y| / φ w₀ * ‖w₀‖ ≤ |φ y| / φ w₀ := mul_le_of_le_one_right (by positivity) hw₀
      linarith
    rw [key, Real.norm_eq_abs, abs_mul, abs_of_pos hc]
    have hcg : c * g w₀ = φ w₀ := by
      simp only [c]
      field_simp
    calc c * |g (y - (φ y / φ w₀) • w₀)|
        ≤ c * (2 * δ * ‖y - (φ y / φ w₀) • w₀‖ * g w₀) := mul_le_mul_of_nonneg_left hgz hc.le
      _ = 2 * δ * φ w₀ * ‖y - (φ y / φ w₀) • w₀‖ := by rw [← hcg]; ring
      _ ≤ 2 * δ * φ w₀ * (‖y‖ + |φ y| / φ w₀) :=
          mul_le_mul_of_nonneg_left hnz (by positivity)
      _ = 2 * δ * φ w₀ * ‖y‖ + 2 * δ * |φ y| := by field_simp
      _ ≤ 2 * δ * ‖y‖ + 2 * δ * ‖y‖ := by
          have h1 : 2 * δ * φ w₀ * ‖y‖ ≤ 2 * δ * ‖y‖ := by
            have := mul_le_mul_of_nonneg_left hφw₀1 (by positivity : 0 ≤ 2 * δ * ‖y‖)
            nlinarith
          have h2 : 2 * δ * |φ y| ≤ 2 * δ * ‖y‖ :=
            mul_le_mul_of_nonneg_left (hφy y) (by positivity)
          linarith
      _ = 4 * δ * ‖y‖ := by ring
  · refine attains_of_max ψ v hv fun b hb => ?_
    rw [hψ, hψ]
    exact mul_le_mul_of_nonneg_left (hgmax b hb) hc.le

end Sol_Plasticity_Ext_BishopPhelps

theorem solution {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (φ : StrongDual ℝ Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : StrongDual ℝ Y, ‖ψ - φ‖ < ε ∧ ∃ y : Y, ‖y‖ ≤ 1 ∧ ψ y = ‖ψ‖ := by
  by_cases h0 : φ = 0
  · exact ⟨0, by simpa [h0] using hε, 0, by simp, by simp⟩
  · have hn : 0 < ‖φ‖ := norm_pos_iff.mpr h0
    let φ₁ : StrongDual ℝ Y := ‖φ‖⁻¹ • φ
    have hφ₁ : ‖φ₁‖ = 1 := by
      simp only [φ₁]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    let δ : ℝ := min (1 / 4) (ε / (8 * ‖φ‖))
    have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
    obtain ⟨ψ₁, hψ₁, y, hy, hψy⟩ :=
      Sol_Plasticity_Ext_BishopPhelps.main_unit φ₁ hφ₁ δ hδ (min_le_left _ _)
    refine ⟨‖φ‖ • ψ₁, ?_, y, hy, ?_⟩
    · have e : ‖φ‖ • ψ₁ - φ = ‖φ‖ • (ψ₁ - φ₁) := by
        simp only [φ₁]
        rw [smul_sub, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [e, norm_smul, norm_norm]
      calc ‖φ‖ * ‖ψ₁ - φ₁‖ ≤ ‖φ‖ * (4 * δ) := mul_le_mul_of_nonneg_left hψ₁ hn.le
        _ ≤ ‖φ‖ * (4 * (ε / (8 * ‖φ‖))) := by
            gcongr
            exact min_le_right _ _
        _ = ε / 2 := by field_simp; ring
        _ < ε := by linarith
    · rw [smul_apply, smul_eq_mul, hψy, norm_smul, norm_norm]
