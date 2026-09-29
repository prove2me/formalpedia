-- Prove2me | solution 1 for ThreeOpSplitting.Convergence.main_convergence_theorem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:28:06.923049+00:00
-- url     : https://prove2.me/submissions/93c50c20-6c34-4f32-ada1-c6d43848c8b9

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_ThreeOpSplitting_Convergence_RegularityConditions

open Filter Topology
open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.Convergence

lemma real_ulim_exists (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) (U : Ultrafilter ℕ) :
    ∃ a, Tendsto f U (𝓝 a) := by
  have hc : IsCompact (Set.Icc (-M) M) := isCompact_Icc
  obtain ⟨a, -, ha⟩ := hc.ultrafilter_le_nhds (U.map f) (by
    rw [Filter.le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact Filter.univ_mem' (fun k => abs_le.1 (hM k)))
  exact ⟨a, ha⟩

lemma exists_ulim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) (M : ℝ) (hM : ∀ k, ‖u k‖ ≤ M) (U : Ultrafilter ℕ) :
    ∃ w : H, ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hb : ∀ y k, |inner ℝ (u k) y| ≤ M * ‖y‖ := fun y k =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _))
  have hex : ∀ y, ∃ a, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 a) :=
    fun y => real_ulim_exists _ _ (hb y) U
  set L : H → ℝ := fun y => limUnder (U : Filter ℕ) (fun k => inner ℝ (u k) y) with hL
  have hLt : ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (L y)) :=
    fun y => tendsto_nhds_limUnder (hex y)
  have hadd : ∀ y y', L (y + y') = L y + L y' := by
    intro y y'
    have h1 := hLt (y + y')
    have h2 := (hLt y).add (hLt y')
    simp only [inner_add_right] at h1
    exact tendsto_nhds_unique h1 h2
  have hsmul : ∀ (c : ℝ) y, L (c • y) = c * L y := by
    intro c y
    have h1 := hLt (c • y)
    have h2 := (hLt y).const_mul c
    simp only [real_inner_smul_right] at h1
    exact tendsto_nhds_unique h1 h2
  let Ll : H →ₗ[ℝ] ℝ :=
    { toFun := L, map_add' := hadd, map_smul' := fun c y => by simp [hsmul] }
  have hbd : ∀ y, ‖Ll y‖ ≤ M * ‖y‖ := by
    intro y
    show |L y| ≤ M * ‖y‖
    have := (hLt y)
    have hmem : ∀ᶠ k in (U : Filter ℕ), inner ℝ (u k) y ∈ Set.Icc (-(M * ‖y‖)) (M * ‖y‖) :=
      Filter.Eventually.of_forall (fun k => abs_le.1 (hb y k))
    exact abs_le.2 (isClosed_Icc.mem_of_tendsto this hmem)
  let Lc : StrongDual ℝ H := Ll.mkContinuous M hbd
  refine ⟨(InnerProductSpace.toDual ℝ H).symm Lc, fun y => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact hLt y

lemma weak_of_ulim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) (M : ℝ) (hM : ∀ k, ‖u k‖ ≤ M) (w0 : H)
    (h : ∀ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop → ∀ w : H,
      (∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y))) → w = w0) :
    WeakTendsto u w0 := by
  intro y
  rw [tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨w, hw⟩ := exists_ulim u M hM U
  have := h U hU w hw
  subst this
  exact hw y

lemma demiclosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → H) (hT : ∀ u v, ‖T u - T v‖ ≤ ‖u - v‖) (z : ℕ → H) (M : ℝ)
    (hM : ∀ k, ‖z k‖ ≤ M)
    (hr : Tendsto (fun k => ‖T (z k) - z k‖) atTop (𝓝 0)) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (w : H)
    (hw : ∀ y, Tendsto (fun k => inner ℝ (z k) y) U (𝓝 (inner ℝ w y))) : T w = w := by
  set d := w - T w with hd
  have key : ∀ k, ‖d‖ ^ 2 + 2 * (inner ℝ (z k) d - inner ℝ w d) ≤
      ‖T (z k) - z k‖ ^ 2 + 2 * ‖T (z k) - z k‖ * (M + ‖w‖) := by
    intro k
    have e1 : z k - T w = (z k - T (z k)) + (T (z k) - T w) := by abel
    have h1 : ‖z k - T w‖ ≤ ‖T (z k) - z k‖ + ‖z k - w‖ := by
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_sub_rev (z k) (T (z k))]
      linarith [hT (z k) w]
    have e2 : z k - T w = (z k - w) + d := by rw [hd]; abel
    have h2 : ‖z k - T w‖ ^ 2 = ‖z k - w‖ ^ 2 + 2 * inner ℝ (z k - w) d + ‖d‖ ^ 2 := by
      rw [e2, norm_add_sq_real]
    have h3 : ‖z k - w‖ ≤ M + ‖w‖ := (norm_sub_le _ _).trans (by linarith [hM k])
    have h0 : 0 ≤ ‖z k - T w‖ := norm_nonneg _
    have hsq : ‖z k - T w‖ ^ 2 ≤ (‖T (z k) - z k‖ + ‖z k - w‖) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    rw [inner_sub_left] at h2
    have hr0 : 0 ≤ ‖T (z k) - z k‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h3 hr0]
  have hL : Tendsto (fun k => ‖d‖ ^ 2 + 2 * (inner ℝ (z k) d - inner ℝ w d)) U
      (𝓝 (‖d‖ ^ 2 + 2 * (inner ℝ w d - inner ℝ w d))) :=
    tendsto_const_nhds.add ((hw d).sub tendsto_const_nhds |>.const_mul 2)
  have hR : Tendsto (fun k => ‖T (z k) - z k‖ ^ 2 + 2 * ‖T (z k) - z k‖ * (M + ‖w‖)) U
      (𝓝 (0 ^ 2 + 2 * 0 * (M + ‖w‖))) := by
    have := hr.mono_left hU
    exact (this.pow 2).add ((this.const_mul 2).mul_const _)
  have hle := le_of_tendsto_of_tendsto' hL hR key
  simp only [sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_mul] at hle
  have : ‖d‖ = 0 := by nlinarith [norm_nonneg d]
  rw [norm_eq_zero, hd, sub_eq_zero] at this
  exact this.symm

lemma opial_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (z : ℕ → H) (w1 w2 : H) (U1 U2 : Ultrafilter ℕ)
    (h1 : (U1 : Filter ℕ) ≤ atTop) (h2 : (U2 : Filter ℕ) ≤ atTop)
    (hw1 : ∀ y, Tendsto (fun k => inner ℝ (z k) y) U1 (𝓝 (inner ℝ w1 y)))
    (hw2 : ∀ y, Tendsto (fun k => inner ℝ (z k) y) U2 (𝓝 (inner ℝ w2 y)))
    (hc1 : ∃ d, Tendsto (fun k => ‖z k - w1‖) atTop (𝓝 d))
    (hc2 : ∃ d, Tendsto (fun k => ‖z k - w2‖) atTop (𝓝 d)) : w1 = w2 := by
  obtain ⟨d1, hd1⟩ := hc1
  obtain ⟨d2, hd2⟩ := hc2
  set v := w1 - w2 with hv
  have hg : Tendsto (fun k => ‖z k - w2‖ ^ 2 - ‖z k - w1‖ ^ 2) atTop (𝓝 (d2 ^ 2 - d1 ^ 2)) :=
    (hd2.pow 2).sub (hd1.pow 2)
  have hid : ∀ k, ‖z k - w2‖ ^ 2 - ‖z k - w1‖ ^ 2 =
      2 * inner ℝ (z k) v - 2 * inner ℝ w1 v + ‖v‖ ^ 2 := by
    intro k
    have e : z k - w2 = (z k - w1) + v := by rw [hv]; abel
    rw [e, norm_add_sq_real, inner_sub_left]; ring
  simp only [hid] at hg
  have g1 : Tendsto (fun k => 2 * inner ℝ (z k) v - 2 * inner ℝ w1 v + ‖v‖ ^ 2) U1
      (𝓝 (2 * inner ℝ w1 v - 2 * inner ℝ w1 v + ‖v‖ ^ 2)) :=
    (((hw1 v).const_mul 2).sub tendsto_const_nhds).add tendsto_const_nhds
  have g2 : Tendsto (fun k => 2 * inner ℝ (z k) v - 2 * inner ℝ w1 v + ‖v‖ ^ 2) U2
      (𝓝 (2 * inner ℝ w2 v - 2 * inner ℝ w1 v + ‖v‖ ^ 2)) :=
    (((hw2 v).const_mul 2).sub tendsto_const_nhds).add tendsto_const_nhds
  have e1 := tendsto_nhds_unique g1 (hg.mono_left h1)
  have e2 := tendsto_nhds_unique g2 (hg.mono_left h2)
  have e3 : inner ℝ w2 v - inner ℝ w1 v = -‖v‖ ^ 2 := by
    rw [← inner_sub_left, ← real_inner_self_eq_norm_sq, hv, ← inner_neg_left, neg_sub]
  have : ‖v‖ ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  rw [norm_eq_zero, hv, sub_eq_zero] at this
  exact this

theorem l23_aux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U T₁ V : H → H) (hU : IsFirmlyNonexpansive U) (hT₁ : IsFirmlyNonexpansive T₁) :
    let S : H → H := fun x => U x + T₁ (V x)
    let W : H → H := fun x => x - ((2 : ℝ) • U x + V x)
    ∀ z w : H,
      ‖S z - S w‖ ^ 2 ≤ ‖z - w‖ ^ 2 - ‖(z - S z) - (w - S w)‖ ^ 2
        - 2 * ⟪T₁ (V z) - T₁ (V w), W z - W w⟫_ℝ := by
  intro S W z w
  set a := U z - U w with ha
  set b := T₁ (V z) - T₁ (V w) with hb
  set d := z - w with hd
  set v := V z - V w with hv
  have e1 : S z - S w = a + b := by simp only [S, ha, hb]; abel
  have e2 : (z - S z) - (w - S w) = d - (a + b) := by simp only [S, ha, hb, hd]; abel
  have e3 : W z - W w = d - (2 : ℝ) • a - v := by simp only [W, ha, hd, hv]; module
  have hUa : ‖a‖ ^ 2 ≤ ⟪a, d⟫_ℝ := hU z w
  have hTb : ‖b‖ ^ 2 ≤ ⟪b, v⟫_ℝ := hT₁ (V z) (V w)
  rw [e1, e2, e3]
  clear_value a b d v
  rw [norm_sub_sq_real d (a + b), norm_add_sq_real a b, inner_add_right d a b,
    inner_sub_right b (d - (2:ℝ) • a) v, inner_sub_right b d ((2:ℝ) • a),
    real_inner_smul_right b a 2]
  have s1 : ⟪d, a⟫_ℝ = ⟪a, d⟫_ℝ := real_inner_comm _ _
  have s2 : ⟪d, b⟫_ℝ = ⟪b, d⟫_ℝ := real_inner_comm _ _
  have s3 : ⟪b, a⟫_ℝ = ⟪a, b⟫_ℝ := real_inner_comm _ _
  nlinarith

/-- `I - T` is firmly nonexpansive when `T` is. -/
lemma firm_compl {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (T : H → H)
    (hT : IsFirmlyNonexpansive T) : IsFirmlyNonexpansive (fun x => x - T x) := by
  intro x y
  have h := hT x y
  have e : (x - T x) - (y - T y) = (x - y) - (T x - T y) := by abel
  simp only
  rw [e, norm_sub_sq_real (x - y) (T x - T y), inner_sub_left (x - y) (T x - T y) (x - y),
    real_inner_self_eq_norm_sq]
  have := real_inner_comm (x - y) (T x - T y)
  linarith

/-- The key inequality for `T = threeOp γ T₁ T₂ C` with a Young parameter `ε > 0`. -/
lemma key_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T₁ T₂ C : H → H) (β γ ε : ℝ)
    (hT₁ : IsFirmlyNonexpansive T₁) (hT₂ : IsFirmlyNonexpansive T₂)
    (hC : IsCocoercive β C) (hγ0 : 0 < γ) (hε : 0 < ε) (z w : H) :
    ‖threeOp γ T₁ T₂ C z - threeOp γ T₁ T₂ C w‖ ^ 2 ≤ ‖z - w‖ ^ 2
      - (1 - ε) * ‖(z - threeOp γ T₁ T₂ C z) - (w - threeOp γ T₁ T₂ C w)‖ ^ 2
      - γ * (2 * β - γ / ε) * ‖C (T₂ z) - C (T₂ w)‖ ^ 2 := by
  set T := threeOp γ T₁ T₂ C with hTdef
  set U : H → H := fun x => x - T₂ x with hUdef
  set V : H → H := fun x => (2 : ℝ) • T₂ x - x - γ • C (T₂ x) with hVdef
  have hS : ∀ x, U x + T₁ (V x) = T x := by
    intro x; simp only [hUdef, hVdef, hTdef, threeOp]; abel
  have hW : ∀ x, x - ((2 : ℝ) • U x + V x) = γ • C (T₂ x) := by
    intro x; simp only [hUdef, hVdef]; module
  have hT1V : ∀ x, T₁ (V x) = T x - x + T₂ x := by
    intro x; rw [← hS x]; simp only [hUdef]; abel
  have h23 := l23_aux U T₁ V (firm_compl T₂ hT₂) hT₁ z w
  simp only [hS, hW] at h23
  rw [hT1V, hT1V] at h23
  set c := C (T₂ z) - C (T₂ w) with hc
  set p := T₂ z - T₂ w with hp
  set e := (T z - z) - (T w - w) with he
  have hsplit : (T z - z + T₂ z) - (T w - w + T₂ w) = e + p := by rw [he, hp]; abel
  have hWd : γ • C (T₂ z) - γ • C (T₂ w) = γ • c := by rw [hc, smul_sub]
  rw [hsplit, hWd, real_inner_smul_right, inner_add_left] at h23
  -- cocoercivity
  have hcoc : β * ‖c‖ ^ 2 ≤ ⟪c, p⟫_ℝ := hC (T₂ z) (T₂ w)
  have hcp : ⟪p, c⟫_ℝ = ⟪c, p⟫_ℝ := real_inner_comm _ _
  -- Young
  have hY0 : 0 ≤ ‖ε • e + γ • c‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε, abs_of_pos hγ0] at hY0
  have hY : -2 * γ * ⟪e, c⟫_ℝ ≤ ε * ‖e‖ ^ 2 + γ ^ 2 / ε * ‖c‖ ^ 2 := by
    have h1 : 0 ≤ (ε * ‖e‖) ^ 2 + 2 * (ε * (γ * ⟪e, c⟫_ℝ)) + (γ * ‖c‖) ^ 2 := hY0
    have h2 : (ε * ‖e‖) ^ 2 + 2 * (ε * (γ * ⟪e, c⟫_ℝ)) + (γ * ‖c‖) ^ 2 =
        ε * (ε * ‖e‖ ^ 2 + 2 * γ * ⟪e, c⟫_ℝ + γ ^ 2 / ε * ‖c‖ ^ 2) := by
      field_simp
    rw [h2] at h1
    have h3 := (mul_nonneg_iff_of_pos_left hε).1 h1
    linarith
  have hnorm : ‖(z - T z) - (w - T w)‖ = ‖e‖ := by
    rw [he, ← norm_neg]; congr 1; abel
  rw [hnorm]
  rw [hnorm] at h23
  have hγc : γ * (2 * β - γ / ε) * ‖c‖ ^ 2 = 2 * γ * (β * ‖c‖ ^ 2) - γ ^ 2 / ε * ‖c‖ ^ 2 := by
    field_simp
  have hγcoc := mul_le_mul_of_nonneg_left hcoc (by linarith : (0:ℝ) ≤ 2 * γ)
  nlinarith

lemma resolvent_firm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (A : H → Set H) (J : H → H) (hγ : 0 < γ) (hAm : IsMonotoneOp A)
    (hJ : IsResolvent γ A J) : IsFirmlyNonexpansive J := by
  intro x y
  have h := hAm (J x) (J y) _ _ (hJ x) (hJ y)
  rw [← smul_sub, real_inner_smul_right] at h
  have h2 : 0 ≤ ⟪J x - J y, x - J x - (y - J y)⟫_ℝ :=
    (mul_nonneg_iff_of_pos_left (inv_pos.2 hγ)).1 h
  have e : x - J x - (y - J y) = (x - y) - (J x - J y) := by abel
  rw [e, inner_sub_right, real_inner_self_eq_norm_sq] at h2
  linarith

lemma affine_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p q : H) (l : ℝ) :
    ‖(1 - l) • p + l • q‖ ^ 2 = (1 - l) * ‖p‖ ^ 2 + l * ‖q‖ ^ 2 - l * (1 - l) * ‖q - p‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
    real_inner_comm p q]
  ring

theorem desc_aux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ ε : ℝ) (JA JB : H → H) (lam : ℕ → ℝ) (z0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ0 : 0 < γ) (hγ : γ < 2 * β * ε)
    (hlam : ∀ j, 0 < lam j ∧ lam j < 1 / alpha ε)
    (zs : H) (hzs : zs ∈ Function.fixedPoints (threeOp γ JA JB C)) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    let xB := xBSeq γ JA JB C lam z0
    (∀ k : ℕ,
        ‖z (k + 1) - zs‖ ^ 2 + tau ε (lam k) * ‖T (z k) - z k‖ ^ 2
          + γ * lam k * (2 * β - γ / ε) * ‖C (xB k) - C (JB zs)‖ ^ 2 ≤ ‖z k - zs‖ ^ 2) ∧
      ∀ c : ℝ, 0 < c → (∀ j, c ≤ lam j) → ∀ k : ℕ,
        Summable (fun i : ℕ => ‖C (xB (k + i)) - C (JB zs)‖ ^ 2) ∧
          ∑' i : ℕ, ‖C (xB (k + i)) - C (JB zs)‖ ^ 2
            ≤ ‖z k - zs‖ ^ 2 / (γ * c * (2 * β - γ / ε)) := by
  intro T z xB
  have hfA := resolvent_firm γ A JA hγ0 hA.1 hJA
  have hfB := resolvent_firm γ B JB hγ0 hB.1 hJB
  have hTzs : T zs = zs := hzs
  have hα : alpha ε = 1 / (2 - ε) := rfl
  have h2e : 0 < 2 - ε := by linarith
  have hcoefα : (1 - alpha ε) / alpha ε = 1 - ε := by
    rw [hα]; field_simp; ring
  have hκ : 0 < 2 * β - γ / ε := by
    rw [sub_pos, div_lt_iff₀ hε0]; linarith
  have hstep : ∀ k, z (k + 1) = (1 - lam k) • (z k - zs) + lam k • (T (z k) - zs) + zs := by
    intro k
    show zSeq γ JA JB C lam z0 (k + 1) = _
    simp only [zSeq, T, threeOp, z]
    module
  have h26 : ∀ k : ℕ,
      ‖z (k + 1) - zs‖ ^ 2 + tau ε (lam k) * ‖T (z k) - z k‖ ^ 2
        + γ * lam k * (2 * β - γ / ε) * ‖C (xB k) - C (JB zs)‖ ^ 2 ≤ ‖z k - zs‖ ^ 2 := by
    intro k
    have hkey : ‖T (z k) - T zs‖ ^ 2 ≤ ‖z k - zs‖ ^ 2
        - (1 - ε) * ‖(z k - T (z k)) - (zs - T zs)‖ ^ 2
        - γ * (2 * β - γ / ε) * ‖C (JB (z k)) - C (JB zs)‖ ^ 2 :=
      key_ineq JA JB C β γ ε hfA hfB hC hγ0 hε0 (z k) zs
    rw [hTzs, sub_self, sub_zero] at hkey
    have hn : ‖z k - T (z k)‖ = ‖T (z k) - z k‖ := norm_sub_rev _ _
    have hxB : xB k = JB (z k) := rfl
    rw [hn] at hkey
    rw [hxB]
    have hz : z (k + 1) - zs = (1 - lam k) • (z k - zs) + lam k • (T (z k) - zs) := by
      rw [hstep k]; abel
    have hq : T (z k) - zs - (z k - zs) = T (z k) - z k := by abel
    rw [hz, affine_sq, hq]
    have hl := (hlam k).1
    have hm := mul_le_mul_of_nonneg_left hkey hl.le
    have htau : tau ε (lam k) = lam k * (1 - lam k) + lam k * (1 - ε) := by
      unfold tau; rw [mul_div_assoc, hcoefα]
    rw [htau]
    nlinarith
  refine ⟨h26, fun c hc hcl k => ?_⟩
  set κ := γ * c * (2 * β - γ / ε) with hκdef
  have hκpos : 0 < κ := by positivity
  set f : ℕ → ℝ := fun i => ‖C (xB (k + i)) - C (JB zs)‖ ^ 2 with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
  have hdesc : ∀ j, κ * ‖C (xB j) - C (JB zs)‖ ^ 2 ≤ ‖z j - zs‖ ^ 2 - ‖z (j + 1) - zs‖ ^ 2 := by
    intro j
    have h := h26 j
    have htau0 : 0 ≤ tau ε (lam j) := by
      unfold tau; rw [mul_div_assoc, hcoefα]
      have h1 := (hlam j).2
      rw [hα, one_div_one_div] at h1
      have := (hlam j).1
      nlinarith
    have hmono : κ * ‖C (xB j) - C (JB zs)‖ ^ 2 ≤
        γ * lam j * (2 * β - γ / ε) * ‖C (xB j) - C (JB zs)‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [hκdef]
      have := hcl j
      have : 0 ≤ γ * (2 * β - γ / ε) := by positivity
      nlinarith
    nlinarith [mul_nonneg htau0 (sq_nonneg ‖T (z j) - z j‖)]
  have hpartial : ∀ n, ∑ i ∈ Finset.range n, f i ≤ ‖z k - zs‖ ^ 2 / κ := by
    intro n
    have htel : ∀ n, κ * ∑ i ∈ Finset.range n, f i ≤ ‖z k - zs‖ ^ 2 - ‖z (k + n) - zs‖ ^ 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, mul_add]
        have := hdesc (k + n)
        simp only [hf]
        rw [show k + (n + 1) = k + n + 1 by ring]
        linarith
    rw [le_div_iff₀ hκpos]
    have := htel n
    nlinarith [sq_nonneg ‖z (k + n) - zs‖]
  exact ⟨summable_of_sum_range_le hf0 hpartial, Real.tsum_le_of_sum_range_le hf0 hpartial⟩

/-- Averagedness from the strengthened inequality. -/
lemma nonexp_of_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → H) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ∀ z w : H, ‖T z - T w‖ ^ 2 ≤ ‖z - w‖ ^ 2 - (1 - α) / α * ‖(z - T z) - (w - T w)‖ ^ 2)
    (z w : H) :
    ‖α⁻¹ • (T z - (1 - α) • z) - α⁻¹ • (T w - (1 - α) • w)‖ ≤ ‖z - w‖ := by
  have hzw := h z w
  set t := T z - T w with ht
  set d := z - w with hd
  have e1 : α⁻¹ • (T z - (1 - α) • z) - α⁻¹ • (T w - (1 - α) • w) =
      α⁻¹ • (t - (1 - α) • d) := by simp only [t, d]; module
  have e2 : (z - T z) - (w - T w) = d - t := by simp only [t, d]; abel
  rw [e2] at hzw
  rw [e1]
  clear_value t d
  rw [norm_sub_sq_real d t] at hzw
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hα0]
  have key : ‖t - (1 - α) • d‖ ^ 2 ≤ (α * ‖d‖) ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0:ℝ) < 1 - α)]
    have hm : α * ‖t‖ ^ 2 ≤ α * ‖d‖ ^ 2 - (1 - α) * (‖d‖ ^ 2 - 2 * ⟪d, t⟫_ℝ + ‖t‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hzw hα0.le
      have e3 : α * ((1 - α) / α * (‖d‖ ^ 2 - 2 * ⟪d, t⟫_ℝ + ‖t‖ ^ 2)) =
          (1 - α) * (‖d‖ ^ 2 - 2 * ⟪d, t⟫_ℝ + ‖t‖ ^ 2) := by field_simp
      nlinarith
    have hdt : ⟪t, d⟫_ℝ = ⟪d, t⟫_ℝ := real_inner_comm _ _
    nlinarith
  have hk : ‖t - (1 - α) • d‖ ≤ α * ‖d‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key
  rw [inv_mul_le_iff₀ hα0]; exact hk

/-- `n f(n) → 0` for antitone nonnegative summable sequences. -/
lemma little_o_of_antitone {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (hfa : Antitone f)
    (hs : Summable f) : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * f k) atTop (𝓝 0) := by
  set S := fun n => ∑ i ∈ Finset.range n, f i with hS
  have hSlim : Tendsto S atTop (𝓝 (∑' i, f i)) := hs.hasSum.tendsto_sum_nat
  have hdiv : Tendsto (fun k : ℕ => k / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b; exact ⟨2 * b, fun a ha => by omega⟩
  have h1 : Tendsto (fun k : ℕ => S (k + 1)) atTop (𝓝 (∑' i, f i)) :=
    hSlim.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k : ℕ => S (k / 2)) atTop (𝓝 (∑' i, f i)) := hSlim.comp hdiv
  have h3 : Tendsto (fun k : ℕ => 2 * (S (k + 1) - S (k / 2))) atTop (𝓝 (2 * (∑' i, f i - ∑' i, f i))) :=
    (h1.sub h2).const_mul 2
  rw [sub_self, mul_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun k => ?_) (fun k => ?_)
  · exact mul_nonneg (by positivity) (hf0 k)
  · have hle : k / 2 ≤ k + 1 := by omega
    have hsum : S (k + 1) - S (k / 2) = ∑ i ∈ Finset.Ico (k / 2) (k + 1), f i := by
      simp only [hS]; rw [Finset.sum_Ico_eq_sub _ hle]
    rw [hsum]
    have hcard := Finset.card_nsmul_le_sum (Finset.Ico (k / 2) (k + 1)) f (f k)
      (fun i hi => hfa (Finset.mem_Ico.1 hi).2.le |> fun h => by
        have := Finset.mem_Ico.1 hi; exact hfa (Nat.lt_succ_iff.1 this.2))
    rw [Nat.card_Ico, nsmul_eq_mul] at hcard
    have hc : ((k : ℝ) + 1) ≤ 2 * (((k + 1 - k / 2 : ℕ) : ℝ)) := by
      have : 2 * (k / 2) ≤ k := Nat.mul_div_le k 2
      have h' : (k + 1 - k / 2 : ℕ) = k + 1 - k / 2 := rfl
      rw [Nat.cast_sub hle]
      push_cast
      have : (2 : ℝ) * ((k / 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast this
      linarith
    nlinarith [hf0 k]
lemma resolvent_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (A : H → Set H) (J : H → H) (hγ : 0 < γ) (hAm : IsMonotoneOp A)
    (hJ : IsResolvent γ A J) (p x : H) (hx : γ⁻¹ • (p - x) ∈ A x) : J p = x := by
  have h := hAm (J p) x _ _ (hJ p) hx
  rw [← smul_sub, real_inner_smul_right] at h
  have h2 : 0 ≤ ⟪J p - x, p - J p - (p - x)⟫_ℝ :=
    (mul_nonneg_iff_of_pos_left (inv_pos.2 hγ)).1 h
  have e : p - J p - (p - x) = -(J p - x) := by abel
  rw [e, inner_neg_right, real_inner_self_eq_norm_sq] at h2
  have : ‖J p - x‖ = 0 := by nlinarith [norm_nonneg (J p - x)]
  rwa [norm_eq_zero, sub_eq_zero] at this

lemma fix_zer {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A B : H → Set H) (C : H → H) (γ : ℝ) (JA JB : H → H) (hγ : 0 < γ)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB) (zs : H)
    (hzs : zs ∈ Function.fixedPoints (threeOp γ JA JB C)) :
    JB zs ∈ zer (opSum A B C) := by
  have hT : JA ((2 : ℝ) • JB zs - zs - γ • C (JB zs)) + zs - JB zs = zs := hzs
  have hxA : JA ((2 : ℝ) • JB zs - zs - γ • C (JB zs)) = JB zs := by
    calc JA ((2 : ℝ) • JB zs - zs - γ • C (JB zs))
        = (JA ((2 : ℝ) • JB zs - zs - γ • C (JB zs)) + zs - JB zs) - zs + JB zs := by abel
      _ = JB zs := by rw [hT]; abel
  have ha := hJA ((2 : ℝ) • JB zs - zs - γ • C (JB zs))
  rw [hxA] at ha
  have hb := hJB zs
  refine ⟨_, ha, _, hb, ?_⟩
  rw [← smul_add]
  have e : (2 : ℝ) • JB zs - zs - γ • C (JB zs) - JB zs + (zs - JB zs) = -(γ • C (JB zs)) := by
    module
  rw [e, smul_neg, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
  abel

theorem corollary_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ ε : ℝ) (JA JB : H → H) (lam : ℕ → ℝ) (z0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ0 : 0 < γ) (hγ : γ < 2 * β * ε)
    (hlam : ∀ j, 0 < lam j ∧ lam j < 1 / alpha ε)
    (hτ : Tendsto (fun n => ∑ i ∈ Finset.range n, tau ε (lam i)) atTop atTop)
    (hFix : (Function.fixedPoints (threeOp γ JA JB C)).Nonempty) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    (∀ zs ∈ Function.fixedPoints T, Antitone (fun j => ‖z j - zs‖)) ∧
      Antitone (fun j => ‖T (z j) - z j‖) ∧
      Tendsto (fun j => ‖T (z j) - z j‖) atTop (𝓝 0) ∧
      ∃ zs ∈ Function.fixedPoints T, WeakTendsto z zs ∧ JB zs ∈ zer (opSum A B C) := by
  intro T z
  have hfA := resolvent_firm γ A JA hγ0 hA.1 hJA
  have hfB := resolvent_firm γ B JB hγ0 hB.1 hJB
  have h2e : 0 < 2 - ε := by linarith
  have hcoefα : (1 - alpha ε) / alpha ε = 1 - ε := by
    unfold alpha
    have : (2 - ε) ≠ 0 := by linarith
    field_simp; ring
  set α := alpha ε with hαdef
  have hα : α = 1 / (2 - ε) := rfl
  have hα0 : 0 < α := by rw [hα]; positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one h2e]; linarith
  have hκ : 0 < 2 * β - γ / ε := by rw [sub_pos, div_lt_iff₀ hε0]; linarith
  have hTin : ∀ u w : H, ‖T u - T w‖ ^ 2 ≤ ‖u - w‖ ^ 2 - (1 - α) / α * ‖(u - T u) - (w - T w)‖ ^ 2 := by
    intro u w
    have h := key_ineq JA JB C β γ ε hfA hfB hC hγ0 hε0 u w
    rw [hcoefα]
    have : 0 ≤ γ * (2 * β - γ / ε) * ‖C (JB u) - C (JB w)‖ ^ 2 := by positivity
    linarith
  have hTne : ∀ u w : H, ‖T u - T w‖ ≤ ‖u - w‖ := by
    intro u w
    have h := hTin u w
    rw [hcoefα] at h
    have : 0 ≤ (1 - ε) * ‖(u - T u) - (w - T w)‖ ^ 2 := by
      have : 0 ≤ 1 - ε := by linarith
      positivity
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  set R : H → H := fun x => α⁻¹ • (T x - (1 - α) • x) with hR
  have hRne : ∀ u w, ‖R u - R w‖ ≤ ‖u - w‖ := fun u w => nonexp_of_ineq T α hα0 hα1 hTin u w
  have hRres : ∀ x, T x - x = α • (R x - x) := by
    intro x
    rw [smul_sub (α) (R x) x]
    simp only [hR]
    rw [smul_smul, mul_inv_cancel₀ hα0.ne', one_smul]
    module
  have hstep : ∀ k, z (k + 1) = z k + lam k • (T (z k) - z k) := by
    intro k
    show zSeq γ JA JB C lam z0 (k + 1) = _
    simp only [zSeq, T, threeOp, z]
    module
  have hresmono : ∀ k, ‖T (z (k + 1)) - z (k + 1)‖ ≤ ‖T (z k) - z k‖ := by
    intro k
    set μ := lam k * α with hμ
    have hμ0 : 0 < μ := mul_pos (hlam k).1 hα0
    have hμ1 : μ ≤ 1 := by
      have := (hlam k).2
      rw [lt_div_iff₀ hα0] at this
      linarith
    have hz1 : z (k + 1) = z k + μ • (R (z k) - z k) := by
      rw [hstep k, hRres, smul_smul]
    have hdec : R (z (k + 1)) - z (k + 1) =
        (R (z (k + 1)) - R (z k)) + (1 - μ) • (R (z k) - z k) := by
      rw [hz1]; module
    have hb : ‖R (z (k + 1)) - z (k + 1)‖ ≤ ‖R (z k) - z k‖ := by
      rw [hdec]
      calc ‖(R (z (k + 1)) - R (z k)) + (1 - μ) • (R (z k) - z k)‖
          ≤ ‖R (z (k + 1)) - R (z k)‖ + ‖(1 - μ) • (R (z k) - z k)‖ := norm_add_le _ _
        _ ≤ ‖z (k + 1) - z k‖ + (1 - μ) * ‖R (z k) - z k‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            linarith [hRne (z (k + 1)) (z k)]
        _ = ‖R (z k) - z k‖ := by
            rw [hz1, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hμ0]; ring
    rw [hRres, hRres, norm_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hresA : Antitone (fun k => ‖T (z k) - z k‖) := antitone_nat_of_succ_le hresmono
  have hdesc := fun zs (hzs : zs ∈ Function.fixedPoints T) =>
    (desc_aux A B C β γ ε JA JB lam z0 hA hB hβ hC hJA hJB hε0 hε1 hγ0 hγ hlam zs hzs).1
  have htau0 : ∀ j, 0 ≤ tau ε (lam j) := by
    intro j
    unfold tau; rw [mul_div_assoc, hcoefα]
    have h1 := (hlam j).2
    rw [hα, one_div_one_div] at h1
    have := (hlam j).1
    nlinarith
  have hfej : ∀ zs ∈ Function.fixedPoints T, ∀ k, ‖z (k + 1) - zs‖ ≤ ‖z k - zs‖ := by
    intro zs hzs k
    have h := hdesc zs hzs k
    have hc : 0 ≤ γ * lam k * (2 * β - γ / ε) *
        ‖C (xBSeq γ JA JB C lam z0 k) - C (JB zs)‖ ^ 2 := by
      have := (hlam k).1; positivity
    have := mul_nonneg (htau0 k) (sq_nonneg ‖T (z k) - z k‖)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  have hfejA : ∀ zs ∈ Function.fixedPoints T, Antitone (fun j => ‖z j - zs‖) :=
    fun zs hzs => antitone_nat_of_succ_le (hfej zs hzs)
  obtain ⟨zs0, hzs0⟩ := hFix
  -- partial sums
  have hsums : ∀ n : ℕ,
      ∑ i ∈ Finset.range n, tau ε (lam i) * ‖T (z i) - z i‖ ^ 2 ≤ ‖z0 - zs0‖ ^ 2 := by
    have htel : ∀ n, ∑ i ∈ Finset.range n, tau ε (lam i) * ‖T (z i) - z i‖ ^ 2 ≤
        ‖z 0 - zs0‖ ^ 2 - ‖z n - zs0‖ ^ 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ]
        have h := hdesc zs0 hzs0 n
        have hc : 0 ≤ γ * lam n * (2 * β - γ / ε) *
            ‖C (xBSeq γ JA JB C lam z0 n) - C (JB zs0)‖ ^ 2 := by
          have := (hlam n).1; positivity
        linarith
    intro n
    have := htel n
    have hz0 : z 0 = z0 := rfl
    rw [hz0] at this
    nlinarith [sq_nonneg ‖z n - zs0‖]
  have hres0 : Tendsto (fun j => ‖T (z j) - z j‖) atTop (𝓝 0) := by
    have hbdd : BddBelow (Set.range fun j => ‖T (z j) - z j‖) :=
      ⟨0, by rintro _ ⟨j, rfl⟩; exact norm_nonneg _⟩
    have hlim := tendsto_atTop_ciInf hresA hbdd
    set L := ⨅ j, ‖T (z j) - z j‖ with hL
    have hL0 : 0 ≤ L := le_ciInf (fun j => norm_nonneg _)
    have hLle : ∀ j, L ≤ ‖T (z j) - z j‖ := fun j => ciInf_le hbdd j
    rcases hL0.eq_or_lt with h | h
    · rw [← h] at hlim; exact hlim
    · exfalso
      obtain ⟨n, hn⟩ := (tendsto_atTop.1 hτ (‖z0 - zs0‖ ^ 2 / L ^ 2 + 1)).exists
      have hs := hsums n
      have hlow : L ^ 2 * ∑ i ∈ Finset.range n, tau ε (lam i) ≤
          ∑ i ∈ Finset.range n, tau ε (lam i) * ‖T (z i) - z i‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have : L ^ 2 ≤ ‖T (z i) - z i‖ ^ 2 := pow_le_pow_left₀ hL0 (hLle i) 2
        nlinarith [htau0 i]
      have hL2 : 0 < L ^ 2 := by positivity
      have : L ^ 2 * (‖z0 - zs0‖ ^ 2 / L ^ 2 + 1) ≤ L ^ 2 * ∑ i ∈ Finset.range n, tau ε (lam i) :=
        mul_le_mul_of_nonneg_left hn hL2.le
      rw [mul_add, mul_div_cancel₀ _ hL2.ne'] at this
      linarith
  -- boundedness
  set M := ‖z0 - zs0‖ + ‖zs0‖ with hM
  have hzb : ∀ k, ‖z k‖ ≤ M := by
    intro k
    have h1 : ‖z k - zs0‖ ≤ ‖z0 - zs0‖ := hfejA zs0 hzs0 (Nat.zero_le k)
    have : z k = (z k - zs0) + zs0 := by abel
    rw [this]
    exact (norm_add_le _ _).trans (by simp only [hM]; linarith)
  have hconv : ∀ zs ∈ Function.fixedPoints T, ∃ d, Tendsto (fun k => ‖z k - zs‖) atTop (𝓝 d) :=
    fun zs hzs => ⟨_, tendsto_atTop_ciInf (hfejA zs hzs)
      ⟨0, by rintro _ ⟨j, rfl⟩; exact norm_nonneg _⟩⟩
  -- weak limit
  set U0 : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ) with hU0
  have hU0le : (U0 : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨w0, hw0⟩ := exists_ulim z M hzb U0
  have hfixU : ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ atTop → ∀ w : H,
      (∀ y, Tendsto (fun k => ⟪z k, y⟫_ℝ) U (𝓝 ⟪w, y⟫_ℝ)) → w ∈ Function.fixedPoints T :=
    fun U hU w hw => demiclosed T hTne z M hzb hres0 U hU w hw
  have hw0fix := hfixU U0 hU0le w0 hw0
  have hweak : WeakTendsto z w0 := by
    apply weak_of_ulim z M hzb w0
    intro U hU w hw
    exact opial_unique z w w0 U U0 hU hU0le hw hw0 (hconv w (hfixU U hU w hw)) (hconv w0 hw0fix)
  exact ⟨hfejA, hresA, hres0, w0, hw0fix, hweak,
    fix_zer A B C γ JA JB hγ0 hJA hJB w0 hw0fix⟩

lemma bdd_of_tendsto {H : Type*} [NormedAddCommGroup H] (f : ℕ → H) (a : H)
    (h : Tendsto f atTop (𝓝 a)) : ∃ M, ∀ k, ‖f k‖ ≤ M := by
  obtain ⟨M, hM⟩ := (h.norm).bddAbove_range
  exact ⟨M, fun k => hM (Set.mem_range_self k)⟩

lemma tendsto_inner_bdd_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : Filter ℕ) (p q : ℕ → H) (M : ℝ) (hp : ∀ k, ‖p k‖ ≤ M)
    (hq : Tendsto q U (𝓝 0)) : Tendsto (fun k => ⟪p k, q k⟫_ℝ) U (𝓝 0) := by
  have hq' : Tendsto (fun k => M * ‖q k‖) U (𝓝 0) := by
    simpa using (hq.norm).const_mul M
  refine squeeze_zero_norm (fun k => ?_) hq'
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hp k) (norm_nonneg _))

lemma tendsto_inner_bdd_zero' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : Filter ℕ) (p q : ℕ → H) (M : ℝ) (hp : ∀ k, ‖p k‖ ≤ M)
    (hq : Tendsto q U (𝓝 0)) : Tendsto (fun k => ⟪q k, p k⟫_ℝ) U (𝓝 0) := by
  have e : (fun k => ⟪q k, p k⟫_ℝ) = fun k => ⟪p k, q k⟫_ℝ :=
    funext fun k => real_inner_comm (p k) (q k)
  rw [e]
  exact tendsto_inner_bdd_zero U p q M hp hq

lemma sum_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A B : H → Set H) (γ : ℝ) (JA JB : H → H) (hγ : 0 < γ)
    (hAm : IsMonotoneOp A) (hBm : IsMonotoneOp B)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (U : Filter ℕ) [U.NeBot] (xA xB a b : ℕ → H) (ha : ∀ k, a k ∈ A (xA k))
    (hb : ∀ k, b k ∈ B (xB k)) (Ma Mb : ℝ) (hMa : ∀ k, ‖a k‖ ≤ Ma) (hMb : ∀ k, ‖xB k‖ ≤ Mb)
    (c x bi : H)
    (hdiff : Tendsto (fun k => xA k - xB k) U (𝓝 0))
    (hsum : Tendsto (fun k => a k + b k) U (𝓝 (-c)))
    (hx : ∀ y, Tendsto (fun k => ⟪xB k, y⟫_ℝ) U (𝓝 ⟪x, y⟫_ℝ))
    (hbi : ∀ y, Tendsto (fun k => ⟪b k, y⟫_ℝ) U (𝓝 ⟪bi, y⟫_ℝ)) : bi ∈ B x := by
  set ai := -c - bi with hai
  have hclaim : ∀ y v y' w, v ∈ A y → w ∈ B y' →
      0 ≤ ⟪x - y, ai - v⟫_ℝ + ⟪x - y', bi - w⟫_ℝ := by
    intro y v y' w hv hw
    have hs : ∀ k, 0 ≤ ⟪xA k - xB k, a k - v⟫_ℝ + ⟪xB k, a k + b k + c⟫_ℝ +
        (⟪xB k, -c - v - w⟫_ℝ - ⟪y, a k + b k⟫_ℝ + ⟪y, b k⟫_ℝ - ⟪y', b k⟫_ℝ
          + ⟪y, v⟫_ℝ + ⟪y', w⟫_ℝ) := by
      intro k
      have h1 := hAm (xA k) y (a k) v (ha k) hv
      have h2 := hBm (xB k) y' (b k) w (hb k) hw
      have e : ⟪xA k - xB k, a k - v⟫_ℝ + ⟪xB k, a k + b k + c⟫_ℝ +
          (⟪xB k, -c - v - w⟫_ℝ - ⟪y, a k + b k⟫_ℝ + ⟪y, b k⟫_ℝ - ⟪y', b k⟫_ℝ
            + ⟪y, v⟫_ℝ + ⟪y', w⟫_ℝ) = ⟪xA k - y, a k - v⟫_ℝ + ⟪xB k - y', b k - w⟫_ℝ := by
        simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
          inner_neg_right]
        ring
      rw [e]; linarith
    have t1 : Tendsto (fun k => ⟪xA k - xB k, a k - v⟫_ℝ) U (𝓝 0) :=
      tendsto_inner_bdd_zero' U (fun k => a k - v) _ (Ma + ‖v‖)
        (fun k => (norm_sub_le _ _).trans (by linarith [hMa k])) hdiff
    have hsc : Tendsto (fun k => a k + b k + c) U (𝓝 0) := by
      have := hsum.add (tendsto_const_nhds (x := c))
      simpa using this
    have t2 : Tendsto (fun k => ⟪xB k, a k + b k + c⟫_ℝ) U (𝓝 0) :=
      tendsto_inner_bdd_zero U xB _ Mb hMb hsc
    have hby : ∀ y, Tendsto (fun k => ⟪y, b k⟫_ℝ) U (𝓝 ⟪y, bi⟫_ℝ) := by
      intro y
      have e : (fun k => ⟪y, b k⟫_ℝ) = fun k => ⟪b k, y⟫_ℝ :=
        funext fun k => real_inner_comm (b k) y
      rw [e, real_inner_comm]
      exact hbi y
    have t3 : Tendsto (fun k => ⟪xB k, -c - v - w⟫_ℝ - ⟪y, a k + b k⟫_ℝ + ⟪y, b k⟫_ℝ
          - ⟪y', b k⟫_ℝ + ⟪y, v⟫_ℝ + ⟪y', w⟫_ℝ) U
        (𝓝 (⟪x, -c - v - w⟫_ℝ - ⟪y, -c⟫_ℝ + ⟪y, bi⟫_ℝ - ⟪y', bi⟫_ℝ + ⟪y, v⟫_ℝ + ⟪y', w⟫_ℝ)) :=
      (((((hx _).sub (tendsto_const_nhds.inner hsum)).add (hby y)).sub (hby y')).add
        tendsto_const_nhds).add tendsto_const_nhds
    have hlim := (t1.add t2).add t3
    have hge := ge_of_tendsto' hlim hs
    have e : (0 : ℝ) + 0 + (⟪x, -c - v - w⟫_ℝ - ⟪y, -c⟫_ℝ + ⟪y, bi⟫_ℝ - ⟪y', bi⟫_ℝ
        + ⟪y, v⟫_ℝ + ⟪y', w⟫_ℝ) = ⟪x - y, ai - v⟫_ℝ + ⟪x - y', bi - w⟫_ℝ := by
      rw [hai]
      simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        inner_neg_right]
      ring
    linarith
  set y := JA (x + γ • ai) with hy
  set v := γ⁻¹ • (x + γ • ai - y) with hv
  set y' := JB (x + γ • bi) with hy'
  set w := γ⁻¹ • (x + γ • bi - y') with hw
  have hvA : v ∈ A y := hJA _
  have hwB : w ∈ B y' := hJB _
  have hγ' : γ⁻¹ * γ = 1 := inv_mul_cancel₀ hγ.ne'
  have ev : ai - v = -(γ⁻¹ • (x - y)) := by
    rw [hv, smul_sub, smul_add, smul_smul, hγ', one_smul, smul_sub]; abel
  have ew : bi - w = -(γ⁻¹ • (x - y')) := by
    rw [hw, smul_sub, smul_add, smul_smul, hγ', one_smul, smul_sub]; abel
  have hc := hclaim y v y' w hvA hwB
  rw [ev, ew, inner_neg_right, inner_neg_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  have hγi : 0 < γ⁻¹ := inv_pos.2 hγ
  have h1 : 0 ≤ γ⁻¹ * ‖x - y‖ ^ 2 := by positivity
  have h2 : γ⁻¹ * ‖x - y'‖ ^ 2 ≤ 0 := by linarith
  have h3 : ‖x - y'‖ ^ 2 ≤ 0 := by
    by_contra hcon; push_neg at hcon; nlinarith
  have h4 : ‖x - y'‖ = 0 := by nlinarith [norm_nonneg (x - y')]
  rw [norm_eq_zero, sub_eq_zero] at h4
  have : w = bi := by
    rw [hw, ← h4, add_sub_cancel_left, smul_smul, hγ', one_smul]
  rw [← this, h4]
  exact hwB

lemma unif_conv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (hU : IsUniformlyMonotoneOnBounded A) (x u : ℕ → H)
    (hu : ∀ k, u k ∈ A (x k)) (xs us : H) (hus : us ∈ A xs) (Mx : ℝ) (hx : ∀ k, ‖x k‖ ≤ Mx)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (hle : ∀ k, ⟪x k - xs, u k - us⟫_ℝ ≤ t k) :
    Tendsto x atTop (𝓝 xs) := by
  set S : Set H := insert xs (Set.range x) with hS
  have hSd : S ⊆ dom A := by
    intro p hp
    rcases hp with rfl | ⟨k, rfl⟩
    · exact ⟨us, hus⟩
    · exact ⟨u k, hu k⟩
  have hSb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : H)) (r := max Mx ‖xs‖)).subset ?_
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right]
    rcases hp with rfl | ⟨k, rfl⟩
    · exact le_max_right _ _
    · exact (hx k).trans (le_max_left _ _)
  obtain ⟨φ, hφm, -, hφ0, hφ⟩ := hU S hSd ⟨xs, Set.mem_insert _ _⟩ hSb
  have hk : ∀ k, φ ‖x k - xs‖₊ ≠ ⊤ ∧ (φ ‖x k - xs‖₊).toReal ≤ t k := by
    intro k
    have h := hφ (x k) (Set.mem_insert_of_mem _ ⟨k, rfl⟩) xs (Set.mem_insert _ _) (u k) (hu k)
      us hus
    have hne : φ ‖x k - xs‖₊ ≠ ⊤ := by
      intro htop
      rw [htop] at h
      simp at h
    refine ⟨hne, ?_⟩
    rw [← EReal.coe_ennreal_toReal hne] at h
    exact (EReal.coe_le_coe_iff.1 h).trans (hle k)
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
  intro δ hδ
  by_contra hcon
  push_neg at hcon
  have hδ' : (⟨δ, hδ.le⟩ : NNReal) ≠ 0 := by
    intro h; have := congrArg NNReal.toReal h; exact hδ.ne' this
  have hφδ : φ ⟨δ, hδ.le⟩ ≠ 0 := fun h => hδ' (hφ0 _ h)
  obtain ⟨k0, hk0⟩ := hcon 0
  have hfin : φ ⟨δ, hδ.le⟩ ≠ ⊤ := by
    have hmono : φ ⟨δ, hδ.le⟩ ≤ φ ‖x k0 - xs‖₊ := by
      apply hφm
      show δ ≤ ‖x k0 - xs‖
      have := hk0.2
      simpa [dist_zero_right] using this
    exact ne_top_of_le_ne_top (hk k0).1 hmono
  set p := (φ ⟨δ, hδ.le⟩).toReal with hp
  have hp0 : 0 < p := ENNReal.toReal_pos hφδ hfin
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht p hp0
  obtain ⟨k, hkN, hk'⟩ := hcon N
  have hmono : φ ⟨δ, hδ.le⟩ ≤ φ ‖x k - xs‖₊ := by
    apply hφm
    show δ ≤ ‖x k - xs‖
    simpa [dist_zero_right] using hk'
  have h1 : p ≤ (φ ‖x k - xs‖₊).toReal := ENNReal.toReal_mono (hk k).1 hmono
  have h2 := (hk k).2
  have h3 := hN k hkN
  rw [Real.dist_eq, sub_zero] at h3
  have := le_abs_self (t k)
  linarith

lemma firm_nonexp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (J : H → H)
    (hJ : IsFirmlyNonexpansive J) (x y : H) : ‖J x - J y‖ ≤ ‖x - y‖ := by
  have h := hJ x y
  have h2 := real_inner_le_norm (J x - J y) (x - y)
  rcases (norm_nonneg (J x - J y)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

theorem main_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ ε : ℝ) (JA JB : H → H) (lam : ℕ → ℝ) (z0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ0 : 0 < γ) (hγ : γ < 2 * β * ε)
    (hlam : ∀ j, 0 < lam j ∧ lam j < 1 / alpha ε)
    (hτ : Tendsto (fun n => ∑ i ∈ Finset.range n, tau ε (lam i)) atTop atTop)
    (hFix : (Function.fixedPoints (threeOp γ JA JB C)).Nonempty)
    (hlam_inf : 0 < ⨅ j, lam j) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    let xB := xBSeq γ JA JB C lam z0
    let xA := xASeq γ JA JB C lam z0
    ∃ zs ∈ Function.fixedPoints T, WeakTendsto z zs ∧
      (∀ xs ∈ zer (opSum A B C), Tendsto (fun j => C (xB j)) atTop (𝓝 (C xs))) ∧
      WeakTendsto xB (JB zs) ∧ JB zs ∈ zer (opSum A B C) ∧
      WeakTendsto xA (JB zs) ∧
      ((IsUniformlyMonotoneOnBounded A ∨ IsUniformlyMonotoneOnBounded B ∨
          ∀ x ∈ zer (opSum A B C), IsDemiregularAt C x) →
        ∃ xs ∈ zer (opSum A B C), Tendsto xB atTop (𝓝 xs) ∧ Tendsto xA atTop (𝓝 xs)) := by
  intro T z xB xA
  obtain ⟨hfejA, hresA, hres0, zs, hzs, hweak, hzer⟩ :=
    corollary_core A B C β γ ε JA JB lam z0 hA hB hβ hC hJA hJB hε0 hε1 hγ0 hγ hlam hτ hFix
  have hfB := resolvent_firm γ B JB hγ0 hB.1 hJB
  set xs0 := JB zs with hxs0
  have hxBdef : ∀ k, xB k = JB (z k) := fun k => rfl
  have hxAdef : ∀ k, xA k = JA ((2 : ℝ) • xB k - z k - γ • C (xB k)) := fun k => rfl
  have hdiffk : ∀ k, xA k - xB k = T (z k) - z k := by
    intro k
    show xA k - xB k = JA ((2 : ℝ) • JB (z k) - z k - γ • C (JB (z k))) + z k - JB (z k) - z k
    rw [hxAdef, hxBdef]; abel
  have hdiff : Tendsto (fun k => xA k - xB k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [hdiffk]; exact hres0
  -- lam lower bound
  set c0 := ⨅ j, lam j with hc0
  have hlbdd : BddBelow (Set.range lam) := ⟨0, by rintro _ ⟨j, rfl⟩; exact (hlam j).1.le⟩
  have hc0le : ∀ j, c0 ≤ lam j := fun j => ciInf_le hlbdd j
  -- Part 1(a)
  have h1a : ∀ xs ∈ zer (opSum A B C), Tendsto (fun j => C (xB j)) atTop (𝓝 (C xs)) := by
    intro xs hxs
    obtain ⟨a, ha, b, hb, hab⟩ := hxs
    set zs' := xs + γ • b with hzs'
    have hγ' : γ⁻¹ * γ = 1 := inv_mul_cancel₀ hγ0.ne'
    have hJBzs' : JB zs' = xs := by
      apply resolvent_unique γ B JB hγ0 hB.1 hJB
      rw [hzs', add_sub_cancel_left, smul_smul, hγ', one_smul]; exact hb
    have hfix' : zs' ∈ Function.fixedPoints T := by
      show JA ((2 : ℝ) • JB zs' - zs' - γ • C (JB zs')) + zs' - JB zs' = zs'
      have harg : (2 : ℝ) • JB zs' - zs' - γ • C (JB zs') = xs + γ • a := by
        rw [hJBzs', hzs']
        have : a = -b - C xs := by
          calc a = (a + b + C xs) - b - C xs := by abel
            _ = -b - C xs := by rw [← hab]; abel
        rw [this]; module
      rw [harg, hJBzs']
      have : JA (xs + γ • a) = xs := by
        apply resolvent_unique γ A JA hγ0 hA.1 hJA
        rw [add_sub_cancel_left, smul_smul, hγ', one_smul]; exact ha
      rw [this]; abel
    have hsum := ((desc_aux A B C β γ ε JA JB lam z0 hA hB hβ hC hJA hJB hε0 hε1 hγ0 hγ hlam
      zs' hfix').2 c0 hlam_inf hc0le 0).1
    simp only [zero_add] at hsum
    have h0 := hsum.tendsto_atTop_zero
    rw [hJBzs'] at h0
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have := h0.sqrt
    simp only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at this
    exact this
  have hCconv := h1a xs0 hzer
  -- bounds
  set Mz := ‖z0 - zs‖ + ‖zs‖ with hMz
  have hzb : ∀ k, ‖z k‖ ≤ Mz := by
    intro k
    have h1 : ‖z k - zs‖ ≤ ‖z0 - zs‖ := hfejA zs hzs (Nat.zero_le k)
    have : z k = (z k - zs) + zs := by abel
    rw [this]
    exact (norm_add_le _ _).trans (by simp only [hMz]; linarith)
  set MB := ‖z0 - zs‖ + ‖xs0‖ with hMB
  have hxBb : ∀ k, ‖xB k‖ ≤ MB := by
    intro k
    have h1 : ‖z k - zs‖ ≤ ‖z0 - zs‖ := hfejA zs hzs (Nat.zero_le k)
    have h2 : ‖xB k - xs0‖ ≤ ‖z k - zs‖ := firm_nonexp JB hfB _ _
    have : xB k = (xB k - xs0) + xs0 := by abel
    rw [this]
    exact (norm_add_le _ _).trans (by simp only [hMB]; linarith)
  obtain ⟨Md, hMd⟩ := bdd_of_tendsto _ _ hdiff
  have hxAb : ∀ k, ‖xA k‖ ≤ Md + MB := by
    intro k
    have : xA k = (xA k - xB k) + xB k := by abel
    rw [this]
    exact (norm_add_le _ _).trans (by linarith [hMd k, hxBb k])
  -- graph sequences
  set b : ℕ → H := fun k => γ⁻¹ • (z k - xB k) with hbdef
  set a : ℕ → H := fun k => γ⁻¹ • ((2 : ℝ) • xB k - z k - γ • C (xB k) - xA k) with hadef
  have hbB : ∀ k, b k ∈ B (xB k) := fun k => hJB (z k)
  have haA : ∀ k, a k ∈ A (xA k) := fun k => hJA _
  have hγ' : γ⁻¹ * γ = 1 := inv_mul_cancel₀ hγ0.ne'
  have habk : ∀ k, a k + b k = -(γ⁻¹ • (xA k - xB k)) - C (xB k) := by
    intro k
    simp only [hadef, hbdef]
    rw [← smul_add]
    have e : (2 : ℝ) • xB k - z k - γ • C (xB k) - xA k + (z k - xB k) =
        -(xA k - xB k) - γ • C (xB k) := by module
    rw [e, smul_sub, smul_neg, smul_smul, hγ', one_smul]
  have habt : Tendsto (fun k => a k + b k) atTop (𝓝 (-C xs0)) := by
    simp only [habk]
    have := ((hdiff.const_smul γ⁻¹).neg).sub hCconv
    simpa using this
  obtain ⟨Mab, hMab⟩ := bdd_of_tendsto _ _ habt
  have hMa : ∀ k, ‖a k‖ ≤ Mab + γ⁻¹ * (Mz + MB) := by
    intro k
    have e : a k = (a k + b k) - b k := by abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have : ‖b k‖ ≤ γ⁻¹ * (Mz + MB) := by
      simp only [hbdef]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hγ0)]
      exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith [hzb k, hxBb k]))
        (inv_pos.2 hγ0).le
    linarith [hMab k]
  -- Part 1(b)
  have h1b : WeakTendsto xB xs0 := by
    apply weak_of_ulim xB MB hxBb xs0
    intro U hU w hw
    have hbi : ∀ y, Tendsto (fun k => ⟪b k, y⟫_ℝ) U (𝓝 ⟪γ⁻¹ • (zs - w), y⟫_ℝ) := by
      intro y
      simp only [hbdef, real_inner_smul_left, inner_sub_left]
      exact (((hweak y).mono_left hU).sub (hw y)).const_mul _
    have hmem := sum_lemma A B γ JA JB hγ0 hA.1 hB.1 hJA hJB (U : Filter ℕ) xA xB a b haA hbB
      _ _ hMa hxBb (C xs0) w _ (hdiff.mono_left hU) (habt.mono_left hU) hw hbi
    exact (resolvent_unique γ B JB hγ0 hB.1 hJB zs w hmem).symm
  -- Part 1(c)
  have h1c : WeakTendsto xA xs0 := by
    intro y
    have e : ∀ k, ⟪xA k, y⟫_ℝ = ⟪xB k, y⟫_ℝ + ⟪xA k - xB k, y⟫_ℝ := by
      intro k; rw [inner_sub_left]; ring
    simp only [e]
    have h2 : Tendsto (fun k => ⟪xA k - xB k, y⟫_ℝ) atTop (𝓝 0) :=
      tendsto_inner_bdd_zero' atTop (fun _ => y) _ ‖y‖ (fun _ => le_rfl) hdiff
    simpa using (h1b y).add h2
  refine ⟨zs, hzs, hweak, h1a, h1b, hzer, h1c, ?_⟩
  -- Part 2
  intro hreg
  obtain ⟨as, has, bs, hbs, habs⟩ := hzer
  have habs' : as + bs = -C xs0 := by
    have := congrArg (fun v => v - C xs0) habs
    simp only [zero_sub, add_sub_cancel_right] at this
    exact this.symm
  -- s_k → 0
  set s : ℕ → ℝ := fun k => ⟪xA k - xs0, a k - as⟫_ℝ + ⟪xB k - xs0, b k - bs⟫_ℝ with hsdef
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have e : ∀ k, s k = ⟪xA k - xB k, a k - as⟫_ℝ +
        ⟪xB k - xs0, (a k + b k) - (as + bs)⟫_ℝ := by
      intro k
      simp only [hsdef, inner_add_right, inner_sub_left, inner_sub_right]
      ring
    rw [show s = fun k => ⟪xA k - xB k, a k - as⟫_ℝ +
        ⟪xB k - xs0, (a k + b k) - (as + bs)⟫_ℝ from funext e]
    have t1 := tendsto_inner_bdd_zero' atTop (fun k => a k - as) _ (Mab + γ⁻¹ * (Mz + MB) + ‖as‖)
      (fun k => (norm_sub_le _ _).trans (by linarith [hMa k])) hdiff
    have hq : Tendsto (fun k => (a k + b k) - (as + bs)) atTop (𝓝 0) := by
      rw [habs']
      simpa using habt.sub (tendsto_const_nhds (x := -C xs0))
    have t2 := tendsto_inner_bdd_zero atTop (fun k => xB k - xs0) _ (MB + ‖xs0‖)
      (fun k => (norm_sub_le _ _).trans (by linarith [hxBb k])) hq
    simpa using t1.add t2
  have hsA : ∀ k, 0 ≤ ⟪xA k - xs0, a k - as⟫_ℝ := fun k => hA.1 _ _ _ _ (haA k) has
  have hsB : ∀ k, 0 ≤ ⟪xB k - xs0, b k - bs⟫_ℝ := fun k => hB.1 _ _ _ _ (hbB k) hbs
  have hzer0 : xs0 ∈ zer (opSum A B C) := ⟨as, has, bs, hbs, habs⟩
  refine ⟨xs0, hzer0, ?_⟩
  have fromB : Tendsto xB atTop (𝓝 xs0) → Tendsto xB atTop (𝓝 xs0) ∧ Tendsto xA atTop (𝓝 xs0) := by
    intro h
    refine ⟨h, ?_⟩
    have : Tendsto (fun k => xB k + (xA k - xB k)) atTop (𝓝 (xs0 + 0)) := h.add hdiff
    simpa using this
  rcases hreg with hUA | hUB | hDR
  · have hA' : Tendsto xA atTop (𝓝 xs0) :=
      unif_conv A hUA xA a haA xs0 as has _ hxAb s hs0 (fun k => by
        simp only [hsdef]; linarith [hsB k])
    refine ⟨?_, hA'⟩
    have : Tendsto (fun k => xA k - (xA k - xB k)) atTop (𝓝 (xs0 - 0)) := hA'.sub hdiff
    simpa using this
  · exact fromB (unif_conv B hUB xB b hbB xs0 bs hbs _ hxBb s hs0 (fun k => by
        simp only [hsdef]; linarith [hsA k]))
  · exact fromB (hDR xs0 hzer0 xB h1b hCconv)

end ThreeOpSplitting.Convergence

open ThreeOpSplitting.Convergence


theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ ε : ℝ) (JA JB : H → H) (lam : ℕ → ℝ) (z0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ0 : 0 < γ) (hγ : γ < 2 * β * ε)
    (hlam : ∀ j, 0 < lam j ∧ lam j < 1 / alpha ε)
    (hτ : Tendsto (fun n => ∑ i ∈ Finset.range n, tau ε (lam i)) atTop atTop)
    (hFix : (Function.fixedPoints (threeOp γ JA JB C)).Nonempty)
    (hlam_inf : 0 < ⨅ j, lam j) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    let xB := xBSeq γ JA JB C lam z0
    let xA := xASeq γ JA JB C lam z0
    ∃ zs ∈ Function.fixedPoints T, WeakTendsto z zs ∧
      -- Part 1(a)
      (∀ xs ∈ zer (opSum A B C), Tendsto (fun j => C (xB j)) atTop (𝓝 (C xs))) ∧
      -- Part 1(b)
      WeakTendsto xB (JB zs) ∧ JB zs ∈ zer (opSum A B C) ∧
      -- Part 1(c)
      WeakTendsto xA (JB zs) ∧
      -- Part 2
      ((IsUniformlyMonotoneOnBounded A ∨ IsUniformlyMonotoneOnBounded B ∨
          ∀ x ∈ zer (opSum A B C), IsDemiregularAt C x) →
        ∃ xs ∈ zer (opSum A B C), Tendsto xB atTop (𝓝 xs) ∧ Tendsto xA atTop (𝓝 xs)) := by
  exact main_core A B C β γ ε JA JB lam z0 hA hB hβ hC hJA hJB hε0 hε1 hγ0 hγ hlam hτ hFix hlam_inf
