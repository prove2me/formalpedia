-- Prove2me | solution 1 for StochSQP.Vanishing.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:58:45.92157+00:00
-- url     : https://prove2.me/submissions/a39f7e40-b746-49a9-a8a2-03c152be3732

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace
open StochSQP.Vanishing

namespace StochSQPVanT3Aux

lemma bound_of_isBounded {α : Type*} [SeminormedAddCommGroup α] {S : Set α}
    (h : Bornology.IsBounded S) : ∃ C, 0 < C ∧ ∀ y ∈ S, ‖y‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 h
  exact ⟨max C 1, by positivity, fun y hy => (hC y hy).trans (le_max_left _ _)⟩

lemma cauchy_core {n m : ℕ} (J : E n →L[ℝ] E m) (c : E m) (w : E n)
    (hw : ⟪c, J w⟫_ℝ = ‖w‖ ^ 2) (κ a εv s : ℝ) (hJ : ‖J‖ ≤ κ) (ha : 0 ≤ a)
    (haκ : a * κ ^ 2 ≤ 1) (hεv : 0 < εv) (hs : 0 ≤ s)
    (h : εv * (‖c‖ - ‖c + a • J (-w)‖) ≤ s) : εv * a * ‖w‖ ^ 2 ≤ 2 * ‖c‖ * s := by
  have e1 : c + a • J (-w) = c - a • J w := by rw [map_neg, smul_neg, sub_eq_add_neg]
  rw [e1] at h
  set q := ‖c - a • J w‖ with hqdef
  have hJw : ‖J w‖ ≤ κ * ‖w‖ :=
    (J.le_opNorm w).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
  have hJw2 : ‖J w‖ ^ 2 ≤ κ ^ 2 * ‖w‖ ^ 2 := by
    have := norm_nonneg (J w)
    rw [← mul_pow]; exact pow_le_pow_left₀ this hJw 2
  have hq2 : q ^ 2 = ‖c‖ ^ 2 - 2 * a * ⟪c, J w⟫_ℝ + a ^ 2 * ‖J w‖ ^ 2 := by
    rw [hqdef, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  have hA : a ^ 2 * ‖J w‖ ^ 2 ≤ a * ‖w‖ ^ 2 := by
    have h1 : a ^ 2 * ‖J w‖ ^ 2 ≤ a ^ 2 * (κ ^ 2 * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hJw2 (sq_nonneg a)
    have h2 : a ^ 2 * (κ ^ 2 * ‖w‖ ^ 2) = (a * κ ^ 2) * (a * ‖w‖ ^ 2) := by ring
    have h3 : (a * κ ^ 2) * (a * ‖w‖ ^ 2) ≤ 1 * (a * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_right haκ (by positivity)
    linarith
  have hq : q ^ 2 ≤ ‖c‖ ^ 2 - a * ‖w‖ ^ 2 := by rw [hq2, hw]; linarith
  have hq0 : 0 ≤ q := norm_nonneg _
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
  have hqc : q ≤ ‖c‖ := by
    have : q ^ 2 ≤ ‖c‖ ^ 2 := by have := mul_nonneg ha (sq_nonneg ‖w‖); linarith
    exact (pow_le_pow_iff_left₀ hq0 hc0 (by norm_num)).1 this
  have k1 : εv * (‖c‖ - q) * (‖c‖ + q) ≤ s * (‖c‖ + q) :=
    mul_le_mul_of_nonneg_right h (by linarith)
  have k2 : s * (‖c‖ + q) ≤ s * (2 * ‖c‖) := mul_le_mul_of_nonneg_left (by linarith) hs
  have k3 : εv * (a * ‖w‖ ^ 2) ≤ εv * (‖c‖ ^ 2 - q ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hεv.le
  nlinarith

lemma inner_c_JJt {n m : ℕ} (P : Problem n m) (x : E n) :
    ⟪P.c x, P.J x (P.Jt x (P.c x))⟫_ℝ = ‖P.Jt x (P.c x)‖ ^ 2 := by
  rw [real_inner_comm, ← real_inner_self_eq_norm_sq]
  simp only [Problem.Jt, ContinuousLinearMap.adjoint_inner_right]

lemma inner_Jt {n m : ℕ} (P : Problem n m) (x : E n) (u : E n) (y : E m) :
    ⟪u, P.Jt x y⟫_ℝ = ⟪P.J x u, y⟫_ℝ := by
  simp only [Problem.Jt, ContinuousLinearMap.adjoint_inner_right]

lemma norm_Jt {n m : ℕ} (P : Problem n m) (x : E n) : ‖P.Jt x‖ = ‖P.J x‖ := by
  simp only [Problem.Jt, LinearIsometryEquiv.norm_map]

end StochSQPVanT3Aux

open StochSQPVanT3Aux

namespace StochSQPVanL2Aux

lemma cond15_false {n : ℕ} (u v : E n) (H : E n →L[ℝ] E n) (κH ζH χ' ζ' : ℝ)
    (hκH : 0 < κH) (hζH : 0 < ζH) (hHn : ‖H‖ ≤ κH) (hz : ζH * ‖u‖ ^ 2 ≤ ⟪u, H u⟫_ℝ)
    (hχ' : 4 * (κH / ζH) * (4 * (κH / ζH) + 1) ≤ χ') (hζ' : ζ' ≤ ζH)
    (h1 : χ' * ‖v‖ ^ 2 ≤ ‖u‖ ^ 2)
    (h2 : (1 / 2 : ℝ) * ⟪v + u, H (v + u)⟫_ℝ < (1 / 4 : ℝ) * ζ' * ‖u‖ ^ 2) : False := by
  set U := ‖u‖
  set V := ‖v‖
  have hU : 0 ≤ U := norm_nonneg _
  have hV : 0 ≤ V := norm_nonneg _
  have bnd : ∀ x y : E n, -(κH * ‖x‖ * ‖y‖) ≤ ⟪x, H y⟫_ℝ := by
    intro x y
    have h1 := abs_real_inner_le_norm x (H y)
    have h2 := neg_abs_le ⟪x, H y⟫_ℝ
    have h3 : ‖H y‖ ≤ κH * ‖y‖ :=
      (H.le_opNorm y).trans (mul_le_mul_of_nonneg_right hHn (norm_nonneg _))
    have h4 : ‖x‖ * ‖H y‖ ≤ ‖x‖ * (κH * ‖y‖) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    nlinarith
  have e : ⟪v + u, H (v + u)⟫_ℝ =
      ⟪v, H v⟫_ℝ + ⟪v, H u⟫_ℝ + ⟪u, H v⟫_ℝ + ⟪u, H u⟫_ℝ := by
    rw [map_add, inner_add_left, inner_add_right, inner_add_right]; ring
  have b1 := bnd v v
  have b2 := bnd v u
  have b3 := bnd u v
  set r := κH / ζH with hr
  have hr0 : 0 < r := div_pos hκH hζH
  have hκ : κH = r * ζH := by rw [hr]; field_simp
  -- AM-GM
  have amgm : 2 * κH * U * V ≤ ζH * (U ^ 2 / 4 + 4 * r ^ 2 * V ^ 2) := by
    rw [hκ]
    have : 0 ≤ ζH * (U / 2 - 2 * r * V) ^ 2 := by positivity
    nlinarith
  have hχV : r * (4 * r + 1) * V ^ 2 ≤ U ^ 2 / 4 := by
    have : 4 * r * (4 * r + 1) * V ^ 2 ≤ χ' * V ^ 2 :=
      mul_le_mul_of_nonneg_right hχ' (sq_nonneg _)
    linarith
  have key : ζH * U ^ 2 / 2 ≤ ⟪v + u, H (v + u)⟫_ℝ := by
    rw [e]
    have hvv : κH * V * V = ζH * (r * V ^ 2) := by rw [hκ]; ring
    have huv : κH * V * U + κH * U * V = 2 * κH * U * V := by ring
    have : ζH * (r * (4 * r + 1) * V ^ 2) ≤ ζH * (U ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hχV hζH.le
    nlinarith
  have : (1 / 4 : ℝ) * ζ' * U ^ 2 ≤ (1 / 4 : ℝ) * ζH * U ^ 2 := by
    have := mul_le_mul_of_nonneg_right hζ' (sq_nonneg U)
    nlinarith
  linarith

end StochSQPVanL2Aux

open StochSQPVanL2Aux

set_option maxHeartbeats 1000000 in
theorem solution {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (κH ζH : ℝ) :
    ∃ χmax > (0 : ℝ), ∃ ζmin > (0 : ℝ), ∀ R : Run n m, IsRun P A R → (∀ k, R.x k ∈ X) →
      Assumption3 P R κH ζH →
        ∃ K : ℕ, (∀ k ≥ K, R.χ k = R.χ K ∧ R.ζ k = R.ζ K) ∧
          0 < R.χ K ∧ R.χ K ≤ χmax ∧ ζmin ≤ R.ζ K := by
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA
  by_cases hpos : 0 < κH ∧ 0 < ζH
  swap
  · refine ⟨1, one_pos, 1, one_pos, ?_⟩
    intro R _ _ hA3
    exact absurd ⟨hA3.1, hA3.2.1⟩ hpos
  obtain ⟨hκH, hζH⟩ := hpos
  set χs := 4 * (κH / ζH) * (4 * (κH / ζH) + 1) with hχs
  set a := 1 + A.εχ with ha
  set b := 1 - A.εζ with hb
  have ha1 : 1 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hb1 : b < 1 := by linarith
  obtain ⟨N1, hN1⟩ := ((tendsto_pow_atTop_atTop_of_one_lt ha1).eventually_ge_atTop
    (χs / A.χ₀)).exists
  obtain ⟨N2, hN2⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hb0.le hb1).eventually
    (gt_mem_nhds (div_pos hζH hζ0))).exists
  set Ns := max N1 N2 with hNs
  have hNs1 : χs ≤ A.χ₀ * a ^ Ns := by
    have h1 : a ^ N1 ≤ a ^ Ns := pow_le_pow_right₀ ha1.le (le_max_left _ _)
    rw [div_le_iff₀ hχ0] at hN1
    nlinarith
  have hNs2 : A.ζ₀ * b ^ Ns ≤ ζH := by
    have h1 : b ^ Ns ≤ b ^ N2 := pow_le_pow_of_le_one hb0.le hb1.le (le_max_right _ _)
    rw [lt_div_iff₀ hζ0] at hN2
    nlinarith
  refine ⟨A.χ₀ * a ^ Ns, by positivity, A.ζ₀ * b ^ Ns, by positivity, ?_⟩
  intro R hR hX hA3
  obtain ⟨-, -, hH⟩ := hA3
  -- invariant: (χ_{k-1}, ζ_{k-1}) = (χ₀ aᴺ, ζ₀ bᴺ) with N ≤ Ns
  have inv : ∀ k, ∃ N ≤ Ns, prev R.χ A.χ₀ k = A.χ₀ * a ^ N ∧
      prev R.ζ A.ζ₀ k = A.ζ₀ * b ^ N := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _, by simp [prev], by simp [prev]⟩
    | succ k ih =>
      obtain ⟨N, hN, hχN, hζN⟩ := ih
      show ∃ N ≤ Ns, R.χ k = A.χ₀ * a ^ N ∧ R.ζ k = A.ζ₀ * b ^ N
      obtain ⟨-, -, -, -, -, -, -, hdd, hd0, hd1, -⟩ := hR k
      by_cases hd : R.d k = 0
      · obtain ⟨-, h1, h2, -⟩ := hd0 hd
        exact ⟨N, hN, h1.trans hχN, h2.trans hζN⟩
      obtain ⟨-, hcz, -, -⟩ := hd1 hd
      by_cases h15 : Cond15 A R k
      · obtain ⟨h1, h2⟩ := hcz.1 h15
        refine ⟨N + 1, ?_, ?_, ?_⟩
        · by_contra hlt
          have hNe : N = Ns := by omega
          obtain ⟨c1, c2⟩ := h15
          obtain ⟨-, hHn, hHz⟩ := hH k
          obtain ⟨-, -, -, -, -, -, hJu, -⟩ := hR k
          have hker : R.u k ∈ LinearMap.ker (P.J (R.x k) : E n →ₗ[ℝ] E m) := by
            simp [LinearMap.mem_ker, hJu]
          rw [hdd] at c2
          rw [hχN, hNe] at c1
          rw [hζN, hNe] at c2
          exact cond15_false (R.u k) (R.v k) (R.H k) κH ζH _ _ hκH hζH hHn (hHz _ hker)
            hNs1 hNs2 c1 c2
        · rw [h1, hχN, pow_succ]; ring
        · rw [h2, hζN, pow_succ]; ring
      · obtain ⟨h1, h2⟩ := hcz.2 h15
        exact ⟨N, hN, h1.trans hχN, h2.trans hζN⟩
  have hχb : ∀ k, 0 < R.χ k ∧ R.χ k ≤ A.χ₀ * a ^ Ns ∧ A.ζ₀ * b ^ Ns ≤ R.ζ k := by
    intro k
    obtain ⟨N, hN, hχN, hζN⟩ := inv (k + 1)
    change R.χ k = _ at hχN
    change R.ζ k = _ at hζN
    refine ⟨by rw [hχN]; positivity, ?_, ?_⟩
    · rw [hχN]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha1.le hN) hχ0.le
    · rw [hζN]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb0.le hb1.le hN) hζ0.le
  -- monotonicity / jump structure of χ
  have hjump : ∀ k, (R.χ (k + 1) = R.χ k ∧ R.ζ (k + 1) = R.ζ k) ∨
      R.χ (k + 1) = a * R.χ k := by
    intro k
    obtain ⟨-, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR (k + 1)
    by_cases hd : R.d (k + 1) = 0
    · obtain ⟨-, h1, h2, -⟩ := hd0 hd
      exact Or.inl ⟨h1, h2⟩
    obtain ⟨-, hcz, -, -⟩ := hd1 hd
    by_cases h15 : Cond15 A R (k + 1)
    · exact Or.inr (hcz.1 h15).1
    · exact Or.inl (hcz.2 h15)
  have hbdd : BddAbove (Set.range R.χ) := ⟨A.χ₀ * a ^ Ns, by
    rintro _ ⟨k, rfl⟩; exact (hχb k).2.1⟩
  set Lχ := ⨆ k, R.χ k with hLχ
  have hLpos : 0 < Lχ := lt_of_lt_of_le (hχb 0).1 (le_ciSup hbdd 0)
  obtain ⟨K, hK⟩ := exists_lt_of_lt_ciSup (show Lχ / a < Lχ by
    rw [div_lt_iff₀ (by linarith)]; nlinarith)
  have hconst : ∀ j, R.χ (K + j) = R.χ K ∧ R.ζ (K + j) = R.ζ K := by
    intro j
    induction j with
    | zero => exact ⟨rfl, rfl⟩
    | succ j ih =>
      rcases hjump (K + j) with ⟨h1, h2⟩ | h1
      · exact ⟨h1.trans ih.1, h2.trans ih.2⟩
      · exfalso
        have hle : R.χ (K + j + 1) ≤ Lχ := le_ciSup hbdd _
        rw [h1, ih.1] at hle
        rw [div_lt_iff₀ (by linarith)] at hK
        linarith
  refine ⟨K, ?_, (hχb K).1, (hχb K).2.1, (hχb K).2.2⟩
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact hconst j
