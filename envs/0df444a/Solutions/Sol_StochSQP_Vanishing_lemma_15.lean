-- Prove2me | solution 1 for StochSQP.Vanishing.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:07:43.413494+00:00
-- url     : https://prove2.me/submissions/aa3b3141-4570-4bdc-a5b7-1688618c12b5

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model
import Theorems.Thm_StochSQP_Vanishing_lemma_3
import Theorems.Thm_StochSQP_Vanishing_lemma_1
import Theorems.Thm_StochSQP_Vanishing_lemma_7
import Theorems.Thm_StochSQP_Vanishing_eq_14

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

theorem tau_nonneg_aux {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (R : Run n m) (hR : IsRun P A R) : ∀ k, 0 ≤ R.τ k := by
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA
  have hJd : ∀ k, P.J (R.x k) (R.d k) = P.J (R.x k) (R.v k) := by
    intro k
    obtain ⟨-, -, -, -, -, -, hJu, hdd, -⟩ := hR k
    rw [hdd, map_add, hJu, add_zero]
  have hs0 : ∀ k, 0 ≤ ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ := by
    intro k
    obtain ⟨-, -, -, -, hcau, -⟩ := hR k
    have h0 := hcau 0 ⟨le_rfl, hω.le⟩
    simp only [zero_smul, add_zero, sub_self, mul_zero] at h0
    exact h0
  -- τ_k ≥ 0
  have hstep : ∀ k, 0 ≤ prev R.τ A.τ₀ k → 0 ≤ R.τ k := by
    intro k hp
    obtain ⟨-, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR k
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).1]; exact hp
    obtain ⟨htr, -⟩ := hd1 hd
    by_cases hD : ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ ≤ 0
    · rw [htr.1 hD]; exact hp
    push_neg at hD
    have h2 := htr.2 hD
    simp only [hJd k] at h2
    by_cases hpt : prev R.τ A.τ₀ k ≤ (1 - A.σ) * (‖P.c (R.x k)‖ -
        ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) / (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ)
    · rw [h2.1 hpt]; exact hp
    push_neg at hpt
    rw [h2.2 hpt]
    exact le_min (mul_nonneg (by linarith) hp)
      (div_nonneg (mul_nonneg (by linarith) (hs0 k)) hD.le)
  have hτnn : ∀ k, 0 ≤ R.τ k := by
    intro k
    induction k with
    | zero => exact hstep 0 hτ0.le
    | succ j ih => exact hstep (j + 1) ih
  exact hτnn

set_option maxHeartbeats 2000000 in
theorem solution {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH)
    (M : ℝ) (hM : 0 < M) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ^ 2 ≤ M)
    (hτ : Filter.Tendsto R.τ Filter.atTop (nhds 0)) :
    (∃ αLow > (0 : ℝ), ∀ k : ℕ, ¬ R.TangDom k → αLow * R.β k ≤ R.α k) ∧
    (∃ C > (0 : ℝ), ∀ γ > (0 : ℝ), ∀ k : ℕ,
      γ ≤ ‖P.Jt (R.x k) (P.c (R.x k))‖ → R.TangDom k →
        min ((C * γ ^ 2) * R.β k)
          ((C * γ ^ 2) * R.β k * R.τ k + A.θ * R.β k ^ 2) ≤ R.α k) := by
  have hτnn := tau_nonneg_aux P A hA R hR
  have h14 := StochSQP.Vanishing.eq_14 P A hA X hA1 R hR hX κH ζH hA3
  obtain ⟨ξmin, hξmin, hL3⟩ := StochSQP.Vanishing.lemma_3 P A hA X hA1 κH ζH
  obtain ⟨κv, hκv, ωl, hωl, hL1⟩ := StochSQP.Vanishing.lemma_1 P A hA X hA1
  have hA' := hA
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA'
  have hA1' := hA1
  obtain ⟨-, -, -, -, -, -, -, -, -, hcB, -, hJB⟩ := hA1'
  obtain ⟨κc, hκc, hc⟩ := bound_of_isBounded hcB
  obtain ⟨κJ, hκJ, hJ⟩ := bound_of_isBounded hJB
  have hA3' := hA3
  obtain ⟨hκH, hζH, hH⟩ := hA3'
  have hcx : ∀ k, ‖P.c (R.x k)‖ ≤ κc := fun k => hc _ ⟨_, hX k, rfl⟩
  have hJx : ∀ k, ‖P.J (R.x k)‖ ≤ κJ := fun k => hJ _ ⟨_, hX k, rfl⟩
  have hw : ∀ k, ‖P.Jt (R.x k) (P.c (R.x k))‖ ≤ κJ * κc := by
    intro k
    calc ‖P.Jt (R.x k) (P.c (R.x k))‖ ≤ ‖P.Jt (R.x k)‖ * ‖P.c (R.x k)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ κJ * κc := by
        rw [norm_Jt]; exact mul_le_mul (hJx k) (hcx k) (norm_nonneg _) hκJ.le
  -- gradient error bound and Lemma 7
  set Eg := max M 1 with hEg
  have hEg0 : 0 < Eg := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hgk : ∀ k, ‖R.g k - P.grad (R.x k)‖ ≤ Eg := by
    intro k
    by_cases h : ‖R.g k - P.grad (R.x k)‖ ≤ 1
    · exact h.trans (le_max_right _ _)
    · push_neg at h
      have := hg k
      have : ‖R.g k - P.grad (R.x k)‖ ≤ M := by nlinarith
      exact this.trans (le_max_left _ _)
  obtain ⟨κu, hκu, hu⟩ := StochSQP.Vanishing.lemma_7 P A hA X hA1 R hR hX κH ζH hA3 Eg hEg0 hgk
  set V := A.ω * (κJ * κc) with hV
  have hV0 : 0 ≤ V := by positivity
  have hdk : ∀ k, ‖R.d k‖ ≤ V + κu := by
    intro k
    obtain ⟨-, -, -, hvn, -, -, -, hdd, -⟩ := hR k
    rw [hdd]
    exact (norm_add_le _ _).trans (add_le_add (hvn.trans
      (mul_le_mul_of_nonneg_left (hw k) hω.le)) (hu k))
  set κd := V + κu with hκd
  have hκd0 : 0 < κd := by positivity
  -- τ ≤ τ₀
  have hτstep : ∀ k, R.τ k ≤ prev R.τ A.τ₀ k := by
    intro k
    have hp : 0 ≤ prev R.τ A.τ₀ k := by
      cases k with
      | zero => exact hτ0.le
      | succ j => exact hτnn j
    obtain ⟨-, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR k
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).1]
    obtain ⟨htr, -⟩ := hd1 hd
    by_cases hD : ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ ≤ 0
    · rw [htr.1 hD]
    push_neg at hD
    have h2 := htr.2 hD
    by_cases hpt : prev R.τ A.τ₀ k ≤ (1 - A.σ) * (‖P.c (R.x k)‖ -
        ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) / (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ)
    · rw [h2.1 hpt]
    push_neg at hpt
    rw [h2.2 hpt]
    exact (min_le_left _ _).trans (by nlinarith)
  have hτup : ∀ k, R.τ k ≤ A.τ₀ := by
    intro k
    induction k with
    | zero => exact hτstep 0
    | succ j ih => exact (hτstep (j + 1)).trans ih
  -- Δl ≥ 0 and the s ≥ 0
  have hs0 : ∀ k, 0 ≤ ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ := by
    intro k
    obtain ⟨-, -, -, -, hcau, -⟩ := hR k
    have h0 := hcau 0 ⟨le_rfl, hω.le⟩
    simp only [zero_smul, add_zero, sub_self, mul_zero] at h0
    exact h0
  have hΔs : ∀ k, A.σ * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) ≤
      deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
    intro k
    obtain ⟨-, -, -, -, -, -, hJu, -⟩ := hR k
    obtain ⟨-, -, hHz⟩ := hH k
    have hker : R.u k ∈ LinearMap.ker (P.J (R.x k) : E n →ₗ[ℝ] E m) := by
      simp [LinearMap.mem_ker, hJu]
    have hz := hHz _ hker
    have := h14 k
    have h1 : 0 ≤ R.τ k * ⟪R.u k, R.H k (R.u k)⟫_ℝ :=
      mul_nonneg (hτnn k) (le_trans (by positivity) hz)
    linarith
  have hΔ0 : ∀ k, 0 ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) :=
    fun k => le_trans (mul_nonneg hσ.le (hs0 k)) (hΔs k)
  -- ξ_k ≥ ξmin for all k
  have hξstep : ∀ k, 0 ≤ prev R.ξ A.ξ₀ k → 0 ≤ R.ξ k ∧ R.ξ k ≤ prev R.ξ A.ξ₀ k := by
    intro k hp0
    obtain ⟨-, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR k
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).2.2.2.1]; exact ⟨hp0, le_rfl⟩
    obtain ⟨-, -, hxi, -⟩ := hd1 hd
    have htr0 : 0 ≤ xiTrial P R k := by
      unfold xiTrial
      split_ifs
      · exact div_nonneg (hΔ0 k) (mul_nonneg (hτnn k) (sq_nonneg _))
      · exact div_nonneg (hΔ0 k) (sq_nonneg _)
    by_cases hh : prev R.ξ A.ξ₀ k ≤ xiTrial P R k
    · rw [hxi.1 hh]; exact ⟨hp0, le_rfl⟩
    · push_neg at hh; rw [hxi.2 hh]
      refine ⟨le_min (mul_nonneg (by linarith) hp0) htr0, ?_⟩
      exact (min_le_left _ _).trans (by nlinarith)
  have hξb : ∀ k, 0 ≤ R.ξ k ∧ R.ξ k ≤ prev R.ξ A.ξ₀ k := by
    intro k
    induction k with
    | zero => exact hξstep 0 hξ0.le
    | succ j ih => exact hξstep (j + 1) ih.1
  have hξanti : Antitone R.ξ := antitone_nat_of_succ_le fun j => (hξb (j + 1)).2
  obtain ⟨K3, hK3c, hK3⟩ := hL3 R hR hX hA3
  have hξlow : ∀ k, ξmin ≤ R.ξ k := by
    intro k
    rcases le_total k K3 with h | h
    · exact hK3.trans (hξanti h)
    · rw [hK3c k h]; exact hK3
  -- common facts
  set Q0 := A.τ₀ * A.L + A.Γ with hQ0
  have hQ00 : 0 < Q0 := by positivity
  have hη' : 0 < 1 - A.η := by linarith
  set c3 := 2 * (1 - A.η) * ξmin / Q0 with hc3
  have hc30 : 0 < c3 := by positivity
  have hQ : ∀ k, A.Γ ≤ R.τ k * A.L + A.Γ ∧ R.τ k * A.L + A.Γ ≤ Q0 := by
    intro k
    constructor
    · have := mul_nonneg (hτnn k) hL.le; linarith
    · have := mul_le_mul_of_nonneg_right (hτup k) hL.le; linarith
  -- lower end of the projection interval, normal case
  have hlo_n : ∀ k, c3 * R.β k ≤ 2 * (1 - A.η) * R.β k * R.ξ k / (R.τ k * A.L + A.Γ) := by
    intro k
    obtain ⟨⟨hβ0, -⟩, -⟩ := hR k
    have hQk := hQ k
    rw [hc3, le_div_iff₀ (by linarith)]
    have h1 : 2 * (1 - A.η) * ξmin / Q0 * (R.τ k * A.L + A.Γ) ≤ 2 * (1 - A.η) * ξmin := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hQ00]
      exact mul_le_mul_of_nonneg_left hQk.2 (by positivity)
    have h2 : 2 * (1 - A.η) * ξmin ≤ 2 * (1 - A.η) * R.ξ k :=
      mul_le_mul_of_nonneg_left (hξlow k) (by positivity)
    have := mul_le_mul_of_nonneg_left (h1.trans h2) hβ0.le
    nlinarith
  -- α ≥ lo and α ≥ min(αsuff, hi) when d ≠ 0
  have hαlo : ∀ k, R.d k ≠ 0 → projLo A R k ≤ R.α k ∧
      min (alphaSuff P A R k) (projHi A R k) ≤ R.α k := by
    intro k hd
    obtain ⟨-, -, -, -, -, -, -, -, -, hd1, -⟩ := hR k
    obtain ⟨-, -, -, hal⟩ := hd1 hd
    rw [hal]; unfold proj
    exact ⟨le_max_left _ _, le_max_right _ _⟩
  constructor
  · refine ⟨min 1 c3, lt_min one_pos hc30, ?_⟩
    intro k hT
    obtain ⟨⟨hβ0, hβ1⟩, -, -, -, -, -, -, -, hd0, -⟩ := hR k
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).2.2.2.2]
      exact (mul_le_mul (min_le_left _ _) hβ1 hβ0.le zero_le_one).trans (by norm_num)
    have h1 := (hαlo k hd).1
    unfold projLo at h1
    rw [if_neg (show ¬ (R.χ k * ‖R.v k‖ ^ 2 ≤ ‖R.u k‖ ^ 2) from hT)] at h1
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hβ0.le) ((hlo_n k).trans h1)
  · set W := κJ * κc with hW
    have hW0 : 0 < W := by positivity
    set C1 := 2 * (1 - A.η) * A.σ * κv / (κc * Q0 * κd ^ 2) with hC1
    have hC10 : 0 < C1 := by positivity
    set C := min C1 (min (1 / W ^ 2) (c3 / W ^ 2)) with hC
    have hC0 : 0 < C := lt_min hC10 (lt_min (by positivity) (by positivity))
    refine ⟨C, hC0, ?_⟩
    intro γ hγ k hγk hT
    obtain ⟨⟨hβ0, hβ1⟩, -, -, -, -, -, -, -, hd0, -⟩ := hR k
    have hγW : γ ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ hγ.le (hγk.trans (hw k)) 2
    have hCγ1 : C * γ ^ 2 ≤ 1 := by
      have : C ≤ 1 / W ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith [mul_le_mul_of_nonneg_left hγW hC0.le]
    have hCγ3 : C * γ ^ 2 ≤ c3 := by
      have : C ≤ c3 / W ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith [mul_le_mul_of_nonneg_left hγW hC0.le]
    set mm := min ((C * γ ^ 2) * R.β k) ((C * γ ^ 2) * R.β k * R.τ k + A.θ * R.β k ^ 2)
      with hmm
    have hm1 : mm ≤ (C * γ ^ 2) * R.β k := min_le_left _ _
    have hm2 : mm ≤ (C * γ ^ 2) * R.β k * R.τ k + A.θ * R.β k ^ 2 := min_le_right _ _
    have hmle1 : mm ≤ 1 := hm1.trans (by nlinarith)
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).2.2.2.2]; exact hmle1
    refine le_trans ?_ (hαlo k hd).2
    refine le_min (le_min ?_ hmle1) ?_
    · -- mm ≤ X
      have hck : 0 < ‖P.c (R.x k)‖ := by
        by_contra h0
        have : P.c (R.x k) = 0 := norm_eq_zero.1 (le_antisymm (not_lt.1 h0) (norm_nonneg _))
        rw [this, map_zero, norm_zero] at hγk
        linarith
      obtain ⟨hL1a, -⟩ := hL1 R hR hX k hck
      set s := ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ with hsd
      have hsγ : κv * γ ^ 2 ≤ κc * s := by
        have h1 : κv * γ ^ 2 ≤ κv * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hγ.le hγk 2) hκv.le
        have h2 : ‖P.c (R.x k)‖ * s ≤ κc * s := mul_le_mul_of_nonneg_right (hcx k) (hs0 k)
        linarith
      have hdpos : 0 < ‖R.d k‖ ^ 2 := by have := norm_pos_iff.2 hd; positivity
      have hd2 : ‖R.d k‖ ^ 2 ≤ κd ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hdk k) 2
      have hQk := hQ k
      refine le_trans hm1 ?_
      rw [le_div_iff₀ (by have : 0 < R.τ k * A.L + A.Γ := by linarith
                          positivity)]
      have hCC : C * γ ^ 2 ≤ C1 * γ ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
      -- C1 γ² Q ‖d‖² ≤ 2(1-η) σ κv γ²/κc ≤ 2(1-η) σ s ≤ 2(1-η) Δ
      have k1 : (R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2 ≤ Q0 * κd ^ 2 :=
        mul_le_mul hQk.2 hd2 hdpos.le hQ00.le
      have k2 : C1 * γ ^ 2 * (Q0 * κd ^ 2) = 2 * (1 - A.η) * A.σ * (κv * γ ^ 2) / κc := by
        rw [hC1]; field_simp
      have k3 : 2 * (1 - A.η) * A.σ * (κv * γ ^ 2) / κc ≤ 2 * (1 - A.η) * A.σ * s := by
        rw [div_le_iff₀ hκc]
        have := mul_le_mul_of_nonneg_left hsγ (by positivity : (0:ℝ) ≤ 2 * (1 - A.η) * A.σ)
        linarith
      have k4 : 2 * (1 - A.η) * (A.σ * s) ≤
          2 * (1 - A.η) * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) :=
        mul_le_mul_of_nonneg_left (hΔs k) (by positivity)
      have k5 : C * γ ^ 2 * ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) ≤ C1 * γ ^ 2 * (Q0 * κd ^ 2) :=
        mul_le_mul hCC k1 (mul_nonneg (by linarith [hQk.1]) hdpos.le) (by positivity)
      have k6 := mul_le_mul_of_nonneg_left ((k5.trans k2.le).trans k3) hβ0.le
      have e1 : C * γ ^ 2 * R.β k * ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) =
          R.β k * (C * γ ^ 2 * ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2)) := by ring
      rw [e1]
      have := mul_le_mul_of_nonneg_left k4 hβ0.le
      nlinarith
    · -- mm ≤ hi
      refine hm2.trans ?_
      unfold projHi projLo
      rw [if_pos (show R.χ k * ‖R.v k‖ ^ 2 ≤ ‖R.u k‖ ^ 2 from hT)]
      have h1 : C * γ ^ 2 * R.β k * R.τ k ≤ c3 * R.β k * R.τ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCγ3 hβ0.le) (hτnn k)
      have h2 : c3 * R.β k * R.τ k ≤ 2 * (1 - A.η) * R.β k * R.ξ k * R.τ k /
          (R.τ k * A.L + A.Γ) := by
        have := mul_le_mul_of_nonneg_right (hlo_n k) (hτnn k)
        calc c3 * R.β k * R.τ k
            ≤ 2 * (1 - A.η) * R.β k * R.ξ k / (R.τ k * A.L + A.Γ) * R.τ k := this
          _ = 2 * (1 - A.η) * R.β k * R.ξ k * R.τ k / (R.τ k * A.L + A.Γ) := by ring
      linarith
