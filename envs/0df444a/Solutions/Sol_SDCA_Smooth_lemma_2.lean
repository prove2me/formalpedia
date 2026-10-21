-- Prove2me | solution 1 for SDCA.Smooth.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:32:07.976712+00:00
-- url     : https://prove2.me/submissions/d0d0dc1c-9941-43f6-be9d-a44321d2859a

import Mathlib
import Definitions.Def_SDCA_Smooth_Model

set_option autoImplicit false
open SDCA.Smooth
open SDCA.Lipschitz (conj)

/-- weak duality for an arbitrary primal point `w`. -/
theorem sds_weak_duality {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (lam : ℝ) (hn : 0 < n) (hlam : 0 < lam) (w : EuclideanSpace ℝ (Fin d)) (α : Fin n → ℝ) :
    dual lam x φ α ≤ ((primal lam x φ w : ℝ) : EReal) := by
  set v := wOf lam x α with hv
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hln : lam * n ≠ 0 := by positivity
  -- Fenchel-Young
  have hFY : ∀ i, -conj (φ i) (-α i) ≤
      ((φ i (inner ℝ w (x i)) + α i * inner ℝ w (x i) : ℝ) : EReal) := by
    intro i
    rw [EReal.neg_le, ← EReal.coe_neg]
    have := le_iSup (fun z : ℝ => ((z * (-α i) - φ i z : ℝ) : EReal)) (inner ℝ w (x i))
    refine le_trans (le_of_eq ?_) this
    congr 1; ring
  have hsum : ∑ i, -conj (φ i) (-α i) ≤
      ((∑ i, (φ i (inner ℝ w (x i)) + α i * inner ℝ w (x i)) : ℝ) : EReal) := by
    have : ((∑ i, (φ i (inner ℝ w (x i)) + α i * inner ℝ w (x i)) : ℝ) : EReal) =
        ∑ i, ((φ i (inner ℝ w (x i)) + α i * inner ℝ w (x i) : ℝ) : EReal) := by
      let f : ℝ →+ EReal := ⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩
      exact map_sum f _ _
    rw [this]
    exact Finset.sum_le_sum (fun i _ => hFY i)
  have hmul : (((1 / (n : ℝ)) : ℝ) : EReal) * ∑ i, -conj (φ i) (-α i) ≤
      (((1 / (n : ℝ)) : ℝ) : EReal) *
        ((∑ i, (φ i (inner ℝ w (x i)) + α i * inner ℝ w (x i)) : ℝ) : EReal) :=
    mul_le_mul_of_nonneg_left hsum (by exact_mod_cast (by positivity : (0:ℝ) ≤ 1 / (n : ℝ)))
  have hmain : dual lam x φ α ≤
      (((1 / (n : ℝ)) * (∑ i, (φ i (inner ℝ w (x i)) + α i * inner ℝ w (x i))) -
        lam / 2 * ‖v‖ ^ 2 : ℝ) : EReal) := by
    unfold dual
    rw [← hv]
    push_cast
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add hmul le_rfl
  refine hmain.trans ?_
  rw [EReal.coe_le_coe_iff]
  -- real inequality
  have hinner : ∑ i, α i * inner ℝ w (x i) = lam * n * inner ℝ w v := by
    have h1 : (lam * n) • v = ∑ i, α i • x i := by
      rw [hv]; unfold wOf
      rw [smul_smul, mul_one_div_cancel hln, one_smul]
    have := congrArg (fun y => inner ℝ w y) h1
    simp only [inner_smul_right, inner_sum] at this
    rw [← this]
  have hsplit : ∑ i, (φ i (inner ℝ w (x i)) + α i * inner ℝ w (x i)) =
      ∑ i, φ i (inner ℝ w (x i)) + lam * n * inner ℝ w v := by
    rw [Finset.sum_add_distrib, hinner]
  rw [hsplit]
  unfold primal
  have hsq : 0 ≤ ‖w - v‖ ^ 2 := sq_nonneg _
  have : ‖w - v‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w v + ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real]
  have e : (1 / (n : ℝ)) * (∑ i, φ i (inner ℝ w (x i)) + lam * n * inner ℝ w v) -
      lam / 2 * ‖v‖ ^ 2 =
      (1 / (n : ℝ)) * ∑ i, φ i (inner ℝ w (x i)) + lam / 2 * ‖w‖ ^ 2 - lam / 2 * ‖w - v‖ ^ 2 := by
    rw [this]; field_simp; ring
  rw [e]
  nlinarith [mul_nonneg hlam.le hsq]

theorem solution {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam : ℝ) (hlam : 0 < lam)
    (hφnn : ∀ i a, 0 ≤ φ i a) (hφ0 : ∀ i, φ i 0 ≤ 1)
    (wstar : EuclideanSpace ℝ (Fin d)) (hwstar : ∀ w, primal lam x φ wstar ≤ primal lam x φ w) :
    (∀ α : Fin n → ℝ, dual lam x φ α ≤ ((primal lam x φ wstar : ℝ) : EReal)) ∧
    primal lam x φ wstar ≤ primal lam x φ 0 ∧ primal lam x φ 0 ≤ 1 ∧
    0 ≤ dual lam x φ 0 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun α => sds_weak_duality φ x lam hn hlam wstar α, hwstar 0, ?_, ?_⟩
  · unfold primal
    simp only [inner_zero_left, norm_zero]
    have : ∑ i : Fin n, φ i 0 ≤ ∑ i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hφ0 i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    have : 1 / (n : ℝ) * ∑ i : Fin n, φ i 0 ≤ 1 := by
      rw [one_div, inv_mul_le_iff₀ hnpos]; linarith
    simpa using this
  · unfold dual
    have hw0 : wOf lam x (0 : Fin n → ℝ) = 0 := by simp [wOf]
    rw [hw0]
    simp only [norm_zero]
    have hc : ∀ i, 0 ≤ -conj (φ i) (-(0 : Fin n → ℝ) i) := by
      intro i
      rw [EReal.neg_nonneg]
      unfold conj
      refine iSup_le (fun z => ?_)
      have := hφnn i z
      have h0 : ((z * -(0 : Fin n → ℝ) i - φ i z : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := by
        rw [EReal.coe_le_coe_iff]; simp; exact this
      simpa using h0
    have hs : 0 ≤ ∑ i, -conj (φ i) (-(0 : Fin n → ℝ) i) := Finset.sum_nonneg (fun i _ => hc i)
    have : 0 ≤ (((1 / (n : ℝ)) : ℝ) : EReal) * ∑ i, -conj (φ i) (-(0 : Fin n → ℝ) i) :=
      mul_nonneg (by exact_mod_cast (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))) hs
    simpa using this
