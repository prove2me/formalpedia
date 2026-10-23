-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.distanceSpectralFloor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:54:56.410759+00:00
-- url     : https://prove2.me/submissions/4a6727d9-4603-4d1f-a65d-63b0504fa53d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

open Matrix

lemma x8_perm_unitary {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    σ.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix,
    ← permMatrix_mul, inv_mul_cancel, permMatrix_one]

lemma x8_perm_diag {d : ℕ} (N : Mat d → ℝ) (hN : IsUINorm N) (σ : Equiv.Perm (Fin d))
    (f : Fin d → ℂ) : N (diagonal (f ∘ σ)) = N (diagonal f) := by
  have h := hN.2.2.2.2 ⟨_, x8_perm_unitary σ⟩ ⟨_, x8_perm_unitary σ⁻¹⟩ (diagonal f)
  simp only at h
  rw [← h]
  congr 1
  ext a b
  simp [Equiv.Perm.permMatrix, mul_apply, PEquiv.toMatrix_apply, diagonal_apply,
    Equiv.toPEquiv_apply, Equiv.symm_apply_eq]
  by_cases h : a = b
  · subst h; simp
  · have : σ a ≠ σ b := fun h' => h (σ.injective h')
    simp [h, Equiv.Perm.inv_eq_iff_eq, this]

lemma x8_sum_le {d : ℕ} (N : Mat d → ℝ) (hN : IsUINorm N) {ι : Type*} (s : Finset ι)
    (A : ι → Mat d) : N (∑ x ∈ s, A x) ≤ ∑ x ∈ s, N (A x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [(hN.2.1 0).2 rfl]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hN.2.2.1 _ _).trans (by linarith)

/-- `e_i - e_j` on the diagonal. -/
def x8g {d : ℕ} (i j : Fin d) : Fin d → ℂ :=
  fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)

lemma x8_g_norm {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N) (i j : Fin d) :
    N (diagonal (x8g i j)) ≤ N (matrixF d) := by
  by_cases hij : i = j
  · subst hij
    have : diagonal (x8g i i) = 0 := by ext a b; simp [x8g, diagonal_apply]
    rw [this, (hN.2.1 0).2 rfl]; exact hN.1 _
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set τ := Equiv.swap j ⟨1, by omega⟩
  have hτi : τ i ≠ ⟨1, by omega⟩ := by
    intro h; apply hij; apply τ.injective; rw [h]; exact (Equiv.swap_apply_left _ _).symm
  set σ := Equiv.swap (τ i) ⟨0, by omega⟩ * τ
  have hσi : σ i = ⟨0, by omega⟩ := by
    show Equiv.swap (τ i) _ (τ i) = _; exact Equiv.swap_apply_left _ _
  have hσj : σ j = ⟨1, by omega⟩ := by
    show Equiv.swap (τ i) _ (τ j) = _
    rw [show τ j = ⟨1, by omega⟩ from Equiv.swap_apply_left _ _,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hτi) (Ne.symm h01)]
  have hF : matrixF d = diagonal (fun k : Fin d =>
      if k.val = 0 then (1 : ℂ) else if k.val = 1 then -1 else 0) := rfl
  rw [hF, ← x8_perm_diag N hN σ (fun k : Fin d =>
      if k.val = 0 then (1 : ℂ) else if k.val = 1 then -1 else 0)]
  apply le_of_eq
  congr 2
  funext k
  simp only [Function.comp_apply, x8g]
  by_cases hki : k = i
  · subst hki; rw [hσi]; simp [hij]
  by_cases hkj : k = j
  · subst hkj; rw [hσj]; simp [hki]
  have h0 : (σ k).val ≠ 0 := by
    intro h; apply hki; apply σ.injective; rw [hσi]; exact Fin.ext h
  have h1 : (σ k).val ≠ 1 := by
    intro h; apply hkj; apply σ.injective; rw [hσj]; exact Fin.ext h
  simp [h0, h1, hki, hkj]

/-- A real traceless diagonal is a nonnegative combination of `t (e_i - e_j)`. -/
lemma x8_diag_bound {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N) (μ : Fin d → ℝ)
    (hμ : ∑ i, μ i = 0) :
    N (diagonal (fun i => (μ i : ℂ))) ≤ (∑ i, max (μ i) 0) * N (matrixF d) := by
  set t := ∑ i, max (μ i) 0
  set p : Fin d → ℝ := fun i => max (μ i) 0
  set n : Fin d → ℝ := fun i => max (-μ i) 0
  have hpn : ∀ i, p i - n i = μ i := by
    intro i; simp only [p, n]
    rcases le_total (μ i) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hn : ∑ i, n i = t := by
    have : ∑ i, (p i - n i) = 0 := by simp only [hpn]; exact hμ
    rw [Finset.sum_sub_distrib] at this
    show _ = ∑ i, p i
    linarith
  have hp0 : ∀ i, 0 ≤ p i := fun i => le_max_right _ _
  have hn0 : ∀ i, 0 ≤ n i := fun i => le_max_right _ _
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => hp0 i
  rcases ht0.lt_or_eq with htpos | htz
  · have hdec : diagonal (fun i => (μ i : ℂ)) =
        ∑ i, ∑ j, ((p i * n j / t : ℝ) : ℂ) • diagonal (x8g i j) := by
      ext a b
      simp only [Matrix.sum_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
      by_cases hab : a = b
      · subst hab
        simp only [if_true]
        have key : ∑ i, ∑ j, (p i * n j / t) * ((if a = i then 1 else 0) - (if a = j then 1 else 0))
            = μ a := by
          simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_eq_single a (fun i _ hi => Finset.sum_eq_zero fun j _ => if_neg
            (Ne.symm hi)) (by simp)]
          simp only [if_true]
          rw [Finset.sum_comm, Finset.sum_eq_single a (fun j _ hj => Finset.sum_eq_zero fun i _ =>
            if_neg (Ne.symm hj)) (by simp)]
          simp only [if_true]
          have e1 : ∑ x, p a * n x / t = p a := by
            rw [← Finset.sum_div, ← Finset.mul_sum, hn, mul_div_assoc, div_self htpos.ne', mul_one]
          have e2 : ∑ x, p x * n a / t = n a := by
            rw [← Finset.sum_div, ← Finset.sum_mul, show ∑ i, p i = t from rfl, mul_comm,
              mul_div_assoc, div_self htpos.ne', mul_one]
          rw [e1, e2]
          exact hpn a
        rw [← key]
        push_cast
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [x8g]
        split_ifs <;> simp
      · simp [hab]
    rw [hdec]
    refine (x8_sum_le N hN _ _).trans ?_
    calc ∑ i, N (∑ j, ((p i * n j / t : ℝ) : ℂ) • diagonal (x8g i j))
        ≤ ∑ i, ∑ j, (p i * n j / t) * N (matrixF d) := by
          refine Finset.sum_le_sum fun i _ => (x8_sum_le N hN _ _).trans ?_
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hN.2.2.2.1, Complex.norm_real, Real.norm_of_nonneg
            (div_nonneg (mul_nonneg (hp0 i) (hn0 j)) htpos.le)]
          exact mul_le_mul_of_nonneg_left (x8_g_norm hd N hN i j)
            (div_nonneg (mul_nonneg (hp0 i) (hn0 j)) htpos.le)
      _ = t * N (matrixF d) := by
          simp only [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum, hn]
          show (∑ i, p i) * t / t * _ = t * _
          rw [show ∑ i, p i = t from rfl, mul_div_assoc, div_self htpos.ne', mul_one]
  · have hz : ∀ i, μ i = 0 := by
      intro i
      have hpz : ∀ i, p i = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hp0 i).1 htz.symm i
          (Finset.mem_univ _)
        exact this
      have hnz : ∀ i, n i = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hn0 i).1 (hn.trans htz.symm) i
          (Finset.mem_univ _)
        exact this
      rw [← hpn i, hpz i, hnz i, sub_zero]
    have : diagonal (fun i => (μ i : ℂ)) = 0 := by
      ext a b; simp [diagonal_apply, hz]
    rw [this, (hN.2.1 0).2 rfl, ← htz, zero_mul]

lemma x8_t_bound {d : ℕ} [NeZero d] (a b : Fin d → ℝ) (beta : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hsa : ∑ i, a i = 1) (hb : ∀ i, 0 ≤ b i) (hbb : ∀ i, beta ≤ b i) (hsb : ∑ i, b i = 1) :
    ∑ i, max (a i - b i) 0 ≤ 1 - beta := by
  by_cases h : ∃ i0, 0 < a i0 - b i0
  · obtain ⟨i0, hi0⟩ := h
    calc ∑ i, max (a i - b i) 0 ≤ ∑ i, (a i - if i = i0 then b i0 else 0) := by
          refine Finset.sum_le_sum fun i _ => ?_
          by_cases hi : i = i0
          · subst hi; rw [if_pos rfl, max_eq_left hi0.le]
          · rw [if_neg hi, sub_zero]; exact max_le (by linarith [hb i]) (ha i)
      _ = 1 - b i0 := by
          rw [Finset.sum_sub_distrib, hsa, Finset.sum_ite_eq']; simp
      _ ≤ 1 - beta := by linarith [hbb i0]
  · push_neg at h
    have : ∑ i, max (a i - b i) 0 = 0 :=
      Finset.sum_eq_zero fun i _ => max_eq_right (h i)
    rw [this]
    have h0 := hbb 0
    have h1 : b 0 ≤ ∑ i, b i := Finset.single_le_sum (fun i _ => hb i) (Finset.mem_univ _)
    linarith

theorem x8_main {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ)
    (hN : IsUINorm N) (rho sigma : Mat d) (hrho : IsDensityMatrix rho)
    (hsigma : IsDensityMatrix sigma) (beta : ℝ)
    (hfloor : (sigma - (beta : ℂ) • (1 : Mat d)).PosSemidef) :
    rescaled N (rho - sigma) ≤ 1 - beta := by
  have : NeZero d := ⟨by omega⟩
  have hΔ : (rho - sigma).IsHermitian := hrho.1.1.sub hsigma.1.1
  set U := hΔ.eigenvectorUnitary
  set W : Mat d := (U : Mat d)
  set μ := hΔ.eigenvalues
  have hWW : star W * W = 1 := Unitary.coe_star_mul_self _
  have hWW' : W * star W = 1 := Unitary.coe_mul_star_self _
  have hspec : rho - sigma = W * diagonal (fun i => (μ i : ℂ)) * star W := by
    conv_lhs => rw [hΔ.spectral_theorem]
    rfl
  have hNΔ : N (rho - sigma) = N (diagonal (fun i => (μ i : ℂ))) := by
    have := hN.2.2.2.2 U (star U) (diagonal (fun i => (μ i : ℂ)))
    rw [Unitary.coe_star] at this
    rw [hspec, ← this]
  have hdiag : diagonal (fun i => (μ i : ℂ)) = star W * rho * W - star W * sigma * W := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, hspec]
    simp only [← Matrix.mul_assoc, hWW, Matrix.one_mul]
    rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  have hW' : star W = Wᴴ := rfl
  have hρ' : (star W * rho * W).PosSemidef := by
    rw [hW']; exact hrho.1.conjTranspose_mul_mul_same W
  have hσ' : (star W * sigma * W).PosSemidef := by
    rw [hW']; exact hsigma.1.conjTranspose_mul_mul_same W
  have hσβ : (star W * sigma * W - (beta : ℂ) • 1).PosSemidef := by
    have := hfloor.conjTranspose_mul_mul_same W
    rw [← hW', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hWW] at this
    exact this
  have htr : ∀ X : Mat d, (star W * X * W).trace = X.trace := by
    intro X
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWW', Matrix.one_mul]
  set a : Fin d → ℝ := fun i => ((star W * rho * W) i i).re
  set b : Fin d → ℝ := fun i => ((star W * sigma * W) i i).re
  have hμab : ∀ i, μ i = a i - b i := by
    intro i
    have := congrArg (fun M => (M i i).re) hdiag
    simpa [diagonal_apply] using this
  have ha : ∀ i, 0 ≤ a i := fun i => (Complex.nonneg_iff.mp (hρ'.diag_nonneg (i := i))).1
  have hb : ∀ i, 0 ≤ b i := fun i => (Complex.nonneg_iff.mp (hσ'.diag_nonneg (i := i))).1
  have hbb : ∀ i, beta ≤ b i := by
    intro i
    have := (Complex.nonneg_iff.mp (hσβ.diag_nonneg (i := i))).1
    simp [one_apply] at this
    simpa [b] using this
  have hsa : ∑ i, a i = 1 := by
    have := congrArg Complex.re ((htr rho).trans hrho.2)
    simpa [Matrix.trace, a] using this
  have hsb : ∑ i, b i = 1 := by
    have := congrArg Complex.re ((htr sigma).trans hsigma.2)
    simpa [Matrix.trace, b] using this
  have hμ0 : ∑ i, μ i = 0 := by
    simp only [hμab, Finset.sum_sub_distrib, hsa, hsb, sub_self]
  have ht : ∑ i, max (μ i) 0 ≤ 1 - beta := by
    simp only [hμab]; exact x8_t_bound a b beta ha hsa hb hbb hsb
  have hF0 : 0 < N (matrixF d) := by
    rcases (hN.1 (matrixF d)).lt_or_eq with h | h
    · exact h
    · exfalso
      have := (hN.2.1 _).1 h.symm
      have h00 := congrFun (congrFun this ⟨0, by omega⟩) ⟨0, by omega⟩
      simp [matrixF] at h00
  unfold rescaled
  rw [div_le_iff₀ hF0, hNΔ]
  exact (x8_diag_bound hd N hN μ hμ0).trans (mul_le_mul_of_nonneg_right ht hF0.le)

end QAlgorithms.Papers.Independent.Gap48.P40


open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)


open QAlgorithms.Papers.Independent.Gap48.P40 in
/-- PDF p.4, Lemma 5: beta is a lower spectral floor, with no positivity restriction. -/
theorem solution {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ)
    (hN : IsUINorm N) (rho sigma : Mat d) (hrho : IsDensityMatrix rho)
    (hsigma : IsDensityMatrix sigma) (beta : ℝ)
    (hfloor : (sigma - (beta : ℂ) • (1 : Mat d)).PosSemidef) :
    rescaled N (rho - sigma) ≤ 1 - beta :=
  x8_main hd N hN rho sigma hrho hsigma beta hfloor



