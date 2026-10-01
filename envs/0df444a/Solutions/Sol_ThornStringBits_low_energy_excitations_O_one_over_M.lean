-- Prove2me | solution 1 for ThornStringBits.low_energy_excitations_O_one_over_M
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T07:59:34.016139+00:00
-- url     : https://prove2.me/submissions/eb15b4db-1fe9-426a-bcec-7f50f3091c8a

import Definitions.Def_ThornStringBits_Defs
import Mathlib

set_option autoImplicit false

open Real Matrix

namespace ThornStringBits

open ZMod in
lemma p2m_sum_shift {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (a k : ZMod N) :
    ∑ j : ZMod N, stdAddChar (-(j * k)) * Φ (j + a)
      = stdAddChar (a * k) * ∑ j : ZMod N, stdAddChar (-(j * k)) * Φ j := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ (fun j => ?_)
  simp only [Equiv.coe_addRight]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

open ZMod in
lemma p2m_key {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (hΦ : Φ ≠ 0) (lam : ℂ)
    (h : ∀ j, 2 * Φ j - Φ (j + 1) - Φ (j + -1) = lam * Φ j) :
    ∃ k : ZMod N, lam = 2 - stdAddChar k - stdAddChar (-k) := by
  have hF : 𝓕 Φ ≠ 0 := by
    intro h0
    apply hΦ
    exact (dft (N := N) (E := ℂ)).injective (h0.trans (map_zero _).symm)
  obtain ⟨k, hk⟩ : ∃ k, 𝓕 Φ k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hF (funext hc)
  refine ⟨k, ?_⟩
  set S := ∑ j : ZMod N, stdAddChar (-(j * k)) * Φ j with hSdef
  have hS : 𝓕 Φ k = S := by
    rw [dft_apply]
    simp only [smul_eq_mul, S]
  have hs : ∑ j : ZMod N, stdAddChar (-(j * k)) * (2 * Φ j - Φ (j + 1) - Φ (j + -1))
      = ∑ j : ZMod N, stdAddChar (-(j * k)) * (lam * Φ j) := by
    simp only [h]
  have hL : ∑ j : ZMod N, stdAddChar (-(j * k)) * (2 * Φ j - Φ (j + 1) - Φ (j + -1))
      = 2 * S - stdAddChar (1 * k) * S - stdAddChar (-1 * k) * S := by
    rw [hSdef, ← p2m_sum_shift Φ 1 k, ← p2m_sum_shift Φ (-1) k, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hR : ∑ j : ZMod N, stdAddChar (-(j * k)) * (lam * Φ j) = lam * S := by
    rw [hSdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hL, hR, one_mul, neg_one_mul] at hs
  have hS0 : S ≠ 0 := hS ▸ hk
  have : (2 - stdAddChar k - stdAddChar (-k)) * S = lam * S := by
    rw [← hs]; ring
  exact (mul_right_cancel₀ hS0 this).symm

open ZMod in
lemma p2m_cos (n : ℕ) (k : ZMod (n + 2)) :
    (stdAddChar k : ℂ) + stdAddChar (-k)
      = ((2 * Real.cos (2 * π * (k.val : ℝ) / ((n : ℝ) + 2)) : ℝ) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, stdAddChar_apply, toCircle_apply]
  have e : (2 * ↑π * Complex.I * ↑(k.val) / ↑(n + 2) : ℂ)
      = ((2 * π * (k.val : ℝ) / ((n : ℝ) + 2) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos]
  ring_nf

lemma p2m_mulVec (n : ℕ) (x : Fin (n + 2) → ℝ) (i : Fin (n + 2)) :
    (cycLaplacian (n + 2) *ᵥ x) i = 2 * x i - x (i + 1) - x (i - 1) := by
  have h1 : ∀ j : Fin (n + 2), (j.val = (i.val + 1) % (n + 2)) ↔ j = i + 1 := by
    intro j
    rw [Fin.ext_iff, Fin.val_add, Fin.val_one]
  have h2 : ∀ j : Fin (n + 2), (i.val = (j.val + 1) % (n + 2)) ↔ j = i - 1 := by
    intro j
    rw [eq_sub_iff_add_eq, Fin.ext_iff, Fin.val_add, Fin.val_one, eq_comm]
  simp only [mulVec, dotProduct, cycLaplacian, h1, h2, sub_mul, ite_mul, zero_mul, one_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- lower bound on positive eigenvalues -/
lemma p2m_lower (n : ℕ) (lam : ℝ) (hl : 0 < lam)
    (h : Module.End.HasEigenvalue (Matrix.toLin' (cycLaplacian (n + 2))) lam) :
    2 - 2 * Real.cos (2 * π / ((n : ℝ) + 2)) ≤ lam := by
  obtain ⟨v, hv, hv0⟩ := h.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv
  have hreal : ∀ i : Fin (n + 2), 2 * v i - v (i + 1) - v (i - 1) = lam * v i := by
    intro i
    have := congrFun hv i
    rw [p2m_mulVec] at this
    simpa using this
  let Φ : ZMod (n + 2) → ℂ := fun j => ((v j : ℝ) : ℂ)
  have hΦ : Φ ≠ 0 := by
    intro h0
    apply hv0
    funext j
    have h' : Φ j = 0 := congrFun h0 j
    simp only [Φ, Complex.ofReal_eq_zero] at h'
    exact h'
  obtain ⟨k, hk⟩ := p2m_key Φ hΦ (lam : ℂ) (by
    intro j
    have := hreal j
    simp only [Φ]
    rw [← sub_eq_add_neg]
    exact_mod_cast this)
  have hc := p2m_cos n k
  set θ := 2 * π * (k.val : ℝ) / ((n : ℝ) + 2) with hθ
  have hlam : lam = 2 - 2 * Real.cos θ := by
    have : (lam : ℂ) = ((2 - 2 * Real.cos θ : ℝ) : ℂ) := by
      rw [hk]; push_cast at hc ⊢
      linear_combination -hc
    exact_mod_cast this
  have hN : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hkN : k.val < n + 2 := ZMod.val_lt k
  have hk0 : k.val ≠ 0 := by
    intro h0
    rw [hθ, h0] at hlam
    (simp at hlam) <;> linarith
  rw [hlam]
  suffices Real.cos θ ≤ Real.cos (2 * π / ((n : ℝ) + 2)) by linarith
  rcases Nat.lt_or_ge (n + 2) (2 * k.val) with hbig | hsmall
  · -- use the reflection m ↦ N - m
    have hθ' : Real.cos θ = Real.cos (2 * π * ((n + 2 - k.val : ℕ) : ℝ) / ((n : ℝ) + 2)) := by
      rw [hθ, Nat.cast_sub hkN.le]
      have : 2 * π * (((n + 2 : ℕ) : ℝ) - (k.val : ℝ)) / ((n : ℝ) + 2)
          = 2 * π - 2 * π * (k.val : ℝ) / ((n : ℝ) + 2) := by
        push_cast; field_simp
      rw [this, Real.cos_two_pi_sub]
    rw [hθ']
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · rw [div_le_iff₀ hN]
      have : (((n + 2 - k.val : ℕ)) : ℝ) * 2 ≤ (n : ℝ) + 2 := by
        have : (n + 2 - k.val) * 2 ≤ n + 2 := by omega
        exact_mod_cast this
      nlinarith [Real.pi_pos]
    · apply div_le_div_of_nonneg_right _ hN.le
      have : (1 : ℝ) ≤ ((n + 2 - k.val : ℕ) : ℝ) := by
        have : 1 ≤ n + 2 - k.val := by omega
        exact_mod_cast this
      nlinarith [Real.pi_pos]
  · rw [hθ]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · rw [div_le_iff₀ hN]
      have : (k.val : ℝ) * 2 ≤ (n : ℝ) + 2 := by
        have : k.val * 2 ≤ n + 2 := by omega
        exact_mod_cast this
      nlinarith [Real.pi_pos]
    · apply div_le_div_of_nonneg_right _ hN.le
      have : (1 : ℝ) ≤ (k.val : ℝ) := by
        have : 1 ≤ k.val := by omega
        exact_mod_cast this
      nlinarith [Real.pi_pos]

open ZMod in
/-- the eigenvalue is attained -/
lemma p2m_attained (n : ℕ) :
    Module.End.HasEigenvalue (Matrix.toLin' (cycLaplacian (n + 2)))
      (2 - 2 * Real.cos (2 * π / ((n : ℝ) + 2))) := by
  let v : Fin (n + 2) → ℝ := fun j => (stdAddChar (N := n + 2) j).re
  have hc := p2m_cos n 1
  have hv1 : (1 : ZMod (n + 2)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hv1] at hc
  push_cast at hc
  rw [mul_one] at hc
  let g : ZMod (n + 2) → ℝ := fun z => (stdAddChar (N := n + 2) z).re
  have key : ∀ z : ZMod (n + 2), g (z + 1) + g (z + -1)
      = g z * (2 * Real.cos (2 * π / ((n : ℝ) + 2))) := by
    intro z
    simp only [g]
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← Complex.add_re, ← mul_add, hc]
    have : (2 * Complex.cos (2 * ↑π / (↑n + 2)) : ℂ)
        = ((2 * Real.cos (2 * π / ((n : ℝ) + 2)) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.re_mul_ofReal]
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    funext i
    rw [p2m_mulVec]
    have hsum : v (i + 1) + v (i - 1)
        = v i * (2 * Real.cos (2 * π / ((n : ℝ) + 2))) := by
      rw [sub_eq_add_neg]
      exact key i
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith
  · intro h0
    have h1 : g 0 = 1 := by simp [g, AddChar.map_zero_eq_one]
    have h2 : v 0 = 0 := congrFun h0 0
    exact one_ne_zero (h1.symm.trans h2)

lemma p2m_part1 (M : ℕ) (hM : 2 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    IsLeast (positiveModeFreqs M ε) (2 / ε * Real.sin (π / M)) := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 2 := ⟨M - 2, by omega⟩
  have hN : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [hcast]
  have hx0 : 0 < π / ((n : ℝ) + 2) := by positivity
  have hxpi : π / ((n : ℝ) + 2) < π := by
    rw [div_lt_iff₀ hN]; nlinarith [Real.pi_pos, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs : 0 < Real.sin (π / ((n : ℝ) + 2)) := Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  -- 4 sin² = 2 - 2 cos(2x)
  have hid : 2 - 2 * Real.cos (2 * π / ((n : ℝ) + 2))
      = (2 * Real.sin (π / ((n : ℝ) + 2))) ^ 2 := by
    have h2 : 2 * π / ((n : ℝ) + 2) = 2 * (π / ((n : ℝ) + 2)) := by ring
    rw [h2, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (π / ((n : ℝ) + 2))]
  constructor
  · refine ⟨by positivity, ?_⟩
    have : ε ^ 2 * (2 / ε * Real.sin (π / ((n : ℝ) + 2))) ^ 2
        = 2 - 2 * Real.cos (2 * π / ((n : ℝ) + 2)) := by
      rw [hid]; field_simp
    rw [this]
    exact p2m_attained n
  · intro ω hω
    obtain ⟨hω0, hωe⟩ := hω
    have hpos : 0 < ε ^ 2 * ω ^ 2 := by positivity
    have hlow := p2m_lower n _ hpos hωe
    rw [hid] at hlow
    have hkey : 2 * Real.sin (π / ((n : ℝ) + 2)) ≤ ε * ω := by
      nlinarith [mul_pos hε hω0]
    rw [div_mul_eq_mul_div, div_le_iff₀ hε]
    linarith

end ThornStringBits

open Real Matrix ThornStringBits in
theorem solution (M : ℕ) (hM : 2 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    IsLeast (positiveModeFreqs M ε) (2 / ε * Real.sin (π / M)) ∧
    IsLeast (positiveModeFreqs 2 ε) (2 / ε) ∧
    2 / ε * Real.sin (π / M) ≤ π / M * (2 / ε) := by
  refine ⟨p2m_part1 M hM ε hε, ?_, ?_⟩
  · have := p2m_part1 2 le_rfl ε hε
    simpa [Real.sin_pi_div_two] using this
  · rw [mul_comm (π / M)]
    exact mul_le_mul_of_nonneg_left (Real.sin_le (by positivity)) (by positivity)

