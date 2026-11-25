-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Gm_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:21.576924+00:00
-- url     : https://prove2.me/submissions/0a83232d-8830-4bb7-acda-ba828806a8e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModHnf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModVanish
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_fac_eq_zero_of_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
private lemma exists_SL2_mul_eq_Tmat_of_det_eq {m : ℕ} (hm : 0 < m) (A B C D : ℤ) (hdet : A * D - B * C = m) :
    ∃ g : SL(2, ℤ), ∃ s ∈ Tm m, 0 < s.2.2 ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) * !![A, B; C, D] = Tmat s := by
  have hAC : A ≠ 0 ∨ C ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : (m : ℤ) = 0 := by rw [← hdet, hc.1, hc.2]; ring
    omega
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = Int.gcd A C := ⟨_, rfl⟩
  have hGpos : 0 < G := by
    rw [hG]
    first
    | exact Int.gcd_pos_iff.mpr hAC
    | (rcases hAC with h | h
       · exact Int.gcd_pos_of_ne_zero_left C h
       · exact Int.gcd_pos_of_ne_zero_right A h)
  obtain ⟨a0, ha0⟩ : (G : ℤ) ∣ A := by
    rw [hG]
    first | exact Int.gcd_dvd_left | exact Int.gcd_dvd_left A C | exact Int.gcd_dvd_left _ _
  obtain ⟨c0, hc0⟩ : (G : ℤ) ∣ C := by
    rw [hG]
    first | exact Int.gcd_dvd_right | exact Int.gcd_dvd_right A C | exact Int.gcd_dvd_right _ _
  obtain ⟨x, y, hbez⟩ : ∃ x y : ℤ, (G : ℤ) = A * x + C * y :=
    ⟨_, _, by rw [hG]; exact Int.gcd_eq_gcd_ab A C⟩
  have hG0 : (G : ℤ) ≠ 0 := by exact_mod_cast hGpos.ne'
  have h1 : a0 * x + c0 * y = 1 := by
    apply mul_left_cancel₀ hG0
    linear_combination -hbez - x * ha0 - y * hc0
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = a0 * D - c0 * B := ⟨_, rfl⟩
  have hGd : (G : ℤ) * d = m := by
    rw [hd]
    linear_combination hdet - D * ha0 + B * hc0
  have hdpos : 0 < d := by
    have h2 : 0 < (G : ℤ) * d := by rw [hGd]; exact_mod_cast hm
    have h3 : (0 : ℤ) < G := by exact_mod_cast hGpos
    by_contra h4
    push_neg at h4
    nlinarith
  obtain ⟨q, b, hdiv, hb0, hbd⟩ : ∃ q b : ℤ, d * q + b = x * B + y * D ∧ 0 ≤ b ∧ b < d :=
    ⟨(x * B + y * D) / d, (x * B + y * D) % d,
      (by first
          | (have h5 := Int.emod_add_ediv (x * B + y * D) d; linarith)
          | (have h5 := Int.ediv_add_emod' (x * B + y * D) d; linarith)
          | (have h5 := Int.mul_ediv_add_emod (x * B + y * D) d; linarith)), Int.emod_nonneg _ hdpos.ne',
      Int.emod_lt_of_pos _ hdpos⟩
  have hdet1 : (x + q * c0) * a0 - (y - q * a0) * -c0 = 1 := by linear_combination h1
  have e1 : (x + q * c0) * A + (y - q * a0) * C = (G : ℤ) := by
    linear_combination -hbez + q * c0 * ha0 - q * a0 * hc0
  have e2 : (x + q * c0) * B + (y - q * a0) * D = b := by
    linear_combination -hdiv + q * hd
  have e3 : -c0 * A + a0 * C = 0 := by
    linear_combination -c0 * ha0 + a0 * hc0
  have e4 : -c0 * B + a0 * D = d := by
    linear_combination -hd
  lift d to ℕ using hdpos.le
  lift b to ℕ using hb0
  have hGdn : G * d = m := by exact_mod_cast hGd
  have hmd : m / G = d := by rw [← hGdn, Nat.mul_div_cancel_left _ hGpos]
  refine ⟨⟨!![x + q * c0, y - q * a0; -c0, a0], by rw [Matrix.det_fin_two_of]; exact hdet1⟩, (G, b, d), ?_, by show 0 < d; exact_mod_cast hdpos, ?_⟩
  · simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
    refine ⟨⟨G, b⟩, ⟨⟨⟨d, hGdn.symm⟩, hm.ne'⟩, ?_⟩, ?_⟩
    · rw [hmd]; exact_mod_cast hbd
    · simp [hmd]
  · show !![x + q * c0, y - q * a0; -c0, a0] * !![A, B; C, D] = Tmat (G, b, d)
    rw [Matrix.mul_fin_two, e1, e2, e3, e4]
    all_goals first | rfl | (unfold Tmat; rfl) | simp [Tmat]
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {m : ℕ} (hm : 0 < m) (τ : ℍ) (A B C D : ℤ) (hdet : A * D - B * C = m)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : Gm m τ = 0 := by
  obtain ⟨g, s, hs, he, hgs⟩ := exists_SL2_mul_eq_Tmat_of_det_eq hm A B C D hdet
  obtain ⟨p, q, r, w, hg⟩ : ∃ p q r w : ℤ, (g : Matrix (Fin 2) (Fin 2) ℤ) = !![p, q; r, w] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdg : p * w - q * r = 1 := by
    have h0 := Matrix.SpecialLinearGroup.det_coe g
    rw [hg, Matrix.det_fin_two_of] at h0
    exact h0
  have hp : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = p := by rw [hg]; rfl
  have hq : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q := by rw [hg]; rfl
  have hr : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r := by rw [hg]; rfl
  have hw : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = w := by rw [hg]; rfl
  rw [hg] at hgs
  unfold Tmat at hgs
  rw [Matrix.mul_fin_two] at hgs
  have e00 : p * A + q * C = ((s.1 : ℕ) : ℤ) := congrFun (congrFun hgs 0) 0
  have e01 : p * B + q * D = ((s.2.1 : ℕ) : ℤ) := congrFun (congrFun hgs 0) 1
  have e10 : r * A + w * C = 0 := congrFun (congrFun hgs 1) 0
  have e11 : r * B + w * D = ((s.2.2 : ℕ) : ℤ) := congrFun (congrFun hgs 1) 1
  have ea : (s.1 : ℂ) = p * A + q * C := by exact_mod_cast e00.symm
  have eb : (s.2.1 : ℂ) = p * B + q * D := by exact_mod_cast e01.symm
  have ez : (r : ℂ) * A + w * C = 0 := by exact_mod_cast e10
  have ee : (s.2.2 : ℂ) = r * B + w * D := by exact_mod_cast e11.symm
  have hE : (s.2.2 : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hden : (r : ℂ) * τ + w ≠ 0 := by
    intro h0
    have him : (r : ℝ) * τ.im = 0 := by
      have h3 := congrArg Complex.im h0
      simpa using h3
    have hτ := τ.im_pos
    have hr0 : r = 0 := by
      rcases mul_eq_zero.mp him with h4 | h4
      · exact_mod_cast h4
      · linarith
    rw [hr0] at h0
    have hw0 : w = 0 := by
      have h3 := congrArg Complex.re h0
      simp at h3
      exact_mod_cast h3
    rw [hr0, hw0] at hdg
    simp at hdg
  have c1 : ∀ z : ℤ, (((algebraMap ℤ ℝ) z : ℝ) : ℂ) = (z : ℂ) := by
    intro z
    rw [eq_intCast]
    push_cast
    rfl
  have hform : ((g • τ : ℍ) : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
      UpperHalfPlane.σ, hp, hq, hr, hw]
    try rw [c1 p, c1 q, c1 r, c1 w]
  have hX : ((s.1 : ℂ) * τ + (s.2.1 : ℂ)) / (s.2.2 : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    rw [div_eq_div_iff hE hden]
    linear_combination ((τ : ℂ) * (r * τ + w)) * ea + ((r : ℂ) * τ + w) * eb
      + ((p : ℂ) * (r * τ + w) - (p * τ + q) * r) * hfix + ((p : ℂ) * τ + q) * τ * ez
      - ((p : ℂ) * τ + q) * ee
  have hpt : pt s.1 s.2.1 s.2.2 τ = g • τ := by
    unfold pt
    rw [hX, ← hform]
    first
    | exact UpperHalfPlane.ofComplex_apply (g • τ)
    | simp
  unfold Gm
  apply Finset.prod_eq_zero hs
  apply fac_eq_zero_of_smul s τ g⁻¹
  rw [hpt, inv_smul_smul]
end ReciprocityTheory.ChartRestriction.L1
