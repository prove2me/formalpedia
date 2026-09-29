-- Prove2me | solution 1 for UndecidableSpectralGap.usg_switch_sector_spectrum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-22T23:13:17.387075+00:00
-- url     : https://prove2.me/submissions/6f69387e-6c4f-45d8-877f-ccff6cf2de23

import Theorems.Thm_UndecidableSpectralGap_usg_switch_entrywise_laplacian
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Matrix

set_option autoImplicit false
open UndecidableSpectralGap

private lemma column_mem_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (k : ι) (ev : ℂ)
    (hcol : ∀ i, A i k = if i = k then ev else 0) : ev ∈ spectrum ℂ A := by
  rw [← Matrix.spectrum_toLin']
  apply Module.End.HasEigenvalue.mem_spectrum
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := Pi.single k 1)
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    change A.mulVec (Pi.single k 1) = ev • Pi.single k 1
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, hcol]
  · intro hz
    have h := congrFun hz k
    simpa using h

private lemma rate_to_constant (L : ℕ) (b : ℝ) (c : Config L 3) (z : Fin 3) :
    switchTransitionRate L b c (fun _ => z) = 0 := by
  have he : ((rowEdges L).filter fun e =>
      c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧
        (fun _ => z) = c ∘ Equiv.swap e.1 e.2) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro e he h
    have hc : ∀ s, c s = z := by
      intro s
      have hh := congrFun h.2.2.2 ((Equiv.swap e.1 e.2) s)
      simpa [Function.comp_def] using hh.symm
    exact h.2.2.1 (by rw [hc, hc])
  simp only [switchTransitionRate, he, Finset.card_empty, Nat.cast_zero, mul_zero]

private lemma constant_column (L : ℕ) (a b : ℝ) (z : Fin 3) :
    ∀ c : Config L 3, switchHam L a b c (fun _ => z) =
      if c = (fun _ => z) then ((switchPotential L a (fun _ => z) : ℝ) : ℂ) else 0 := by
  intro c
  rw [usg_switch_entrywise_laplacian]
  by_cases hc : c = (fun _ => z)
  · subst c
    simp [switchTransitionRate]
  · simp [hc, rate_to_constant]

theorem solution
    (b a : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (ha : |a| ≤ b) :
    ∀ L : ℕ, 2 ≤ L →
      0 ∈ specReal (switchHam L a b) ∧
      a * (L : ℝ) ^ 2 ∈ specReal (switchHam L a b) ∧
      ∀ μ ∈ specReal (switchHam L a b),
        min 0 (a * (L : ℝ) ^ 2) ≤ μ := by
  classical
  intro L hL
  have hbnd (z : Fin 3) : switchBoundaryCount L (fun _ => z) = 0 := by
    have he (s : Finset (Site L × Site L)) :
        s.filter (switchBoundaryAt (fun _ => z)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he
      simp [switchBoundaryAt]
    simp only [switchBoundaryCount, he, Finset.card_empty, zero_add]
  have hvac : switchPotential L a (fun _ => (0 : Fin 3)) = 0 := by
    simp [switchPotential, switchOccupiedCount, hbnd]
  have hfull : switchPotential L a (fun _ => (1 : Fin 3)) = a * (L : ℝ) ^ 2 := by
    simp [switchPotential, switchOccupiedCount, hbnd,
      Site, Fintype.card_prod, pow_two]
  have h0 : (0 : ℂ) ∈ spectrum ℂ (switchHam L a b) := by
    apply column_mem_spectrum _ (fun _ => (0 : Fin 3)) 0
    simpa only [hvac, Complex.ofReal_zero] using constant_column L a b 0
  have hE : ((a * (L : ℝ) ^ 2 : ℝ) : ℂ) ∈ spectrum ℂ (switchHam L a b) := by
    apply column_mem_spectrum _ (fun _ => (1 : Fin 3)) _
    simpa only [hfull] using constant_column L a b 1
  refine ⟨by simpa only [specReal, Set.mem_setOf_eq, Complex.ofReal_zero] using h0, hE, ?_⟩
  intro μ hμ
  have heigen : Module.End.HasEigenvalue (Matrix.toLin' (switchHam L a b)) (μ : ℂ) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rw [Matrix.spectrum_toLin']
    exact hμ
  obtain ⟨c, hc⟩ := eigenvalue_mem_ball heigen
  have hrate : ∀ i j : Config L 3, 0 ≤ switchTransitionRate L b i j := by
    intro i j
    exact mul_nonneg hb.le (Nat.cast_nonneg _)
  have hradius : (∑ j ∈ Finset.univ.erase c, ‖switchHam L a b c j‖) =
      ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hcj : c ≠ j := (Finset.mem_erase.mp hj).1.symm
    rw [usg_switch_entrywise_laplacian, if_neg hcj]
    simp [Complex.norm_real, abs_of_nonneg (hrate c j)]
  rw [Metric.mem_closedBall, dist_eq_norm, hradius,
    usg_switch_entrywise_laplacian, if_pos rfl] at hc
  have habs : |μ - (switchPotential L a c +
      ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j)| ≤
      ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hc
  have hpot : switchPotential L a c ≤ μ := by
    have := (abs_le.mp habs).1
    linarith
  have hcount : (switchOccupiedCount L c : ℝ) ≤ (L : ℝ) ^ 2 := by
    have hn : switchOccupiedCount L c ≤ L * L := by
      calc
        _ ≤ (Finset.univ : Finset (Site L)).card := Finset.card_filter_le _ _
        _ = L * L := by simp [Site]
    exact_mod_cast (show switchOccupiedCount L c ≤ L ^ 2 by simpa [pow_two] using hn)
  have hboundary : (0 : ℝ) ≤ switchBoundaryCount L c := Nat.cast_nonneg _
  have hocc : (0 : ℝ) ≤ switchOccupiedCount L c := Nat.cast_nonneg _
  apply le_trans _ hpot
  unfold switchPotential
  by_cases ha0 : 0 ≤ a
  · have hnonneg : 0 ≤ a * (L : ℝ) ^ 2 := mul_nonneg ha0 (sq_nonneg _)
    rw [min_eq_left hnonneg]
    exact add_nonneg (mul_nonneg ha0 hocc) hboundary
  · have han : a ≤ 0 := le_of_not_ge ha0
    have hnonpos : a * (L : ℝ) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg han (sq_nonneg _)
    rw [min_eq_right hnonpos]
    have := mul_le_mul_of_nonpos_left hcount han
    linarith
