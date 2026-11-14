-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.bethe_dirac_zero_general
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:47:42.405195+00:00
-- url     : https://prove2.me/submissions/df2ce2ae-68f3-4d6c-b904-0b83d6c34fbb

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (d : ℕ)
    (hπ : ∀ a, m.pi t a ≠ 0) (hsum : (∑ a, m.pi t a) = 1) :
    betheK m t d (diracPi m t) = 0 := by
  classical
  let p : m.Spin → ℝ := m.pi t
  have hrow (a : m.Spin) : Mmul m t p a = 1 := by
    unfold Mmul Model.M
    have heach (j : m.Spin) :
        m.P t a j / (m.pi t a * m.pi t j) * p j = m.P t a j / m.pi t a := by
      dsimp [p]
      field_simp [hπ a,hπ j]
    simp_rw [heach, ← Finset.sum_div]
    change (m.pi t a) / (m.pi t a) = 1
    exact div_self (hπ a)
  have hE : edgeFactor m t p p = 1 := by
    unfold edgeFactor
    calc
      _ = ∑ a, p a * Mmul m t p a := by
        simp only [Mmul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = 1 := by simp [hrow,p,hsum]
  have hV : vertexFactor m t d (fun _ => p) = 1 := by
    unfold vertexFactor
    simp [hrow,hsum]
  have hae : ∀ᵐ xs ∂(Measure.pi fun _ : Fin d => Measure.dirac p), ∀ i, xs i = p := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi (fun _ : Fin d => ae_eq_dirac (fun x : m.Spin → ℝ => x))
  have hv : (∫ xs : Fin d → m.Spin → ℝ, xlogx (vertexFactor m t d xs)
      ∂(Measure.pi fun _ : Fin d => Measure.dirac p)) = 0 := by
    calc
      _ = ∫ _xs : Fin d → m.Spin → ℝ, (0:ℝ) ∂(Measure.pi fun _ : Fin d => Measure.dirac p) := by
        apply integral_congr_ae
        filter_upwards [hae] with xs hx
        have heq : xs = fun _ => p := funext hx
        rw [heq,hV]
        simp [xlogx]
      _ = 0 := integral_zero _ _
  have he : (∫ q : (m.Spin → ℝ) × (m.Spin → ℝ), xlogx (edgeFactor m t q.1 q.2)
      ∂((Measure.dirac p).prod (Measure.dirac p))) = 0 := by
    rw [Measure.dirac_prod_dirac,integral_dirac]
    simp [hE,xlogx]
  unfold betheK
  change (∫ xs : Fin d → m.Spin → ℝ, xlogx (vertexFactor m t d xs)
      ∂(Measure.pi fun _ : Fin d => Measure.dirac p)) - (d:ℝ)/2 *
    (∫ q : (m.Spin → ℝ) × (m.Spin → ℝ), xlogx (edgeFactor m t q.1 q.2)
      ∂((Measure.dirac p).prod (Measure.dirac p))) = 0
  rw [hv,he]
  ring
