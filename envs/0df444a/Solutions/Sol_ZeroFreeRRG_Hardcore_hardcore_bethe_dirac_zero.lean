-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_bethe_dirac_zero
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:24:32.820505+00:00
-- url     : https://prove2.me/submissions/be0b1675-38fd-47c8-bc66-1602610c2f7b

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_centered_factors
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (α : ℝ) (ha : 0 < α) (ha1 : α < 1/2) :
    betheK .hardcore α d (diracPi .hardcore α) = 0 := by
  let p : Fin 2 → ℝ := Model.pi .hardcore α
  have hp0 : p 0 = 1-α := by simp [p,Model.pi,Model.Spin,Model.P,Fin.sum_univ_two] <;> ring
  have hp1 : p 1 = α := by simp [p,Model.pi,Model.Spin,Model.P,Fin.sum_univ_two] <;> ring
  have hs : (∑ i, p i) = 1 := by rw [Fin.sum_univ_two,hp0,hp1]; ring
  have hh := hardcore_centered_factors α ha ha1 p p hs hs
  have hM0 : Mmul .hardcore α p (0 : Fin 2) = 1 := by
    simpa [hp1] using hh.1
  have hM1 : Mmul .hardcore α p (1 : Fin 2) = 1 := by
    simpa [hp1] using hh.2.1
  have hE : edgeFactor .hardcore α p p = 1 := by
    simpa [hp1] using hh.2.2
  have hV : vertexFactor .hardcore α d (fun _ => p) = 1 := by
    unfold vertexFactor
    change (∑ a : Fin 2, Model.pi .hardcore α a * ∏ _i : Fin d, Mmul .hardcore α p a)=1
    rw [Fin.sum_univ_two]
    change p 0 * (∏ _i : Fin d, Mmul .hardcore α p (0 : Fin 2)) + p 1 * (∏ _i : Fin d, Mmul .hardcore α p (1 : Fin 2)) = 1
    simp [hM0,hM1,hp0,hp1]
  have hae : ∀ᵐ xs ∂(Measure.pi fun _ : Fin d => Measure.dirac p), ∀ i, xs i = p := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi (fun _ : Fin d => ae_eq_dirac (fun x : Fin 2 → ℝ => x))
  have hv : (∫ xs : Fin d → Fin 2 → ℝ, xlogx (vertexFactor .hardcore α d xs)
      ∂(Measure.pi fun _ : Fin d => Measure.dirac p)) = 0 := by
    calc
      _ = ∫ _xs : Fin d → Fin 2 → ℝ, (0:ℝ) ∂(Measure.pi fun _ : Fin d => Measure.dirac p) := by
        apply integral_congr_ae
        filter_upwards [hae] with xs hx
        have heq : xs = fun _ => p := funext hx
        rw [heq,hV]
        simp [xlogx]
      _ = 0 := integral_zero _ _
  have he : (∫ q : (Fin 2 → ℝ) × (Fin 2 → ℝ), xlogx (edgeFactor .hardcore α q.1 q.2)
      ∂((Measure.dirac p).prod (Measure.dirac p))) = 0 := by
    rw [Measure.dirac_prod_dirac,integral_dirac]
    simp [hE,xlogx]
  unfold betheK
  change (∫ xs : Fin d → Fin 2 → ℝ, xlogx (vertexFactor .hardcore α d xs)
      ∂(Measure.pi fun _ : Fin d => Measure.dirac p)) - (d:ℝ)/2 *
    (∫ q : (Fin 2 → ℝ) × (Fin 2 → ℝ), xlogx (edgeFactor .hardcore α q.1 q.2)
      ∂((Measure.dirac p).prod (Measure.dirac p))) = 0
  rw [hv,he]
  ring
