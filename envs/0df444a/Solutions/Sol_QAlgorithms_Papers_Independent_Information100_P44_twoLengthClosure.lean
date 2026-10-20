-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.twoLengthClosure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:33:03.070993+00:00
-- url     : https://prove2.me/submissions/f5a2848d-88e7-42b7-9d54-0a33b2be7a5e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

theorem g52c_trace_kraus {K : Type*} [Fintype K] {d : ℕ} (E : K → Mat d)
    (hK : IsKrausFamily E) (X : Mat d) : (krausApply E X).trace = X.trace := by
  simp only [krausApply, Matrix.trace_sum]
  have : ∀ j, (E j * X * (E j)ᴴ).trace = ((E j)ᴴ * E j * X).trace := fun j => by
    rw [Matrix.trace_mul_cycle]
  simp only [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  rw [show ∑ j, (E j)ᴴ * E j = 1 from hK, Matrix.one_mul]

theorem g52c_trace_channel {d : ℕ} (Phi : Map d) (hPhi : IsChannel Phi) (X : Mat d) :
    (Phi X).trace = X.trace := by
  obtain ⟨m, E, hK, hE⟩ := hPhi
  rw [hE]; exact g52c_trace_kraus E hK X

theorem g52c_diag_sum_zero {d : ℕ} (Phi : Map d) (hTP : ∀ X, (Phi X).trace = X.trace)
    (i j : Fin d) (hij : i ≠ j) : ∑ r, Phi (matrixUnit i j) r r = 0 := by
  have := hTP (matrixUnit i j)
  simp only [Matrix.trace, Matrix.diag] at this
  rw [this]
  apply Finset.sum_eq_zero
  intro r _
  simp only [matrixUnit, Matrix.single_apply]
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  exact hij rfl

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution {d : ℕ} (hd : 0 < d) (Phi : Map d) (hPhi : IsChannel Phi)
    (i j : Fin d) (hij : i ≠ j) (r1 r2 : Fin d) (hr : r1 ≠ r2)
    (h1 : 0 < population Phi r1 i * population Phi r1 j)
    (h2 : 0 < population Phi r2 i * population Phi r2 j)
    (hzero : ∀ r, r ≠ r1 → r ≠ r2 → population Phi r i * population Phi r j = 0)
    (hsat : ∀ r, ‖Phi (matrixUnit i j) r r‖ =
      Real.sqrt (population Phi r i * population Phi r j)) :
    Real.sqrt (population Phi r1 i * population Phi r1 j) =
      Real.sqrt (population Phi r2 i * population Phi r2 j) ∧
    population Phi r1 i * population Phi r1 j = population Phi r2 i * population Phi r2 j := by
  have hsum := g52c_diag_sum_zero Phi (g52c_trace_channel Phi hPhi) i j hij
  have hz : ∀ r, r ≠ r1 → r ≠ r2 → Phi (matrixUnit i j) r r = 0 := by
    intro r h1' h2'
    have := hsat r
    rw [hzero r h1' h2', Real.sqrt_zero] at this
    exact norm_eq_zero.mp this
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r1),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hr, Finset.mem_univ r2⟩),
    Finset.sum_eq_zero (fun r hr' => by
      obtain ⟨hr2, hr1⟩ := Finset.mem_erase.mp hr'
      exact hz r (Finset.mem_erase.mp hr1).1 hr2)] at hsum
  have heq : Phi (matrixUnit i j) r1 r1 = -Phi (matrixUnit i j) r2 r2 := by
    linear_combination hsum
  have hs : Real.sqrt (population Phi r1 i * population Phi r1 j) =
      Real.sqrt (population Phi r2 i * population Phi r2 j) := by
    rw [← hsat, ← hsat, heq, norm_neg]
  refine ⟨hs, ?_⟩
  have := congrArg (fun x => x ^ 2) hs
  simp only [Real.sq_sqrt h1.le, Real.sq_sqrt h2.le] at this
  exact this
