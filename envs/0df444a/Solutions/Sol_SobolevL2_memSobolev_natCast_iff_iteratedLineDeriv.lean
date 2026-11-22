-- Prove2me | solution 1 for SobolevL2.memSobolev_natCast_iff_iteratedLineDeriv
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:39:59.747942+00:00
-- url     : https://prove2.me/submissions/4caa4e72-8536-405b-ad92-c08cb423b04d

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv Laplacian

set_option autoImplicit false
set_option maxHeartbeats 1000000

section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem besselPotential_two (u : 𝓢'(E, F)) :
    besselPotential E F 2 u = u + (-(2 * (Real.pi : ℂ)) ^ 2)⁻¹ • Δ u := by
  let g : E → ℂ := fun x => ((‖x‖ : ℝ) : ℂ) ^ 2
  let c : ℂ := -(2 * (Real.pi : ℂ)) ^ 2
  have hg : g.HasTemperateGrowth := by
    simpa only [g, Complex.ofReal_pow] using
      (show (fun x : E => ((‖x‖ ^ 2 : ℝ) : ℂ)).HasTemperateGrowth from by fun_prop)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)))
  rw [laplacian_eq_fourierMultiplierCLM, ← Complex.coe_smul]
  push_cast
  change besselPotential E F 2 u = u + c⁻¹ • (c • fourierMultiplierCLM F g u)
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hSymbol : (fun x : E => (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ)) + g := by
    funext x
    simp [g]
  rw [besselPotential, hSymbol]
  have hOne : (fun _ : E => (1 : ℂ)).HasTemperateGrowth := by fun_prop
  simp [fourierMultiplierCLM_apply, smulLeftCLM_add hOne hg, smulLeftCLM_const]

private theorem memSobolev_succ_of_first {s : ℝ} {u : 𝓢'(E, F)}
    (hu : MemSobolev s 2 u) (hD : ∀ e : E, MemSobolev s 2 (∂_{e} u)) :
    MemSobolev (s + 1) 2 u := by
  let b := stdOrthonormalBasis ℝ E
  have hSum (S : Finset (Fin (Module.finrank ℝ E))) : MemSobolev (s - 1) 2
      (∑ i ∈ S, ∂_{b i} (∂_{b i} u)) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (hD (b i)).lineDerivOp.add ih
  have hLap : MemSobolev (s - 1) 2 (Δ u) := by
    rw [laplacian_eq_sum b]
    exact hSum Finset.univ
  have h := (hu.mono (sub_le_self s zero_le_one)).add
    (hLap.smul ((-(2 * (Real.pi : ℂ)) ^ 2)⁻¹))
  rw [← besselPotential_two, memSobolev_besselPotential_iff] at h
  convert h using 1
  ring

private theorem memSobolev_iteratedLineDeriv {s : ℝ} {u : 𝓢'(E, F)}
    (hu : MemSobolev s 2 u) (j : ℕ) (m : Fin j → E) :
    MemSobolev (s - j) 2 (∂^{m} u) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    convert (ih (Fin.tail m)).lineDerivOp (m := m 0) using 1
    push_cast
    ring

theorem solution (k : ℕ) (u : 𝓢'(E, F)) :
    MemSobolev (k : ℝ) 2 u ↔ ∀ j ≤ k, ∀ m : Fin j → E, MemSobolev 0 2 (∂^{m} u) := by
  constructor
  · intro h j hj m
    exact (memSobolev_iteratedLineDeriv h j m).mono (sub_nonneg.mpr (by exact_mod_cast hj))
  · induction k generalizing u with
    | zero =>
      intro h
      simpa using h 0 le_rfl Fin.elim0
    | succ k ih =>
      intro h
      have h0 := ih u (fun j hj m => h j (hj.trans (Nat.le_succ k)) m)
      have h1 (e : E) : MemSobolev (k : ℝ) 2 (∂_{e} u) := by
        apply ih
        intro j hj m
        simpa only [LineDeriv.iteratedLineDerivOp_succ_right, Fin.init_snoc, Fin.snoc_last] using
          h (j + 1) (Nat.succ_le_succ hj) (Fin.snoc m e)
      simpa only [Nat.cast_succ] using memSobolev_succ_of_first h0 h1

end
