-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFock.evX_temperate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:20:24.704797+00:00
-- url     : https://prove2.me/submissions/000e189a-a2e4-4579-bbe0-cdf5a40403b7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_EvXTemperate
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply


section
noncomputable section
open scoped SchwartzMap
open PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
private theorem hasTemperateGrowth_evX' {m n : ℕ} (k : Fin m × Fin n × Bool) :
    Function.HasTemperateGrowth
      (fun x : Fin m → Fin n → ℂ => if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1) := by
  obtain ⟨a, i, b⟩ := k
  have hc : Function.HasTemperateGrowth (fun x : Fin m → Fin n → ℂ => x a i) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)).hasTemperateGrowth
  cases b with
  | false => simpa using hc
  | true =>
    have hs := (Complex.conjCLE.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a))).hasTemperateGrowth
    convert hs using 1
    funext x
    simp
end PositivityTheory.SiegelWeilFormula.KFock
end
end

set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
open PositivityTheory.Rg.Sw
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFock
namespace PositivityTheory.SiegelWeilFormula.KFock
theorem _root_.solution {m n : ℕ} (P : PX m n) :
    Function.HasTemperateGrowth (fun x : Fin m → Fin n → ℂ => evX P x) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    convert Function.HasTemperateGrowth.const (E := Fin m → Fin n → ℂ) a using 1
    funext x
    simp [evX]
  | add p q hp hq =>
    convert hp.add hq using 1
    funext x
    simp [evX]
  | mul_X p k hp =>
    have e : (fun x : Fin m → Fin n → ℂ => evX (p * MvPolynomial.X k) x) =
        fun x => evX p x * (if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1) := by
      funext x
      simp [evX]
    rw [e]
    exact hp.fun_mul (hasTemperateGrowth_evX' k)
end PositivityTheory.SiegelWeilFormula.KFock
