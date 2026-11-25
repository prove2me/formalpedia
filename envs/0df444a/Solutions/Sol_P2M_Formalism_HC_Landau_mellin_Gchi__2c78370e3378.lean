-- Prove2me | solution 1 for P2M_Formalism_HC_Landau_mellin_Gchi__2c78370e3378
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:54.687452+00:00
-- url     : https://prove2.me/submissions/6d8ec432-1a0a-46e6-9313-4b4e2494e9ff

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_Schi_eq_Sa
import Theorems.Thm_Formalism_cint_of_abs
import Theorems.Thm_Formalism_int_abs_rpow
import Theorems.Thm_Formalism_mellinElem
import Theorems.Thm_Formalism_mellinSgen
import Theorems.Thm_Formalism_twist_bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
open DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace Formalism.HC.Landau
theorem _root_.solution (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (Gchi χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1:ℝ), (Gchi χ x : ℂ) * (x : ℂ) ^ (-s - 1) =
      LSeries (fun n => ((Λ n * (χ n).re : ℝ) : ℂ)) s / (s * (s - 1))
        + (((deriv (LFunction χ) 1 / LFunction χ 1).re : ℝ) : ℂ) * (1 / (s - 1)) := by
  have h5 := mellinElem
  have hS := mellinSgen _ 1 (twist_bound χ)
  have i1 : IntegrableOn (fun x : ℝ => (Sa (fun n => Λ n * (χ n).re) x : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi 1) := cint_of_abs _ hS.1 s (hS.2.1 _ hs)
  have i3 : IntegrableOn (fun x : ℝ => ((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  set c : ℝ := (deriv (LFunction χ) 1 / LFunction χ 1).re
  have hfun : (fun x : ℝ => (Gchi χ x : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x =>
      (Sa (fun n => Λ n * (χ n).re) x : ℂ) * (x : ℂ) ^ (-s - 1)
        + (c : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [Gchi, Schi_eq_Sa, Real.rpow_one, c]
    push_cast
    ring
  have j3 := Integrable.const_mul i3 (c : ℂ)
  refine ⟨by rw [hfun]; exact i1.add j3, ?_⟩
  rw [hfun, integral_add i1 j3, integral_const_mul, hS.2.2 s hs, h5.2.2.1 1 s (by simpa using hs)]
  push_cast
  ring
end Formalism.HC.Landau
