-- Prove2me | solution 1 for P2M_Formalism_HC_Landau_integral_real__9be9cb33e88c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:53.740093+00:00
-- url     : https://prove2.me/submissions/e5bef92e-d792-42ef-b855-d03a009c0b8a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
namespace Formalism.HC.Landau
theorem _root_.solution (H : ℝ → ℝ) (σ : ℝ) :
    ∫ x in Ioi (1:ℝ), ((H x : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1) =
      ((∫ x in Ioi (1:ℝ), H x * x ^ (-σ - 1) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 ≤ x := by linarith [mem_Ioi.mp hx]
  simp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0]
  push_cast
  ring_nf
end Formalism.HC.Landau
