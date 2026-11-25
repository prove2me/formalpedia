-- Prove2me | solution 1 for P2M_Formalism_HC_Landau_natOrder_ne_zero__cbc415af1e91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:55.491822+00:00
-- url     : https://prove2.me/submissions/9303cf5b-1677-4d89-9abb-307de8d3004e

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
theorem _root_.solution {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z y : ℂ} (hy : f y ≠ 0)
    (hz : f z = 0) : analyticOrderNatAt f z ≠ 0 := by
  have han : AnalyticOnNhd ℂ f univ := analyticOnNhd_univ_iff_differentiable.mpr hf
  have h0 : analyticOrderAt f z ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨han z trivial, hz⟩
  have htop : analyticOrderAt f z ≠ ⊤ :=
    han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ y) (mem_univ z)
      (by rw [analyticOrderAt_eq_zero.mpr (Or.inr hy)]; simp)
  simp only [analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
  exact ⟨h0, htop⟩
end Formalism.HC.Landau
