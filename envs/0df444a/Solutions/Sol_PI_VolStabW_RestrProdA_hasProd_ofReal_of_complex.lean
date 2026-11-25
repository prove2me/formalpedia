-- Prove2me | solution 1 for PI.VolStabW.RestrProdA.hasProd_ofReal_of_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:20.190653+00:00
-- url     : https://prove2.me/submissions/047baf9b-66f1-4eb8-a054-99b581c226f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RestrProdA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW.RestrProdA
theorem _root_.solution {β : Type} {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) {q : ℂ}
    (h : HasProd (fun b => (f b : ℂ)) q) :
    HasProd (fun b => ENNReal.ofReal (f b)) (ENNReal.ofReal q.re) := by
  unfold HasProd at h ⊢
  have h1 := ((ENNReal.continuous_ofReal.comp Complex.continuous_re).tendsto q).comp h
  refine h1.congr fun s => ?_
  simp only [Function.comp_apply, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact ENNReal.ofReal_prod_of_nonneg fun b _ => hf b
end PI.VolStabW.RestrProdA
