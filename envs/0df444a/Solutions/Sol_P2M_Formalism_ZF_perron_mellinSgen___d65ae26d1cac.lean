-- Prove2me | solution 1 for P2M_Formalism_ZF_perron_mellinSgen___d65ae26d1cac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:17:22.307394+00:00
-- url     : https://prove2.me/submissions/2f713a6d-6865-4810-9d6e-332af66323d9

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Theorems.Thm_Formalism_mellinSgen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution :
    Measurable (Formalism.Sa (fun n => (Λ n : ℝ))) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |Formalism.Sa (fun n => (Λ n : ℝ)) x| * x ^ (-σ - 1))
      (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (Formalism.Sa (fun n => (Λ n : ℝ)) x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => ((Λ n : ℝ) : ℂ)) s / (s * (s - 1)) := Formalism.mellinSgen (fun n => (Λ n : ℝ)) 1 (fun n => by
    rw [one_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg])
end Formalism.ZF
