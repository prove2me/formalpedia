-- Prove2me | solution 1 for PI.GreenHCLabel.supportExists_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:16:31.070259+00:00
-- url     : https://prove2.me/submissions/2b06e26e-52a4-415d-80d2-c29cc1a2d28b

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_GreenHCLabelOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_SupportExistsOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
open scoped TensorProduct
open PI PI.GreenHCLabel
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable {K}
namespace PI.GreenHCLabel
theorem _root_.solution (h1 : Jacquet K) (h2 : Frob K) (h3 : HCFin K) (h4 : ConstSymm) : SupportExists K := by
  intro n τ hτ
  obtain ⟨s, b, lam, Φ, hb, hlam, hΦ, hpar⟩ := h1 n τ hτ
  obtain ⟨ψ, hψ, hψ0⟩ := h2 (Fin n) s b lam τ Φ hΦ hpar
  refine ⟨s, b, lam, hb, hlam, ?_⟩
  haveI := h3 (Fin n) s b lam
  exact (h4 (GL (Fin n) K) τ (hcSpace K b lam) (hcRep K b lam) hτ).mpr ⟨ψ, hψ, hψ0⟩
end PI.GreenHCLabel
