-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_basis_eq_elim_c623a59c968c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:11.167901+00:00
-- url     : https://prove2.me/submissions/70868261-1e07-4644-918c-0ed8453fc61b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotGramLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.KLinesQuotGramLog
namespace GroundTheory.Heights₂.Heights.KLinesQuotGramLog
theorem _root_.solution {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (b : Fin m → Fin n → K) (τ : Fin k → Fin n)
    (hBl : ∀ i, B (Sum.inl i) = b i) (hBr : ∀ j, B (Sum.inr j) = Pi.single (τ j) 1) :
    (⇑B : Fin m ⊕ Fin k → Fin n → K) = Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K) := by
  funext x
  cases x with
  | inl i => exact hBl i
  | inr j => exact hBr j
end GroundTheory.Heights₂.Heights.KLinesQuotGramLog
