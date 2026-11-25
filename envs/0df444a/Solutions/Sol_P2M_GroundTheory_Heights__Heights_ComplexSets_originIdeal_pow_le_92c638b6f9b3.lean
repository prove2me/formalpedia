-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_92c638b6f9b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:28:53.707602+00:00
-- url     : https://prove2.me/submissions/3aa09772-10c0-49ab-9d64-5777da341523

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_span_901177580971

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {N : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (h : ∀ m : Fin n →₀ ℕ, m.degree = N → monomial m (1 : ℂ) ∈ I) : originIdeal n ^ N ≤ I := by
  refine (originIdeal_pow_le_span N).trans (Ideal.span_le.2 ?_)
  rintro _ ⟨m, hm, rfl⟩
  exact h m hm
end GroundTheory.Heights₂.Heights.ComplexSets
