-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Irrelevant_proof_a0f9d6421b8f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:17.455347+00:00
-- url     : https://prove2.me/submissions/c6fb418a-2de2-495d-91ce-bc3b58357b64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace PrimeFiltration.Irrelevant
theorem _root_.solution : PrimeFiltration.Irrelevant.Statement.{u} := by
  intro S _ _ N pp _ _ hX
  refine ⟨1, fun c hc f hf => ?_⟩
  have hle : Ideal.span ((X : Fin (N + 1) → Poly S N) '' Set.univ) ≤ pp := by
    rw [Ideal.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact hX i
  apply hle
  rw [mem_ideal_span_X_image]
  intro m hm
  by_contra h
  push Not at h
  have hm0 : m = 0 := by
    ext i
    exact h i (Set.mem_univ _)
  have hdeg := hf (mem_support_iff.mp hm)
  rw [hm0] at hdeg
  simp at hdeg
  omega
end PrimeFiltration.Irrelevant
end GroundTheory.Heights₂.Heights.Kleiman
