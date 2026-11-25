-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexAt_conj_smul_60104c53b1e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:52:03.539581+00:00
-- url     : https://prove2.me/submissions/31840e03-d49e-4d33-92c3-15662422ca3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexAt
variable {K : Type*} {_ : Field K} (σ : K →+* ℂ)
namespace GroundTheory.Heights₂.Heights.ComplexAt
theorem _root_.solution (c : ℂ) (z : ComplexAt σ) : conj σ (c • z) = starRingEnd ℂ c • conj σ z := by
  rw [complex_smul_def, map_mul, conj_ofComplex, complex_smul_def]
end GroundTheory.Heights₂.Heights.ComplexAt
