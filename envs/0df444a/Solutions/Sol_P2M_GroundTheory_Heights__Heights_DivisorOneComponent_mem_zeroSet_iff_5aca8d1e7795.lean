-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DivisorOneComponent_mem_zeroSet_iff_5aca8d1e7795
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:25.539252+00:00
-- url     : https://prove2.me/submissions/f89cbb5b-2153-483c-aca1-7e1eb5f37613

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorOneComponent

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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorOneComponent
namespace GroundTheory.Heights₂.Heights.DivisorOneComponent
theorem _root_.solution {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    q ∈ zeroSet K ↔ K ≤ RingHom.ker (eval q) :=
  ⟨fun h f hf => RingHom.mem_ker.2 (h f hf), fun h _ hf => RingHom.mem_ker.1 (h hf)⟩
end GroundTheory.Heights₂.Heights.DivisorOneComponent
