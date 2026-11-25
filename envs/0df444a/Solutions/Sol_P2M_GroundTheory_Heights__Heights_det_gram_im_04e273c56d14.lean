-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_gram_im_04e273c56d14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:32.695505+00:00
-- url     : https://prove2.me/submissions/74264c16-dcc4-4451-861b-9a043a675e68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (v : n → V) :
    (det (gram ℂ v)).im = 0 :=
  ((Complex.nonneg_iff.mp (posSemidef_gram ℂ v).det_nonneg).2).symm
end GroundTheory.Heights₂.Heights
