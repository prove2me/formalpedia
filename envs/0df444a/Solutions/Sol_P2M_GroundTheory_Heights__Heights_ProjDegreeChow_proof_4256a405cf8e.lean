-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjDegreeChow_proof_4256a405cf8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:39.098716+00:00
-- url     : https://prove2.me/submissions/d86825ec-e829-4723-8aca-0ac21359ec76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjDegreeChow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjDegreeChow

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ProjDegreeChow
theorem _root_.solution (h₁ : ProjSecDegree.Statement) (h₂ : ProjSecDomain.Statement)
    (h₃ : ProjChowNonzero.Statement) (h₄ : SecDegreeLe.Statement) (h₅ : SecDegreeGe.Statement) :
    ProjDegreeChow.Statement := by
  intro n e δ W f A hW hf hδ hA
  rw [h₁ n e W A]
  obtain ⟨hdom, hfin⟩ := h₂ n e W A hW.isPrime hA
  have hc := h₃ n e W f A hW hf hA
  have hsep : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
      (Vertical.SecAlg
        (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
        (projPar A)) :=
    ⟨fun x => PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral x))⟩
  refine le_antisymm (h₄ ℂ _ n e δ W f (projPar A) hW hf hδ hfin hdom hsep fun h => hc ?_)
    (h₅ ℂ _ n e δ W f (projPar A) hW hf hδ hc).2
  rw [h, map_zero]
end ProjDegreeChow
end GroundTheory.Heights₂.Heights
