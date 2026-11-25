-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_cross_7af2443d38e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:56.957215+00:00
-- url     : https://prove2.me/submissions/e90f853b-3a78-4f60-98ec-8a6aa323ec2d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroMore

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionInjectivity
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.SectionInjectivity
theorem _root_.solution {P : ArithVariety n} {num den : MvPolynomial (Coord n) ℤ}
    (hden : den ∉ P.ideal) {c : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ}
    {f f' : MvPolynomial (Coord n) ℤ} (h : den * f - num * chartMonomial c d ∈ P.ideal)
    (h' : den * f' - num * chartMonomial c d' ∈ P.ideal) :
    f * chartMonomial c d' - f' * chartMonomial c d ∈ P.ideal := by
  have hmul : den * (f * chartMonomial c d' - f' * chartMonomial c d) ∈ P.ideal := by
    have e : den * (f * chartMonomial c d' - f' * chartMonomial c d) =
        (den * f - num * chartMonomial c d) * chartMonomial c d' -
          (den * f' - num * chartMonomial c d') * chartMonomial c d := by ring
    rw [e]
    exact P.ideal.sub_mem (P.ideal.mul_mem_right _ h) (P.ideal.mul_mem_right _ h')
  exact (P.isPrime.mem_or_mem hmul).resolve_left hden
end GroundTheory.Heights₂.Heights.SectionInjectivity
