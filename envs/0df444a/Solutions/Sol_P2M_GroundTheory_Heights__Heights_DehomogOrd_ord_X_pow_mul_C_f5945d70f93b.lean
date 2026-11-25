-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_X_pow_mul_C_f5945d70f93b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:26:57.718901+00:00
-- url     : https://prove2.me/submissions/4befceb5-42b9-47d5-9cab-b2bd72569b9b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_mul_of_notMem_ddcfc676d20e

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
open GroundTheory.Heights₂.Heights.DehomogOrd
namespace GroundTheory.Heights₂.Heights.DehomogOrd
theorem _root_.solution (h₁ : OrdPolynomialLocalization.Statement) {Q : Type} [CommRing Q] (p : Ideal Q)
    [p.IsPrime] [(Ideal.map (C : Q →+* MvPolynomial Unit Q) p).IsPrime] (q : Q) (d : ℕ) :
    Ring.ord (Localization.AtPrime (Ideal.map (C : Q →+* MvPolynomial Unit Q) p))
        (algebraMap (MvPolynomial Unit Q) _ (X () ^ d * C q)) =
      Ring.ord (Localization.AtPrime p) (algebraMap Q _ q) := by
  have hX : (X () : MvPolynomial Unit Q) ∉ Ideal.map (C : Q →+* MvPolynomial Unit Q) p := by
    intro h
    rw [MvPolynomial.mem_map_C_iff] at h
    have h1 : (1 : Q) ∈ p := by simpa using h (Finsupp.single () 1)
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr h1)
  rw [ord_atPrime_mul_of_notMem _ (fun h => hX (Ideal.IsPrime.mem_of_pow_mem ‹_› d h))]
  exact h₁ Q Unit p q
end GroundTheory.Heights₂.Heights.DehomogOrd
