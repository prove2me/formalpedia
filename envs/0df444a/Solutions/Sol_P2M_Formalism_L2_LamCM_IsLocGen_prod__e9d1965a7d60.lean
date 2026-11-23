-- Prove2me | solution 1 for P2M_Formalism_L2_LamCM_IsLocGen_prod__e9d1965a7d60
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:48.096839+00:00
-- url     : https://prove2.me/submissions/9c5e4a15-a2aa-47a9-b121-8802d816c47b

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Theorems.Thm_P2M_Formalism_L2_LamCM_IsLocGen_mul__c4e282433e61

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}
namespace Formalism.L2.LamCM
namespace IsLocGen
theorem _root_.solution {ι : Type} (s : Finset ι) (a : ι → K) (I : ι → FractionalIdeal (𝓞 K)⁰ K)
    (h : ∀ i, IsLocGen p (a i) (I i)) (hI : ∀ i, I i ≠ 0) : IsLocGen p (∏ i ∈ s, a i) (∏ i ∈ s, I i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ⟨one_ne_zero, by rw [FractionalIdeal.spanSingleton_one]⟩
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i).mul' ih (hI i) (Finset.prod_ne_zero_iff.mpr fun j _ => hI j)
end IsLocGen
end Formalism.L2.LamCM
