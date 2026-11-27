-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__quadratic_example_rank_two_package_4ea384e90e84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:13.735081+00:00
-- url     : https://prove2.me/submissions/e630a0e2-1f7d-48b1-9a93-267b43ad8492

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Theorems.Thm_P2M_Formalism_L2_Indef_Examples__one_wf_bae69f86be42
import Theorems.Thm_P2M_Formalism_L2_Indef_Examples__two_wf_0e62dc323dfc
import Theorems.Thm_P2M_Formalism_L2_Indef_Examples__conjAt_6819ae325d9e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Examples₂
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open NumberField.IsCMField
namespace Formalism.L2.Indef.Examples₂
theorem _root_.solution (v0 : InfinitePlace K3) (w : HeightOneSpectrum (𝓞 K3)) (C CH : ℝ) :
    (two.df K3 v0).WF ∧ Nonempty (IndefPkg (faceTwo v0 w).A (faceTwo v0 w).fc C CH) := by
  exact ⟨two.wf K3 v0 (conjAt v0), ⟨pkgOf rfl (coreTwo v0 w) C CH⟩⟩
end Formalism.L2.Indef.Examples₂
