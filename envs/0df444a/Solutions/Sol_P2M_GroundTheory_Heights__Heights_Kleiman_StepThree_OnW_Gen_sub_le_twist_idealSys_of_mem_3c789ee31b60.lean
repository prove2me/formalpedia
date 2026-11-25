-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_sub_le_twist_idealSys_of_mem_3c789ee31b60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:10:22.871427+00:00
-- url     : https://prove2.me/submissions/c7366cd3-d005-43b4-8d05-6c3381ed42ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubvarDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen

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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen
theorem _root_.solution (F : SubSystem S x Ω) {pp : Ideal (Poly S N)} (I : Chart x)
    {i : Fin (N + 1)} (hi : i ∈ I.1) (hX : (X i : Poly S N) ∈ pp) :
    F.sub I ≤ (F.twist (idealSys x pp)).sub I := by
  intro z hz
  have hx : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have h1 : (1 : Ω) ∈ idealMod (x := x) pp I :=
    Submodule.subset_span ⟨X i, X i, 1, hX, X_mem_monos hi, isHomogeneous_X S i, isHomogeneous_X S i, by
      rw [aeval_X, div_self hx]⟩
  exact Submodule.subset_span ⟨1, h1, z, hz, (one_smul Ω z).symm⟩
end GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen
