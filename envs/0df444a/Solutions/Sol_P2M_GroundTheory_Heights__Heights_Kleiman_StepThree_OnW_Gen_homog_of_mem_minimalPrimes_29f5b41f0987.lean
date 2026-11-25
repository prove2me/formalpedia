-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_homog_of_mem_minimalPrimes_29f5b41f0987
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:53.376799+00:00
-- url     : https://prove2.me/submissions/5c4e1fb8-56ae-42f6-8ccc-8dfec4b225f7

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
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen
theorem _root_.solution (D : SubSystem S x Ω) (s : Ω) {pp : Ideal (Poly S N)}
    (hpp : pp ∈ (zeroIdeal D s).minimalPrimes) :
    ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp := by
  have hJ : (zeroIdeal D s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) S) :=
    Ideal.homogeneous_span _ _ fun f ⟨c, hf, _⟩ => ⟨c, (mem_homogeneousSubmodule c f).mpr hf⟩
  have hcore : (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal.IsPrime :=
    hpp.1.1.homogeneousCore
  have hle : zeroIdeal D s ≤ (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal :=
    hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hpp.1.2)
  have heq : (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal = pp :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
      (hpp.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _))
  have hW : pp.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) S) := by
    rw [Ideal.IsHomogeneous.iff_eq]
    exact heq
  intro p hp d
  have h := hW d hp
  have hc : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) S) p d : Poly S N) =
      homogeneousComponent d p := decomposition.decompose'_apply p d
  rwa [hc] at h
end GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen
