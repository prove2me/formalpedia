-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_LocalizedFibreSets_starO___c01796a1051a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:40.595626+00:00
-- url     : https://prove2.me/submissions/888ef2ba-ec92-4311-9b8b-7ac4130ac37e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardPhiSucc
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_change


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalizedFibreSets
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
namespace Formalism.L2.SG.Pf.LocalizedFibreSets
theorem _root_.solution (a : 𝓞 F) : star (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap (𝓞 F) (𝓞 K) a := by
  apply RingOfIntegers.ext
  change star ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K) = ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K)
  have h1 : ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K) = algebraMap F K (a : F) := by
    first
    | rfl
    | exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K a).symm.trans
        (IsScalarTower.algebraMap_apply (𝓞 F) F K a)
  rw [h1]
  exact ((Fact.out : IsFixF K F) _).2 ⟨_, rfl⟩
end Formalism.L2.SG.Pf.LocalizedFibreSets
