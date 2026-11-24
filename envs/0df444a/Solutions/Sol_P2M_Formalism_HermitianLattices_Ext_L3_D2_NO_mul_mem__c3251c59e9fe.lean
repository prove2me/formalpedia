-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_D2_NO_mul_mem__c3251c59e9fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:43:16.3278+00:00
-- url     : https://prove2.me/submissions/72df5283-8196-428c-91b2-15197c5a1427

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mul_mem_pK


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.NO
namespace Formalism.HermitianLattices.Ext.L3.D2.NO
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {a b : K} (ha : a ∈ pK K 𝔭 k)
    (hb : b ∈ pK K 𝔭 0) : a * b ∈ pK K 𝔭 k := by
  have h := mul_mem_pK h𝔭 ha hb
  rwa [add_zero] at h
end Formalism.HermitianLattices.Ext.L3.D2.NO
