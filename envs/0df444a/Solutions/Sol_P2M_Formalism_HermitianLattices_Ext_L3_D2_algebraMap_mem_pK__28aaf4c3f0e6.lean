-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_D2_algebraMap_mem_pK__28aaf4c3f0e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:33:03.949578+00:00
-- url     : https://prove2.me/submissions/6e6c6638-35f9-40ef-b782-3ae4dd718f20

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF


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
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) {k : ℕ} {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    algebraMap (𝓞 K) K z ∈ pK K 𝔭 k :=
  LocF.le_locF 𝔭 _ ⟨z, hz, rfl⟩
end Formalism.HermitianLattices.Ext.L3.D2
