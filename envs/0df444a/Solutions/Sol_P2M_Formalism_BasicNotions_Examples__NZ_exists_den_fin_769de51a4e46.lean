-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exists_den_fin_769de51a4e46
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:41:58.412877+00:00
-- url     : https://prove2.me/submissions/3d1cc6ba-c2ef-4761-a23a-994fdbdc127e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_den_6be64aadeaa6
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Formalism.MainNotions.G
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q] [Algebra W Q] [IsFractionRing W Q]
  (ϖ : W) (hϖ : Irreducible ϖ)
local notation "π" => algebraMap W Q ϖ
include hϖ
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {ι : Type} [Fintype ι] (q : ι → Q) : ∃ N : ℕ, ∀ i, π ^ N * q i ∈ (algebraMap W Q).range := by
  choose N hN using fun i => exists_den (Q := Q) ϖ hϖ (q i)
  exact ⟨∑ i, N i, fun i => hN i _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))⟩
end Formalism.BasicNotions.Examples₂.NZ
