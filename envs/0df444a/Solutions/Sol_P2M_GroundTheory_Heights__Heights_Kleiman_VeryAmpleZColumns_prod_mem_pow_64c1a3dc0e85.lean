-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_prod_mem_pow_64c1a3dc0e85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:12:11.543399+00:00
-- url     : https://prove2.me/submissions/28c00354-22d3-4c7a-9c29-617dd7f8e12a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns

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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
theorem _root_.solution {I : Chart x} (Q : Submodule (chartRing S x I) Ω) (h : Fin (r + 1) → Ω)
    (hh : ∀ j, h j ∈ Q) (T : Finset (Fin (r + 1))) : ∏ j ∈ T, h j ∈ Q ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.card_empty, pow_zero]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact Submodule.mul_mem_mul (hh a) ih
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
