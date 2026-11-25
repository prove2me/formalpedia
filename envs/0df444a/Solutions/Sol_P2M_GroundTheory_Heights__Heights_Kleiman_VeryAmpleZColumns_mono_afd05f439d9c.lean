-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_mono_afd05f439d9c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:34.411527+00:00
-- url     : https://prove2.me/submissions/18157532-5f36-4446-97a4-76c6567928a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_prod_mem_pow_64c1a3dc0e85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_pow_613b8211fa30

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
variable {G : SubSystem S x E} {H : SubSystem S x Ω} {h : Fin (r + 1) → Ω} {I : Chart x}
omit [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
theorem _root_.solution (hH : ∀ j, h j ∈ H.sub I) {J J' : Chart h} (hJJ' : J.1 ⊆ J'.1) :
    secsOnZChart G H h I J ≤ secsOnZChart G H h I J' := by
  classical
  refine Submodule.span_le.mpr ?_
  rintro e ⟨n, hn⟩
  refine Submodule.subset_span ⟨n, ?_⟩
  have hq : (∏ j ∈ J'.1 \ J.1, h j) ^ n ∈ H.sub I ^ ((J'.1 \ J.1).card * n) := by
    rw [pow_mul]; exact Submodule.pow_mem_pow _ (prod_mem_pow _ h hH _) n
  have := smul_mem_twist_pow hq hn
  have hx : xProd J' = (∏ j ∈ J'.1 \ J.1, h j) * xProd J := (Finset.prod_sdiff hJJ').symm
  have hc : J'.1.card = J.1.card + (J'.1 \ J.1).card := by
    rw [Finset.card_sdiff_of_subset hJJ']; have := Finset.card_le_card hJJ'; omega
  rw [hx, mul_pow, mul_smul, hc, add_mul]
  exact this
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
