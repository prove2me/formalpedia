-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_proof_6fbc83fd5ae7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:03:47.784133+00:00
-- url     : https://prove2.me/submissions/ff29986e-584d-451f-ab5d-6c4e1d32cad8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZChartRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_exists_pow_mul_mem_ampleRing_f5e83a2a2460
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_ampleBase_le_chartRing_2377a54c4d9f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_pow_div_xProd_mem_d75dc4a6d385
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_xProd_ne_zero_5c3b01ddff8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9


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
open MvPolynomial Filter
noncomputable section
universe u w
open VeryAmpleZChartRing
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleZChartRing
theorem _root_.solution : VeryAmpleZChartRing.Statement.{u, w} := by
  intro S _ Ω _ _ N x H r h hv J j hjJ c hc K hrat α hα
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hjJ)
  have hh : ∀ I : Chart x, h j ∈ (H.pow 1).sub I := fun I => by
    rw [SubSystem.pow_sub, pow_one]
    exact (Submodule.mem_iInf _).mp (hv.mem_secs j) I
  have hJ0 : xProd J ≠ 0 := AmpleAffineGen.xProd_ne_zero J
  obtain ⟨n, hn⟩ := hα
  set g : Ω := xProd J / h j ^ J.1.card with hg
  have hy : α * g ^ n ∈ ampleChart H.toSubSystem 1 (h j) K := by
    refine ⟨J.1.card * n, ?_⟩
    have e1 : α * g ^ n * h j ^ (J.1.card * n) = α * xProd J ^ n := by
      rw [hg, div_pow, pow_mul, ← pow_mul, mul_comm J.1.card n, pow_mul, mul_assoc,
        div_mul_cancel₀ _ (pow_ne_zero _ (pow_ne_zero _ hj0))]
    rw [e1, one_mul]
    exact hn
  obtain ⟨M₀, hM₀⟩ := exists_pow_mul_mem_ampleRing H hh hc K hrat hy
  have hbase := ampleBase_le_chartRing (S := S) J hjJ
  have h1 : c ^ M₀ * (α * g ^ n) ∈ chartRing S h J := hbase (hv.closed j hj0 hM₀)
  have hcJ : c ∈ chartRing S h J := hbase (hv.closed j hj0 hc)
  have h2 : c ^ M₀ * α ∈ chartRing S h J := by
    have e2 : c ^ M₀ * α = c ^ M₀ * (α * g ^ n) * (h j ^ J.1.card / xProd J) ^ n := by
      rw [hg, mul_assoc (c ^ M₀), mul_assoc α, ← mul_pow, div_mul_div_cancel₀ (pow_ne_zero _ hj0),
        div_self hJ0, one_pow, mul_one]
    rw [e2]
    exact mul_mem h1 (pow_mem (pow_div_xProd_mem J j) n)
  refine eventually_atTop.mpr ⟨M₀, fun M hM => ?_⟩
  have e3 : c ^ M * α = c ^ (M - M₀) * (c ^ M₀ * α) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hM]
  rw [e3]
  exact mul_mem (pow_mem hcJ _) h2
end VeryAmpleZChartRing
end GroundTheory.Heights₂.Heights.Kleiman
