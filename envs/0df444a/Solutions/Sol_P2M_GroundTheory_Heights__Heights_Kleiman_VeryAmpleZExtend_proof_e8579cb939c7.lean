-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_proof_e8579cb939c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:04:07.625553+00:00
-- url     : https://prove2.me/submissions/32c05879-8628-4acd-9780-74e0d16bd835

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZExtend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_prod_mem_pow_64615a997730
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_smul_mem_twist_pow_e1c974636e30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_gen_smul_e549be2950d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mul_chartRatio_21e198efb704
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_866e61ad51fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_left_2c27ecd7d652
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_right_b54617500f30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619


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
open Filter
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
theorem _root_.solution : VeryAmpleZExtend.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hh J j hj c hc K hK f hf
  classical
  have key : ∀ I : Chart x, ∀ᶠ M in atTop, c ^ M • f ∈ secsOnZChart F.toSubSystem H h I J := by
    intro I
    obtain ⟨a, ha⟩ := Set.mem_iInter.mp hc I
    rw [one_mul] at ha
    obtain ⟨e, n, hn⟩ := hK I
    rw [one_mul] at hn
    change c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n ∈ (H.pow n).sub I at hn

    have hfU := F.mono K (AmpleAffineGen.unionChart I K) (AmpleAffineGen.subset_unionChart_right I K) f hf
    obtain ⟨t, ht, htf⟩ := (F.mem_iff I (AmpleAffineGen.unionChart I K)
      (AmpleAffineGen.subset_unionChart_left I K) f).mp hfU
    obtain ⟨v, hv⟩ := ht.exists_left_inv
    obtain ⟨D, hD⟩ := AmpleAffineGen.exists_pow_mul_mem I K v.2
    have hv' : (v : Ω) * (t : Ω) = 1 := congrArg Subtype.val hv
    have hρf : AmpleAffineGen.chartRatio I K ^ D • f ∈ F.sub I := by
      have e1 : AmpleAffineGen.chartRatio I K ^ D • f =
          (⟨_, hD⟩ : chartRing S x I) • ((t : Ω) • f) := by
        rw [Subalgebra.smul_def, smul_smul]
        congr 1
        change _ = AmpleAffineGen.chartRatio I K ^ D * (v : Ω) * (t : Ω)
        rw [mul_assoc, hv', mul_one]
      rw [e1]
      exact Submodule.smul_mem _ _ htf

    have hP := prod_mem_pow H hh I (J.1.erase j)
    have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
    have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
    have hz : (c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n) ^ D •
        (AmpleAffineGen.chartRatio I K ^ D • f) ∈ (F.toSubSystem.twist (H.pow (n * D))).sub I :=
      Submodule.subset_span ⟨_, AmpleTwistLocal.pow_mem_pow H I hn D, _, hρf, rfl⟩
    have hz2 := smul_mem_twist_pow F.toSubSystem H I hz
      (AmpleTwistLocal.pow_mem_pow H I hP (n * D))
    have h0 : ∃ m : ℕ, xProd J ^ m • (c ^ (e * D) • f) ∈
        (F.toSubSystem.twist (H.pow (J.1.card * m))).sub I := by
      refine ⟨n * D, ?_⟩
      have e1 : xProd J ^ (n * D) • (c ^ (e * D) • f) =
          (∏ l ∈ J.1.erase j, h l) ^ (n * D) • ((c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n) ^ D •
            (AmpleAffineGen.chartRatio I K ^ D • f)) := by
        rw [smul_smul, smul_smul, smul_smul, hJ]
        congr 1
        have hr := AmpleAffineGen.chartRatio_mul_chartRatio I K
        calc (h j * ∏ l ∈ J.1.erase j, h l) ^ (n * D) * c ^ (e * D)
            = (∏ l ∈ J.1.erase j, h l) ^ (n * D) * ((c ^ e * h j ^ n) ^ D *
                (AmpleAffineGen.chartRatio K I * AmpleAffineGen.chartRatio I K) ^ D) := by
              rw [hr, one_pow, mul_one]; ring
          _ = _ := by ring
      have e2 : J.1.card * (n * D) = n * D + (J.1.erase j).card * (n * D) := by
        rw [← hcard]; ring
      rw [e1, e2]
      exact hz2

    have hstep : ∀ q : ℕ, ∃ m : ℕ, xProd J ^ m • (c ^ (e * D + q) • f) ∈
        (F.toSubSystem.twist (H.pow (J.1.card * m))).sub I := by
      intro q
      induction q with
      | zero => exact h0
      | succ q ih =>
        rw [← Nat.add_assoc, pow_succ', ← smul_smul]
        exact gen_smul F.toSubSystem H hh I J hj ha ih
    refine eventually_atTop.mpr ⟨e * D, fun M hM => ?_⟩
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hM
    exact Submodule.subset_span (hstep q)
  exact (eventually_all.mpr key).mono fun M hM => (Submodule.mem_iInf _).mpr hM
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
