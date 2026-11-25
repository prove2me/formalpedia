-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_proof_28af41600539
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:27.208162+00:00
-- url     : https://prove2.me/submissions/1e7ce1ec-2dfc-4b7c-a3eb-a72b19bcc8bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_chart_smul_eq_66ee2ccdfd04
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_twist_83284b5696ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_pow_7d26be4ef798
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_mem_twist_pow_add_56f5d31f05e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_prod_mem_pow_9c644647d1e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619
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
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
theorem _root_.solution (hFam : VeryAmpleZFamily.Statement.{u, v, w}) : VeryAmpleZTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hH a J
  obtain ⟨F', hF'⟩ := hFam S Ω N x E F H r h hH
  obtain ⟨j, hj⟩ := J.2.1
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hj)
  have hmem : ∀ l I, h l ∈ H.sub I := fun l I => (Submodule.mem_iInf _).mp (hH.mem_secs l) I
  have hpow : ∀ I, h j ^ a ∈ (H.pow a).sub I := fun I => by
    have h1 : h j ∈ (H.pow 1).sub I := by rw [SubSystem.pow_sub, pow_one]; exact hmem j I
    simpa using AmpleTwistLocal.pow_mem_pow H.toSubSystem I h1 a

  have fwd : ∀ y ∈ secsOnZ F.toSubSystem H.toSubSystem h J,
      h j ^ a • y ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J := by
    intro y hy
    refine (Submodule.mem_iInf _).mpr fun I => ?_
    have hyI : y ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J := (Submodule.mem_iInf _).mp hy I
    refine Submodule.span_induction (p := fun y _ =>
      h j ^ a • y ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J) ?_ ?_ ?_ ?_ hyI
    · rintro y ⟨n, hn⟩
      refine Submodule.subset_span ⟨n, ?_⟩
      rw [smul_smul, mul_comm (xProd J ^ n), ← smul_smul]
      exact smul_mem_twist_twist _ _ _ I (hpow I) hn
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
    · intro s e _ he; rw [smul_comm]; exact Submodule.smul_mem _ s he

  have bwd : ∀ e ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J,
      (h j ^ a)⁻¹ • e ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
    classical
    intro e he
    refine (Submodule.mem_iInf _).mpr fun I => ?_
    have heI : e ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J := (Submodule.mem_iInf _).mp he I
    set u := ∏ l ∈ J.1.erase j, h l with hu
    have hxu : xProd J = h j * u := (Finset.mul_prod_erase J.1 h hj).symm
    have hk : J.1.card = (J.1.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    have hua : u ^ a ∈ (H.pow ((J.1.erase j).card * a)).sub I :=
      AmpleTwistLocal.pow_mem_pow H.toSubSystem I (prod_mem_pow H.toSubSystem I (fun l => hmem l I) _) a
    refine Submodule.span_induction (p := fun e _ =>
      (h j ^ a)⁻¹ • e ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J) ?_ ?_ ?_ ?_ heI
    · rintro e ⟨n, hn⟩
      refine Submodule.subset_span ⟨n + a, ?_⟩
      have heq : xProd J ^ (n + a) • (h j ^ a)⁻¹ • e = u ^ a • (xProd J ^ n • e) := by
        rw [smul_smul, smul_smul, hxu]
        congr 1
        field_simp
        ring
      have hdeg : a + J.1.card * n + (J.1.erase j).card * a = J.1.card * (n + a) := by
        rw [hk]; ring
      rw [heq, ← hdeg]
      exact smul_mem_twist_pow _ _ I hua (mem_twist_pow_add _ _ I hn)
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
    · intro s e _ he; rw [smul_comm]; exact Submodule.smul_mem _ s he
  have hq : h j ^ a ∈ twistMod S h (a : ℤ) J := by
    rw [twistMod_eq_span (a : ℤ) J hj, zpow_natCast]
    exact Submodule.mem_span_singleton_self _
  apply le_antisymm
  · intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    suffices H1 : ∀ c : chartRing S h J, c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J by
      simpa using H1 1
    refine Submodule.span_induction (p := fun z _ => ∀ c : chartRing S h J,
      c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, y, hy, rfl⟩ c
      rw [twistMod_eq_span (a : ℤ) J hj, Submodule.mem_span_singleton] at hq
      obtain ⟨d, rfl⟩ := hq
      have hy' : y ∈ F'.sub J := by
        have : y ∈ (F'.sub J).restrictScalars S := by rw [hF' J]; exact hy
        exact this
      have hcd : (c * d) • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
        rw [← hF' J]; exact Submodule.smul_mem _ (c * d) hy'
      have heq : c • ((d • h j ^ (a : ℤ)) • y) = h j ^ a • ((c * d) • y) := by
        rw [chart_smul_eq, chart_smul_eq, smul_eq_mul, zpow_natCast, smul_smul, chart_smul_eq (c * d),
          smul_smul]
        congr 1
        push_cast
        ring
      rw [heq]
      exact fwd _ hcd
    · intro c; rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he c; rw [smul_add]; exact Submodule.add_mem _ (hb c) (he c)
    · intro c' e _ he c; rw [smul_smul]; exact he (c * c')
  · intro e he
    have heq : e = h j ^ a • ((h j ^ a)⁻¹ • e) := by
      rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hj0), one_smul]
    rw [Submodule.restrictScalars_mem, heq]
    exact Submodule.subset_span ⟨h j ^ a, by exact_mod_cast hq, _, bwd e he, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
