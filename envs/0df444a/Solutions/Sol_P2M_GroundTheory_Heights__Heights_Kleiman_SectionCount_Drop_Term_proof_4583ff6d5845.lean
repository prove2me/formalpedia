-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_proof_4583ff6d5845
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:15.649102+00:00
-- url     : https://prove2.me/submissions/e876a623-00f9-4dff-8de5-f79c1d9cce68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_of_mul_mem_2055e05b01b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_one_mem_idealMod_62acac57e0fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_idealMod_prime_39c5dd2dd8c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_idealMod_mul_of_mem_c3f7741d6a4f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_sec_not_mem_of_generated_d9e1535c48d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_finrank_quotH_le_b9556f2e26a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_twistSys_sub_zero_37c528144722
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_pow_mem_twistSys_30d864c5f0c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_powBundle_toSubSystem_418f6a814041
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_twistMul_fe4f7be26a50
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_sub_ecdec4e29c5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_mul_ed3d7223ab6a


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
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
theorem _root_.solution (hGA : GeneratedAmple.Statement.{u, w}) (hFin : QuotSectionsFinite.Statement.{u, w}) :
    SectionCount.Drop.Term.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb b pp e c hN hW
  have hP := hW.isPrime
  obtain ⟨r, hh, hhN⟩ := hN
  obtain ⟨c₀, hc₀⟩ := hGA k Ω N x Nb (ampleDataOfVeryAmple Nb hhN) (twistBundle k x (-c))

  let GB : LineBundle k x := (twistBundle k x (-c)).tensorProd (Nb.powBundle c₀)
  have hGBs : GB.toSubSystem = (twistSys k x (-c)).twist (Nb.toSubSystem.pow c₀) := by
    change (twistSys k x (-c)).twist (Nb.powBundle c₀).toSubSystem = _
    rw [LineBundle.powBundle_toSubSystem]
  have hGgen : GB.toSubSystem.Generated := by rw [hGBs]; exact hc₀ c₀ le_rfl

  obtain ⟨i₀, hi₀⟩ := hW.relevant
  have hxi₀ : x i₀ ≠ 0 := by
    intro h0
    exact hi₀ (hW.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i₀)).mpr (by
      rw [aeval_X]; exact h0)))
  let I₀ : Chart x := singleChart hxi₀
  have hI₀ : ∀ i ∈ I₀.1, (X i : Poly k N) ∉ pp := fun i hi => by
    rw [Finset.mem_singleton.mp hi]; exact hi₀
  obtain ⟨t, ht, htI₀⟩ := exists_sec_not_mem_of_generated GB.toSubSystem hGgen GB.invertible hP hW.le hI₀
  have htI : ∀ I, t ∈ GB.sub I := fun I => (Submodule.mem_iInf _).mp ht I
  refine ⟨c₀, fun n i => ?_⟩

  obtain ⟨L2, hL2⟩ := exists_lineBundle_twistMul Nb (n + c₀) 0
  have hfin : Module.Finite k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c₀) 0)
      ((twistMul Nb.toSubSystem (n + c₀) 0).twist (idealSys x pp)) 0) := by
    rw [← hL2]; exact hFin k Ω N x L2 pp
  refine ⟨hfin, ?_⟩

  obtain ⟨L1, hL1⟩ := exists_lineBundle_twistMul Nb n (-((i : ℤ) * b))
  let F1B : LineBundle k x := L1.tensorProd (twistBundle k x c)
  have hF1B : F1B.toSubSystem = (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x c) := by
    change L1.toSubSystem.twist (twistSys k x c) = _
    rw [hL1]

  let LB : LineBundle k x := (twistBundle k x ((i : ℤ) * b)).tensorProd GB
  have hcast : (((i * b : ℕ)) : ℤ) = (i : ℤ) * b := by push_cast; ring
  have hLBsub : ∀ I, LB.sub I = GB.sub I * (twistSys k x ((i : ℤ) * b)).sub I := fun I =>
    SubSystem.twist_sub_eq_mul_sub (twistSys k x ((i : ℤ) * b)) GB.toSubSystem I
  have hGBsub : ∀ I, GB.sub I = Nb.sub I ^ c₀ * (twistSys k x (-c)).sub I := fun I => by
    rw [show GB.sub I = GB.toSubSystem.sub I from rfl, hGBs, SubSystem.twist_sub_eq_mul_sub,
      SubSystem.pow_sub]
  let s : Ω := x i₀ ^ (i * b) * t
  have hsI : ∀ I, s ∈ LB.sub I := fun I => by
    rw [hLBsub, mul_comm (GB.sub I)]
    have := pow_mem_twistSys (k := k) i₀ (i * b) I
    rw [hcast] at this
    exact Submodule.mul_mem_mul this (htI I)

  have hsI₀ : s ∉ idealMod pp I₀ * LB.sub I₀ := by
    intro hs
    have hneg : x i₀ ^ (-((i : ℤ) * b)) ∈ (twistSys k x (-((i : ℤ) * b))).sub I₀ := by
      change _ ∈ twistMod k x _ I₀
      rw [twistMod_eq_span _ I₀ (Finset.mem_singleton_self i₀)]
      exact Submodule.mem_span_singleton_self _
    have h1 := Submodule.mul_mem_mul hneg hs
    have hst : x i₀ ^ (-((i : ℤ) * b)) * s = t := by
      change x i₀ ^ (-((i : ℤ) * b)) * (x i₀ ^ (i * b) * t) = t
      rw [← mul_assoc, ← hcast, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hxi₀), one_mul]
    rw [hst, hLBsub, show (twistSys k x (-((i : ℤ) * b))).sub I₀ * (idealMod pp I₀ * (GB.sub I₀ *
        (twistSys k x ((i : ℤ) * b)).sub I₀)) = idealMod pp I₀ * GB.sub I₀ *
        ((twistSys k x ((i : ℤ) * b)).sub I₀ * (twistSys k x (-((i : ℤ) * b))).sub I₀) by ring,
      twistSys_sub_mul, add_neg_cancel, twistSys_sub_zero, mul_one] at h1
    exact htI₀ h1

  have hprod : ∀ I, LB.sub I * F1B.sub I = (twistMul Nb.toSubSystem (n + c₀) 0).sub I := fun I => by
    rw [show F1B.sub I = F1B.toSubSystem.sub I from rfl, hF1B, SubSystem.twist_sub_eq_mul_sub,
      twistMul_sub, twistMul_sub, hLBsub, hGBsub, twistSys_sub_zero, one_mul]
    rw [show Nb.sub I ^ c₀ * (twistSys k x (-c)).sub I * (twistSys k x ((i : ℤ) * b)).sub I *
        ((twistSys k x c).sub I * ((twistSys k x (-((i : ℤ) * b))).sub I * Nb.sub I ^ n)) =
        ((twistSys k x (-c)).sub I * (twistSys k x c).sub I) *
        ((twistSys k x ((i : ℤ) * b)).sub I * (twistSys k x (-((i : ℤ) * b))).sub I) *
        (Nb.sub I ^ n * Nb.sub I ^ c₀) by ring,
      twistSys_sub_mul, twistSys_sub_mul, neg_add_cancel, add_neg_cancel, twistSys_sub_zero, ← pow_add,
      one_mul, one_mul]

  refine finrank_quotH_le _ _ _ _ s (fun I y hy => ?_) (fun I y hy hyG => ?_) (fun I y hy hsy => ?_)
  · rw [← hprod I, ← hF1B] at *
    exact Submodule.mul_mem_mul (hsI I) hy
  · rw [SubSystem.twist_sub_eq_mul_sub] at hyG ⊢
    change s * y ∈ idealMod pp I * (twistMul Nb.toSubSystem (n + c₀) 0).sub I
    rw [← hprod I, mul_left_comm]
    rw [← hF1B] at hyG
    exact Submodule.mul_mem_mul (hsI I) hyG
  · rw [SubSystem.twist_sub_eq_mul_sub] at hsy ⊢
    change s * y ∈ idealMod pp I * (twistMul Nb.toSubSystem (n + c₀) 0).sub I at hsy
    rw [← hprod I] at hsy
    rw [← hF1B] at hy ⊢
    by_cases hcase : ∀ j ∈ I.1, (X j : Poly k N) ∉ pp
    ·
      obtain ⟨LB', hLB'⟩ := LB.invertible I
      obtain ⟨F1', hF1'⟩ := F1B.invertible I
      refine mem_of_mul_mem hLB' hF1' (idealMod_prime hP hW.le hcase) (hsI I) ?_ hy hsy
      intro hsW
      let K : Chart x := ⟨I₀.1 ∪ I.1, I.2.1.mono Finset.subset_union_right,
        Finset.union_subset I₀.2.2 I.2.2⟩
      have hK : ∀ j ∈ K.1, (X j : Poly k N) ∉ pp := fun j hj => by
        rcases Finset.mem_union.mp hj with hj | hj
        · exact hI₀ j hj
        · exact hcase j hj
      have hsK : s ∈ idealMod pp K * LB.sub K := by
        have := (LB.toSubSystem.twist (idealSys x pp)).mono I K Finset.subset_union_right s
          (by rw [SubSystem.twist_sub_eq_mul_sub]; exact hsW)
        rwa [SubSystem.twist_sub_eq_mul_sub] at this
      exact hsI₀ (mem_idealMod_mul_of_mem LB hP hW.le Finset.subset_union_left hK (hsI I₀) hsK)
    ·
      push Not at hcase
      obtain ⟨j, hj, hjp⟩ := hcase
      rw [← one_mul y]
      exact Submodule.mul_mem_mul (one_mem_idealMod hj hjp) hy
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
