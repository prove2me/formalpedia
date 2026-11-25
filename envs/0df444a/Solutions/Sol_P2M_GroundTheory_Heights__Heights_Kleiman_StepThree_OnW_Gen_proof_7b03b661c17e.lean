-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_proof_7b03b661c17e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:01.252546+00:00
-- url     : https://prove2.me/submissions/aae31e2e-8b5a-4abc-bfdc-889481ff5123

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubvarDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_sub_le_twist_idealSys_of_mem_3c789ee31b60
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_primeOf_le_zeroIdeal_c79a644ed284
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_homog_of_mem_minimalPrimes_29f5b41f0987
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_exists_restrict_powBundle_537c07f8abf7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_twistMulBundle_toSubSystem_f2bd5bc814eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_exists_restrict_twistMulBundle_1b736d316c28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Extension_proof_3fa22c8847fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Generated_proof_7390091ed2be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_pow_f814712537f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twist_944da96fb0e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mem_sub_of_mem_secs_926533cb8e92
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_powBundle_toSubSystem_418f6a814041
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_NefRestrict_proof_5f3005d2aa4f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Irrelevant_proof_a0f9d6421b8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Point_proof_d22f31b4a055
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Restrict_proof_9254d696b6ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_proof_16e6dc336e3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepData_JProper_proof_0fc41ca14e1a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_assoc_e501c3cc2859
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_comm_31b97c8bd736
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubvarDrop_proof_4b488f96c14b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistAlg_proof_fef5e6275e9c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleNefPlusAmple_proof_cc5777b7bc68
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
open StepThree.OnW.Gen
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace StepThree.OnW.Gen
theorem _root_.solution (hRL : RestrLenRestrict.Statement.{u, w})
    (hRG : RestrictGenerated.Statement.{u, w}) : StepThree.OnW.Gen.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  have hpr : pp.IsPrime := hpp.1.1
  have hhom := homog_of_mem_minimalPrimes T.D T.si hpp
  have hle : primeOf (S := k) x ≤ pp := (primeOf_le_zeroIdeal T.D T.si).trans hpp.1.2
  by_cases hrel : ∃ j, (X j : Poly k N) ∉ pp
  swap
  · push Not at hrel
    refine ⟨0, fun b c _ _ I => ?_⟩
    obtain ⟨i, hi⟩ := I.2.1
    exact le_sup_of_le_right (sub_le_twist_idealSys_of_mem _ I hi (hrel i))
  obtain ⟨j, hjp⟩ := hrel
  have hj : x j ≠ 0 := fun h0 => hjp (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := PrimeFiltration.Point.proof k Ω N x pp hpr hhom hle j hj hjp

  have := hcp
  let A := chartRing k x (singleChart hj)
  let Ip : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] Ip.ResidueField := IsScalarTower.toAlgHom k A Ip.ResidueField
  have hker : RingHom.ker ψ = Ip := Ideal.ker_algebraMap_residueField Ip
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    rw [h0, map_zero]
  have hpy : primeOf (S := k) (fun i => ψ (ratio hj i)) = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := hpy ▸ hle

  obtain ⟨f, e₀, hfJ, hfh, hfq⟩ := StepData.JProper.proof k Ω N x T
  obtain ⟨e, he, hsub⟩ :=
    SubvarDrop.proof k Ω N x T.d pp T.dim hpr hhom hle ⟨j, hjp⟩ ⟨f, hpp.1.2 hfJ, hfq⟩
  have hsubW : IsSubvar (fun i => ψ (ratio hj i)) (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by
    rw [hpy]
    exact ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩

  obtain ⟨M', rM, hM'⟩ := PrimeFiltration.Restrict.proof k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy T.M
  have hRM : RestrictData T.M.toSubSystem hxy M'.toSubSystem rM :=
    ⟨fun I => (hM' I).1, fun I => (hM' I).2.1, fun I => (hM' I).2.2.1, fun I => (hM' I).2.2.2⟩
  have hnef : Nef M'.toSubSystem :=
    NefRestrict.proof RestrictTwist.proof hRL k Ω N x _ _ hxy hxy' T.M M' rM hRM T.nef

  have hts : 0 < T.t - T.s' := by
    have hd : (1 : ℚ) ≤ (T.d : ℚ) + 1 := by
      have := (Nat.cast_nonneg T.d : (0 : ℚ) ≤ T.d); linarith
    have ht : 0 < T.t := by
      by_contra hneg'
      have hneg : T.t ≤ 0 := not_lt.mp hneg'
      have : T.t / ((T.d : ℚ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith [T.s'_pos, T.s'_lt]
    have : T.t / ((T.d : ℚ) + 1) ≤ T.t := div_le_self ht.le hd
    linarith [T.s'_lt]
  obtain ⟨q, m', hq, hm', hva⟩ := hK e he _ N _ M' hsubW hnef (T.t - T.s') hts
  obtain ⟨rr, h, hvb⟩ := hva
  have hqm : (q : ℤ) * T.m = T.p * m' := by
    have : (((q : ℤ) * T.m : ℤ) : ℚ) = ((T.p * m' : ℤ) : ℚ) := by
      push_cast; rw [T.m_eq, hm']; ring
    exact_mod_cast this

  have hBgen : (twistMul M'.toSubSystem q m').Generated := fun I => le_antisymm
    (Submodule.span_le.mpr fun z hz => KThm.mem_sub_of_mem_secs hz I)
    (by rw [← hvb.generates I]; exact Submodule.span_mono (Set.range_subset_iff.mpr hvb.mem_secs))

  have hv : ∀ b₂ : ℕ, ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c →
      (((twistMul M'.toSubSystem T.p T.m).pow b₂).twist
        (twistSys k (fun i => ψ (ratio hj i)) c)).Generated := by
    intro b₂
    obtain ⟨c₀, hc₀⟩ := Generated.proof Extension.proof k _ N _ ((twistMulBundle M' T.p T.m).powBundle b₂)
    refine ⟨c₀, fun c hc => ?_⟩
    have hs := hc₀ c hc
    rwa [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem] at hs
  choose cv hcv using hv
  refine ⟨∑ b₂ ∈ Finset.range q, |cv b₂|, fun b c _ hc I => ?_⟩

  obtain ⟨rL, hrL⟩ := exists_restrict_twistMulBundle hxy hxy' T.M M' rM hRM T.p T.m
  obtain ⟨rb, hrb⟩ := exists_restrict_powBundle hxy hxy' _ _ rL hrL b
  obtain ⟨rc, hrc⟩ := RestrictTwist.proof.1 k Ω N x _ _ hxy hxy' c
  obtain ⟨r'', hr''⟩ := RestrictTwist.proof.2 k Ω N x _ _ hxy _ (twistBundle k x c) _
    (twistBundle k (fun i => ψ (ratio hj i)) c) rb rc hrb hrc
  have hQ : ((twistMulBundle T.M T.p T.m).powBundle b).toSubSystem.twist (twistSys k x c) =
      (T.L.pow b).twist (twistSys k x c) := by
    rw [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem]
    rfl
  have hlt : b % q < q := Nat.mod_lt b (by omega)
  have hcb : cv (b % q) ≤ c :=
    le_trans (le_abs_self _) (le_trans (Finset.single_le_sum (f := fun b₂ => |cv b₂|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hlt)) hc)
  have hW : (twistMul M'.toSubSystem T.p T.m).pow b = ((twistMul M'.toSubSystem T.p T.m).pow (b % q)).twist
      ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))) := by
    rw [← TwistAlg.proof k _ N _ M'.toSubSystem T.p q T.m m' (b / q) (b % q) hqm, Nat.div_add_mod b q]
  have hgen : (((twistMulBundle M' T.p T.m).powBundle b).tensorProd
      (twistBundle k (fun i => ψ (ratio hj i)) c)).toSubSystem.Generated := by
    change (((twistMulBundle M' T.p T.m).powBundle b).toSubSystem.twist
      (twistSys k (fun i => ψ (ratio hj i)) c)).Generated
    rw [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem, hW, SubSystem.twist_assoc,
      SubSystem.twist_comm ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))), ← SubSystem.twist_assoc]
    exact KThm.generated_twist (hcv _ c hcb) (KThm.generated_pow hBgen _)
  have key := hRG k Ω N x _ _ hxy pp hle hpy (((twistMulBundle T.M T.p T.m).powBundle b).tensorProd
    (twistBundle k x c))
    (((twistMulBundle M' T.p T.m).powBundle b).tensorProd (twistBundle k (fun i => ψ (ratio hj i)) c)) r'' hr''
    hgen I
  have hQ' : (((twistMulBundle T.M T.p T.m).powBundle b).tensorProd (twistBundle k x c)).toSubSystem =
      (T.L.pow b).twist (twistSys k x c) := hQ
  rw [hQ'] at key
  exact key
end StepThree.OnW.Gen
end GroundTheory.Heights₂.Heights.Kleiman
