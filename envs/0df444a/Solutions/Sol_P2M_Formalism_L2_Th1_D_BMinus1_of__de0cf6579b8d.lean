-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_D_BMinus1_of__de0cf6579b8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:05.175666+00:00
-- url     : https://prove2.me/submissions/f289dfac-c6d9-4caa-a05c-779ad21ded2b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_zXY_eq
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_cc_zXY
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_sumE_eq
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_sumO_eq
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_comb_zXY
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_comb_back
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_subst_comb
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_artin_hasse_log_eq_generic_log
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_coeff_one_gLog
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_isIdMod2_letLog
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_coeff_one_subst
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_coeff_keep
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_keep_eq_subst
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_hasSubst_keepX
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_keepX_pos
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_keepX_neg
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_keep_letLog
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_keep_zXY
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_shiftType_zXY
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_funEq_of_shift
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_FG_funEqHomV
import Theorems.Thm_Formalism_FG_subst_injective_vector
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
import Theorems.Thm_Formalism_L2_Th1_D_Pair_exp_log
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_single_var
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_subst1
import Theorems.Thm_Formalism_L2_Th1_D_ShiftIP_of_frobSq
import Theorems.Thm_Formalism_L2_Th1_D_frobenius_square
import Theorems.Thm_Formalism_L2_Th1_D_integral_part_lemma
import Theorems.Thm_Formalism_L2_Th1_D_letter_shift
import Theorems.Thm_Formalism_LT_InvIntP_key
import Theorems.Thm_Formalism_LT_PadicP_coeff_one_subst
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211
import Theorems.Thm_P2M_Formalism_L2_Th1_D_Pair_subst_zero__1c375b19f91e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog frobVar frobVar_eq_expand)
open MvPowerSeries
open Pair TranslateJetMomentLawAnyIdempotentLevel
namespace Formalism.L2.Th1.D
theorem _root_.solution (hE : ExpSpec) : BMinus1 := by
  intro K _ _ _ l d _ σ hU _ hd ι _ _ om oms hO hT
  have hl : l.Prime := hU.1
  have hl2 : 2 ≤ l := hl.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.ne_zero
  obtain ⟨hset, hball⟩ := frobenius_square K l σ hU
  have hfix := hO.2
  have hLS : ShiftType l σ (fun s : ZMod d => letLog (K := K) l s) :=
    (letter_shift K l d σ hl).2.1
  have hZS := shiftType_zXY hl hd hball hO
  have hid := isIdMod2_letLog (K := K) (d := d) hl
  obtain ⟨T0, hT00, hT0I, hT0s⟩ := Formalism.FG.funEqHomV K l (l ^ 2) hq (σ.comp σ) hset (ZMod d)
    (sM K d) (by intro j k; unfold sM; split_ifs <;> simp) (letLog l) hid
    (funEq_of_shift hq σ hLS) (Bool × ι) (zXY l σ om oms) (cc_zXY hl2 σ om oms)
    (funEq_of_shift hq σ hZS)
  have hT0S : HasSubst T0 := hasSubst_of_constantCoeff_zero hT00

  let PX : ZMod d → Bool × ι → Prop := fun s x => (x.1 = false ↔ s.val % 2 = 0)
  let T : ZMod d → MvPowerSeries (Bool × ι) K := fun s => keep (PX s) (T0 s)
  have hTc0 : ∀ s, constantCoeff (T s) = 0 := by
    intro s
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_keep]
    split_ifs
    · rw [coeff_zero_eq_constantCoeff_apply, hT00]
    · rfl
  have hTI : ∀ s, Integral (T s) := by
    intro s n
    rw [coeff_keep]
    split_ifs
    · exact hT0I s n
    · simp
  have hTS : HasSubst T := hasSubst_of_constantCoeff_zero hTc0
  have hTlog : ∀ j, subst T (letLog (K := K) l j) = zXY l σ om oms j := by
    intro j
    let PZ : ZMod d → Prop := fun s => (s.val % 2 = 0 ↔ j.val % 2 = 0)
    have hfam : (fun s => subst T (keepX (K := K) PZ s)) =
        fun s => subst (keepX (K := K) (PX j)) (subst T0 (keepX (K := K) PZ s)) := by
      funext s
      by_cases hs : PZ s
      · rw [keepX_pos hs, subst_X hTS, subst_X hT0S, ← keep_eq_subst]
        have hP : PX s = PX j := by
          funext x
          exact propext ⟨fun h => h.trans hs, fun h => h.trans hs.symm⟩
        change keep (PX s) (T0 s) = keep (PX j) (T0 s)
        rw [hP]
      · rw [keepX_neg hs, subst_zero' hTS, subst_zero' hT0S, subst_zero' (hasSubst_keepX _)]
    have hcomp : HasSubst (fun s => subst T0 (keepX (K := K) PZ s)) := by
      refine hasSubst_of_constantCoeff_zero fun s => ?_
      by_cases hs : PZ s
      · rw [keepX_pos hs, subst_X hT0S, hT00]
      · rw [keepX_neg hs, subst_zero' hT0S, map_zero]
    calc subst T (letLog (K := K) l j)
        = subst T (subst (keepX (K := K) PZ) (letLog (K := K) l j)) := by
          rw [← keep_eq_subst, keep_letLog hd]
      _ = subst (fun s => subst T (keepX (K := K) PZ s)) (letLog (K := K) l j) :=
          subst_comp_subst_apply (hasSubst_keepX _) hTS _
      _ = subst (fun s => subst (keepX (K := K) (PX j)) (subst T0 (keepX (K := K) PZ s)))
            (letLog (K := K) l j) := by rw [hfam]
      _ = subst (keepX (K := K) (PX j))
            (subst (fun s => subst T0 (keepX (K := K) PZ s)) (letLog (K := K) l j)) :=
          (subst_comp_subst_apply hcomp (hasSubst_keepX _) _).symm
      _ = subst (keepX (K := K) (PX j))
            (subst T0 (subst (keepX (K := K) PZ) (letLog (K := K) l j))) := by
          rw [subst_comp_subst_apply (hasSubst_keepX _) hT0S]
      _ = zXY l σ om oms j := by
          rw [← keep_eq_subst PZ, keep_letLog hd, hT0s, ← keep_eq_subst, keep_zXY]

  let G : Bool × ι → MvPowerSeries (ZMod d) K :=
    fun x => ∑ s : ZMod d, C (pXY σ om oms x s) * letLog l s
  have hG : ∀ x, IP l σ (G x) := by
    rintro ⟨b, r⟩
    have h := ShiftIP_of_frobSq frobenius_square K l d σ hU hd (ZMod d) (fun s => letLog l s) hLS
    cases b
    · have h1 := (h (oms r) (hO.1 r).2 (hfix r).2).1
      unfold linEL at h1
      rw [sumE_eq σ om oms r] at h1
      exact h1
    · have h1 := (h (om r) (hO.1 r).1 (hfix r).1).2
      unfold linOL at h1
      rw [sumO_eq σ om oms r] at h1
      exact h1
  choose Xi hXi0 hXiI hXil using fun x => integral_part_lemma K l σ hU (ZMod d) (G x) (hG x)
  have hXiS : HasSubst Xi := hasSubst_of_constantCoeff_zero hXi0
  refine ⟨T, Xi, fun s => ⟨hTc0 s, hTI s⟩, fun x => ⟨hXi0 x, hXiI x⟩, hTlog, ?_, ?_, ?_, ?_⟩
  · intro s x
    rw [← coeff_one_subst hid hTc0 s x, hTlog, zXY_eq, map_sum, Finset.sum_eq_single x]
    · rw [coeff_C_mul, artin_hasse_log_eq_generic_log (d := 1) l x 0, coeff_one_gLog hl, if_pos rfl, mul_one]
    · intro y _ hy
      rw [coeff_C_mul, artin_hasse_log_eq_generic_log (d := 1) l y 0, coeff_one_gLog hl, if_neg (Ne.symm hy),
        mul_zero]
    · intro h
      exact absurd (Finset.mem_univ x) h
  · intro s
    have hj : ∀ j, subst (fun s => subst Xi (T s)) (letLog (K := K) l j) =
        subst (X : ZMod d → MvPowerSeries (ZMod d) K) (letLog (K := K) l j) := by
      intro j
      rw [← subst_comp_subst_apply hTS hXiS, hTlog, zXY_eq, subst_comb hXiS, subst_self]
      simp only [subst_single_var hXiS, hXil]
      exact comb_back hd σ hfix hT _ j
    have key := Formalism.FG.subst_injective_vector K (ZMod d) (ZMod d) (letLog l)
      (fun s => subst Xi (T s)) X hid
      (fun s => constantCoeff_subst_eq_zero hXiS hXi0 (hTc0 s)) (fun s => constantCoeff_X s) hj
    exact congrFun key s
  · intro x
    have h1 : PowerSeries.subst (subst T (Xi x)) (lgF K l) =
        PowerSeries.subst (X x : MvPowerSeries (Bool × ι) K) (lgF K l) := by
      rw [← subst_subst1 hTS (PowerSeries.HasSubst.of_constantCoeff_zero (hXi0 x)), hXil,
        subst_comb hTS]
      simp only [hTlog]
      exact comb_zXY hd l σ hfix hT x
    have h2 := exp_log hE hl2 (constantCoeff_subst_eq_zero hTS hTc0 (hXi0 x))
    rw [h1, exp_log hE hl2 (constantCoeff_X x)] at h2
    exact h2.symm
  · intro s n hn x hx
    rw [coeff_keep] at hn
    split_ifs at hn with h
    · exact h x hx
    · exact absurd rfl hn
end Formalism.L2.Th1.D
