-- Prove2me | solution 1 for UpperTheory.exists_unit_eq_rootOfUnity_mul_conj_phase_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:31:26.562502+00:00
-- url     : https://prove2.me/submissions/e023f4c5-abdd-44da-bb0d-873f9e528eaa

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcEqOfPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_RootOfUnityGaloisActionCMDatum
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypePhaseOneAddRootOfUnity
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ExistsUnitEqRootOfUnityMulConjPhaseOne
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_cmType
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_mem_Psi_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_kc_eq_of_pow_eq_one
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_Frame_natCard_Psi
import Theorems.Thm_Formalism_HC_Frame_two_pow_dvd_ord
import Theorems.Thm_Formalism_HC_HostAx_galE_mem_Psi_iff
import Theorems.Thm_Formalism_HC_HostAx_sqd_ne_zero
import Theorems.Thm_Formalism_HC_HostRaw_conj_sqd
import Theorems.Thm_Formalism_HC_HostRaw_d_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_isMu_iff
import Theorems.Thm_Formalism_HC_HostRaw_two_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_w_dvd_condN
import Theorems.Thm_UpperTheory_prod_cmType_phase_one_add_rootOfUnity
import Theorems.Thm_UpperTheory_rootOfUnity_galois_action_CMDatum
import Theorems.Thm_UpperTheory_root_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open NumberField IsDedekindDomain Formalism.BasicNotions
private theorem emb_sqd {R : Ranks} (H : Host R) (g : R.Psi) :
    H.emb (g : R.GG) H.sqd = Complex.I * (Real.sqrt H.d : ℂ) := by
  have hfix : (H.gal.symm (g : R.GG)) H.sqd = H.sqd := by
    have := (Formalism.HC.HostAx.galE_mem_Psi_iff H.toHostAx (H.gal.symm (g : R.GG))).1
    apply this
    simp [Formalism.HC.HostRaw.galE]
  have h0 := H.φ₀_mem
  simp only [Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq] at h0
  simp only [Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf, RingHom.comp_apply]
  change H.φ₀ ((H.gal.symm (g : R.GG)) H.sqd) = _
  rw [hfix, h0]
private theorem four_dvd {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : 4 ∣ Nat.card φ.Psi := by
  rw [Formalism.HC.Frame.natCard_Psi]
  have h1 : 4 ∣ 2 ^ φ.e := by
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact Nat.pow_dvd_pow 2 H.two_le_e
  exact Dvd.dvd.mul_left (h1.trans φ.two_pow_dvd_ord) 2
private theorem val_sqrt {L : Type} [Field L] [NumberField L] (d : ℕ) (δ : L) (h : δ ^ 2 = -(d : L))
    (P : HeightOneSpectrum (𝓞 L)) (hP : ((d : ℕ) : 𝓞 L) ∉ P.asIdeal) : P.valuation L δ = 1 := by
  have hd : P.valuation L (d : L) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 L) L) d, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact hP
  have h2 : P.valuation L δ ^ 2 = 1 := by
    rw [← map_pow, h, Valuation.map_neg, hd]
  exact sq_eq_one.mp h2
private theorem val_one_add {L : Type} [Field L] [NumberField L] (N : ℕ) (hN : Even N) (hN0 : 0 < N) (z : L)
    (hz : z ^ N = 1) (hne : z ≠ -1) (P : HeightOneSpectrum (𝓞 L)) (hP : ((N : ℕ) : 𝓞 L) ∉ P.asIdeal) :
    P.valuation L (1 + z) = 1 := by
  have hint : IsIntegral ℤ z := by
    refine ⟨Polynomial.X ^ N - 1, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C 1 hN0.ne'
    · simp [hz]
  set zi : 𝓞 L := ⟨z, hint⟩ with hzi
  have hcoe : algebraMap (𝓞 L) L zi = z := rfl
  have hzi1 : zi ^ N = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, hcoe, hz, map_one]
  have hm1 : (-1 : 𝓞 L) ^ N = 1 := hN.neg_one_pow
  have hmem : (1 + zi) ∉ P.asIdeal := by
    intro h
    apply hne
    have : zi = -1 := by
      refine Formalism.HC.Der.kc_eq_of_pow_eq_one P.asIdeal hP hzi1 hm1 ?_
      simpa [sub_neg_eq_add, add_comm] using h
    have := congrArg (algebraMap (𝓞 L) L) this
    rwa [hcoe, map_neg, map_one] at this
  have : (1 + z : L) = algebraMap (𝓞 L) L (1 + zi) := by
    rw [map_add, map_one, hcoe]
  rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
  exact hmem
end

set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions
namespace UpperTheory
theorem _root_.solution :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) →
      ∃ δ : (H.E)ˣ, (δ : H.E) = z * H.conj (δ : H.E) ∧
        (∀ P : HeightOneSpectrum (𝓞 H.E), ((H.condN : ℕ) : 𝓞 H.E) ∉ P.asIdeal → P.valuation H.E (δ : H.E) = 1) ∧
        ∏ τ, (H.emb ((eT τ : R.Psi) : R.GG) (δ : H.E) / ((‖H.emb ((eT τ : R.Psi) : R.GG) (δ : H.E)‖ : ℝ) : ℂ)) = 1 := by
  intro R H ι _ eT z hz
  by_cases hne : z = -1
  · subst hne
    have hs : H.sqd ≠ 0 := H.sqd_ne_zero
    refine ⟨Units.mk0 H.sqd hs, ?_, ?_, ?_⟩
    · have hc : H.conj H.sqd = -H.sqd := H.conj_sqd
      rw [Units.val_mk0, hc]
      ring
    · intro P hP
      refine val_sqrt H.d _ H.sqd_sq P fun hm => hP ?_
      obtain ⟨k, hk⟩ := H.d_dvd_condN
      rw [hk, Nat.cast_mul]
      exact P.asIdeal.mul_mem_right _ hm
    · have hd : 0 < H.d := H.hyp.2.1.pos
      have hr : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast hd)
      have ht : ∀ g : R.Psi, H.emb (g : R.GG) H.sqd / ((‖H.emb (g : R.GG) H.sqd‖ : ℝ) : ℂ) = Complex.I := fun g => by
        rw [emb_sqd H g, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg hr.le, mul_div_assoc, div_self (by exact_mod_cast hr.ne'), mul_one]
      simp only [Units.val_mk0, ht]
      rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_congr eT]
      obtain ⟨k, hk⟩ : 4 ∣ Nat.card R.Psi := four_dvd H.toHostRaw
      rw [hk, pow_mul, Complex.I_pow_four, one_pow]
  · have hδ : 1 + z ≠ 0 := fun h0 => hne (by linear_combination h0)
    have hconj : H.conj z = z⁻¹ := (UpperTheory.rootOfUnity_galois_action_CMDatum _ H.toHostAx z hz).2.1
    have hz0 : z ≠ 0 := UpperTheory.root_ne_zero hz
    refine ⟨Units.mk0 (1 + z) hδ, ?_, ?_, ?_⟩
    · rw [Units.val_mk0, map_add, map_one, hconj]
      field_simp
      ring
    · intro P hP
      have hw : z ^ H.toHostRaw.w = 1 := (H.toHostRaw.isMu_iff z).1 hz
      obtain ⟨k, hk⟩ := H.toHostRaw.w_dvd_condN
      have hN : z ^ H.condN = 1 := by rw [hk, pow_mul, hw, one_pow]
      exact val_one_add H.condN (even_iff_two_dvd.2 H.two_dvd_condN) (Nat.pos_of_ne_zero H.condN_ne_zero) z hN hne P hP
    · exact UpperTheory.prod_cmType_phase_one_add_rootOfUnity R H ι eT z hz hne
end UpperTheory
