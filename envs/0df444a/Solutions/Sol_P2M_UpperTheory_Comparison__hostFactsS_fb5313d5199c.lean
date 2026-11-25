-- Prove2me | solution 1 for P2M_UpperTheory_Comparison__hostFactsS_fb5313d5199c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:23:53.997305+00:00
-- url     : https://prove2.me/submissions/ac152db4-77f0-409d-9482-fc50ad01c97d

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_hostFactsS
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_two_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_coprime_QSq_d
import Theorems.Thm_Formalism_HC_HostRaw_d_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_d_mod_four
import Theorems.Thm_Formalism_HC_HostRaw_d_ne_two
import Theorems.Thm_Formalism_HC_HostRaw_d_not_dvd_QSq
import Theorems.Thm_Formalism_HC_HostRaw_dvd_QSq_iff
import Theorems.Thm_Formalism_HC_HostRaw_two_dvd_QS
import Theorems.Thm_Formalism_HC_jacobi_congr
import Theorems.Thm_Formalism_HC_jacobi_neg_recip
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_exists_unit_crt
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_frobUnit_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_jac_two_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_mem_inertia_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_mem_localUnits_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_parts_of_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_sgn2_toAdd_eq_zero_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unitsMap_eq_one_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unramified_spec
import Theorems.Thm_P2M_UpperTheory_Comparison__toE_bij_c11c42203b6c
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost
private lemma inPhi_of_jac {φ : Frame} (H : HostAx φ) (u : (ZMod H.toHostRaw.condN)ˣ) (k : ℕ)
    (hk : (u : ZMod H.toHostRaw.condN).val ≡ k [MOD H.d]) (hj : jacobiSym (k : ℤ) H.d = 1) :
    Formalism.D5.InPhi (Multiplicative.toAdd (recH H.toHostRaw u)) := by
  have h1 : ((H.toHostRaw.art u).1.2 : ℤ) = 1 := by
    rw [H.der.art_ch u, jacobi_congr hk, hj]
  have h2 : (H.toHostRaw.art u).1.2 = 1 := Units.ext h1
  show Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (H.toHostRaw.art u).1.2) = 0
  rw [Formalism.LFunctionChainParameters.LHost.sgn2_toAdd_eq_zero_iff]
  exact h2
private lemma jac_of_dvd {φ : Frame} (H : HostRaw φ) {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q) :
    jacobiSym (p : ℤ) H.d = 1 := by
  have hd4 := H.d_mod_four
  rcases (H.dvd_QSq_iff hp).mp h with hQ | rfl
  · by_cases h2 : p = 2
    · subst h2
      exact jac_two_d H.hyp
    · have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left h2
      rw [← jacobi_neg_recip hd4 hodd]
      exact H.QS_split p hp h2 hQ
  · have hodd : H.q % 2 = 1 := by
      have := H.hyp.2.2.1
      omega
    rw [← jacobi_neg_recip hd4 hodd]
    exact H.hyp.2.2.2.2
private lemma d_dvd_ordCompl {φ : Frame} (H : HostRaw φ) {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q) :
    H.d ∣ ordCompl[p] H.condN := by
  apply Nat.dvd_ordCompl_of_dvd_not_dvd H.d_dvd_condN
  intro hpd
  have hpe : p = H.d := (Nat.prime_dvd_prime_iff_eq hp H.d_prime).mp hpd
  exact H.d_not_dvd_QSq (hpe ▸ h)
private lemma toE_iod' (φ : Frame) : Multiplicative.toAdd (toE φ φ.iod) = sgc0 := by
  rw [(toE_bij φ).2.1]
  rfl
private theorem hostFactsS_pf :
    ∀ (φ : Frame) (H : HostAx φ), HostFactsS (arith H.toHostRaw) (H.QS * H.q).primeFactors := by
  intro φ H
  haveI : NeZero H.toHostRaw.condN := ⟨H.toHostRaw.condN_ne_zero⟩
  have hQq0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
  refine
    { d_prime := H.d_prime
      two_mem := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_of_dvd_left H.two_dvd_QS _, hQq0⟩
      q1_mem := Nat.mem_primeFactors.mpr ⟨H.q_prime, dvd_mul_left _ _, hQq0⟩
      d_not_mem := fun hm => H.d_not_dvd_QSq (Nat.dvd_of_mem_primeFactors hm)
      unram := ?_
      split_inertia := ?_
      split_frob := ?_
      inertia_d := ?_ }
  · intro p hp hpS hpd
    have hpN : ¬ p ∣ H.toHostRaw.condN := by
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
      · exact hpS (Nat.mem_primeFactors.mpr ⟨hp, h1, hQq0⟩)
      · exact hpd ((Nat.prime_dvd_prime_iff_eq hp H.d_prime).mp h1)
    have hloc := (unramified_spec _ p H.toHostRaw.condN_ne_zero hp hpN).1
    rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff H.q H.d (recH H.toHostRaw) p x).mp hx
    rw [hloc, Subgroup.mem_bot] at hu
    subst hu
    simp
  · intro p hpS x hx
    have hp := Nat.prime_of_mem_primeFactors hpS
    have hdvd := Nat.dvd_of_mem_primeFactors hpS
    obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff H.q H.d (recH H.toHostRaw) p x).mp hx
    rw [mem_localUnits_iff] at hu
    exact inPhi_of_jac H u 1 (Nat.ModEq.of_dvd (d_dvd_ordCompl H.toHostRaw hp hdvd) hu) (by simp)
  · intro p hpS
    have hp := Nat.prime_of_mem_primeFactors hpS
    have hdvd := Nat.dvd_of_mem_primeFactors hpS
    have hf := (frobUnit_modEq (N := H.toHostRaw.condN) hp).1
    exact inPhi_of_jac H _ p (Nat.ModEq.of_dvd (d_dvd_ordCompl H.toHostRaw hp hdvd) hf)
      (jac_of_dvd H.toHostRaw hp hdvd)
  · intro x
    have hparts := parts_of_eq (N := H.toHostRaw.condN) (k := 1) (m := H.QS * H.q) H.d_prime
      (by show H.QS * H.q * H.d = _; ring) H.d_not_dvd_QSq hQq0
    refine (mem_inertia_iff H.q H.d (recH H.toHostRaw) H.d x).trans ?_
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [mem_localUnits_iff, hparts.2] at hu
      rcases H.art_d u hu with h | h
      · left
        simp [recH, h]
      · right
        show Multiplicative.toAdd (toE φ (H.toHostRaw.art u)) = sgc0
        rw [h]
        exact toE_iod' φ
    · rintro (rfl | rfl)
      · exact ⟨1, Subgroup.one_mem _, by simp⟩
      · obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.toHostRaw.condN) (a := H.QS * H.q) (b := H.d)
          rfl H.coprime_QSq_d (dvd_mul_right _ _) H.d_dvd_condN 1 (-1)
        have hloc : (u : ZMod H.toHostRaw.condN).val ≡ 1 [MOD H.QS * H.q] :=
          (unitsMap_eq_one_iff _ u).mp hu1
        refine ⟨u, ?_, ?_⟩
        · rw [mem_localUnits_iff, hparts.2]
          exact hloc
        · have hcast : (((u : ZMod H.toHostRaw.condN).val : ℤ) : ZMod H.d) = ((-1 : ℤ) : ZMod H.d) := by
            have h3 := congrArg (fun v : (ZMod H.d)ˣ => (v : ZMod H.d)) hu2
            simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply,
              Units.val_neg, Units.val_one] at h3
            push_cast
            rw [ZMod.natCast_val]
            exact h3
          rw [ZMod.intCast_eq_intCast_iff] at hcast
          have hjac : ((H.toHostRaw.art u).1.2 : ℤ) = -1 := by
            rw [H.der.art_ch u, jacobiSym.mod_left,
              show (((u : ZMod H.toHostRaw.condN).val : ℕ) : ℤ) % (H.d : ℤ) = (-1) % (H.d : ℤ) from hcast,
              ← jacobiSym.mod_left, jacobiSym.at_neg_one (H.d_prime.odd_of_ne_two H.d_ne_two),
              ZMod.χ₄_nat_three_mod_four H.d_mod_four]
          rcases H.art_d u hloc with h | h
          · exfalso
            rw [h] at hjac
            simp at hjac
          · show Multiplicative.toAdd (toE φ (H.toHostRaw.art u)) = sgc0
            rw [h]
            exact toE_iod' φ
end

set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost
namespace UpperTheory.Comparison₂
theorem _root_.solution :
    ∀ (φ : Frame) (H : HostAx φ), HostFactsS (arith H.toHostRaw) (insert H.q H.small) := by
  intro φ H
  have hset : insert H.q H.small = (H.QS * H.q).primeFactors := by
    rw [Nat.primeFactors_mul H.QS_ne_zero H.q_prime.ne_zero, H.q_prime.primeFactors]
    show insert H.q H.QS.primeFactors = _
    ext a
    simp [or_comm]
  rw [hset]
  exact hostFactsS_pf φ H
end UpperTheory.Comparison₂
