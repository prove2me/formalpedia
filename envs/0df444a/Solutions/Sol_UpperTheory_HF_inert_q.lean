-- Prove2me | solution 1 for UpperTheory.HF.inert_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:01:22.31656+00:00
-- url     : https://prove2.me/submissions/d4a8d6f8-54a5-4a1a-b825-356c5fce1738

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTameWild
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_inertQ
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_coprime_QSd_q
import Theorems.Thm_Formalism_HC_HostRaw_q_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_q_mod_four
import Theorems.Thm_Formalism_HC_HostRaw_q_ne_two
import Theorems.Thm_Formalism_HC_HostRaw_val_unitOfCoprime
import Theorems.Thm_Formalism_HC_jacobi_congr
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_inertG
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_unitsOne
import Theorems.Thm_UpperTheory_HF_condE_spec
import Theorems.Thm_UpperTheory_HF_mem_ram
import Theorems.Thm_UpperTheory_HF_vd_tame_wild
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
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
private theorem ordCompl_q {φ : Frame} (H : HostRaw φ) : ordCompl[H.q] H.condN = H.QS * H.d := by
  have hq := H.q_prime
  have hQd : H.QS * H.d ≠ 0 := Nat.mul_ne_zero H.QS_ne_zero H.d_prime.ne_zero
  have hnd : ¬ H.q ∣ H.QS * H.d := fun h =>
    hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm H.coprime_QSd_q) h)
  have hN : H.condN = H.QS * H.d * H.q := by
    show H.QS * H.q * H.d = H.QS * H.d * H.q
    ring
  have hfac : H.condN.factorization H.q = 1 := by
    rw [hN, Nat.factorization_mul hQd hq.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, hq.factorization_self]
  rw [hfac, pow_one, hN]
  exact Nat.mul_div_cancel _ hq.pos
private theorem QSd_dvd {φ : Frame} (H : HostRaw φ) : H.QS * H.d ∣ H.condN :=
  ⟨H.q, by unfold HostRaw.condN; ring⟩
private theorem cyc_unitsOne {φ : Frame} (H : HostRaw φ) : IsCyclic (H.unitsOne (H.QS * H.d)) := by
  haveI : Fact (Nat.Prime H.q) := ⟨H.q_prime⟩
  have hN : H.condN = H.QS * H.d * H.q := by
    show H.QS * H.q * H.d = H.QS * H.d * H.q
    ring
  haveI : NeZero H.condN := ⟨by
    rw [hN]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_ne_zero H.d_prime.ne_zero) H.q_prime.ne_zero⟩
  let f : H.unitsOne (H.QS * H.d) →* ZMod H.q :=
    (Units.coeHom (ZMod H.q)).comp ((ZMod.unitsMap H.q_dvd_condN).comp (Subgroup.subtype _))
  refine isCyclic_of_injective_ringHom f ?_
  intro a b hab
  have ha := (H.mem_unitsOne (QSd_dvd H) a).1 a.2
  have hb := (H.mem_unitsOne (QSd_dvd H) b).1 b.2
  have hq : ((a : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ ((b : (ZMod H.condN)ˣ) : ZMod H.condN).val [MOD H.q] := by
    simp only [f, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply, Subgroup.coe_subtype,
      ZMod.unitsMap_val] at hab
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_val]
    exact hab
  have hm := (Nat.modEq_and_modEq_iff_modEq_mul H.coprime_QSd_q).1 ⟨ha.trans hb.symm, hq⟩
  rw [← hN] at hm
  have := Nat.ModEq.eq_of_lt_of_lt hm (ZMod.val_lt _) (ZMod.val_lt _)
  exact Subtype.ext (Units.ext (ZMod.val_injective _ this))
private theorem el_q_dvd {φ : Frame} (H : HostRaw φ) : H.el H.q ∣ 2 := by
  show Nat.card (H.inertG H.q) ∣ 2
  show Nat.card (H.imgOne (H.condN / H.q ^ H.condN.factorization H.q)) ∣ 2
  rw [ordCompl_q H]
  show Nat.card (Subgroup.map H.art (H.unitsOne (H.QS * H.d))) ∣ 2
  haveI := cyc_unitsOne H
  haveI : IsCyclic (Subgroup.map H.art (H.unitsOne (H.QS * H.d))) :=
    isCyclic_of_surjective (H.art.subgroupMap _) (H.art.subgroupMap_surjective _)
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  rintro ⟨g, hg⟩
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hg
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact H.art_q u ((H.mem_unitsOne (QSd_dvd H) u).1 hu)
private theorem el_q_ne_one {φ : Frame} (H : HostRaw φ) (h : H.PsQ) : H.el H.q ≠ 1 := by
  intro h1
  have hq := H.q_prime
  have hbot : H.inertG H.q = ⊥ := Subgroup.card_eq_one.1 h1
  obtain ⟨p, hp1, hp2⟩ := Nat.chineseRemainder H.coprime_QSd_q 1 (H.q - 1)
  have hN : H.condN = H.QS * H.d * H.q := by
    show H.QS * H.q * H.d = H.QS * H.d * H.q
    ring
  have hcq : Nat.Coprime p H.q := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hp2, Nat.gcd_comm, ← Nat.Coprime, hq.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (by have := hq.two_le; omega) (by have := hq.two_le; omega)
  have hcQd : Nat.Coprime p (H.QS * H.d) := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hp1, Nat.gcd_one_left]
  have hcop : Nat.Coprime p H.condN := by
    rw [hN]
    exact Nat.Coprime.mul_right hcQd hcq
  set u := ZMod.unitOfCoprime p hcop
  have hu : (u : ZMod H.condN).val ≡ p [MOD H.condN] := H.val_unitOfCoprime hcop
  have hmem : H.art u ∈ H.inertG H.q := by
    refine (H.mem_inertG H.q _).2 ⟨u, ?_, rfl⟩
    rw [ordCompl_q H]
    exact (hu.of_dvd (QSd_dvd H)).trans hp1
  rw [hbot, Subgroup.mem_bot] at hmem
  have hJ := h u
  rw [hmem, jacobi_congr ((hu.of_dvd H.q_dvd_condN).trans hp2)] at hJ
  have hc : ((H.q - 1 : ℕ) : ℤ) = -1 + (H.q : ℤ) * 1 := by
    push_cast [Nat.cast_sub hq.one_le]
    ring
  rw [hc, jacobiSym.mod_left, Int.add_mul_emod_self_left, ← jacobiSym.mod_left,
    jacobiSym.at_neg_one (hq.odd_of_ne_two H.q_ne_two), ZMod.χ₄_nat_three_mod_four H.q_mod_four] at hJ
  simp at hJ
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), H.el H.q ≤ 2 ∧ H.sl H.q = 1 ∧ (H.q ∈ H.ram → H.el H.q = 2 ∧ H.vdH H.q = 1 / 2 ∧ H.condE.factorization H.q = 1) ∧ (H.q ∉ H.ram → H.vdH H.q = 0) ∧ (H.PsQ → H.q ∈ H.ram) := by
  intro φ H
  have hq := H.q_prime
  have h2 := el_q_dvd H.toHostRaw
  have hndvd : ¬ H.q ∣ H.el H.q := fun h =>
    H.q_ne_two ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (h.trans h2))
  have htw := vd_tame_wild H hq
  have hram := mem_ram H hq
  have hs : H.sl H.q = 1 := htw.2.2 hndvd
  refine ⟨Nat.le_of_dvd two_pos h2, hs, fun hmem => ?_, fun hmem => ?_, fun hP => ?_⟩
  · have hel : H.el H.q = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact absurd h (hram.1.1 hmem)
      · exact h
    refine ⟨hel, ?_, ?_⟩
    · rw [htw.1 hndvd, hel]
      norm_num
    · have hpos := (condE_spec H.toHostRaw).2.1
      have hdvd : H.q ∣ H.condE := hram.2.1.1 hmem
      have hle : H.condE.factorization H.q ≤ 1 := by
        have h : max 1 (H.condE.factorization H.q) = 1 := hs
        exact max_eq_left_iff.1 h
      exact le_antisymm hle ((hq.dvd_iff_one_le_factorization hpos.ne').1 hdvd)
  · by_contra h
    exact hmem (hram.2.2.1.2 h)
  · exact hram.1.2 (el_q_ne_one H.toHostRaw hP)
end UpperTheory.HF
