-- Prove2me | solution 1 for UpperTheory.HF.frobG_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:02.224057+00:00
-- url     : https://prove2.me/submissions/3720bbb2-de9d-4bd1-a8e7-e1c9e7cf22d0

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_SizeDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobGSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_Frame_mem_Psi_iff
import Theorems.Thm_Formalism_HC_HostAx_frob_iff
import Theorems.Thm_Formalism_HC_HostRaw_d_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_d_mod_four
import Theorems.Thm_Formalism_HC_HostRaw_odd_of_coprime
import Theorems.Thm_Formalism_HC_HostRaw_psAt_of_coprime
import Theorems.Thm_Formalism_HC_HostRaw_tower_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_val_unitOfCoprime
import Theorems.Thm_Formalism_HC_jacobi_congr
import Theorems.Thm_Formalism_HC_jacobi_neg_recip
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_frobG_of_coprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open UpperTheory.HF
open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ↔ H.galE σ = H.frobG p) ∧
      (((H.frobG p).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧ (((H.frobG p).1.1 : ℤˣ) : ℤ) = H.psAt p ∧
      (H.frobG p ∉ φ.Psi ↔ H.Inert p) ∧ (H.frobG p ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1) ∧
      ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.frobG p).2 = hcl φ.e v := by
  intro φ H p hpr hnd
  have hp : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hpr.out).2 hnd
  have hodd : p % 2 = 1 := H.odd_of_coprime hp
  set u := ZMod.unitOfCoprime p hp with hu
  have hval : (u : ZMod H.condN).val ≡ p [MOD H.condN] := H.val_unitOfCoprime hp
  have hF : H.frobG p = H.art u := H.frobG_of_coprime hp
  have hjac : (((H.frobG p).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p := by
    rw [hF, H.der.art_ch u, jacobi_neg_recip H.d_mod_four hodd]
    exact jacobi_congr (hval.of_dvd H.d_dvd_condN)
  have hne : jacobiSym (-(H.d : ℤ)) p = 1 ∨ jacobiSym (-(H.d : ℤ)) p = -1 := by
    rw [← hjac]
    rcases Int.units_eq_one_or ((H.frobG p).1.2) with h | h <;> simp [h]
  have hpsi : H.frobG p ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1 := by
    rw [Frame.mem_Psi_iff, ← hjac]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Units.ext h
  refine ⟨?_, hjac, ?_, ?_, hpsi, ?_⟩
  · intro P _ _ σ
    rw [hF]
    exact H.frob_iff p hp P σ
  · rw [hF, H.psAt_of_coprime hp]
  · rw [hpsi]
    unfold UpperTheory.HF.Formalism.HC.HostRaw.Inert
    constructor
    · intro h
      refine ⟨hpr.out, ?_⟩
      rcases hne with h1 | h1
      · exact absurd h1 h
      · exact h1
    · rintro ⟨-, h⟩
      rw [h]
      decide
  · have hc2 : Nat.Coprime p (2 ^ (φ.e + 2)) :=
      Nat.Coprime.coprime_dvd_right H.tower_dvd_condN hp
    refine ⟨ZMod.unitOfCoprime p hc2, by simp, ?_⟩
    rw [hF]
    apply H.art_h
    rw [ZMod.coe_unitOfCoprime]
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).2 (hval.of_dvd H.tower_dvd_condN)).symm
end UpperTheory.HF
