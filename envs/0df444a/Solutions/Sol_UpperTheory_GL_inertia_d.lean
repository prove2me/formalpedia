-- Prove2me | solution 1 for UpperTheory.GL.inertia_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:04:12.020457+00:00
-- url     : https://prove2.me/submissions/2f44467e-85bf-4932-b8f1-ed0758b804cc

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_hostFactsS
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_InertiaD
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_d_not_dvd_QSq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_frobUnit_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_parts_of_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_sgn2_toAdd_eq_ite
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_zmod_two_eq_zero_or_eq_one
import Theorems.Thm_P2M_UpperTheory_Comparison__hostFactsS_fb5313d5199c
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
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal
namespace UpperTheory.GL
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), (∀ x, x ∈ (arith H.toHostRaw).inertia H.d ↔ x = 0 ∨ x = sgc0) ∧
      ((arith H.toHostRaw).frob H.d).1.2 = 1 ∧
      ∀ i : ℕ, ∃! g : E0 × φ.A, g - i • (arith H.toHostRaw).frob H.d ∈ (arith H.toHostRaw).inertia H.d ∧ ¬ InPhi g := by
  intro φ H
  have hS := hostFactsS φ H
  have hI : ∀ x, x ∈ (arith H.toHostRaw).inertia H.d ↔ x = 0 ∨ x = sgc0 := hS.inertia_d
  refine ⟨hI, ?_, ?_⟩
  · have hd := H.toHostRaw.d_prime
    have hm : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
    have hN : H.condN = H.d ^ 1 * (H.QS * H.q) := by
      simp only [HostRaw.condN, pow_one]; ring
    haveI : NeZero H.condN := ⟨by simp only [HostRaw.condN]; exact Nat.mul_ne_zero hm hd.ne_zero⟩
    obtain ⟨-, h2⟩ := parts_of_eq hd hN H.d_not_dvd_QSq hm
    obtain ⟨h1, -⟩ := frobUnit_modEq (N := H.condN) hd
    rw [h2] at h1
    have hart := H.der.ps_d (frobUnit H.condN H.d) h1
    show Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (H.art (frobUnit H.condN H.d)).1.1) = 1
    rw [sgn2_toAdd_eq_ite, hart]
    decide
  · intro i
    set F := (arith H.toHostRaw).frob H.d
    rcases zmod_two_eq_zero_or_eq_one (i • F).1.1 with h | h
    · refine ⟨i • F + sgc0, ⟨?_, ?_⟩, ?_⟩
      · rw [hI]; right; abel
      · simp only [InPhi, sgc0, Prod.fst_add, h]; decide
      · rintro g ⟨hg, hg'⟩
        rw [hI] at hg
        rcases hg with hg | hg
        · exfalso; apply hg'
          have : g = i • F := sub_eq_zero.mp hg
          simp only [InPhi, this, h]
        · exact (sub_eq_iff_eq_add.mp hg).trans (add_comm _ _)
    · refine ⟨i • F, ⟨?_, ?_⟩, ?_⟩
      · rw [hI]; left; simp
      · simp only [InPhi, h]; decide
      · rintro g ⟨hg, hg'⟩
        rw [hI] at hg
        rcases hg with hg | hg
        · exact sub_eq_zero.mp hg
        · exfalso; apply hg'
          have : g = i • F + sgc0 := (sub_eq_iff_eq_add.mp hg).trans (add_comm _ _)
          simp only [InPhi, this, sgc0, Prod.fst_add, h]; decide
end UpperTheory.GL
