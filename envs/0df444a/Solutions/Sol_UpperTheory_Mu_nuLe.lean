-- Prove2me | solution 1 for UpperTheory.Mu.nuLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:44:59.286387+00:00
-- url     : https://prove2.me/submissions/5386c096-521d-49f8-a43d-6adb416604ae

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TotientLeOfCycPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuSumApprox
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_HostApprox
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_NuLe
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_two_dvd_QS
import Theorems.Thm_Formalism_HC_HostRaw_two_dvd_condN
import Theorems.Thm_KStar_Tree_exists_unit_not_dvd
import Theorems.Thm_KStar_Tree_nuOf_le_of_approx
import Theorems.Thm_UpperTheory_Mu_hostApprox
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
open NumberField Formalism.HC KStar.Tree
namespace UpperTheory.Mu
theorem _root_.solution :
    ∀ (φ : Frame) (H : HostRaw φ) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (n : ℕ), Odd n → l ≠ H.q → l ≠ H.d → nuOf l (cyc l H.E Ω) n ≤ H.QS.factorization l + (if l ∣ H.QS then n.factorization l else 0) := by
  intro φ H l _ Ω _ _ _ n hn hq hd
  have hQS0 : H.QS ≠ 0 := H.QS_pos.ne'
  obtain ⟨u, hu1, hun⟩ := exists_unit_not_dvd l H.QS n hQS0 H.two_dvd_QS hn
  apply nuOf_le_of_approx l (cyc l H.E Ω) n _ u _ hun
  have hN : H.condN = H.QS * H.q * H.d := rfl
  have hfac : H.condN.factorization l = H.QS.factorization l := by
    have hq0 : H.q ≠ 0 := H.q_prime.ne_zero
    have hd0 : H.d ≠ 0 := H.d_prime.ne_zero
    rw [hN, Nat.factorization_mul (mul_ne_zero hQS0 hq0) hd0, Nat.factorization_mul hQS0 hq0]
    simp only [Finsupp.add_apply]
    rw [H.q_prime.factorization, H.d_prime.factorization]
    simp [Finsupp.single_apply, Ne.symm hq, Ne.symm hd]
  have h2 : 2 ≤ H.condN := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero H.condN_ne_zero) H.two_dvd_condN
    exact this
  haveI : Fact (1 < H.condN) := ⟨by omega⟩
  intro k
  apply UpperTheory.Mu.hostApprox φ H l Ω 1 (map_one _) u _ k
  rw [hfac]
  simpa [ZMod.val_one] using hu1
end UpperTheory.Mu
