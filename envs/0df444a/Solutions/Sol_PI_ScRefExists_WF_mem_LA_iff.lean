-- Prove2me | solution 1 for PI.ScRefExists.WF.mem_LA_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:54:29.968792+00:00
-- url     : https://prove2.me/submissions/cc053b77-5626-4e57-bb1f-20f12977b46a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Theorems.Thm_PI_ScRefExists_WF_ap_smul
import Theorems.Thm_PI_ScRefExists_WF_osmul
import Theorems.Thm_PI_ScRefExists_WF_natsmul_mem_L
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScRefExists_WF_inv_mem_Ap
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
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}
namespace PI.ScRefExists.WF
theorem _root_.solution (hp : p.Prime) {x : Fin I.n → I.E} :
    x ∈ LA I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • x ∈ I.L := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using hx⟩
    | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
      have : ((s * t : ℕ) : I.E) • (x + y) = (t : I.E) • ((s : I.E) • x) + (s : I.E) • ((t : I.E) • y) := by
        push_cast; module
      rw [this]
      exact I.L.add_mem (natsmul_mem_L hsx) (natsmul_mem_L hty)
    | smul a x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨s0, hs0, a0, ha0⟩ := a.2
      refine ⟨s0 * s, Nat.Coprime.mul_left hs0 hs, ?_⟩
      have : ((s0 * s : ℕ) : I.E) • (a • x) = a0 • ((s : I.E) • x) := by
        rw [ap_smul, osmul, ← ha0]; push_cast; module
      rw [this]
      exact I.L.smul_mem _ hsx
  · rintro ⟨s, hs, hsx⟩
    have hsA : ((s : I.E))⁻¹ ∈ Ap I p := inv_mem_Ap hp hs
    have hs0 : (s : I.E) ≠ 0 := by
      have : s ≠ 0 := by
        rintro rfl
        exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs)
      exact_mod_cast this
    have : x = (⟨_, hsA⟩ : Ap I p) • ((s : I.E) • x) := by
      rw [ap_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
end PI.ScRefExists.WF
