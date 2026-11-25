-- Prove2me | solution 1 for PI.ScRefExists.WF.dual_LA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:13:21.731687+00:00
-- url     : https://prove2.me/submissions/6bd13d55-2aab-4e88-83a7-eef456fee6e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Theorems.Thm_PI_ScRefExists_WF_osmul
import Theorems.Thm_PI_ScRefExists_WF_mem_LA_iff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScRefExists_WF_hG_add_left
import Theorems.Thm_PI_ScRefExists_WF_hG_smul_left
import Theorems.Thm_PI_ScRefExists_WF_hG_smul_right
import Theorems.Thm_PI_ScRefExists_WF_hG_zero_left
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
theorem _root_.solution (hp : p.Prime) {x : Fin I.n → I.E} (hx : ∀ y ∈ I.L, hG I y x ∈ Ap I p) : x ∈ LA I p := by
  classical
  obtain ⟨T, hT⟩ := I.L_fg
  have hden : ∀ t ∈ T, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * hG I t x = (a : I.E) := by
    intro t ht
    exact hx t (hT ▸ Submodule.subset_span ht)
  choose! s hs a ha using hden
  let S : ℕ := ∏ t ∈ T, s t
  have hS : Nat.Coprime S p := Nat.Coprime.prod_left fun t ht => hs t ht
  have key : ∀ y ∈ I.L, hG I y ((S : I.E) • x) ∈ (algebraMap (𝓞 I.E) I.E).range := by
    intro y hy
    rw [← hT] at hy
    induction hy using Submodule.span_induction with
    | mem t ht =>
      have hdvd : s t ∣ S := Finset.dvd_prod_of_mem s ht
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨(c : 𝓞 I.E) * a t, ?_⟩
      rw [hG_smul_right, hc]; push_cast
      rw [mul_comm ((s t : ℕ) : I.E), mul_assoc, ha t ht]
    | zero => exact ⟨0, by simp [hG_zero_left]⟩
    | add y z _ _ hy hz =>
      obtain ⟨o1, h1⟩ := hy; obtain ⟨o2, h2⟩ := hz
      exact ⟨o1 + o2, by rw [hG_add_left, ← h1, ← h2]; simp⟩
    | smul o y _ hy =>
      obtain ⟨o1, h1⟩ := hy
      refine ⟨PI.ScRefExists.TH.sg I o * o1, ?_⟩
      rw [osmul, hG_smul_left, ← h1]; simp [PI.ScRefExists.TH.sg_coe]
  have hSx : (S : I.E) • x ∈ I.L := (I.L_dual _).2 key
  exact (mem_LA_iff hp).2 ⟨S, hS, hSx⟩
end PI.ScRefExists.WF
