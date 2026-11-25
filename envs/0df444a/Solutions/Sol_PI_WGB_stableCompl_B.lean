-- Prove2me | solution 1 for PI.WGB.stableCompl_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:52.289033+00:00
-- url     : https://prove2.me/submissions/be145ca2-8def-4b17-ab0b-b6b26a3a0ba6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Theorems.Thm_PI_WGB_fockF_smul_left_B
import Theorems.Thm_PI_WGB_fd_B
import Theorems.Thm_PI_WGB_embGL_gStarB
import Theorems.Thm_PI_WGB_sqAct_mem_B
import Theorems.Thm_PI_WGB_fock_sqAct_adj_B
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution : StableCompl := by
  intro n N h lam W hW hstab
  classical
  let W' : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
    { carrier := {f | f ∈ nablaSq ℂ N lam ∧ ∀ w ∈ W, Formalism.REAL.fockF f w = 0}
      add_mem' := fun {a b} ha hb => ⟨(nablaSq ℂ N lam).add_mem ha.1 hb.1, fun w hw => by
        rw [fockF_add_left_B, ha.2 w hw, hb.2 w hw, add_zero]⟩
      zero_mem' := ⟨(nablaSq ℂ N lam).zero_mem, fun w _ => by simp [Formalism.REAL.fockF]⟩
      smul_mem' := fun c a ha => ⟨(nablaSq ℂ N lam).smul_mem c ha.1, fun w hw => by
        rw [fockF_smul_left_B, ha.2 w hw, mul_zero]⟩ }
  have hW'V : W' ≤ nablaSq ℂ N lam := fun f hf => hf.1
  refine ⟨W', hW'V, ?_, ?_, ?_⟩
  · intro g f hf
    refine ⟨sqAct_mem_B lam _ f hf.1, fun w hw => ?_⟩
    rw [fock_sqAct_adj_B, ← embGL_gStarB]
    exact hf.2 _ (hstab (gStarB g) w hw)
  · apply le_antisymm (sup_le hW hW'V)
    intro f hf
    letI := coreB lam
    letI : NormedAddCommGroup (nablaSq ℂ N lam) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    letI : InnerProductSpace ℂ (nablaSq ℂ N lam) := InnerProductSpace.ofCore (coreB lam).toCore
    haveI : FiniteDimensional ℂ (nablaSq ℂ N lam) := fd_B N lam
    let K : Submodule ℂ (nablaSq ℂ N lam) := W.comap (nablaSq ℂ N lam).subtype
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq K K.orthogonal
    rw [Submodule.inf_orthogonal_eq_bot, finrank_bot, add_zero, Submodule.finrank_add_finrank_orthogonal] at h1
    have hs : K ⊔ K.orthogonal = ⊤ := Submodule.eq_top_of_finrank_eq h1
    have hmem : (⟨f, hf⟩ : nablaSq ℂ N lam) ∈ K ⊔ K.orthogonal := by
      rw [hs]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    rw [Submodule.mem_sup]
    refine ⟨(a : MvPolynomial (Fin N × Fin N) ℂ), ha, (b : MvPolynomial (Fin N × Fin N) ℂ),
      ⟨b.2, fun w hw => ?_⟩, ?_⟩
    · exact (Submodule.mem_orthogonal K b).mp hb ⟨w, hW hw⟩ hw
    · have hv := congrArg Subtype.val hab
      simpa using hv
  · rw [eq_bot_iff]
    intro f hf
    obtain ⟨hfW, hfW'⟩ := Submodule.mem_inf.mp hf
    have h0 : Formalism.REAL.fockF f f = 0 := hfW'.2 f hfW
    rw [Submodule.mem_bot]
    by_contra hne
    have hpos := (Formalism.GradedWeylDivisibility.fockPos _ f hne).1
    rw [h0] at hpos
    simp at hpos
end PI.WGB
