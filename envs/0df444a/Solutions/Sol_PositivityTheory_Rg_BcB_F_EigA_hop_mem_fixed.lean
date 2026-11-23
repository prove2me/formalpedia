-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.hop_mem_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:37.011643+00:00
-- url     : https://prove2.me/submissions/d9f98108-ec39-418b-ace6-4125537a5c4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_out_mk_inv
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_mem_fixed_iff
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_hop_apply
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_term_inv
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution {ρ : Representation ℂ G V} {K : Subgroup G} {g : G} [Finite (K ⧸ stabK K g)] {v : V}
    (hv : v ∈ fixed ρ K) : hop ρ K g v ∈ fixed ρ K := by
  letI := Fintype.ofFinite (K ⧸ stabK K g)
  rw [mem_fixed_iff]
  intro k hk
  rw [hop_apply, finsum_eq_sum_of_fintype, map_sum]
  let F : K → V := fun y => ρ (y : G) (ρ g v)
  have hF : ∀ x, ∀ h ∈ stabK K g, F (x * h) = F x := term_inv hv
  have step : ∀ q : K ⧸ stabK K g, ρ k (ρ ((q.out : K) : G) (ρ g v)) =
      F (((⟨k, hk⟩ : K) • q).out) := by
    intro q
    have hq : ((⟨k, hk⟩ : K) • q) = (((⟨k, hk⟩ : K) * q.out : K) : K ⧸ stabK K g) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, out_mk_inv _ F hF]
    simp only [F, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp only [step]
  exact Equiv.sum_comp (MulAction.toPerm (⟨k, hk⟩ : K)) (fun q : K ⧸ stabK K g => F q.out)
end PositivityTheory.Rg.BcB.F.EigA
