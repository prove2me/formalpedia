-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.finrank_fixed_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:25:36.276516+00:00
-- url     : https://prove2.me/submissions/c8e94889-6d36-4434-b53c-20ad89cbbf67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_hop_mem_fixed
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_hop_comm
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_finite_quot
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_fixed_simple
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
theorem _root_.solution {K : Subgroup G} (hK : GelPair K) (ρ : Representation ℂ G V)
    (hirr : ρ.IsIrreducible) (hne : fixed ρ K ≠ ⊥) [FiniteDimensional ℂ (fixed ρ K)] :
    Module.finrank ℂ (fixed ρ K) = 1 := by
  classical
  haveI : Nontrivial (fixed ρ K) := (Submodule.nontrivial_iff_ne_bot).2 hne
  haveI : ∀ g, Finite (K ⧸ stabK K g) := finite_quot hK
  let T : G → Module.End ℂ (fixed ρ K) := fun g => (hop ρ K g).restrict fun _ hv => hop_mem_fixed hv
  have hT : ∀ g (x : fixed ρ K), ((T g x : fixed ρ K) : V) = hop ρ K g x := fun _ _ => rfl

  have hscal : ∀ g : G, ∃ c : ℂ, ∀ x : fixed ρ K, T g x = c • x := by
    intro g
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T g)
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    let E : Submodule ℂ (fixed ρ K) := LinearMap.ker (T g - c • 1)
    have hmemE : ∀ w, w ∈ E ↔ T g w = c • w := fun w => by
      simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero]
    have hvE : v ∈ E := (hmemE v).2 hv.apply_eq_smul
    have hEne : E ≠ ⊥ := fun hb => hv.2 (by rw [hb] at hvE; exact (Submodule.mem_bot ℂ).1 hvE)
    have hEst : ∀ h : G, ∀ w : fixed ρ K, w ∈ E → ∀ y : fixed ρ K, (y : V) = hop ρ K h w → y ∈ E := by
      intro h w hw y hy
      rw [hmemE] at hw ⊢
      apply Subtype.ext
      have hw' : hop ρ K g (w : V) = c • (w : V) := by rw [← hT]; exact congrArg Subtype.val hw
      rw [hT, hy, Submodule.coe_smul, hy, hop_comm hK ρ g h w.2, hw', map_smul]
    have hEtop := fixed_simple hK ρ hirr E hEne hEst
    refine ⟨c, fun x => ?_⟩
    have hx : x ∈ E := hEtop ▸ Submodule.mem_top
    exact (hmemE x).1 hx
  obtain ⟨x0, hx0⟩ := exists_ne (0 : fixed ρ K)
  let L : Submodule ℂ (fixed ρ K) := ℂ ∙ x0
  have hLne : L ≠ ⊥ := by
    intro hb
    have : x0 ∈ L := Submodule.mem_span_singleton_self x0
    rw [hb, Submodule.mem_bot] at this
    exact hx0 this
  have hLst : ∀ h : G, ∀ w : fixed ρ K, w ∈ L → ∀ y : fixed ρ K, (y : V) = hop ρ K h w → y ∈ L := by
    intro h w hw y hy
    obtain ⟨c, hc⟩ := hscal h
    have : y = c • w := by
      apply Subtype.ext
      rw [hy, ← hT, hc]
    rw [this]
    exact L.smul_mem c hw
  have hLtop := fixed_simple hK ρ hirr L hLne hLst
  rw [← finrank_top ℂ (fixed ρ K), ← hLtop, finrank_span_singleton hx0]
end PositivityTheory.Rg.BcB.F.EigA
