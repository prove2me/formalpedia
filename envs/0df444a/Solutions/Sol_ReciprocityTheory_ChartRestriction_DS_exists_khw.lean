-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.exists_khw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:53.277601+00:00
-- url     : https://prove2.me/submissions/581ba38f-26c7-4995-8a9b-0c4f1d41b6e7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_Lemmata_SimultaneousEigenvectors_BlSimeig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kUnit_weight_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kUnit_exists_joint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kUnit_eig_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kUnitWtLin_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hA : IsGlRep A) (hU : IsKUnitary ε A) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w := by
  classical
  have hSc : ∀ c, ∀ v ∈ S, A c c v ∈ S := fun c => hS c c rfl
  let P : Set (Fin n → ℝ) := {μ | ∃ w ∈ S, w ≠ 0 ∧ ∀ c, A c c w = (μ c : ℂ) • w}
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (r : ℂ)})
      (fun c => (Module.End.finite_hasEigenvalue _).preimage
        (Complex.ofReal_injective.injOn))).subset ?_
    rintro μ ⟨w, hw, hw0, hμ⟩ c -
    show Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (μ c : ℂ)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa using hμ c)
    · intro h
      exact hw0 (congrArg Subtype.val h)
  have hPne : P.Nonempty := by
    obtain ⟨w, hw, hw0, z, hz⟩ := kUnit_exists_joint hA Finset.univ S hfd hSc hne
    refine ⟨fun c => (z c).re, w, hw, hw0, fun c => ?_⟩
    rw [hz c (Finset.mem_univ c)]
    congr 1
    exact kUnit_eig_real hU hw0 (hz c (Finset.mem_univ c))
  obtain ⟨μ, ⟨w, hw, hw0, hμ⟩, hmax⟩ := Set.exists_max_image P kUnitWtLin hPfin hPne
  refine ⟨w, hw, hw0, μ, hμ, ?_⟩
  intro a b hab hεab
  by_contra h
  have hmem : (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) ∈ P :=
    ⟨A a b w, hS a b hεab w hw, h, fun c => kUnit_weight_shift hA hμ (ne_of_lt hab) c⟩
  exact absurd (hmax _ hmem) (not_le.mpr (kUnitWtLin_shift μ hab))
end ReciprocityTheory.ChartRestriction.DS
