-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.exists_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:19.678949+00:00
-- url     : https://prove2.me/submissions/e5b69da6-5344-4c4f-b1c3-edb298ec2911

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_finite_resK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_resK_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finite_resK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_resK_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
variable {p} {K}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) :
    ∃ f : ℕ, 0 < f ∧ qK p L = qK p K ^ f ∧ ∃ ω : Fin f → Obar p, (∀ j, (ω j : PadicAlgCl p) ∈ L) ∧
      LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i)) := by
  have hfL : Finite (resK p L) := finite_resK L hL
  have hfW : Finite (resMod hKL) := hfL
  have hMF : Module.Finite (resK p K) (resMod hKL) := Module.Finite.of_finite
  have hcard : Nat.card (resMod hKL) = Nat.card (resK p K) ^ Module.finrank (resK p K) (resMod hKL) :=
    Module.natCard_eq_pow_finrank
  have hnt : Nontrivial (resMod hKL) :=
    ⟨⟨⟨1, (resK p L).one_mem⟩, 0, fun h => one_ne_zero (congrArg Subtype.val h)⟩⟩
  refine ⟨Module.finrank (resK p K) (resMod hKL), Module.finrank_pos, hcard, ?_⟩
  let B := Module.finBasis (resK p K) (resMod hKL)
  have hex : ∀ i, ∃ x : Obar p, (x : PadicAlgCl p) ∈ L ∧ res x = (B i : kbar p) :=
    fun i => (mem_resK_iff L _).1 (B i).2
  choose ω h1 h2 using hex
  refine ⟨ω, h1, ?_⟩
  have h3 : (fun i => IsLocalRing.residue (Obar p) (ω i)) = (resMod hKL).subtype ∘ B := by
    funext i; exact h2 i
  rw [h3]
  exact B.linearIndependent.map' _ (Submodule.ker_subtype _)
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
