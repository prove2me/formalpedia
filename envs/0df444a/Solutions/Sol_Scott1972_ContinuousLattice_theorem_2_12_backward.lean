-- Prove2me | solution 1 for Scott1972.ContinuousLattice.theorem_2_12_backward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:42:36.553399+00:00
-- url     : https://prove2.me/submissions/41c75277-bdb7-48c1-ac38-84734abe5060

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Theorems.Thm_Scott1972_ContinuousLattice_idemFix_isContinuousLattice
import Theorems.Thm_Scott1972_ContinuousLattice_idemFix_scottTopology
import Theorems.Thm_Scott1972_ContinuousLattice_ScottMap_continuous
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_preservesDirectedSup
import Theorems.Thm_Scott1972_ContinuousLattice_preservesDirectedSup_monotone
import Theorems.Thm_Scott1972_ContinuousLattice_scottTopology_sierpinskiPower
import Theorems.Thm_Scott1972_ContinuousLattice_sierpinskiPower_isContinuousLattice
import Theorems.Thm_corollary_1_6


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
namespace Scott1972.ContinuousLattice
theorem _root_.solution {D : Type u} [TopologicalSpace D] [T0Space D]
    (hD : IsInjectiveSpace.{u, u} D) :
    ∃ (E : Type u) (inst : CompleteLattice E),
      @IsContinuousLattice E inst ∧
        Nonempty (@Homeomorph D E _ (@scottTopologicalSpace E inst)) := by
  obtain ⟨ι, ⟨R⟩⟩ := (corollary_1_6 D).1 hD
  -- `e = s ∘ r` on the Sierpiński power `L = ι → Prop`.
  have hidem : ∀ x, R.section' (R.retraction (R.section' (R.retraction x)))
      = R.section' (R.retraction x) :=
    fun x => congrArg R.section' (R.retraction_section (R.retraction x))
  have hL : IsContinuousLattice (ι → Prop) := sierpinskiPower_isContinuousLattice ι
  -- `e` is Scott-continuous: it is product-continuous (`s ∘ r`), and the Scott topology of the
  -- Sierpiński power is its product topology.
  have hcont_e : @Continuous (ι → Prop) (ι → Prop) scottTopologicalSpace scottTopologicalSpace
      (fun x => R.section' (R.retraction x)) := by
    rw [scottTopology_sierpinskiPower ι]
    exact R.section'.continuous.comp R.retraction.continuous
  have hsc : PreservesDirectedSup (fun x => R.section' (R.retraction x)) :=
    continuous_preservesDirectedSup hcont_e
  refine ⟨IdemFix (fun x => R.section' (R.retraction x)),
    IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc),
    idemFix_isContinuousLattice hidem hsc hL, ?_⟩
  -- The Scott topology of `IdemFix e` equals the subspace topology it inherits as a subtype of the
  -- Sierpiński power: both are `induced Subtype.val` of the (Scott = product) topology of `𝕆^I`.
  have heq : (@scottTopologicalSpace (IdemFix (fun x => R.section' (R.retraction x)))
      (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)))
      = instTopologicalSpaceSubtype := by
    rw [idemFix_scottTopology hidem hsc hL, scottTopology_sierpinskiPower ι]
    rfl
  rw [heq]
  -- the homeomorphism `D ≃ₜ IdemFix e`, with the subspace topology (where `Continuous.comp` works)
  have hfix : ∀ d, (fun x => R.section' (R.retraction x)) (R.section' d) = R.section' d :=
    fun d => congrArg R.section' (R.retraction_section d)
  exact ⟨{
    toFun := fun d => ⟨R.section' d, hfix d⟩
    invFun := fun k => R.retraction k.1
    left_inv := fun d => R.retraction_section d
    right_inv := fun k => Subtype.ext k.2
    continuous_toFun := by exact R.section'.continuous.subtype_mk hfix
    continuous_invFun := by exact R.retraction.continuous.comp continuous_subtype_val }⟩
end Scott1972.ContinuousLattice
