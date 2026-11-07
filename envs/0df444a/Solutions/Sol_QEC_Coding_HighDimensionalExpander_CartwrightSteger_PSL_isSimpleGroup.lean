-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_isSimpleGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:04:43.255196+00:00
-- url     : https://prove2.me/submissions/5c07d40e-01de-4a48-be80-e7c07d8d28c6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialLinearGroup_commutator_eq_top
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialToProjective_eq_one_of_fixed_projective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_abstractSpecialLinearToPSL_surjective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionPSL_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsSimpleGroup (PSL P r level) := by
  letI : Nontrivial (PSL P r level) :=
    (CongruenceLifting.residueTransvectionPSL_injective
      P r level).nontrivial
  refine ⟨?_⟩
  intro H hH
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  right
  let φ := abstractSpecialLinearToPSL P r level
  let N := H.comap φ
  letI : H.Normal := hH
  letI : N.Normal := inferInstance
  have hfixed : MulAction.fixedPoints N
      (ℙ (ResidueField P r level)
        (Fin r.matrixRank → ResidueField P r level)) ≠ Set.univ := by
    intro hall
    apply hbot
    apply bot_unique
    intro g hg
    obtain ⟨a, rfl⟩ := abstractSpecialLinearToPSL_surjective P r level g
    have haN : a ∈ N := hg
    have hafix : ∀ x : ℙ (ResidueField P r level)
        (Fin r.matrixRank → ResidueField P r level), a • x = x := by
      intro x
      exact (MulAction.mem_fixedPoints.mp
        (Set.eq_univ_iff_forall.mp hall x)) ⟨a, haN⟩
    let s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
      Matrix.SpecialLinearGroup.toLin'_equiv.symm a
    have hsfix : ∀ x : ℙ (ResidueField P r level)
        (Fin r.matrixRank → ResidueField P r level), s • x = x := by
      intro x
      rw [Projectivization.matrixSpecialLinearGroup_smul_def]
      simpa [s] using hafix x
    have hsone := specialToProjective_eq_one_of_fixed_projective
      P r level s hsfix
    apply Subtype.ext
    simpa [φ, abstractSpecialLinearToPSL, specialLinearToPSL, s] using hsone
  have hcomm : commutator
      (SpecialLinearGroup (ResidueField P r level)
        (Fin r.matrixRank → ResidueField P r level)) = ⊤ := by
    letI : Group.IsPerfect
        (Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ResidueField P r level)) :=
      ⟨specialLinearGroup_commutator_eq_top r⟩
    let e : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) ≃*
        SpecialLinearGroup (ResidueField P r level)
          (Fin r.matrixRank → ResidueField P r level) :=
      Matrix.SpecialLinearGroup.toLin'_equiv
    letI : Group.IsPerfect
        (SpecialLinearGroup (ResidueField P r level)
          (Fin r.matrixRank → ResidueField P r level)) :=
      Group.IsPerfect.ofSurjective
        (f := e.toMonoidHom) e.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hcomm_le := (specialLinearIwasawaStructure r).commutator_le N hfixed
  rw [hcomm] at hcomm_le
  have hNtop : N = ⊤ := top_unique hcomm_le
  apply top_unique
  intro g hg
  obtain ⟨a, rfl⟩ := abstractSpecialLinearToPSL_surjective P r level g
  have ha : a ∈ N := by
    rw [hNtop]
    exact Subgroup.mem_top a
  exact ha
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
