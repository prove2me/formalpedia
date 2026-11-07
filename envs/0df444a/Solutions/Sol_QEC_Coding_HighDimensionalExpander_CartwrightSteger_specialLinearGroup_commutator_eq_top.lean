-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialLinearGroup_commutator_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:46:57.095335+00:00
-- url     : https://prove2.me/submissions/06fb8196-cde9-40ce-9517-53f7bbcf7a9d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialTransvection_mem_commutator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    {K : Type*} [Field K] (r : Rank) :
    commutator (Matrix.SpecialLinearGroup (Fin r.matrixRank) K) = ⊤ := by
  apply top_unique
  intro g hg
  let Q : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K → Prop :=
    fun M ↦ ∃ hdet : Matrix.det M = 1,
      (⟨M, hdet⟩ : Matrix.SpecialLinearGroup (Fin r.matrixRank) K) ∈
        commutator (Matrix.SpecialLinearGroup (Fin r.matrixRank) K)
  have htrans : ∀ t : Matrix.TransvectionStruct
      (Fin r.matrixRank) K, Q t.toMatrix := by
    intro t
    refine ⟨Matrix.det_transvection_of_ne t.i t.j t.hij t.c, ?_⟩
    change specialTransvection t.i t.j t.hij t.c ∈
      commutator (Matrix.SpecialLinearGroup (Fin r.matrixRank) K)
    exact specialTransvection_mem_commutator r t.i t.j t.hij t.c
  have hmul : ∀ A B, Q A → Q B → Q (A * B) := by
    rintro A B ⟨hA, hAmem⟩ ⟨hB, hBmem⟩
    have hdet : Matrix.det (A * B) = 1 := by
      rw [Matrix.det_mul, hA, hB, one_mul]
    refine ⟨hdet, ?_⟩
    have hprod :=
      (commutator (Matrix.SpecialLinearGroup
        (Fin r.matrixRank) K)).mul_mem hAmem hBmem
    exact hprod
  have hQ : Q (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K) := by
    apply Matrix.diagonal_transvection_induction Q
    · intro D hD
      have hdet : Matrix.det (Matrix.diagonal D) = 1 := hD.trans g.prop
      cases r with
      | three =>
          exact CongruenceLifting.property_fin3_diagonal
            Q htrans hmul D hdet
      | four =>
          exact CongruenceLifting.property_fin4_diagonal
            Q htrans hmul D hdet
    · exact htrans
    · exact hmul
  obtain ⟨hdet, hmem⟩ := hQ
  have heq :
      (⟨(g : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K), hdet⟩ :
        Matrix.SpecialLinearGroup (Fin r.matrixRank) K) = g := by
    rfl
  rw [← heq]
  exact hmem
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
