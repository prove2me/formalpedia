-- Prove2me | solution 1 for QEC.Coding.FiniteSymplectic.exists_mem_orthogonal_pairing_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:58:42.109203+00:00
-- url     : https://prove2.me/submissions/a281570b-c415-4e3c-b424-348ff18364ed

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_isAlt
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_nondegenerate

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u v
open QEC.Coding.FiniteSymplectic
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteSymplectic
theorem _root_.solution
    (S : Submodule F (SymplecticVector F ι))
    {e : SymplecticVector F ι}
    (_heOrthogonal : e ∈ (form (F := F) (ι := ι)).orthogonal S)
    (he : e ∉ S) :
    ∃ f, f ∈ (form (F := F) (ι := ι)).orthogonal S ∧ form e f ≠ 0 := by
  by_contra h
  push Not at h
  have heDouble :
      e ∈ (form (F := F) (ι := ι)).orthogonal
        ((form (F := F) (ι := ι)).orthogonal S) := by
    intro f hf
    exact form_isAlt.isRefl e f (h f hf)
  have heS : e ∈ S := by
    rw [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate
      form_isAlt.isRefl S] at heDouble
    exact heDouble
  exact he heS
end QEC.Coding.FiniteSymplectic
