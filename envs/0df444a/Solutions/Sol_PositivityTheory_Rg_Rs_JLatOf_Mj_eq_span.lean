-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.Mj_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:37.297047+00:00
-- url     : https://prove2.me/submissions/bcc6a296-f572-4027-a4a1-68afea26f756

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.JLatOf
open PositivityTheory.Rg.Rs
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.Rg.Rs.JLatOf
theorem _root_.solution (N j m : ℕ) (h : m + j = N) :
    Mj k N j = Submodule.span k (Set.range (ej (k := k) N j m h)) := by
  apply le_antisymm
  · intro x hx
    have hx' : x = ∑ i : Fin m, x ⟨j + i, by omega⟩ • ej (k := k) N j m h i := by
      ext a
      simp only [Finset.sum_apply, Pi.smul_apply, ej, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases ha : (a : ℕ) < j
      · rw [hx a ha]
        symm
        apply Finset.sum_eq_zero
        intro i _
        rw [if_neg]
        intro hai
        rw [hai] at ha
        simp at ha
      · rw [Finset.sum_eq_single (⟨(a : ℕ) - j, by omega⟩ : Fin m)]
        · rw [if_pos (Fin.ext (by simp; omega))]
          congr 1
          exact Fin.ext (by simp; omega)
        · intro i _ hi
          rw [if_neg]
          intro hai
          apply hi
          have h3 := congrArg Fin.val hai
          simp at h3
          exact Fin.ext (by simp; omega)
        · intro hne
          exact absurd (Finset.mem_univ _) hne
    rw [hx']
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ a ha
    have hne : a ≠ ⟨j + i, by omega⟩ := by
      intro he
      rw [he] at ha
      simp at ha
    simp [ej, Pi.single_apply, hne]
end PositivityTheory.Rg.Rs.JLatOf
