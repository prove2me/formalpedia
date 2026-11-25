-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.latDeg_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:10.248838+00:00
-- url     : https://prove2.me/submissions/3c16fdd9-e67c-4bd8-9088-a3dd24adf6fc

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_spanIdx_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (C B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (hCB : C ≤ B) (hB : B.FG) (hbC : IsKBasisIn C b)
    (hbB : IsKBasisIn B b) : latDeg H C b ≤ latDeg H B b := by
  have hSC : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup ≤ C.toAddSubgroup := by
    intro x hx
    exact (Submodule.span_le.mpr (Set.range_subset_iff.mpr hbC.1)) hx
  have hCB' : C.toAddSubgroup ≤ B.toAddSubgroup := fun x hx => hCB hx
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hSC hCB'
  have hne : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 :=
    spanIdx_ne_zero B b hB hbB
  have h1 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex C.toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hne) ⟨_, hmul.symm⟩
  have h2 : 0 < (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex C.toAddSubgroup := by
    refine Nat.pos_of_ne_zero fun h => hne ?_
    rw [← hmul, h, zero_mul]
  unfold latDeg
  have h3 : Real.log (((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex
      C.toAddSubgroup : ℕ) : ℝ) ≤ Real.log (((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex
      B.toAddSubgroup : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast h2) (by exact_mod_cast h1)
  linarith
end ReciprocityTheory.MultiplicativeHeights.SemiPt
