-- Prove2me | solution 1 for P2M_GlobalTheory_FiniteGL_signGL__cuspidal_fcc895e2b0eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:43.308518+00:00
-- url     : https://prove2.me/submissions/2d646883-38c4-44a2-9d2a-1e7811f9e896

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Theorems.Thm_GlobalTheory_FiniteGL_mem_unipRadical
import Theorems.Thm_GlobalTheory_FiniteGL_isCuspidal_iff_twoBlocks
import Theorems.Thm_GlobalTheory_FiniteGL_genericLine_apply
import Theorems.Thm_GlobalTheory_FiniteGL_mirabInduced_apply
import Theorems.Thm_GlobalTheory_FiniteGL_restrictMirab_apply
import Theorems.Thm_GlobalTheory_FiniteGL_lineRep_apply
import Theorems.Thm_GlobalTheory_FiniteGL_lineRep_isIrreducible
import Theorems.Thm_P2M_GlobalTheory_FiniteGL_signGL__transv_06c297012854
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteGL.genericLine_apply
attribute [local simp] GlobalTheory.FiniteGL.mirabInduced_apply
attribute [local simp] GlobalTheory.FiniteGL.restrictMirab_apply

set_option autoImplicit false
noncomputable section
open Matrix Formalism.EigenvalueLevelCeiling Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.FiniteGL
namespace GlobalTheory.FiniteGL
theorem _root_.solution : (lineRep signGL₂).IsIrreducible ∧ IsCuspidal (lineRep signGL₂) := by
  refine ⟨lineRep_isIrreducible _, (isCuspidal_iff_twoBlocks _).mpr fun a ha0 ha2 v hv => ?_⟩
  obtain rfl : a = 1 := by omega
  have hmem : transvGL₂ ∈ unipRadical (ZMod 2) (twoBlocks 2 1) := by
    rw [mem_unipRadical]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [twoBlocks, transvGL₂]
  have h := hv transvGL₂ hmem
  rw [lineRep_apply, signGL₂_transv] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul] at hi
  simp only [Pi.zero_apply]
  linear_combination (-1 / 2 : ℂ) * hi
end GlobalTheory.FiniteGL
