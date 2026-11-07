-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.inv_mem_lpsQuaternionGeneratorsPSL_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:37:52.366911+00:00
-- url     : https://prove2.me/submissions/cca2e752-9fb1-4df8-8024-c02df35ade59

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_conj_mem_lpsQuaternionShell_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionPSL_conj_eq_inv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) {g : PSL(2, ZMod a.q)}
    (hg : g ∈ lpsQuaternionGeneratorsPSL a) :
    g⁻¹ ∈ lpsQuaternionGeneratorsPSL a := by
  classical
  rw [lpsQuaternionGeneratorsPSL] at hg ⊢
  rcases Finset.mem_image.mp hg with ⟨t, ht, rfl⟩
  let tc : {u // u ∈ lpsQuaternionShell p} :=
    ⟨t.1.conj, (conj_mem_lpsQuaternionShell_iff
      a.degreePrime.pos t.1).mpr t.2⟩
  refine Finset.mem_image.mpr ⟨tc, Finset.mem_attach _ tc, ?_⟩
  simpa [tc] using lpsQuaternionPSL_conj_eq_inv a t.1
    (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)
end QEC.Coding.TannerLiftedProduct
