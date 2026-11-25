-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.up_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:53:39.845614+00:00
-- url     : https://prove2.me/submissions/87348bcc-1e75-4c0b-b4c4-b30dc05522ac

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Theorems.Thm_ReciprocityTheory_PGsh_Up_ht_cp_surj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_domain
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_cp_ne
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_E
import Theorems.Thm_ReciprocityTheory_PGsh_Up_cj_cj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_ht_block_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) :
    ∀ m : cokE H.Ht U.εT U.εL (U.cj i) i, cp • m = 0 := by
  haveI := htd_domain hS
  obtain ⟨hEt, hdiag, hdet⟩ := htd_E H
  have hsumL : ∑ k, (U.εL k)ᵀ = 1 := by
    rw [← Matrix.transpose_sum, U.εL_sum, Matrix.transpose_one]
  have key1 : H.Ht * U.εT i = (U.εL (U.cj i))ᵀ * H.Ht * U.εT i := by
    conv_lhs => rw [← Matrix.one_mul H.Ht, ← hsumL, Matrix.sum_mul, Matrix.sum_mul]
    rw [Finset.sum_eq_single (U.cj i)]
    · intro k _ hk
      apply ht_block_zero hS H U
      intro h
      apply hk
      rw [← h, cj_cj hS U]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have key2 : (U.εL (U.cj i))ᵀ * H.Ht * U.εT i = (U.εL (U.cj i))ᵀ * H.Ht := by
    conv_rhs => rw [← Matrix.mul_one ((U.εL (U.cj i))ᵀ * H.Ht), ← U.εT_sum, Matrix.mul_sum]
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      apply ht_block_zero hS H U
      rw [cj_cj hS U]
      exact fun h => hj h.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  intro m
  refine Submodule.Quotient.induction_on _ m fun x => ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
  obtain ⟨t, ht⟩ := ht_cp_surj H.Ht H.Bt _ cp hEt hdiag hdet (htd_cp_ne hS) H.form_eq_alt y
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, Submodule.mem_map,
    LinearMap.mem_range]
  refine ⟨U.εT i *ᵥ t, ⟨t, rfl⟩, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  rw [key1, key2, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul]
end ReciprocityTheory.PGsh.Up
