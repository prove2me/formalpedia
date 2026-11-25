-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.isPrecomplete_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:49.352038+00:00
-- url     : https://prove2.me/submissions/1e891d47-b61a-403a-a04b-16d49e417606

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_smul_top_self
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_mem_pow_smul_top_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {p : ℕ} [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] M) : IsPrecomplete (maximalIdeal ℤ_[p]) M := by
  rw [isPrecomplete_iff]
  intro F hF
  have hP := (inferInstance : IsPrecomplete (maximalIdeal ℤ_[p]) ℤ_[p])
  rw [isPrecomplete_iff] at hP
  have hc : ∀ i, ∃ L : ℤ_[p], ∀ k, b.repr (F k) i ≡ L
      [SMOD ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] ℤ_[p])] := by
    intro i
    refine hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_
    have := hF hmn
    rw [SModEq.sub_mem, mem_pow_smul_top_iff b] at this
    rw [SModEq.sub_mem, smul_top_self]
    simpa using this i
  choose L hL using hc
  refine ⟨∑ i, L i • b i, fun k => ?_⟩
  rw [SModEq.sub_mem, mem_pow_smul_top_iff b]
  intro i
  have := hL i k
  rw [SModEq.sub_mem, smul_top_self] at this
  have hr : b.repr (∑ j, L j • b j) i = L i := by
    have h := congrFun (b.equivFun.apply_symm_apply L) i
    rwa [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at h
  rw [map_sub, Finsupp.sub_apply, hr]
  exact this
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
