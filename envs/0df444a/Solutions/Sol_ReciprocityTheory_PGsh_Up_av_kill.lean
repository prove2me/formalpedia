-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.av_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:34:37.222802+00:00
-- url     : https://prove2.me/submissions/f0f6ded6-e1b5-4e11-ad74-007495021139

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Theorems.Thm_ReciprocityTheory_PGsh_Up_ht_cp_surj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_domain
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_cp_ne
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_E

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
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) (a b : O) (hab : σ b = a) :
    ∀ m : htCoker H a b, cp • m = 0 := by
  haveI := htd_domain hS
  obtain ⟨hEt, hdiag, hdet⟩ := htd_E H
  intro m
  refine Submodule.Quotient.induction_on _ m fun x => ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
  obtain ⟨t, ht⟩ := ht_cp_surj H.Ht H.Bt _ cp hEt hdiag hdet (htd_cp_ne hS) H.form_eq_alt y
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, Submodule.mem_map,
    tPart, LinearMap.mem_range]
  refine ⟨(H.ρ b).map (algebraMap ℤ_[p] R) *ᵥ t, ⟨t, rfl⟩, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, H.Ht_equivariant.1 b, hab]
  rw [← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul]
end ReciprocityTheory.PGsh.Up
