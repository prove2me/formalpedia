-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.lenIdB_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:18.098455+00:00
-- url     : https://prove2.me/submissions/0bfdcef8-a3a7-4efe-b6ed-4cff7aa08bc2

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFromRowsMulVecIff
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Theorems.Thm_ReciprocityTheory_PGsh_Up_P_fix
import Theorems.Thm_ReciprocityTheory_PGsh_Up_matU_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_Up_matV_matU
import Theorems.Thm_ReciprocityTheory_PGsh_Up_matU_matV
import Theorems.Thm_ReciprocityTheory_PGsh_Up_cok_kill
import Theorems.Thm_ReciprocityTheory_PGsh_Up_exists_fromRows_mulVec_iff
import Theorems.Thm_ReciprocityTheory_PGsh_Up_hasLen_of_equiv


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
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hPL : DualLenStatement) : LenIdBStatement := by
  intro C _ v R _ _ hv g m Ht Bt E cp hcp hE hform εT εL π hπ hTo hTs hLo hLs hHt hBt hadj i d hd
    c₁ hc₁
  haveI : IsDomain R := Function.Injective.isDomain _ hv.hom_inj
  obtain ⟨φ⟩ := hd
  have hP : εL i * εL i = εL i := by rw [hLo, if_pos rfl]
  set U := matU (εL i) φ with hU
  set V := matV (εL i) φ with hV
  have hVU : V * U = 1 := matV_matU (εL i) hP φ
  have hUV : U * V = εL i := matU_matV (εL i) φ
  have hHtT : (εT (π i))ᵀ * Htᵀ = Htᵀ * εL i := by
    have h := congrArg transpose (hHt (π i))
    rw [hπ i, transpose_mul, transpose_mul, transpose_transpose] at h
    exact h
  set A : Matrix (Fin d) (Ix g) R := Uᵀ * Ht * εT (π i) with hA
  have hmemT : ∀ w, Vᵀ *ᵥ w ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) := by
    intro w
    refine ⟨Vᵀ *ᵥ w, ?_⟩
    show (εL i)ᵀ *ᵥ (Vᵀ *ᵥ w) = Vᵀ *ᵥ w
    rw [mulVec_mulVec, ← transpose_mul, ← hUV, ← Matrix.mul_assoc, hVU, Matrix.one_mul]
  have hfixT : ∀ f ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ), (εL i)ᵀ *ᵥ f = f := by
    rintro f ⟨z, rfl⟩
    show (εL i)ᵀ *ᵥ ((εL i)ᵀ *ᵥ z) = (εL i)ᵀ *ᵥ z
    rw [mulVec_mulVec, ← transpose_mul, hP]
  let ψ : LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) ≃ₗ[R] (Fin d → R) :=
    { toFun := fun f => Uᵀ *ᵥ (f : Fin g → R)
      invFun := fun y => ⟨Vᵀ *ᵥ y, hmemT y⟩
      map_add' := fun f f' => by simp [mulVec_add]
      map_smul' := fun a f => by simp [mulVec_smul]
      left_inv := fun f => by
        apply Subtype.ext
        show Vᵀ *ᵥ (Uᵀ *ᵥ (f : Fin g → R)) = f
        rw [mulVec_mulVec, ← transpose_mul, hUV, hfixT f f.2]
      right_inv := fun y => by
        show Uᵀ *ᵥ (Vᵀ *ᵥ y) = y
        rw [mulVec_mulVec, ← transpose_mul, hVU, transpose_one, one_mulVec] }
  have hmapC : (((LinearMap.range (Matrix.mulVecLin (εT (π i)))).map (Matrix.mulVecLin Ht)).comap
      (LinearMap.range (Matrix.mulVecLin (εL i)ᵀ)).subtype).map
        (ψ : LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) →ₗ[R] (Fin d → R)) =
      LinearMap.range A.mulVecLin := by
    ext y
    constructor
    · rintro ⟨f, ⟨_, ⟨t, rfl⟩, hft⟩, rfl⟩
      refine ⟨t, ?_⟩
      show A *ᵥ t = Uᵀ *ᵥ (f : Fin g → R)
      have hft' : Ht *ᵥ (εT (π i) *ᵥ t) = (f : Fin g → R) := hft
      rw [← hft']
      show A *ᵥ t = Uᵀ *ᵥ (Ht *ᵥ (εT (π i) *ᵥ t))
      rw [hA, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    · rintro ⟨t, rfl⟩
      have hmem : Ht *ᵥ (εT (π i) *ᵥ t) ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) := by
        refine ⟨Ht *ᵥ t, ?_⟩
        show (εL i)ᵀ *ᵥ (Ht *ᵥ t) = Ht *ᵥ (εT (π i) *ᵥ t)
        rw [mulVec_mulVec, mulVec_mulVec, hHt (π i), hπ i]
      refine ⟨⟨_, hmem⟩, ⟨_, ⟨t, rfl⟩, rfl⟩, ?_⟩
      show Uᵀ *ᵥ (Ht *ᵥ (εT (π i) *ᵥ t)) = A *ᵥ t
      rw [hA, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hcA : HasLen v R ((Fin d → R) ⧸ LinearMap.range A.mulVecLin) c₁ :=
    hasLen_of_equiv (Submodule.Quotient.equiv _ _ ψ hmapC).symm hc₁
  have hkill : ∀ w : Fin d → R, ∃ t, A *ᵥ t = cp • w := by
    intro w
    obtain ⟨t, ht⟩ := cok_kill hcp hE hform εT εL π i (hπ i) hHt _ (hmemT w)
    refine ⟨t, ?_⟩
    rw [hA, ← mulVec_mulVec, ← mulVec_mulVec, ht, mulVec_smul, mulVec_mulVec, ← transpose_mul,
      hVU, transpose_one, one_mulVec]
  obtain ⟨y, hy, hyc⟩ := hPL C v R hv d (Ix g) A cp hcp hkill c₁ hcA
  have hmapY : ((sxE Ht Bt εT εL π i).comap (inclE εL i (π i))).map
      (φ : LinearMap.range (Matrix.mulVecLin (εL i)) →ₗ[R] (Fin d → R)) = zSub A cp := by
    have key : ∀ x : LinearMap.range (Matrix.mulVecLin (εL i)),
        x ∈ (sxE Ht Bt εT εL π i).comap (inclE εL i (π i)) ↔ φ x ∈ zSub A cp := by
      intro x
      have hx : εL i *ᵥ (x : Fin g → R) = x := P_fix (εL i) hP _ x.2
      have hAx : Aᵀ *ᵥ φ x = Htᵀ *ᵥ (x : Fin g → R) := by
        have hAT : Aᵀ = (εT (π i))ᵀ * Htᵀ * U := by
          rw [hA, transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc]
        rw [hAT, hHtT, ← mulVec_mulVec, ← mulVec_mulVec, matU_mulVec, LinearEquiv.symm_apply_apply,
          hx]
      rw [Submodule.mem_comap]
      show (∃ s, s ∈ LinearMap.range (Matrix.mulVecLin (εT i)) ∧
          fromRows Ht Bt *ᵥ s = Sum.elim (0 : Fin g → R) (x : Fin g → R)) ↔ ∃ z, Aᵀ *ᵥ φ x = cp • z
      rw [hAx, ← exists_fromRows_mulVec_iff hcp hE hform εT εL π i (hHt i) (hBt i) _ hx]
      constructor
      · rintro ⟨_, ⟨t, rfl⟩, h⟩; exact ⟨t, h⟩
      · rintro ⟨t, h⟩; exact ⟨_, ⟨t, rfl⟩, h⟩
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (key x).1 hx
    · intro hz
      refine ⟨φ.symm z, (key _).2 (by rwa [LinearEquiv.apply_symm_apply]), ?_⟩
      exact LinearEquiv.apply_symm_apply φ z
  exact ⟨y, hasLen_of_equiv (Submodule.Quotient.equiv _ _ φ hmapY) hy, hyc⟩
end ReciprocityTheory.PGsh.Up
