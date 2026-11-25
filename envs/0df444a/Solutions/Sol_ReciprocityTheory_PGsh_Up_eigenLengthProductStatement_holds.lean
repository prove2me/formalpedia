-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.eigenLengthProductStatement_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:38:34.790124+00:00
-- url     : https://prove2.me/submissions/427a3ac3-c7d9-4538-a92b-b07c6fbfe929

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Tot_hasLen_equiv
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Tot_hasLen_pi
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Tot_sum_fromBlocks_diag
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_Tot_sum_mulVec__b7773400bc89
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_hasLen_coker_det
import Theorems.Thm_ReciprocityTheory_PGsh_Up_hasLen_unique


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
open Tot
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : EigenLengthProductStatement := by
  intro C _ v R _ _ hv g m Ht Bt εT εL π hπ hTo hTs hLo hLs hHt hBt X hX
  classical
  set Φ := fromRows Ht Bt with hΦ
  set Pm : Fin m → Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R :=
    fun i => fromBlocks ((εL (π i))ᵀ) 0 0 (εL i) with hPm
  have hPmv : ∀ i w, Pm i *ᵥ w =
      Sum.elim ((εL (π i))ᵀ *ᵥ (w ∘ Sum.inl)) (εL i *ᵥ (w ∘ Sum.inr)) := by
    intro i w
    simp only [hPm, fromBlocks_mulVec, zero_mulVec, add_zero, zero_add]
  have hmem : ∀ i w, Pm i *ᵥ w ∈ qE εL i (π i) := by
    intro i w
    refine Submodule.mem_inf.2 ⟨⟨w ∘ Sum.inl, ?_⟩, ⟨w ∘ Sum.inr, ?_⟩⟩
    · show (εL (π i))ᵀ *ᵥ (w ∘ Sum.inl) = (Pm i *ᵥ w) ∘ Sum.inl
      rw [hPmv]; rfl
    · show εL i *ᵥ (w ∘ Sum.inr) = (Pm i *ᵥ w) ∘ Sum.inr
      rw [hPmv]; rfl
  have hsel : ∀ i k w, w ∈ qE εL i (π i) → Pm k *ᵥ w = if k = i then w else 0 := by
    intro i k w hw
    obtain ⟨⟨y1, hy1⟩, ⟨y2, hy2⟩⟩ := Submodule.mem_inf.1 hw
    have e1 : w ∘ Sum.inl = (εL (π i))ᵀ *ᵥ y1 := hy1.symm
    have e2 : w ∘ Sum.inr = εL i *ᵥ y2 := hy2.symm
    rw [hPmv, e1, e2, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, hLo, hLo]
    by_cases hki : k = i
    · subst hki
      simp only [if_true]
      rw [← e1, ← e2, Sum.elim_comp_inl_inr]
    · have hne : π i ≠ π k := fun h => hki (π.injective h).symm
      simp only [hki, hne, if_false, transpose_zero, zero_mulVec]
      ext s; cases s <;> rfl
  have hT : ∑ i, (εL (π i))ᵀ = 1 := by
    rw [← transpose_sum, Equiv.sum_comp π εL, hLs, transpose_one]
  have hPsum : ∑ i, Pm i = 1 := by
    simp only [hPm]
    rw [sum_fromBlocks_diag, hT, hLs, fromBlocks_one]
  have hsum : ∀ w, ∑ i, Pm i *ᵥ w = w := by
    intro w
    rw [← sum_mulVec', hPsum, one_mulVec]
  have hPΦ : ∀ i, Pm i * Φ = Φ * εT i := by
    intro i
    rw [hΦ, hPm, fromBlocks_mul_fromRows, fromRows_mul, Matrix.zero_mul, Matrix.zero_mul, add_zero,
      zero_add,
      hHt, hBt]
  set Ψ : (Fin g ⊕ Fin g → R) →ₗ[R] ((i : Fin m) → xModE Ht Bt εT εL π i) :=
    LinearMap.pi fun i => Submodule.mkQ _ ∘ₗ
      LinearMap.codRestrict (qE εL i (π i)) (mulVecLin (Pm i)) (hmem i) with hΨdef
  have hΨ : ∀ w i, Ψ w i = Submodule.Quotient.mk ⟨Pm i *ᵥ w, hmem i w⟩ := fun _ _ => rfl
  have hsurj : Function.Surjective Ψ := by
    intro q
    choose w hw using fun i => Submodule.Quotient.mk_surjective _ (q i)
    refine ⟨∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R), funext fun k => ?_⟩
    rw [hΨ, ← hw k]
    congr 1
    apply Subtype.ext
    show Pm k *ᵥ ∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R) = (w k : Fin g ⊕ Fin g → R)
    rw [mulVec_sum]
    simp only [fun i => hsel i k _ (w i).2]
    simp
  have hker : LinearMap.ker Ψ = LinearMap.range (mulVecLin Φ) := by
    ext w
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      have hi : ∀ i, ∃ t, Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ w := by
        intro i
        have := congrFun h i
        rw [hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        obtain ⟨y, ⟨t, rfl⟩, hy⟩ := this
        exact ⟨t, hy⟩
      choose t ht using hi
      refine ⟨∑ i, εT i *ᵥ t i, ?_⟩
      show Φ *ᵥ ∑ i, εT i *ᵥ t i = w
      rw [mulVec_sum]
      simp only [ht]
      exact hsum w
    · rintro ⟨t, rfl⟩
      funext i
      rw [hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨εT i *ᵥ t, ⟨t, rfl⟩, ?_⟩
      show Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ (Φ *ᵥ t)
      rw [mulVec_mulVec, mulVec_mulVec, hPΦ]
  have iso : ((Fin g ⊕ Fin g → R) ⧸ LinearMap.range (mulVecLin Φ)) ≃ₗ[R]
      ((i : Fin m) → xModE Ht Bt εT εL π i) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (Ψ.quotKerEquivOfSurjective hsurj)
  set e : Fin g ⊕ Fin g ≃ Fin (g + g) := finSumFinEquiv with he
  set Φ' := reindex e e Φ with hΦ'
  have hdet : Φ'.det = Φ.det := det_reindex_self e Φ
  set F : (Fin (g + g) → R) ≃ₗ[R] (Fin g ⊕ Fin g → R) := LinearEquiv.funCongrLeft R R e with hF
  have hFapp : ∀ y, F y = y ∘ e := fun y => rfl
  have hcomm : ∀ y, F (Φ' *ᵥ y) = Φ *ᵥ F y := by
    intro y
    rw [hFapp, hFapp, hΦ', reindex_apply, submatrix_mulVec_equiv]
    ext s
    simp
  have hmap : (LinearMap.range (mulVecLin Φ')).map F.toLinearMap = LinearMap.range (mulVecLin Φ) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨F y, (hcomm y).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨Φ' *ᵥ F.symm t, ⟨F.symm t, rfl⟩, ?_⟩
      show F (Φ' *ᵥ F.symm t) = Φ *ᵥ t
      rw [hcomm, LinearEquiv.apply_symm_apply]
  have hcok := Submodule.Quotient.equiv _ _ F hmap
  have hL1 := Smith.hasLen_coker_det (C := C) (v := v) hv Φ'
  have hL2 : HasLen v R ((Fin (g + g) → R) ⧸ LinearMap.range (mulVecLin Φ')) (∏ i, X i) :=
    hasLen_equiv (hcok.trans iso) (hasLen_pi _ X hX)
  rw [hasLen_unique hv hL2 hL1, hdet]
end ReciprocityTheory.PGsh.Up
