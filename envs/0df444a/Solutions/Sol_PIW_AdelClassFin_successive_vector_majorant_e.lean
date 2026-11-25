-- Prove2me | solution 1 for PIW.AdelClassFin.successive_vector_majorant_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:10.561271+00:00
-- url     : https://prove2.me/submissions/1a7fbf80-922a-4f3c-9dda-62a086d21d5c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorMajorantE
import Theorems.Thm_PIW_AdelClassFin_successive_vector_majorant
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField Matrix
open scoped ComplexOrder
namespace PIW.AdelClassFin
theorem _root_.solution : SvMajE := by
  intro F E _ _ _ _ _ _ hCM m J hJ hdet
  have hstar : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a) := hCM.cmUnram.2.1
  have hTC : NumberField.IsTotallyComplex E := hCM.cmUnram.1
  have hne : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := by
    intro φ h
    have hc := hTC.isComplex (InfinitePlace.mk φ)
    rw [InfinitePlace.isComplex_mk_iff] at hc
    exact hc (ComplexEmbedding.isReal_iff.2 h)
  have hJe : ∀ i j, star (J j i) = J i j := by
    intro i j
    have := congrFun (congrFun hJ i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hherm : ∀ φ : E →+* ℂ, (J.map φ).IsHermitian := by
    intro φ
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.map_apply]
    rw [← hJe i j, hstar]
    rfl
  have hdetφ : ∀ φ : E →+* ℂ, (J.map φ).det ≠ 0 := by
    intro φ
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).2 hdet
  have hmapT : ∀ M : Matrix (Fin m) (Fin m) ℂ, M.IsHermitian → M.map (starRingEnd ℂ) = Mᵀ := by
    intro M hM
    ext i j
    rw [Matrix.map_apply, Matrix.transpose_apply, ← hM.apply j i]
    rfl
  have hid : ∀ (N : Matrix (Fin m) (Fin m) ℂ) (z : Fin m → ℂ),
      star z ⬝ᵥ (N.map (starRingEnd ℂ) *ᵥ z) = starRingEnd ℂ (z ⬝ᵥ (N *ᵥ star z)) := by
    intro N z
    simp [dotProduct, mulVec, map_sum, map_mul]
  choose H0 hH0 using fun φ : E →+* ℂ => successive_vector_majorant m (J.map φ) (hherm φ) (hdetφ φ)
  let ι := Fintype.equivFin (E →+* ℂ)
  refine ⟨fun φ => if ι φ < ι (ComplexEmbedding.conjugate φ) then H0 φ
    else (H0 (ComplexEmbedding.conjugate φ)).map (starRingEnd ℂ), ?_⟩
  intro φ
  have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
  by_cases hp : ι φ < ι (ComplexEmbedding.conjugate φ)
  · have hp' : ¬ ι (ComplexEmbedding.conjugate φ) < ι φ := lt_asymm hp
    simp only [if_pos hp]
    refine ⟨(hH0 φ).1, (hH0 φ).2.1, (hH0 φ).2.2, ?_⟩
    rw [hcc, if_neg hp']
  · set ψ := ComplexEmbedding.conjugate φ with hψ
    have hψφ : ι ψ < ι (ComplexEmbedding.conjugate ψ) := by
      rw [hψ, hcc]
      refine lt_of_le_of_ne (not_lt.1 hp) fun h => hne φ (ι.injective h.symm ▸ rfl)
    have hJφ : J.map φ = (J.map ψ).map (starRingEnd ℂ) := by
      ext i j
      simp [hψ, ComplexEmbedding.conjugate_coe_eq]
    have hM := hH0 ψ
    simp only [if_neg hp, if_pos hψφ, ← hψ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hmapT _ hM.1.1]
      exact hM.1.transpose
    · have hdc : ∀ N : Matrix (Fin m) (Fin m) ℂ,
          (N.map (starRingEnd ℂ)).det = starRingEnd ℂ N.det := fun N => by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rw [hmapT _ hM.1.1, Matrix.det_transpose, hM.2.1, hJφ, hdc, Complex.norm_conj]
    · intro z
      have h1 := hM.2.2 (star z)
      rw [star_star] at h1
      rw [hJφ, hid, hid, Complex.norm_conj, Complex.conj_re]
      exact h1
    · rw [Matrix.map_map]
      ext i j
      simp
end PIW.AdelClassFin
