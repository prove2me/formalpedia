-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_gram_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:23:48.705567+00:00
-- url     : https://prove2.me/submissions/fa96287d-f49b-4208-9b82-a0e09e4bbe22

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegD
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_cut_quad
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_det_mono
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_embM_inj
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_gramC_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_gramX_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_schur

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder
private theorem posDef_diagonal_ofReal_of_pos {r : ℕ} (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) :
    (diagonal fun l => (d l : ℂ)).PosDef := by
  first
  | exact Matrix.posDef_diagonal_iff.mpr fun l => Complex.zero_lt_real.mpr (hd l)
  | exact Matrix.posDef_diagonal_iff.mpr fun l => by exact_mod_cast hd l
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r e k₀ k₁ : ℕ} (σ : K →+* ℂ)
    (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) (b₀ : Fin k₀ → Fin r → K) (c b₁ : Fin k₁ → Fin r → K)
    (hb₀cut : ∀ i, b₀ i ∈ cutSub K r e) (hb₀li : LinearIndependent K b₀)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁li : LinearIndependent K b₁) :
    Real.log (gramC (diagonal fun l => (d l : ℂ)) σ b₁).det.re ≤
      Real.log (quotGramC (diagonal fun l => (d l : ℂ)) σ b₀ c).det.re := by

  have hcutz : ∀ i (l : Fin r), e ≤ (l : ℕ) → b₀ i l = 0 := by
    intro i l hl
    have h := hb₀cut i
    simp only [cutSub, UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub] at h
    exact h l hl
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal fun l => (d l : ℂ) with hDdef
  have hDpd : D.PosDef := posDef_diagonal_ofReal_of_pos d hd
  have hG0 : ((embM σ b₀)ᴴ * D * embM σ b₀).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₀ hb₀li)
  have hG1 : ((embM σ b₁)ᴴ * D * embM σ b₁).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₁ hb₁li)
  have hu : IsUnit ((embM σ b₀)ᴴ * D * embM σ b₀).det := by
    first
    | exact (Matrix.isUnit_iff_isUnit_det _).mp hG0.isUnit
    | exact hG0.det_pos.ne'.isUnit
  set E : Matrix (Fin r) (Fin k₁) ℂ := embM σ c - embM σ b₀ *
    (((embM σ b₀)ᴴ * D * embM σ b₀)⁻¹ * ((embM σ b₀)ᴴ * D * embM σ c)) with hE

  have hq : quotGramC D σ b₀ c = Eᴴ * D * E := by
    simp only [quotGramC, sdd_gramC_eq, sdd_gramX_eq]
    exact sdd_schur _ _ _ hDpd.1 hG0.1 hu

  have hB1 : ∀ (l : Fin r) (j : Fin k₁),
      embM σ b₁ l j = if e ≤ (l : ℕ) then E l j else 0 := by
    intro l j
    have hb1 : b₁ j l = if e ≤ (l : ℕ) then c j l else 0 := by
      rw [← hcb j]; rfl
    by_cases hl : e ≤ (l : ℕ)
    · have hz : ∀ i, b₀ i l = 0 := fun i => hcutz i l hl
      rw [if_pos hl, hE]
      simp [embM, Matrix.mul_apply, hb1, hl, hz]
    · rw [if_neg hl]
      simp [embM, hb1, hl]
  have hquad : ∀ v : Fin k₁ → ℂ, (star v ⬝ᵥ (((embM σ b₁)ᴴ * D * embM σ b₁) *ᵥ v)).re ≤
      (star v ⬝ᵥ ((Eᴴ * D * E) *ᵥ v)).re :=
    sdd_cut_quad d (fun l => (hd l).le) e E (embM σ b₁) hB1
  obtain ⟨hpos, hle⟩ := sdd_det_mono _ _ hG1 (Matrix.isHermitian_conjTranspose_mul_mul E hDpd.1) hquad
  rw [sdd_gramC_eq, hq]
  exact Real.log_le_log hpos hle
end ReciprocityTheory.MultiplicativeHeights
