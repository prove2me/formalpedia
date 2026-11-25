-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.det_gram_projectedLatticeVectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:01:46.199592+00:00
-- url     : https://prove2.me/submissions/573e5348-3e87-44eb-9b66-a1bf56b8b2c2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_conj_sum_projected_inner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_quotientGram_det_re_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_inner_projectedVector_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_quotientGram_eq_projector


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder Kronecker
variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (b : Fin k → Fin r → K) (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) :
    (gram ℝ (hwv b c)).det =
      |(discr K : ℝ)| ^ m * ∏ σ : K →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re := by
  classical
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (K →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank,
      Module.finrank_eq_card_chooseBasisIndex]
  obtain ⟨e⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →+* ℂ)) :=
    ⟨Fintype.equivOfCardEq hcard⟩
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
      (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℂ, Ω = Matrix.of fun q p => e q (integralBasis K p) :=
    ⟨_, rfl⟩

  have hent : ∀ j p j' p', ((gram ℝ (hwv b c) (j, p) (j', p') : ℝ) : ℂ) =
      ∑ q, star (Ω q p) * ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c j j' * Ω q p' := by
    intro j p j' p'
    rw [Matrix.gram_apply]
    simp only [hwv]
    rw [inner_projectedVector_smul, Complex.conj_eq_iff_re.mp (conj_sum_projected_inner b hb _ _ _ _)]
    symm
    refine Fintype.sum_equiv e _ _ (fun q => ?_)
    rw [quotientGram_eq_projector (e q) hb c j j', hΩ]
    simp only [Matrix.of_apply]
    rw [show star ((e q) (integralBasis K p)) = conj ((e q) (integralBasis K p)) from rfl]
    ring
  have hmat : (gram ℝ (hwv b c)).map Complex.ofRealHom =
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω)ᴴ *
        Matrix.blockDiagonal (fun q => ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c) *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω) := by
    ext ⟨j, p⟩ ⟨j', p'⟩
    rw [Matrix.map_apply, Complex.ofRealHom_eq_coe, hent]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Matrix.one_apply, ite_mul, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite (starRingEnd ℂ), map_zero]
  have hdet : ((gram ℝ (hwv b c)).det : ℂ) =
      star ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det *
        (Matrix.blockDiagonal (fun q => ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c)).det *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det := by
    have h := RingHom.map_det Complex.ofRealHom (gram ℝ (hwv b c))
    rw [Complex.ofRealHom_eq_coe] at h
    rw [h, RingHom.mapMatrix_apply, hmat, det_mul, det_mul, det_conjTranspose]
  have hT : ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det = Ω.det ^ m := by
    simp [Matrix.det_kronecker]
  have hdisc : Ω.det ^ 2 = (discr K : ℂ) := by
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis K)
      (e.trans (RingHom.equivRatAlgHom K ℂ))
    rw [← NumberField.coe_discr] at h1
    have h2 : Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis K)
        (e.trans (RingHom.equivRatAlgHom K ℂ)) = Ωᵀ := by
      ext i j
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, hΩ, RingHom.equivRatAlgHom]
    rw [h2, det_transpose] at h1
    rw [← h1]
    simp
  have hnorm : star Ω.det * Ω.det = ((|(discr K : ℝ)| : ℝ) : ℂ) := by
    rw [show star Ω.det = conj Ω.det from rfl, Complex.conj_mul', ← Complex.ofReal_pow, ← norm_pow,
      hdisc, Complex.norm_intCast]
  apply Complex.ofReal_injective
  rw [hdet, hT, Matrix.det_blockDiagonal]
  push_cast
  rw [← Equiv.prod_comp e (fun σ => (((ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re : ℝ) : ℂ))]
  simp_rw [quotientGram_det_re_eq _ hb c]
  rw [star_pow, ← hnorm]
  ring
end ReciprocityTheory.ChartRestriction.G.T0
