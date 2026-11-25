-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.uniformizer_of_residue_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:36:26.668618+00:00
-- url     : https://prove2.me/submissions/3752876a-69c7-46af-b3a6-bd3c058e44ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_exists_val_coeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_wt_cancel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {Ω : Type} [Field Ω] {σ τ : Type}
    (w : AddValuation (FractionRing (MvPolynomial σ Ω)) (WithTop ℤ)) (hw : IsNormDiscrete w)
    (t : τ → FractionRing (MvPolynomial σ Ω)) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω (FractionRing (MvPolynomial σ Ω)))
      AlgebraicIndependent (IsLocalRing.ResidueField
          ((vRing w).comap (algebraMap Ω (FractionRing (MvPolynomial σ Ω)))))
        (fun s => IsLocalRing.residue (vRing w) ⟨t s, ht s⟩))
    (g : σ → MvPolynomial τ Ω)
    (hg : ∀ x, algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) (X x) =
      aeval t (g x)) :
    ∃ π : Ω, w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) π) = 1 := by
  classical
  obtain ⟨hw1, f, hf⟩ := hw
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ Ω) f
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have key : ∀ P : MvPolynomial σ Ω,
      algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) P =
        aeval t (bind₁ g P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      rw [bind₁_C_right, aeval_C, ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P x hP => simp only [map_mul, hP, bind₁_X_right, hg]
  have hinj := IsFractionRing.injective (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, AddValuation.map_zero] at hf
    simp at hf
  have hne : ∀ P : MvPolynomial σ Ω, P ≠ 0 → bind₁ g P ≠ 0 := by
    intro P hP h0
    apply hP
    apply hinj
    rw [key, h0, map_zero, map_zero]
  obtain ⟨c, hc0, hc⟩ := ValuationResidueLemmas.exists_val_coeff w t ht hind _ (hne p hp0)
  obtain ⟨d, hd0, hd⟩ := ValuationResidueLemmas.exists_val_coeff w t ht hind _ (hne q hq0)
  rw [← key] at hc hd
  have hqa : algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) q ≠ 0 := by
    intro h0; exact hq0 (hinj (by rw [h0, map_zero]))
  have hda : algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d ≠ 0 :=
    (map_ne_zero _).2 hd0
  refine ⟨c / d, ?_⟩
  have h1 : w (algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) p) =
      1 + w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d) := by
    rw [← hf, ← hd, ← AddValuation.map_mul, div_mul_cancel₀ _ hqa]
  have h2 : w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) c) =
      w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) (c / d)) +
        w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d) := by
    rw [← AddValuation.map_mul, ← map_mul, div_mul_cancel₀ _ hd0]
  exact ValuationResidueLemmas.wt_cancel (hw1 _ hda) (by rw [← h2, ← hc, h1])
end ReciprocityTheory.ChartRestriction.G.T0
