-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.val_polyToAway_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:36:55.027227+00:00
-- url     : https://prove2.me/submissions/0da96ad2-e398-4c79-bd5a-0cb5d197294d

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC
import Theorems.Thm_ReciprocityTheory_AnForm_R_val_polyToAway_X
import Theorems.Thm_ReciprocityTheory_AnForm_R_val_polyToAway_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    letI := segreGraded hP
    (polyToAway hP p f).val * algebraMap _ (Localization.Away (segreW P p)) (segreW P p) ^ (∑ k, a k) =
      algebraMap _ (Localization.Away (segreW P p))
        (Ideal.Quotient.mk (segreIdeal P) (rename (chartUpd p) f)) := by
  letI := segreGraded hP
  let W := algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))
    (segreW P p)
  let ψ : MvPolynomial (Σ k, ι k) ℂ →+* Localization.Away (segreW P p) :=
    (algebraMap (HomogeneousLocalization.Away (segreGrading P) (segreW P p))
      (Localization.Away (segreW P p))).comp (polyToAway hP p)
  let τ : MvPolynomial (Σ k, ι k) ℂ →+* Localization.Away (segreW P p) :=
    (algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (Localization.Away (segreW P p))).comp
      ((Ideal.Quotient.mk (segreIdeal P)).comp (rename (chartUpd p)).toRingHom)
  have hψ : ∀ g, ψ g = (polyToAway hP p g).val := fun g => HomogeneousLocalization.algebraMap_apply _
  have hX : ∀ q, ψ (X q) * W = τ (X q) := by
    intro q
    have hs := IsLocalization.mk'_spec (Localization.Away (segreW P p)) (segreW P (chartUpd p q))
      (⟨segreW P p, Submonoid.mem_powers _⟩ : Submonoid.powers (segreW P p))
    rw [hψ, val_polyToAway_X hP p q]
    refine hs.trans ?_
    simp [τ]
  have hC : ∀ r, ψ (C r) = τ (C r) := fun r => by
    rw [hψ, val_polyToAway_C hP p r]
    simp [τ]
  have key : ∀ m ∈ f.support, ψ (monomial m (coeff m f)) * W ^ (∑ k, a k) =
      τ (monomial m (coeff m f)) := by
    intro m hm

    have hW : W ^ (∑ k, a k) = m.prod (fun _ e => W ^ e) := by
      rw [Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, Fintype.sum_sigma]
      congr 1
      exact Finset.sum_congr rfl fun k _ => (hf m hm k).symm
    rw [hW, monomial_eq, map_mul, map_mul, map_finsuppProd, map_finsuppProd, mul_assoc,
      ← Finsupp.prod_mul]
    simp only [map_pow, ← mul_pow, hX, hC]
  show ψ f * W ^ (∑ k, a k) = τ f
  calc ψ f * W ^ (∑ k, a k) = (∑ m ∈ f.support, ψ (monomial m (coeff m f))) * W ^ (∑ k, a k) := by
        rw [← map_sum, ← f.as_sum]
    _ = ∑ m ∈ f.support, ψ (monomial m (coeff m f)) * W ^ (∑ k, a k) := Finset.sum_mul _ _ _
    _ = ∑ m ∈ f.support, τ (monomial m (coeff m f)) := Finset.sum_congr rfl key
    _ = τ f := by rw [← map_sum, ← f.as_sum]
end ReciprocityTheory.AnForm.R
