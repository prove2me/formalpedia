-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.away_eq_mk_of_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:12.920102+00:00
-- url     : https://prove2.me/submissions/38ed449b-5bb4-4960-bb2e-ba14056e396c

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC

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
theorem _root_.solution {N : ℕ} (n : MvPolynomial ((k : K) → ι k) ℂ) (hn : n.IsHomogeneous N)
    (a : letI := segreGraded hP; HomogeneousLocalization.Away (segreGrading P) (segreW P p))
    (h : letI := segreGraded hP; a.val * algebraMap _ (Localization.Away (segreW P p)) (segreW P p) ^ N =
      algebraMap _ _ (Ideal.Quotient.mk (segreIdeal P) n)) :
    letI := segreGraded hP
    a = HomogeneousLocalization.mk
      ({ deg := N
         num := ⟨Ideal.Quotient.mk _ n, n, (mem_homogeneousSubmodule N n).mpr hn, rfl⟩
         den := ⟨segreW P p ^ N, by simpa using SetLike.pow_mem_graded N (segreW_mem P p)⟩
         den_mem := ⟨N, rfl⟩ } :
        HomogeneousLocalization.NumDenSameDeg (segreGrading P) (Submonoid.powers (segreW P p))) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  simpa [map_pow] using h
end ReciprocityTheory.AnForm.R
