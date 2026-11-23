-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_R_eval__mk_one_83d5260a9710
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:04.342624+00:00
-- url     : https://prove2.me/submissions/f4dbf765-4b4f-4334-b9e3-0606bd2fb42d

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {τ : Type} (I : Ideal (MvPolynomial τ ℂ)) (M : Submonoid (MvPolynomial τ ℂ ⧸ I))
    {σ : Type} (Y : σ → MvPolynomial τ ℂ) (f : MvPolynomial σ ℂ) :
    eval₂ (algebraMap ℂ (Localization M)) (fun q => Localization.mk (Ideal.Quotient.mk I (Y q)) 1) f =
      Localization.mk (Ideal.Quotient.mk I (aeval Y f)) 1 := by
  simp only [Localization.mk_one_eq_algebraMap]
  have h := MvPolynomial.eval₂_comp_left
    ((algebraMap (MvPolynomial τ ℂ ⧸ I) (Localization M)).comp (Ideal.Quotient.mk I))
    (algebraMap ℂ (MvPolynomial τ ℂ)) Y f
  rw [RingHom.comp_apply] at h
  rw [aeval_def, h]
  congr 1
end ReciprocityTheory.AnForm.R
