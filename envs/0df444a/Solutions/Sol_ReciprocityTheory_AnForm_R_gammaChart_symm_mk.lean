-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.gammaChart_symm_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:13:34.555854+00:00
-- url     : https://prove2.me/submissions/68ec6333-2dc4-47e2-a59a-0bf056bf96e2

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Theorems.Thm_ReciprocityTheory_AnForm_R_gammaChart_symm_C

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
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    (gammaChart hP p).symm (Ideal.Quotient.mk _ f) =
      eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) f := by
  have h : (gammaChart hP p).symm.toRingHom.comp (Ideal.Quotient.mk (chartIdeal P p)) =
      eval₂Hom (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_eval₂Hom,
        eval₂_C]
      exact gammaChart_symm_C hP p c
    · intro q
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_eval₂Hom,
        eval₂_X]
      rfl
  exact RingHom.congr_fun h f
end ReciprocityTheory.AnForm.R
