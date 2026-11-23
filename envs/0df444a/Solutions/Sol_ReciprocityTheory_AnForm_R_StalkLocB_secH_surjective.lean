-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.StalkLocB.secH_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:33.576679+00:00
-- url     : https://prove2.me/submissions/cb3c2b8f-aa26-4089-84b3-fd667ef9531e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
open ReciprocityTheory.AnForm.R.StalkLocB
variable {W : Scheme.{0}} (V : W.Opens) {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
  (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))
namespace ReciprocityTheory.AnForm.R.StalkLocB
theorem _root_.solution : Function.Surjective (secH V K iso) := by
  have h1 : Function.Surjective V.topIso.hom.hom := (V.topIso.commRingCatIsoToRingEquiv).surjective
  haveI : IsIso iso.hom.appTop := by
    rw [← Scheme.Γ_map_op]
    exact (Scheme.Γ.mapIso iso.op).isIso_hom
  have h2 : Function.Surjective iso.hom.appTop.hom :=
    (asIso iso.hom.appTop).commRingCatIsoToRingEquiv.surjective
  have h3 : Function.Surjective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv.hom :=
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp (h2.comp (h3.comp Ideal.Quotient.mk_surjective))
end ReciprocityTheory.AnForm.R.StalkLocB
