-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.chart_aff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:02:03.18149+00:00
-- url     : https://prove2.me/submissions/a35a382d-d69d-4175-a1d5-a3b292cde15c

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WCharts
import Theorems.Thm_ReciprocityTheory_AnForm_R_affPres_of_iso
import Theorems.Thm_ReciprocityTheory_AnForm_R_adjoin_yC
import Theorems.Thm_ReciprocityTheory_AnForm_R_specMap_constSec


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
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    {W : Scheme.{0}} (π : W ⟶ projX P hP) {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1))
    (i : Fin m) (V : W.Opens) (e : V.toScheme ≅ Spec (.of (FinalTheorems.reesChart g i)))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(projX P hP, (chartOpen hP p).1)
      (FinalTheorems.reesChart g i))) ≫ (chartOpen hP p).2.fromSpec = V.ι ≫ π) :
    ∃ (I : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ))
      (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ ⧸ I)))
      (hiso : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ ⧸ I))) = V.ι ≫ (π ≫ toSpecC hP)),
      ∀ l, (AffPres.mk V _ I iso hiso : AffPres (π ≫ toSpecC hP)).secHom (X l) =
        V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso _).inv (yC hP p g i l))) := by
  let _ : Algebra ℂ (FinalTheorems.reesChart g i) := ((algebraMap _ (FinalTheorems.reesChart g i)).comp
    (constSec (toSpecC hP) (chartOpen hP p).1)).toAlgebra
  have h1 : CommRingCat.ofHom (algebraMap ℂ (FinalTheorems.reesChart g i)) =
      CommRingCat.ofHom (constSec (toSpecC hP) (chartOpen hP p).1) ≫
        CommRingCat.ofHom (algebraMap _ (FinalTheorems.reesChart g i)) := rfl
  have heC : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (FinalTheorems.reesChart g i))) =
      V.ι ≫ (π ≫ toSpecC hP) := by
    calc e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (FinalTheorems.reesChart g i)))
        = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(projX P hP, (chartOpen hP p).1)
            (FinalTheorems.reesChart g i))) ≫ (chartOpen hP p).2.fromSpec ≫ toSpecC hP := by
          rw [h1, Spec.map_comp, specMap_constSec]
      _ = (V.ι ≫ π) ≫ toSpecC hP := by rw [← he]; simp only [Category.assoc]
      _ = V.ι ≫ (π ≫ toSpecC hP) := Category.assoc _ _ _
  exact affPres_of_iso (π ≫ toSpecC hP) V (FinalTheorems.reesChart g i) e heC _ (yC hP p g i) (adjoin_yC hP p g i)
end ReciprocityTheory.AnForm.R
