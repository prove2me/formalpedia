-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isOpen_regularLocus_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:28:47.517805+00:00
-- url     : https://prove2.me/submissions/9642876e-4439-4ed5-b321-942c13ee5723

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Theorems.Thm_ReciprocityTheory_AnForm_R_isRegularLocalRing_stalk_fromSpec_iff

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
theorem _root_.solution {X : Scheme.{0}} {J : Type} (U : J → X.affineOpens)
    (hcov : ∀ x, ∃ i, x ∈ (U i).1)
    (h : ∀ i, IsOpen {Q : PrimeSpectrum Γ(X, (U i).1) |
      IsRegularLocalRing (Localization.AtPrime Q.asIdeal)}) :
    IsOpen {x : X | IsRegularLocalRing (X.presheaf.stalk x)} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨i, hi⟩ := hcov x
  have hU : IsAffineOpen (U i).1 := (U i).2
  refine ⟨(⇑hU.fromSpec) '' {Q : PrimeSpectrum Γ(X, (U i).1) |
    IsRegularLocalRing (Localization.AtPrime Q.asIdeal)}, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : hU.fromSpec q ∈ (U i).1 := hU.range_fromSpec.le ⟨q, rfl⟩
    exact (isRegularLocalRing_stalk_fromSpec_iff hU q hq').mpr hq
  · exact (IsAffineOpen.fromSpec hU).isOpenEmbedding.isOpenMap _ (h i)
  · refine ⟨hU.primeIdealOf ⟨x, hi⟩, ?_, hU.fromSpec_primeIdealOf ⟨x, hi⟩⟩
    have h1 := hU.fromSpec_primeIdealOf ⟨x, hi⟩
    have h2 := isRegularLocalRing_stalk_fromSpec_iff hU (hU.primeIdealOf ⟨x, hi⟩) (by rw [h1]; exact hi)
    rw [h1] at h2
    exact h2.mp hx
end ReciprocityTheory.AnForm.R
