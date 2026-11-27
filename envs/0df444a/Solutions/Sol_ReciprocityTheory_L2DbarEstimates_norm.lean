-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:40.640678+00:00
-- url     : https://prove2.me/submissions/21141d5b-6c2b-4f9e-95df-da0fb8219b9b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_NormFib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_NormOrd
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_NormVanishOfHoloSection
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_ImportsAlt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Norm_normVanish
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_normFib
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_normOrd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) (M : Type u) [TopologicalSpace M] : NORMStatement n M := by
  intro z Δ u C m hΔ hcov himg hfin hconn hu hgr hvan
  have hpre : z ⁻¹' {y : V n | MvPolynomial.eval (fun i => y i) Δ ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall himg
  have hz : IsLocalHomeomorph z := by
    have h := hcov.isLocalHomeomorphOn
    rw [hpre] at h
    exact isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.2 h
  obtain ⟨δ, hδ⟩ := normFib.{u} n M z _ hcov himg hfin hconn
  have hΔ0 : Norm.polyAt n Δ 0 ≠ 0 := by
    have h0 : Norm.polyAt n Δ 0 = MvPolynomial.constantCoeff Δ := by
      rw [← MvPolynomial.eval_zero]
      rfl
    rw [h0]
    exact hΔ
  funext x
  exact Norm.normVanish.{u} n M z Δ δ m C u hΔ0 hcov himg hδ hu hgr
    (fun x hx => normOrd.{u} n M z u x m hz hu (hvan x hx)) x
end ReciprocityTheory.L2DbarEstimates
