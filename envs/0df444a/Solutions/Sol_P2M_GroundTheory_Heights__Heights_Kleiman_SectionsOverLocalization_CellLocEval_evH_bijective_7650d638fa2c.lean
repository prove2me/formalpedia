-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_evH_bijective_7650d638fa2c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:53:44.097508+00:00
-- url     : https://prove2.me/submissions/85343ea8-b93b-4067-ad8f-03a717880e38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDMemLocPart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_cechD_mem_cechCc_323ca366457f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_evC_lift_e8f11abc73fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_evC_injOn_b8a8d0effb1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_mem_cechBc_of_fdfb8453d5c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_evH_mk_b528b4acb21d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc cechZc cechBc cechHc
  mIdealOver quotPart)
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
variable (γ : K → ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
theorem _root_.solution (n : ℕ) : Function.Bijective (evH (S := S) y γ n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp ((evH_mk y γ n z).symm.trans hx)
    rw [Submodule.Quotient.mk_eq_zero]
    exact mem_cechBc_of y γ n (Submodule.mem_inf.mp z.2).1 hx'
  · intro q
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨hC, hK⟩ := Submodule.mem_inf.mp z'.2
    obtain ⟨w, hw, hwz⟩ := evC_lift y γ n hC
    have hdw : cechD S ι _ n w = 0 := by
      refine evC_injOn y γ (n + 1) (cechD_mem_cechCc y γ n hw) (Submodule.zero_mem _) ?_
      rw [evC_cechD, hwz, map_zero]
      exact LinearMap.mem_ker.mp hK
    have hwZ : w ∈ cechZc ι (quotPart S (mIdealOver S y)) γ n :=
      Submodule.mem_inf.mpr ⟨hw, by rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]; exact hdw⟩
    refine ⟨Submodule.Quotient.mk ⟨w, hwZ⟩, ?_⟩
    exact (evH_mk y γ n ⟨w, hwZ⟩).trans (congrArg Submodule.Quotient.mk (Subtype.ext hwz))
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
