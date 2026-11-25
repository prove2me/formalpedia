-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_subsingleton_of_not_258815edc3e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:03.920443+00:00
-- url     : https://prove2.me/submissions/6cdca9ae-e590-49ed-99f8-d68b23eeb15f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt

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
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc mIdealOver mConeMapOver
  quotPart)
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
theorem _root_.solution {I : ∀ k, Finset (ι k)} (hI : ¬ CellMeets y I) :
    Subsingleton (LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) := by
  unfold CellMeets at hI
  push Not at hI
  obtain ⟨k, i, hi, hy⟩ := hI
  have hX : (X ⟨k, i⟩ : MRingOver S ι) ∈ cellMon S I := Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hmem : (X ⟨k, i⟩ : MRingOver S ι) ∈ mIdealOver S y := by
    simp [mIdealOver, mConeMapOver, RingHom.mem_ker, hy]
  have hz : ∀ w : MRingOver S ι ⧸ mIdealOver S y, (X ⟨k, i⟩ : MRingOver S ι) • w = 0 := by
    intro w
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hmem
  refine ⟨fun a b => ?_⟩
  induction a using LocalizedModule.induction_on with
  | h m t =>
    induction b using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨_, hX⟩, ?_⟩
      simp only [Submonoid.smul_def]
      rw [hz, hz]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
