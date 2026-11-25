-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1_vanish_generated_of_localized_subsingleton_ba7e604619d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:53.988564+00:00
-- url     : https://prove2.me/submissions/6821ce92-08ea-44f6-876f-08255a337737

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ImportsSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_H1VanishGeneratedOfLocalizedSubsingleton
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultiHomog_one_zero_4334cb17c577


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution
    (h : ∀ (n : ℕ) (I : KH.Cell K ι n), Subsingleton (LocalizedModule (KH.cellMon S I.1) M))
    (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    Subsingleton (KH.cechHc ι 𝓜 d 1) ∧ GeneratedMod S ι 𝓜 d := by
  have : Subsingleton (KH.CechC S ι M 1) := ⟨fun f g => funext fun I => (h 1 I).elim _ _⟩
  refine ⟨⟨fun x y => ?_⟩, fun I x _ => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]
  · refine ⟨1, 0, 0, Fin.elim0, Fin.elim0, Submonoid.one_mem _, isMultiHomog_one_zero, fun j => j.elim0,
      fun j => j.elim0, ?_⟩
    rw [one_smul, Fin.sum_univ_zero]
    exact (h 0 I).elim _ _
end GroundTheory.Heights₂.Heights.HilbertSamuel
