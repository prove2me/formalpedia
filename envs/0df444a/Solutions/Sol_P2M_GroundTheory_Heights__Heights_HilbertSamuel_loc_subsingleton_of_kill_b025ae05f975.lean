-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_loc_subsingleton_of_kill_b025ae05f975
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:10.456981+00:00
-- url     : https://prove2.me/submissions/bb103584-6169-4d71-b46d-0ec0b6e5014e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ImportsSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_H1VanishGeneratedOfLocalizedSubsingleton

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
omit [Fintype K] [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [Module S M]
  [IsScalarTower S (MRingOver S ι) M]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {T : Submonoid (MRingOver S ι)} {u : MRingOver S ι} (hu : u ∈ T)
    (hk : ∀ y : M, u • y = 0) : Subsingleton (LocalizedModule T M) := by
  have h0 : ∀ x : LocalizedModule T M, x = 0 := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h y s =>
      rw [← LocalizedModule.zero_mk s]
      refine LocalizedModule.mk_eq.mpr ⟨⟨u, hu⟩, ?_⟩
      simp only [Submonoid.smul_def, smul_zero]
      rw [smul_comm, hk, smul_zero]
  exact ⟨fun a b => by rw [h0 a, h0 b]⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel
