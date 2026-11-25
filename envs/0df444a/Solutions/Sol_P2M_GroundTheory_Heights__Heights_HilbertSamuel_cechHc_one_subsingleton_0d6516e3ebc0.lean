-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_cechHc_one_subsingleton_0d6516e3ebc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:54:44.222168+00:00
-- url     : https://prove2.me/submissions/62628b5c-713c-48f3-804e-be1f4e970480

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_succ_isEmpty_c7809aa49cfb

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
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    Subsingleton (KH.cechHc ι 𝓜 d 1) := by
  have := cell_succ_isEmpty (K := K) (ι := ι) 0
  have : Subsingleton (KH.CechC S ι M 1) := ⟨fun f g => funext fun I => (IsEmpty.false I).elim⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]
end GroundTheory.Heights₂.Heights.HilbertSamuel
