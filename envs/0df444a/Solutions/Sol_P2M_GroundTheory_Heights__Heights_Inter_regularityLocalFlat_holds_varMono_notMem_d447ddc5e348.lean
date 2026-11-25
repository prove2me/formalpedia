-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_varMono_notMem_d447ddc5e348
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:59:02.189864+00:00
-- url     : https://prove2.me/submissions/19689cde-8302-460b-b25b-7b4a3233ae06

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
theorem _root_.solution {I : Ideal (MRing ι)} [I.IsPrime] {v : ∀ k, ι k}
    (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ I) (e : K →₀ ℕ) : varMono v e ∉ I := by
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hv k (Ideal.IsPrime.mem_of_pow_mem ‹_› _ hk)
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
