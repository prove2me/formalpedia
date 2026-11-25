-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_clear_mem_f30bf8927550
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:20:40.253095+00:00
-- url     : https://prove2.me/submissions/f630e345-d30f-458e-8f65-0bd773ab45c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_varMono_d425fcc92f17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_varMono_notMem_d447ddc5e348
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_sum_mem_f3caf2e9abdf


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
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
theorem _root_.solution {I : Ideal (MRing ι)} [I.IsPrime] (hI : IsMultiHomogIdeal I) {v : ∀ k, ι k}
    (hvI : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ I) (s : Finset (K →₀ ℕ)) {b : K → ℕ} {N : (K →₀ ℕ) → MRing ι}
    (hN : ∀ e, IsMultiHomog (N e) b) (h : ∑ e ∈ s, N e * varMono v e ∈ I) : ∀ e ∈ s, N e ∈ I := by
  intro e he
  have := mem_of_sum_mem hI s (fun e => N e * varMono v e) (fun e => b + ⇑e) ?_
    (fun e _ => homog_mul (hN e) (homog_varMono v e)) h e he
  · exact (Ideal.IsPrime.mem_or_mem ‹_› this).resolve_right (varMono_notMem hvI e)
  · intro e1 _ e2 _ h12
    exact DFunLike.coe_injective (add_left_cancel h12)
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
