-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_embedC_eq_d6410787624d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:07:18.20899+00:00
-- url     : https://prove2.me/submissions/862ae91c-fcec-44aa-9983-a29a294d4e81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_zero_of_mem_coneDeg_593a1a927cdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution (n : ℕ) (w : Cech.Cochain (fun _ : StdCell N => ConeLaurent S x) n)
    (hw : w ∈ Cech.Cdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) n) :
    ∃ s, M.embedC c n s = w := by
  have hv : ∀ K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n, ∀ h : K.1.1 ⊆ support x,
      ∃ v ∈ M.tilde c ⟨K.1.1, K.1.2.1, h⟩, w K = coneSingle S x c v :=
    fun K h => (M.mem_coneDeg_of_subset c h).mp (hw K (Set.mem_univ _))
  have key : ∀ K : Cech.Idx (support x) n,
      coeffAt S x c (w (ofChartIdx K)) ∈ (M.tildeSys c).sub K.1 := by
    intro K
    obtain ⟨v, hv', hwv⟩ := hv (ofChartIdx K) K.1.2.2
    rw [hwv, coeffAt_coneSingle_same]
    exact hv'
  refine ⟨fun K => ⟨coeffAt S x c (w (ofChartIdx K)), key K⟩, funext fun K => ?_⟩
  by_cases h : K.1.1 ⊆ support x
  · rw [M.embedC_of_subset c _ K h]
    obtain ⟨v, -, hwv⟩ := hv K h
    change coneSingle S x c (coeffAt S x c (w K)) = w K
    rw [hwv, coeffAt_coneSingle_same]
  · rw [M.embedC_of_not c _ K h]
    exact (M.eq_zero_of_mem_coneDeg c h (hw K (Set.mem_univ _))).symm
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman
