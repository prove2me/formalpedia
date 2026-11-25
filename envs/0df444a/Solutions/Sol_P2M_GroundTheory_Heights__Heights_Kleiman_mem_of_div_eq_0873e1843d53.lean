-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_div_eq_0873e1843d53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:35.675181+00:00
-- url     : https://prove2.me/submissions/348052f8-b5cd-4f25-a2c5-41629ff250cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_notMem_of_mem_monos_single_81fb4626dda4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hj : x j ≠ 0) {pp : Ideal (Poly S N)} [hpp : pp.IsPrime]
    (hle : primeOf (S := S) x ≤ pp) (hX : (X j : Poly S N) ∉ pp) {f s' G s : Poly S N} {e D : ℕ}
    (hf : f.IsHomogeneous e) (hs' : s' ∈ monos {j}) (hs'e : s'.IsHomogeneous e) (hG : G ∈ pp)
    (hGD : G.IsHomogeneous D) (hs : s ∈ monos {j}) (hsD : s.IsHomogeneous D)
    (h : aeval x f / aeval x s' = aeval x G / aeval x s) : f ∈ pp := by
  have h0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  have h0' : aeval x s' ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs'
  rw [div_eq_div_iff h0' h0] at h
  have h2 : (s' * G).IsHomogeneous (D + e) := by
    rw [add_comm D e]
    exact hs'e.mul hGD
  have hF : s * f - s' * G ∈ primeOf (S := S) x := by
    rw [mem_primeOf_of_isHomogeneous x ((hsD.mul hf).sub h2)]
    simp only [map_sub, map_mul]
    linear_combination h
  have h3 : s * f ∈ pp := by
    have := pp.add_mem (hle hF) (pp.mul_mem_left s' hG)
    rwa [sub_add_cancel] at this
  exact (hpp.mem_or_mem h3).resolve_left (notMem_of_mem_monos_single hX hs)
end GroundTheory.Heights₂.Heights.Kleiman
