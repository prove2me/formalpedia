-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartPrime_iff_8a48624344f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:25.751195+00:00
-- url     : https://prove2.me/submissions/5d3a87de-7177-46c5-9481-9936bbaba6b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_div_eq_0873e1843d53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartPrime_le_chartPrimeIdeal_1aa727f25bd6

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
theorem _root_.solution (hj : x j ≠ 0) {pp : Ideal (Poly S N)} [pp.IsPrime]
    (hle : primeOf (S := S) x ≤ pp) (hX : (X j : Poly S N) ∉ pp) {a : chartRing S x (singleChart hj)}
    {f s : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s ∈ monos {j}) (hse : s.IsHomogeneous e)
    (ha : (a : Ω) = aeval x f / aeval x s) : a ∈ chartPrime pp hj ↔ f ∈ pp := by
  constructor
  · intro h
    obtain ⟨G, t, D, hG, ht, hGD, htD, hat⟩ := chartPrime_le_chartPrimeIdeal hj pp h
    exact mem_of_div_eq hj hle hX hf hs hse hG hGD ht htD (ha.symm.trans hat)
  · intro h
    exact Ideal.subset_span ⟨f, s, e, h, hs, hf, hse, ha⟩
end GroundTheory.Heights₂.Heights.Kleiman
