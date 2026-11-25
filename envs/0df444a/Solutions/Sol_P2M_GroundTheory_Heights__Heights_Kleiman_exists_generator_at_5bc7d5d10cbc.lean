-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_generator_at_5bc7d5d10cbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:34.618543+00:00
-- url     : https://prove2.me/submissions/1190c4a0-9d42-4ac5-bd8b-37b7834b27ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict

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
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
  {K' : Type w} [Field K'] [Algebra S K'] (ψ : chartRing S x (singleChart hj) →ₐ[S] K')
variable (hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {Q0 Q1 : Submodule (chartRing S x (singleChart hj)) Ω} (h : Q0 * Q1 = 1) :
    ∃ q0 ∈ Q0, ∃ q1 ∈ Q1, ∃ c0 : chartRing S x (singleChart hj), (c0 : Ω) = q0 * q1 ∧ ψ c0 ≠ 0 := by
  by_contra H
  push Not at H
  have h1 : (1 : Ω) ∈ Q0 * Q1 := by rw [h]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨c, hc, hψc⟩ : ∃ c : chartRing S x (singleChart hj), (c : Ω) = 1 ∧ ψ c = 0 := by
    refine Submodule.mul_induction_on
      (C := fun z => ∃ c : chartRing S x (singleChart hj), (c : Ω) = z ∧ ψ c = 0) h1 ?_ ?_
    · intro m hm n hn
      have hmn := Submodule.mul_mem_mul hm hn
      rw [h] at hmn
      obtain ⟨c, hc⟩ := Submodule.mem_one.mp hmn
      exact ⟨c, hc, H m hm n hn c hc⟩
    · rintro a b ⟨c, hc, hc0⟩ ⟨d, hd, hd0⟩
      exact ⟨c + d, by rw [Subalgebra.coe_add, hc, hd], by rw [map_add, hc0, hd0, add_zero]⟩
  have : c = 1 := Subtype.ext hc
  rw [this, map_one] at hψc
  exact one_ne_zero hψc
end GroundTheory.Heights₂.Heights.Kleiman
