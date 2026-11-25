-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_exists_clear_7e98f59cc546
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:34:33.188776+00:00
-- url     : https://prove2.me/submissions/6d3a17f7-c7f2-4350-888d-e1a0c4472b55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination

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
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution {A : Subalgebra S Ω} {B : Submodule A Ω} (hB : B.FG) (P : Set Ω) (hP1 : (1 : Ω) ∈ P)
    (hPmul : ∀ a ∈ P, ∀ b ∈ P, a * b ∈ P) (hPA : ∀ a ∈ P, a ∈ A)
    (h : ∀ g ∈ B, ∃ d ∈ P, d * g ∈ A) : ∃ d ∈ P, ∀ b ∈ B, d * b ∈ A := by
  classical
  obtain ⟨t, ht⟩ := hB
  have h' : ∀ g : t, ∃ d ∈ P, d * (g : Ω) ∈ A := fun g =>
    h g (by rw [← ht]; exact Submodule.subset_span (Finset.mem_coe.mpr g.2))
  choose d hdP hdA using h'
  refine ⟨∏ g, d g, Finset.prod_induction _ (· ∈ P) (fun a b ha hb => hPmul a ha b hb) hP1
    fun g _ => hdP g, ?_⟩
  intro b hb
  rw [← ht] at hb
  induction hb using Submodule.span_induction with
  | mem g hg =>
    have hg' : g ∈ t := Finset.mem_coe.mp hg
    rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ ⟨g, hg'⟩),
      show ∀ p q r : Ω, p * q * r = q * (p * r) from fun p q r => by ring]
    exact A.mul_mem (Finset.prod_induction _ (· ∈ A) (fun a b ha hb => A.mul_mem ha hb) A.one_mem
      fun g' _ => hPA _ (hdP g')) (hdA ⟨g, hg'⟩)
  | zero => rw [mul_zero]; exact A.zero_mem
  | add a b _ _ ha hb => rw [mul_add]; exact A.add_mem ha hb
  | smul c a _ ha =>
    change (∏ g, d g) * ((c : Ω) * a) ∈ A
    rw [mul_left_comm]
    exact A.mul_mem c.2 ha
end GroundTheory.Heights₂.Heights.Kleiman.Domination
