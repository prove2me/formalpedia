-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_module_finite_of_forall_isMaximal_5580b993f60a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:45.608643+00:00
-- url     : https://prove2.me/submissions/3c1a1a93-1ffe-475f-8871-369c56d4ce34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped nonZeroDivisors
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal →
      ∃ r ∉ 𝔪, ∃ N : Submodule A M, N.FG ∧ ∀ x : M, ∃ n : ℕ, r ^ n • x ∈ N) :
    Module.Finite A M := by
  classical
  choose! r hr N hN hx using h
  set s : Set A := r '' {𝔪 | 𝔪.IsMaximal}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr 𝔪 h𝔪 (hle (Ideal.subset_span ⟨𝔪, h𝔪, rfl⟩))
  obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  have hmt : ∀ a ∈ t, ∃ 𝔪 : Ideal A, 𝔪.IsMaximal ∧ r 𝔪 = a := fun a ha => hts ha
  choose! m hm hrm using hmt
  let P : Submodule A M := ⨆ a ∈ t, N (m a)
  have hP : P.FG := Submodule.fg_biSup t _ fun a ha => hN (m a) (hm a ha)
  suffices hPt : P = ⊤ from ⟨hPt ▸ hP⟩
  rw [eq_top_iff]
  rintro x -
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem P (t : Set A) ht x ?_
  rintro ⟨a, ha⟩
  obtain ⟨n, hn⟩ := hx (m a) (hm a ha) x
  refine ⟨n, ?_⟩
  have hle : N (m a) ≤ P := le_iSup₂ (f := fun a (_ : a ∈ t) => N (m a)) a ha
  show a ^ n • x ∈ P
  rw [← hrm a ha]
  exact hle hn
end GroundTheory.Heights₂.Heights.Model
