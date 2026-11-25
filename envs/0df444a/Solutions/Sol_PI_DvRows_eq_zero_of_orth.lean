-- Prove2me | solution 1 for PI.DvRows.eq_zero_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:43.742627+00:00
-- url     : https://prove2.me/submissions/49e62343-328e-4359-8090-e3e54cce1029

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_PI_DvRows_h_smul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (hH : IsHermE A e h) (hee : e * e = e) (hn : 0 < n) (S : Set A.V)
    (hS : Submodule.span K S = ⊤) (y : A.V) (hy : y ∈ LinearMap.range e)
    (h0 : ∀ g ∈ S, h (((n : ℕ) : 𝓞 K) • e g) y = 0) : y = 0 := by
  obtain ⟨hsym, hnd, hself⟩ := hH
  obtain ⟨z, rfl⟩ := hy
  have hez : e (e z) = e z := by
    show (e * e) z = e z
    rw [hee]
  have hS' : ∀ g ∈ S, h g (e z) = 0 := by
    intro g hg
    have := h0 g hg
    rw [h_smul_left, hself, hez] at this
    have hn0 : star (algebraMap (𝓞 K) K ((n : ℕ) : 𝓞 K)) ≠ 0 := by
      rw [map_natCast, star_natCast]
      exact_mod_cast hn.ne'
    exact (mul_eq_zero.1 this).resolve_left hn0
  have hall : ∀ x, h x (e z) = 0 := by
    intro x
    have hker : S ⊆ (LinearMap.ker (h.flip (e z)) : Set A.V) := by
      intro g hg
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]
      exact hS' g hg
    have hx : x ∈ LinearMap.ker (h.flip (e z)) := by
      have := Submodule.span_le.2 hker
      rw [hS] at this
      exact this Submodule.mem_top
    rwa [LinearMap.mem_ker, LinearMap.flip_apply] at hx
  apply hnd
  intro x
  rw [hsym x (e z), hall x, star_zero]
end PI.DvRows
