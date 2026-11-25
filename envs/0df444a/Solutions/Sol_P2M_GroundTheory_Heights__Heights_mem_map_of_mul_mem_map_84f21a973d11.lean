-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_map_of_mul_mem_map_84f21a973d11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:48.742937+00:00
-- url     : https://prove2.me/submissions/18ef36d4-be8c-49f2-ac6f-5267fd81aa0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadicalPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) (K : Ideal R) (hK : K.IsPrime) (b : R) (hb : b ∉ K)
    (h : (K ⊔ Ideal.span {b}) ⊓ RingHom.ker φ ≤ RingHom.ker φ * (K ⊔ Ideal.span {b}))
    (g : R') (hg : φ b * g ∈ K.map φ) : g ∈ K.map φ := by
  obtain ⟨a, rfl⟩ := hφ g
  rw [← map_mul] at hg
  obtain ⟨κ, hκ, hκa⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hg
  have hμ : b * a - κ ∈ (K ⊔ Ideal.span {b}) ⊓ RingHom.ker φ :=
    ⟨Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b)))
      (Ideal.mem_sup_left hκ), RingHom.mem_ker.2 (by rw [map_sub, hκa, sub_self])⟩
  have h2 := h hμ
  rw [Ideal.mul_sup] at h2
  obtain ⟨κ', hκ', w, hw, hsum⟩ := Submodule.mem_sup.1 h2
  obtain ⟨ν, hν, hνw⟩ := (Ideal.mem_mul_span_singleton (I := RingHom.ker φ)).1 hw
  have hκ'K : κ' ∈ K := (Ideal.mul_le_inf hκ').2
  have hb' : b * (a - ν) ∈ K := by
    have e : b * (a - ν) = κ + κ' := by linear_combination -hsum - hνw
    rw [e]
    exact K.add_mem hκ hκ'K
  have haν : a - ν ∈ K := (hK.mem_or_mem hb').resolve_left hb
  have : φ a = φ (a - ν) := by rw [map_sub, RingHom.mem_ker.1 hν, sub_zero]
  rw [this]
  exact Ideal.mem_map_of_mem φ haν
end GroundTheory.Heights₂.Heights
