-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_mem_2f9ce7653ab7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:49:47.070105+00:00
-- url     : https://prove2.me/submissions/8dfdba5a-9229-451b-b08d-69c700958b22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIsotropicScaling
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_apply_eff752ab2046
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_conj_mem_integralClosure_f3da3bddeddb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_congruenceUnits_f43d8290014c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
theorem _root_.solution (h : HermitianForm F E W) {La : AddSubgroup W} (hLa : IsLattice E La)
    (hint : IsIntegralOn h La) {v w : W} (hv : v ∈ La) {N : ℕ} (hNw : N • w ∈ La)
    {u : (𝓞 E)ˣ} (hu : u ∈ congruenceUnits E N) {x : W} (hx : x ∈ La) :
    scalingMap h v w (((u : 𝓞 E) : E) - 1) ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) x ∈ La := by
  have smem : ∀ z ∈ integralClosure ℤ E, ∀ y ∈ La, z • y ∈ La :=
    fun z hz y hy => hLa.smul_mem ⟨z, hz⟩ y hy
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (mem_congruenceUnits.1 hu)
  have ht' : ((u : 𝓞 E) : E) - 1 = (t : E) * N := by exact_mod_cast ht.symm
  have hu0 : conj F E ((u : 𝓞 E) : E) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast u.ne_zero
  have hinv : (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((u : 𝓞 E) : E)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    exact_mod_cast u.inv_mul
  have hN : h.toSesq (N • w) x = N * h.toSesq w x := by
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  have e2 : ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) * h.toSesq v x =
      (-conj F E (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * conj F E (t : E) * h.toSesq v x) * N := by
    have hct : conj F E ((u : 𝓞 E) : E) - 1 = conj F E (t : E) * N := by
      rw [← map_one (conj F E), ← map_sub, ht', map_mul, map_natCast]
    rw [hinv, map_inv₀]
    field_simp
    linear_combination (-h.toSesq v x) * hct
  have key : scalingMap h v w (((u : 𝓞 E) : E) - 1) ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) x =
      x + ((t : E) * h.toSesq (N • w) x) • v +
        (-conj F E (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * conj F E (t : E) * h.toSesq v x) • (N • w) := by
    rw [scalingMap_apply, e2, ht', hN, ← Nat.cast_smul_eq_nsmul E]
    module
  rw [key]
  refine add_mem (add_mem hx (smem _ ?_ v hv)) (smem _ ?_ _ hNw)
  · exact mul_mem t.2 (hint _ hNw x hx)
  · exact mul_mem (mul_mem (neg_mem (conj_mem_integralClosure (u⁻¹ : (𝓞 E)ˣ).val.2))
      (conj_mem_integralClosure t.2)) (hint v hv x hx)
end GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
