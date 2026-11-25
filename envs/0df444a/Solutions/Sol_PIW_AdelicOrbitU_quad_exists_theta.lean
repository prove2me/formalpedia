-- Prove2me | solution 1 for PIW.AdelicOrbitU.quad_exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:38:02.018728+00:00
-- url     : https://prove2.me/submissions/d3a5adb3-6ca6-42e9-b4ef-ce1e7d5d2f87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Theorems.Thm_PIW_AdelicOrbitU_quad_exists_not_mem
import Theorems.Thm_PIW_AdelicOrbitU_quad_li
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
section Field
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
private lemma linearIndependent_one_of_not_mem_range {a : E} (ha : a ∉ (algebraMap F E).range) :
    LinearIndependent F ![(1 : E), a] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    refine ⟨?_, rfl⟩
    simpa using hst
  · exfalso
    apply ha
    refine ⟨-(s / t), ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    have h' : t • a = -(s • (1 : E)) := by
      linear_combination hst
    calc (-(s / t)) • (1 : E) = t⁻¹ • (-(s • (1 : E))) := by
          rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      _ = t⁻¹ • (t • a) := by rw [h']
      _ = a := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
private lemma exists_eq_add_mul_of_finrank_two_of_linearIndependent (h2 : Module.finrank F E = 2) {a : E}
    (hli : LinearIndependent F ![(1 : E), a]) (z : E) :
    ∃ p q : F, z = algebraMap F E p + algebraMap F E q * a := by
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hb : ⇑b = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  refine ⟨b.repr z 0, b.repr z 1, ?_⟩
  conv_lhs => rw [← b.sum_repr z]
  rw [Fin.sum_univ_two, hb]
  simp [Algebra.smul_def]
private lemma exists_mul_self_eq_and_sigma_eq_sub_of_not_mem (h2 : Module.finrank F E = 2)
    (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) {a : E}
    (ha : a ∉ (algebraMap F E).range) :
    ∃ s t : F, a * a = algebraMap F E t + algebraMap F E s * a ∧ σ a = algebraMap F E s - a := by
  obtain ⟨t, s, hts⟩ := exists_eq_add_mul_of_finrank_two_of_linearIndependent h2 (linearIndependent_one_of_not_mem_range ha) (a * a)
  refine ⟨s, t, hts, ?_⟩
  have hσ := congrArg σ hts
  simp only [map_mul, map_add, AlgHom.commutes] at hσ
  have hne : σ a ≠ a := fun h => ha ((hfix a).mp h)
  have key : (σ a - a) * (σ a + a - algebraMap F E s) = 0 := by
    linear_combination hσ - hts
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linear_combination h
end Field
section Ring
variable {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
  (h2 : Module.finrank F E = 2) {θ : E} (hli : LinearIndependent F ![(1 : E), θ])
  (R : Type) [CommRing R] [Algebra F R]
end Ring
end PIW.AdelicOrbitU
end
end

set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
namespace PIW.AdelicOrbitU
theorem _root_.solution [CharZero F] (h2 : Module.finrank F E = 2)
    (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) :
    ∃ θ : E, θ ≠ 0 ∧ σ θ = -θ ∧ (∃ d : F, d ≠ 0 ∧ θ * θ = algebraMap F E d) ∧
      LinearIndependent F ![(1 : E), θ] := by
  obtain ⟨a, ha⟩ := quad_exists_not_mem h2
  obtain ⟨s, t, hts, hs⟩ := exists_mul_self_eq_and_sigma_eq_sub_of_not_mem σ h2 hfix ha
  have hσθ : σ (2 * a - algebraMap F E s) = -(2 * a - algebraMap F E s) := by
    simp only [map_sub, map_mul, map_ofNat, AlgHom.commutes, hs]
    ring
  have hθ0 : 2 * a - algebraMap F E s ≠ 0 := by
    intro h
    apply ha
    refine ⟨2⁻¹ * s, ?_⟩
    have e : algebraMap F E 2⁻¹ * 2 = 1 := by
      rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
    rw [map_mul]
    linear_combination (-(algebraMap F E 2⁻¹)) * h + a * e
  have hsq : (2 * a - algebraMap F E s) * (2 * a - algebraMap F E s) =
      algebraMap F E (4 * t + s ^ 2) := by
    rw [map_add, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hts
  have hd0 : (4 * t + s ^ 2 : F) ≠ 0 := by
    intro hd
    apply hθ0
    have h0 : (2 * a - algebraMap F E s) * (2 * a - algebraMap F E s) = 0 := by
      rw [hsq, hd, map_zero]
    exact mul_self_eq_zero.mp h0
  exact ⟨_, hθ0, hσθ, ⟨4 * t + s ^ 2, hd0, hsq⟩, quad_li σ hθ0 hσθ⟩
end PIW.AdelicOrbitU
