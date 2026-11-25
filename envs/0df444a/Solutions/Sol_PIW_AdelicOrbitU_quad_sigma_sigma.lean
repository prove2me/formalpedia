-- Prove2me | solution 1 for PIW.AdelicOrbitU.quad_sigma_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:22:19.907984+00:00
-- url     : https://prove2.me/submissions/cd837838-aa26-40ca-94d6-a801f1b3f3e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
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
theorem _root_.solution (h2 : Module.finrank F E = 2)
    (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) (a : E) : σ (σ a) = a := by
  by_cases ha : a ∈ (algebraMap F E).range
  · rw [(hfix a).mpr ha, (hfix a).mpr ha]
  · obtain ⟨s, t, -, hs⟩ := exists_mul_self_eq_and_sigma_eq_sub_of_not_mem σ h2 hfix ha
    rw [hs, map_sub, AlgHom.commutes, hs]
    ring
end PIW.AdelicOrbitU
