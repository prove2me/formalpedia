-- Prove2me | solution 1 for PadicAlgCl.norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c21b9ce1-4883-540c-9e2a-ef01bd838689

import Mathlib
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace TW8

open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p

section Setup

variable (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (E : IntermediateField F (PadicAlgCl p))

abbrev OF : Subalgebra ℤ_[p] F := integralClosure ℤ_[p] F

scoped instance towZFΩ : IsScalarTower ℤ_[p] F Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance algZE : Algebra ℤ_[p] E :=
  ((algebraMap (OF p F) E).comp (algebraMap ℤ_[p] (OF p F))).toAlgebra

scoped instance towZOE : IsScalarTower ℤ_[p] (OF p F) E := IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance towZEΩ : IsScalarTower ℤ_[p] E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

variable [FiniteDimensional ℚ_[p] F] [FiniteDimensional F E]

scoped instance isIntegrallyClosed_OF : IsIntegrallyClosed (OF p F) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension ℚ_[p] (R := ℤ_[p]) (L := F)

scoped instance isFractionRing_OF : IsFractionRing (OF p F) F :=
  IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] F (OF p F)

omit [FiniteDimensional ℚ_[p] F] [FiniteDimensional F E] in

lemma mem_one_iff_norm_le_one (t : F) :
    t ∈ (1 : Submodule (OF p F) F) ↔ ‖(t : Ω)‖ ≤ 1 := by
  rw [Submodule.mem_one, ← PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p (t : Ω),
    show ((t : F) : Ω) = algebraMap F Ω t from rfl,
    isIntegral_algebraMap_iff (algebraMap F Ω).injective]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro ht
    exact ⟨⟨t, ht⟩, rfl⟩

omit [FiniteDimensional ℚ_[p] F] [FiniteDimensional F E] in

lemma norm_le_one_of_isIntegral {y : E} (hy : IsIntegral (OF p F) y) : ‖(y : Ω)‖ ≤ 1 := by
  have h1 : IsIntegral ℤ_[p] y := isIntegral_trans y hy
  have h2 : IsIntegral ℤ_[p] (algebraMap E Ω y) := h1.algebraMap
  exact (PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p _).mp h2

omit [FiniteDimensional ℚ_[p] F] [FiniteDimensional F E] in

lemma isIntegral_of_norm_le_one {y : E} (hy : ‖(y : Ω)‖ ≤ 1) : IsIntegral (OF p F) y := by
  have h1 : IsIntegral ℤ_[p] (algebraMap E Ω y) :=
    (PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p _).mpr hy
  have h2 : IsIntegral ℤ_[p] y := (isIntegral_algebraMap_iff (algebraMap E Ω).injective).mp h1
  exact h2.tower_top

theorem main {α : E} (hα : ‖(α : Ω)‖ ≤ 1) (hgen : IntermediateField.adjoin F {α} = ⊤) (z : E)
    (hz : ∀ w : E, ‖(w : Ω)‖ ≤ 1 → ‖((Algebra.trace F E (z * w) : F) : Ω)‖ ≤ 1) :
    ‖((z * aeval α (derivative (minpoly F α)) : E) : Ω)‖ ≤ 1 := by
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  have hαF : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hαA : IsIntegral (OF p F) α := isIntegral_of_norm_le_one p F E hα

  have htop : Algebra.adjoin F {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαF.isAlgebraic, hgen,
      IntermediateField.top_toSubalgebra]

  have heuler := traceForm_dualSubmodule_adjoin (OF p F) F htop hαA
  set δ : E := aeval α (derivative (minpoly F α)) with hδdef
  have hδne : δ ≠ 0 :=
    (Algebra.IsSeparable.isSeparable F α).aeval_derivative_ne_zero (minpoly.aeval F α)

  have hzdual : z ∈ (Algebra.traceForm F E).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin (OF p F) {α})) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rw [Algebra.traceForm_apply, mem_one_iff_norm_le_one]
    refine hz y (norm_le_one_of_isIntegral p F E ?_)
    exact (mem_integralClosure_iff (↥(OF p F)) (↥E)).mp (adjoin_le_integralClosure hαA hy)
  rw [heuler, Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hδne), inv_inv,
    Subalgebra.mem_toSubmodule] at hzdual

  have hint : IsIntegral (OF p F) (δ * z) :=
    (mem_integralClosure_iff (↥(OF p F)) (↥E)).mp (adjoin_le_integralClosure hαA hzdual)
  rw [mul_comm]
  exact norm_le_one_of_isIntegral p F E hint

end Setup

end TW8
p2m_reactivate "P2MW.S_PadicAlgCl_norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one.TW8"

end
p2m_reactivate "P2MW.S_PadicAlgCl_norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one.TW8"

theorem solution
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F]
    (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] {α : E}
    (hα : ‖(α : PadicAlgCl p)‖ ≤ 1) (hgen : IntermediateField.adjoin F {α} = ⊤) (z : E)
    (hz : ∀ w : E, ‖(w : PadicAlgCl p)‖ ≤ 1 →
      ‖((Algebra.trace F E (z * w) : F) : PadicAlgCl p)‖ ≤ 1) :
    ‖((z * Polynomial.aeval α (Polynomial.derivative (minpoly F α)) : E) : PadicAlgCl p)‖ ≤ 1 :=
  TW8.main p F E hα hgen z hz

end S_PadicAlgCl_norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one
end P2MW
export P2MW.S_PadicAlgCl_norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one (solution)
