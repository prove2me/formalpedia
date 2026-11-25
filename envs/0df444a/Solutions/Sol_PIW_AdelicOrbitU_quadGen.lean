-- Prove2me | solution 1 for PIW.AdelicOrbitU.quadGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:46.516967+00:00
-- url     : https://prove2.me/submissions/a3684e05-7c73-4228-a679-cc291d715c6d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
namespace PIW.AdelicOrbitU
theorem _root_.solution : QuadGen := by
  intro F E _ _ _ _ σ hfin hfix
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hfin
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨e, he⟩ : ∃ e : E, e ∉ (algebraMap F E).range := by
    by_contra h
    push_neg at h
    have hle : Module.finrank F E ≤ 1 := by
      refine finrank_le_one (1 : E) fun w => ?_
      obtain ⟨c, hc⟩ := h w
      exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩
    omega
  have hli : LinearIndependent F ![(1 : E), e] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply he
      refine RingHom.mem_range.mpr ⟨-s * t⁻¹, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have hT : algebraMap F E t ≠ 0 := (map_ne_zero _).mpr ht
      have h' := mul_inv_cancel₀ hT
      rw [map_mul, map_neg, map_inv₀]
      linear_combination (-(algebraMap F E t)⁻¹) * hst + e * h'
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [hfin, Fintype.card_fin]
  obtain ⟨Bs, hBs⟩ : ∃ Bs : Module.Basis (Fin 2) F E, ⇑Bs = ![(1 : E), e] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard,
      coe_basisOfLinearIndependentOfCardEqFinrank hli hcard⟩
  have hspan : ∀ x : E, ∃ c0 c1 : F, x = algebraMap F E c0 + algebraMap F E c1 * e := by
    intro x
    refine ⟨Bs.repr x 0, Bs.repr x 1, ?_⟩
    nth_rewrite 1 [← Bs.sum_repr x]
    rw [Fin.sum_univ_two, hBs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Algebra.smul_def, mul_one]
  obtain ⟨v, u, hsq⟩ := hspan (e ^ 2)
  have hse : σ e ≠ e := fun h => he ((hfix e).mp h)
  have hσsq : σ e ^ 2 = algebraMap F E v + algebraMap F E u * σ e := by
    rw [← map_pow, hsq, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]
  have hsum : σ e = algebraMap F E u - e := by
    have h0 : (σ e - e) * (σ e + e - algebraMap F E u) = 0 := by
      linear_combination hσsq - hsq
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) hse
    · linear_combination h
  have hθsq : (2 * e - algebraMap F E u) ^ 2 = algebraMap F E (4 * v + u ^ 2) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hsq
  refine ⟨2 * e - algebraMap F E u, 4 * v + u ^ 2, hθsq, ?_, ?_, ?_⟩
  · rw [map_sub, map_mul, map_ofNat, AlgHom.commutes, hsum]
    ring
  · intro hd0
    rw [hd0, map_zero] at hθsq
    have h2 : 2 * e - algebraMap F E u = 0 := (pow_eq_zero_iff two_ne_zero).mp hθsq
    apply hse
    rw [hsum]
    linear_combination -1 * h2
  · intro x
    obtain ⟨c0, c1, hx⟩ := hspan x
    refine ⟨c0 + c1 * u / 2, c1 / 2, ?_⟩
    rw [hx]
    simp only [map_add, map_mul, map_div₀, map_ofNat]
    ring
end PIW.AdelicOrbitU
