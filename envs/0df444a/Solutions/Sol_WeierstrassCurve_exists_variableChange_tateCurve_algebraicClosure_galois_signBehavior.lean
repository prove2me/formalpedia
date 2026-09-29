-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5c0ad6d4-f098-5881-bdc4-711609a8e28c

import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Theorems.Thm_WeierstrassCurve_variableChange_smul_eq_self_iff_of_tateNormalForm
import Theorems.Thm_WeierstrassCurve_exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer
import Theorems.Thm_TateCurve_nnnorm_c_six
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (hj : (TateCurve.curve qT).c₄ ^ 3
        = (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[p])
            * (TateCurve.curve qT).Δ) :
    ∃ (d : ℚ_[p]), ‖d‖₊ = 1 ∧
      ∃ (s : AlgebraicClosure ℚ_[p]), s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d ∧
        ∃ C : VariableChange (AlgebraicClosure ℚ_[p]),
          C • ((W.map (Int.castRingHom ℚ_[p])).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
            = (TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) ∧
          ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
            (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧
            (σ s ≠ s → C.map σ.toAlgHom.toRingHom
              = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p])) * C) := by
  set E' := (TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) with hE'

  have ha₁ : E'.a₁ = 1 := by simp only [E', map_a₁, TateCurve.curve, map_one]
  have ha₂ : E'.a₂ = 0 := by simp only [E', map_a₂, TateCurve.curve, map_zero]
  have ha₃ : E'.a₃ = 0 := by simp only [E', map_a₃, TateCurve.curve, map_zero]

  have hc₄_qp : (TateCurve.curve qT).c₄ ≠ 0 := fun h => by
    have := TateCurve.nnnorm_c₄ hqT1; rw [h, nnnorm_zero] at this; exact one_ne_zero this.symm
  have hc₆_qp : (TateCurve.curve qT).c₆ ≠ 0 := fun h => by
    have := TateCurve.nnnorm_c_six hqT1; rw [h, nnnorm_zero] at this; exact one_ne_zero this.symm
  have hc₄ : E'.c₄ ≠ 0 := by
    rw [hE', map_c₄]; exact fun h => hc₄_qp ((algebraMap ℚ_[p] _).injective (h.trans (map_zero _).symm))
  have hc₆ : E'.c₆ ≠ 0 := by
    rw [hE', map_c₆]; exact fun h => hc₆_qp ((algebraMap ℚ_[p] _).injective (h.trans (map_zero _).symm))

  have hstab : ∀ D : VariableChange (AlgebraicClosure ℚ_[p]), D • E' = E' →
      D = 1 ∨ D = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p])) := fun D hD =>
    (WeierstrassCurve.variableChange_smul_eq_self_iff_of_tateNormalForm E' ha₁ ha₂ ha₃ hc₄ hc₆ D).mp hD

  exact WeierstrassCurve.exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer
    W p hΔ hpΔ hpc₄ qT hqT0 hqT1 hj hstab

end S_WeierstrassCurve_exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior (solution)
