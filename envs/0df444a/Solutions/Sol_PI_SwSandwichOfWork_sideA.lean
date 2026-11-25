-- Prove2me | solution 1 for PI.SwSandwichOfWork.sideA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:55.789721+00:00
-- url     : https://prove2.me/submissions/1678b5ae-e9c3-412e-a336-ad2c6288e590

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SideAUnrealifyRL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
namespace PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
private theorem SideA_unrealify_RL (X : Mat k r) : unrealify (RL X) = X := by
  ext i j
  first
    | (apply Complex.ext <;> simp [unrealify, RL, realifyFun])
    | (apply Complex.ext <;> rfl)
private theorem SideA_rhoS_le (S : Set (Mat k r)) (X : Mat k r) (hX : RL X ∈ lieE S) (x : Mt k r)
    (hx : NormedSpace.exp X = Matrix.of x) :
    rhoS k r S x ^ 2 ≤ ENNReal.ofReal (‖RL X‖ ^ 2) := by
  have h1 : rhoS k r S x ≤ (‖(RL X : EuclideanSpace ℝ _)‖₊ : ℝ≥0∞) := by
    unfold rhoS
    refine iInf₂_le (⟨RL X, hX⟩ : lieE S) ?_
    funext i j
    simp only [SideA_unrealify_RL, hx, Matrix.of_apply]
  calc rhoS k r S x ^ 2 ≤ (‖(RL X : EuclideanSpace ℝ _)‖₊ : ℝ≥0∞) ^ 2 := by gcongr
    _ = ENNReal.ofReal (‖RL X‖ ^ 2) := by
      first
        | (rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_pow (norm_nonneg _)])
        | (rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl)
        | simp [ENNReal.ofReal_pow]
end PI.SwSandwichOfWork
end
end

set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
namespace PI.SwSandwichOfWork
theorem _root_.solution : SideA := by
  intro hNR hLG hLW hGU hPF hW0 hLEN hExpN hLI hCB k r ε hε hε1
  obtain ⟨δ, hδ, hCBδ⟩ := hCB k r (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun ρ hρ hρδ n c m n' hn hm hn' hPsi => ?_⟩
  obtain ⟨x, hxball, hxeq⟩ := hPsi
  have hxmem : (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) ∈
      (uH k r).map RL := by
    rw [← hLG k r]
    exact x.2
  obtain ⟨Y, hY, hYx⟩ := Submodule.mem_map.mp hxmem
  have hYn : ‖Y‖ < ρ := by
    rw [← hNR k r Y, hYx]
    exact mem_ball_zero_iff.mp hxball
  have hexpY : NormedSpace.exp Y =
      w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) := by
    ext i j
    have h := congrFun (congrFun hxeq i) j
    simp only [Psi] at h
    rw [← hYx, SideA_unrealify_RL] at h
    exact h
  obtain ⟨v, hv, hPhi, hvη, hLm⟩ := hCBδ Y hY (hYn.trans hρδ)
  have hv' := hv
  rw [Vs, Submodule.mem_prod, Submodule.mem_prod, Submodule.mem_prod] at hv'
  obtain ⟨hv1, -, hv3, hv4⟩ := hv'

  have hEq : Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹ =
      NormedSpace.exp v.1 * bigCell k r (1 + v.2.1) 1 * NormedSpace.exp v.2.2.1 *
        (NormedSpace.exp v.2.2.2)⁻¹ := by
    have h := hexpY.symm.trans (hPhi.symm.trans (hPF k r _ _ _ _))
    have h2 : w0B k r * (w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)) =
        w0B k r * (w0B k r * (NormedSpace.exp v.1 * bigCell k r (1 + v.2.1) 1 *
          NormedSpace.exp v.2.2.1 * (NormedSpace.exp v.2.2.2)⁻¹)) := by rw [h]
    simp only [← Matrix.mul_assoc, hW0 k r, Matrix.one_mul] at h2
    exact h2
  have hc2 : ∀ a, (1 + v.2.1) a ≠ 0 := by
    intro a h0
    have hxa : ‖v.2.1 a‖ < 1 := by
      calc ‖v.2.1 a‖ ≤ ‖v.2.1‖ := norm_le_pi_norm _ a
        _ ≤ ‖v.2‖ := norm_fst_le _
        _ ≤ ‖v‖ := norm_snd_le _
        _ < ε / 2 := hvη
        _ < 1 := by linarith
    have h1 : v.2.1 a = -1 := by
      simp only [Pi.add_apply, Pi.one_apply] at h0
      linear_combination h0
    rw [h1] at hxa
    simp at hxa
  obtain ⟨hnX, hcx, hmZ, hn'X'⟩ := hGU k r _ _ _ _ _ _ c (1 + v.2.1) hn (hExpN k r _ hv1) hm
    ((hLW k r).1 _ hv3) hn' (hExpN k r _ hv4) hc2 hEq
  have hA := SideA_rhoS_le (Nset k r) v.1
    (by rw [hLEN k r]; exact Submodule.mem_map_of_mem hv1) n hnX.symm
  have hB := SideA_rhoS_le (UWb k r) v.2.2.1
    (by rw [(hLW k r).2]; exact Submodule.mem_map_of_mem hv3) m hmZ.symm
  have hC := SideA_rhoS_le (Nset k r) v.2.2.2
    (by rw [hLEN k r]; exact Submodule.mem_map_of_mem hv4) n' hn'X'.symm
  have hcs : ∑ a, ‖c a - 1‖ ^ 2 = ∑ a, ‖v.2.1 a‖ ^ 2 := by
    rw [hcx]
    simp
  have hL0 : 0 ≤ ‖Lm k r v‖ := norm_nonneg _
  have hlt : ‖Lm k r v‖ < (1 + ε) * ρ := by
    have h1 : (1 - ε / 2) * ‖Lm k r v‖ < ρ := lt_of_le_of_lt hLm hYn
    nlinarith [mul_nonneg hε.le hL0, mul_nonneg (mul_nonneg hε.le (sub_nonneg.mpr hε1.le)) hL0]
  have hsq : ‖Lm k r v‖ ^ 2 < ((1 + ε) * ρ) ^ 2 := by nlinarith
  have hsum : ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2 =
      ‖Lm k r v‖ ^ 2 := by
    rw [← (hLI k r).2.2 v hv, hNR k r]
  unfold Qf
  calc rhoS k r (Nset k r) n ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) +
        rhoS k r (UWb k r) m ^ 2 + rhoS k r (Nset k r) n' ^ 2
      ≤ ENNReal.ofReal (‖RL v.1‖ ^ 2) + ENNReal.ofReal (2 * ∑ a, ‖v.2.1 a‖ ^ 2) +
        ENNReal.ofReal (‖RL v.2.2.1‖ ^ 2) + ENNReal.ofReal (‖RL v.2.2.2‖ ^ 2) := by
        rw [hcs]
        gcongr
    _ = ENNReal.ofReal (‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 +
        ‖RL v.2.2.2‖ ^ 2) := by
        rw [ENNReal.ofReal_add, ENNReal.ofReal_add, ENNReal.ofReal_add] <;> positivity
    _ = ENNReal.ofReal (‖Lm k r v‖ ^ 2) := by rw [hsum]
    _ < ENNReal.ofReal (((1 + ε) * ρ) ^ 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hsq
end PI.SwSandwichOfWork
