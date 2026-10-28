-- Prove2me | solution 1 for ProdHedgeCVaR.Joint.eq_49
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T14:46:50.277691+00:00
-- url     : https://prove2.me/submissions/83b62433-34e4-43e1-93d3-f9edc5b1e4a8

import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

theorem eq_49 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC : ℝ) (hlamC : M.IsLamC α lamC) :
    1 - α = ∫ ω, (1 - max (1 - lamC * M.Z ω) 0) ∂M.P ∧
    ∫ ω, (1 - max (1 - lamC * M.Z ω) 0) ∂M.P = ∫ ω, min 1 (lamC * M.Z ω) ∂M.P ∧
    ∫ ω, min 1 (lamC * M.Z ω) ∂M.P ≤ lamC * ∫ ω, M.Z ω ∂M.P ∧
    lamC * ∫ ω, M.Z ω ∂M.P = lamC := by
  haveI := hM.isProb
  have hWm : Measurable M.W := hM.W_meas.mono hM.G_le le_rfl
  have hZeq : ∀ ω, M.Z ω = Real.exp (-M.θ.eta ^ 2 * M.θ.T / 2) *
      Real.exp ((-M.θ.eta) * M.W ω) := by
    intro ω
    unfold Model.Z
    rw [← Real.exp_add]; congr 1; ring
  have hmgf := mgf_gaussianReal hM.W_law (-M.θ.eta)
  have hTnn : ((M.θ.T.toNNReal : NNReal) : ℝ) = M.θ.T :=
    Real.coe_toNNReal _ hM.params.T_pos.le
  have hexpInt : Integrable (fun ω => Real.exp ((-M.θ.eta) * M.W ω)) M.P := by
    have : 0 < mgf M.W M.P (-M.θ.eta) := by rw [hmgf]; exact Real.exp_pos _
    exact (mgf_pos_iff.mp this)
  have hZint : Integrable M.Z M.P := by
    have : M.Z = fun ω => Real.exp (-M.θ.eta ^ 2 * M.θ.T / 2) *
        Real.exp ((-M.θ.eta) * M.W ω) := funext hZeq
    rw [this]; exact hexpInt.const_mul _
  have hZ1 : ∫ ω, M.Z ω ∂M.P = 1 := by
    simp_rw [hZeq]
    rw [integral_const_mul]
    have : ∫ ω, Real.exp ((-M.θ.eta) * M.W ω) ∂M.P = mgf M.W M.P (-M.θ.eta) := rfl
    rw [this, hmgf, hTnn, ← Real.exp_add]
    rw [show -M.θ.eta ^ 2 * M.θ.T / 2 + (0 * -M.θ.eta + M.θ.T * (-M.θ.eta) ^ 2 / 2) = 0 by ring]
    simp
  have hZmeas : Measurable M.Z := by
    unfold Model.Z; fun_prop
  have hlamZint : Integrable (fun ω => lamC * M.Z ω) M.P := hZint.const_mul _
  have hmaxInt : Integrable (fun ω => max (1 - lamC * M.Z ω) 0) M.P :=
    ((integrable_const 1).sub hlamZint).sup (integrable_const 0)
  have hminInt : Integrable (fun ω => min 1 (lamC * M.Z ω)) M.P :=
    (integrable_const 1).inf hlamZint
  have hb : ∫ ω, max (1 - lamC * M.Z ω) 0 ∂M.P = α := hlamC
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [integral_sub (integrable_const 1) hmaxInt, hb]
    simp
  · congr 1; funext ω
    rcases le_total 1 (lamC * M.Z ω) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  · rw [← integral_const_mul]
    exact integral_mono hminInt hlamZint (fun ω => min_le_right _ _)
  · rw [hZ1, mul_one]

end ProdHedgeCVaR.Joint


-- Platform entry point: restates the target verbatim.
namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- (49), p. 19: if λ° solves the first equation of (45), then
1 − α = E[1 − (1 − λ°Z_T)⁺] = E(1 ∧ λ°Z_T) ≤ λ°E(Z_T) = λ°. -/
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC : ℝ) (hlamC : M.IsLamC α lamC) :
    1 - α = ∫ ω, (1 - max (1 - lamC * M.Z ω) 0) ∂M.P ∧
    ∫ ω, (1 - max (1 - lamC * M.Z ω) 0) ∂M.P = ∫ ω, min 1 (lamC * M.Z ω) ∂M.P ∧
    ∫ ω, min 1 (lamC * M.Z ω) ∂M.P ≤ lamC * ∫ ω, M.Z ω ∂M.P ∧
    lamC * ∫ ω, M.Z ω ∂M.P = lamC := by
  apply @ProdHedgeCVaR.Joint.eq_49 <;> assumption

end ProdHedgeCVaR.Joint
