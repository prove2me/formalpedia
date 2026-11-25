-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrA.cong_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:41.667042+00:00
-- url     : https://prove2.me/submissions/24c61468-9514-47b6-b44f-77a25dd45b61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocalDataSatisfyLinearHypotheses
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_inv_mem_of_val
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_hl_int
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_hl_smul_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_hl_sub_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_hl_swap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrA
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrA
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) {g c : ℕ} (hc : Valued.v ((c : v.adicCompletion I.F)) = 1)
    (X X0 Z w : Fin I.n → RV I v)
    (hZ : Z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    (hw : w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    (hD : (c : RV I v) • (X0 - X) = (g : RV I v) • w) (q : RV I v)
    (hq : hl I v X0 Z = (g : RV I v) * q) (hq1 : p1 q ∈ OV I v) (hq2 : p1 (sigV I v q) ∈ OV I v) :
    (∃ s ∈ OV I v, p1 (hl I v X Z) = (g : KV I v) * s) ∧
      (∃ s ∈ OV I v, p1 (hl I v Z X) = (g : KV I v) * s) := by
  have hc0 : (c : KV I v) ≠ 0 := by
    intro h0
    have h0' : ((c : v.adicCompletion I.F)) = 0 := h0
    rw [h0', map_zero] at hc
    exact zero_ne_one hc
  have hinv : ((c : KV I v))⁻¹ * (c : KV I v) = 1 := inv_mul_cancel₀ hc0
  have hci := inv_mem_of_val I v c hc
  have hsig : ∀ m : ℕ, sigV I v (m : RV I v) = m := fun m => map_natCast _ m
  have key : (c : RV I v) * hl I v X Z = (g : RV I v) * ((c : RV I v) * q - hl I v w Z) := by
    have h1 : hl I v X Z = hl I v X0 Z - hl I v (X0 - X) Z := by rw [hl_sub_left]; ring
    have h2 : hl I v ((c : RV I v) • (X0 - X)) Z = hl I v ((g : RV I v) • w) Z := by rw [hD]
    rw [hl_smul_left, hl_smul_left, hsig, hsig] at h2
    rw [h1, mul_sub, h2, hq]
    ring
  have key2 : (c : RV I v) * hl I v Z X = (g : RV I v) * ((c : RV I v) * sigV I v q - hl I v Z w) := by
    have h3 : sigV I v ((c : RV I v) * hl I v X Z) =
        sigV I v ((g : RV I v) * ((c : RV I v) * q - hl I v w Z)) := by rw [key]
    simp only [map_mul, map_sub, hsig] at h3
    rw [hl_swap I v X Z, hl_swap I v w Z]
    exact h3
  have hwZ := hl_int I v ε p1 hp w Z hw hZ
  have hZw := hl_int I v ε p1 hp Z w hZ hw
  constructor
  · refine ⟨((c : KV I v))⁻¹ * ((c : KV I v) * p1 q - p1 (hl I v w Z)),
      mul_mem hci (sub_mem (mul_mem (natCast_mem _ c) hq1) hwZ), ?_⟩
    have k1 := congrArg p1 key
    simp only [map_mul, map_sub, map_natCast] at k1
    linear_combination ((c : KV I v))⁻¹ * k1 - p1 (hl I v X Z) * hinv
  · refine ⟨((c : KV I v))⁻¹ * ((c : KV I v) * p1 (sigV I v q) - p1 (hl I v Z w)),
      mul_mem hci (sub_mem (mul_mem (natCast_mem _ c) hq2) hZw), ?_⟩
    have k1 := congrArg p1 key2
    simp only [map_mul, map_sub, map_natCast] at k1
    linear_combination ((c : KV I v))⁻¹ * k1 - p1 (hl I v Z X) * hinv
end PI.UnitaryGroupMassFormula.ScXuExists.BrA
