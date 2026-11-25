-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.hJ_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:57:11.072246+00:00
-- url     : https://prove2.me/submissions/2a5ffb72-998d-468b-9b1c-1513dd003db5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_sum
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_conj
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_fe
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_f_Pw
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_e_Pw
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open Matrix
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) (x y : Fin n → ℂ) :
    hJ ε (Afun ε e f s x) (Afun ε e f s y) = hJ ε x y := by
  have addl : ∀ x x' y, hJ ε (x + x') y = hJ ε x y + hJ ε x' y := fun x x' y => by
    rw [hJ_conj ε y (x + x'), hJ_add, star_add, ← hJ_conj ε y x, ← hJ_conj ε y x']
  have smull : ∀ (c : ℂ) x y, hJ ε (c • x) y = star c * hJ ε x y := fun c x y => by
    rw [hJ_conj ε y (c • x), hJ_smul, star_mul', ← hJ_conj ε y x]
  have suml : ∀ (g : Fin r → Fin n → ℂ) y, hJ ε (∑ b, g b) y = ∑ b, hJ ε (g b) y := fun g y => by
    rw [hJ_conj ε y, hJ_sum, star_sum]
    exact Finset.sum_congr rfl fun b _ => (hJ_conj ε y (g b)).symm
  have ePw : ∀ b v, hJ ε (e b) (Pw ε e f v) = 0 := e_Pw hG
  have fPw : ∀ b v, hJ ε (f b) (Pw ε e f v) = 0 := f_Pw hG
  have Pwe : ∀ b v, hJ ε (Pw ε e f v) (e b) = 0 := fun b v => by rw [hJ_conj, ePw, star_zero]
  have Pwf : ∀ b v, hJ ε (Pw ε e f v) (f b) = 0 := fun b v => by rw [hJ_conj, fPw, star_zero]
  have key : ∀ (α β α' β' : Fin r → ℂ) (v v' : Fin n → ℂ),
      hJ ε (∑ b, α b • e b + ∑ b, β b • f b + Pw ε e f v)
        (∑ b, α' b • e b + ∑ b, β' b • f b + Pw ε e f v') =
        ∑ b, (star (α b) * β' b + star (β b) * α' b) + hJ ε (Pw ε e f v) (Pw ε e f v') := by
    intro α β α' β' v v'
    simp only [addl, hJ_add, suml, hJ_sum, smull, hJ_smul, hG.ee, hG.ff, hG.ef, fe hG, ePw, fPw,
      Pwe, Pwf, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_add_distrib]
    try ring
  have dec : ∀ v, v = ∑ b, hJ ε (f b) v • e b + ∑ b, hJ ε (e b) v • f b + Pw ε e f v := fun v => by
    unfold Pw
    abel
  have hA : ∀ v, Afun ε e f s v = ∑ b, ((s b : ℂ) * hJ ε (f b) v) • e b +
      ∑ b, ((s b : ℂ)⁻¹ * hJ ε (e b) v) • f b + Pw ε e f v := fun v => rfl
  rw [hA, hA, key]
  conv_rhs => rw [dec x, dec y, key]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  have hsb : (s b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hs b)
  have hst : star (s b : ℂ) = s b := by
    first
      | simp
      | exact Complex.conj_ofReal _
  rw [star_mul', star_mul', star_inv₀, hst]
  field_simp
  try ring
end PI.NMeasInv.UnitaryGroupMassFormula
