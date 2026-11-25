-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.orth_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:51.9745+00:00
-- url     : https://prove2.me/submissions/c0770604-0d14-4bea-a49f-11b4e72c93a5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_IsoRightInv
import Theorems.Thm_PI_PolynomialProperness_CoreW_key_ineq
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_H
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_nonneg
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_sq
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_sub
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_H_self
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_conj
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_le
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_proj_right
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_smul_left
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_sub_left
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_sub_right
import Theorems.Thm_PI_PolynomialProperness_CoreW_proj_bound
import Theorems.Thm_PI_PolynomialProperness_CoreW_proj_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
open PI.PolynomialProperness.CoreW
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.PolynomialProperness.CoreW
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (Γi : Matrix ι ι ℂ) (q : ι → Fin n → ℂ) (hG : gramOf H q * Γi = 1) (R : ℝ) (hR : 0 ≤ R)
    (hq : ∀ k, eN (q k) ≤ R) (hpsd : ∀ w, (∀ i, herm H w (q i) = 0) → 0 ≤ (herm H w w).re)
    (v : Fin n → ℂ) (hv : ∀ j, herm H v (q j) = 0) :
    nsq v ≤ (1 + (Fintype.card ι : ℝ) * (∑ j, ∑ k, ‖Γi j k‖) * (R * R)) * (herm H v v).re := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ j, ∑ k, ‖Γi j k‖ := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg _
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 + (Fintype.card ι : ℝ) * A * (R * R) := ⟨_, rfl⟩
  rw [← hcdef]
  have hc : 0 < c := by
    have := mul_nonneg (mul_nonneg (Nat.cast_nonneg (Fintype.card ι)) hA0) (mul_self_nonneg R)
    rw [hcdef]
    linarith
  obtain ⟨y, hy⟩ : ∃ y, y = H *ᵥ v := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y', y' = y - proj H Γi q y := ⟨_, rfl⟩
  have hy'q : ∀ j, herm H y' (q j) = 0 := fun j => by
    rw [hy']
    exact proj_orth H Γi q hG y j
  have hvy : herm H v y' = ((nsq v : ℝ) : ℂ) := by
    rw [hy', herm_sub_right H hH, herm_proj_right H hH Γi q y v hv, sub_zero, hy,
      herm_H_self H hH hHH]
  have hyv : herm H y' v = ((nsq v : ℝ) : ℂ) := by
    rw [← herm_conj H hH, hvy, Complex.conj_ofReal]
  have e1 : herm H y' (y - proj H Γi q y) = herm H y' y := by
    rw [herm_sub_right H hH, herm_proj_right H hH Γi q y y' hy'q, sub_zero]
  rw [← hy'] at e1
  have hey : eN y = eN v := by
    rw [hy]
    exact eN_H H hH hHH v
  have hpb := proj_bound H hH hHH Γi q R hR hq y
  rw [← hA, hey] at hpb
  have hey' : eN y' ≤ eN v * c := by
    calc eN y' ≤ eN y + eN (proj H Γi q y) := by
          rw [hy']
          exact eN_sub _ _
      _ ≤ eN v + (Fintype.card ι : ℝ) * (A * (eN v * R)) * R := by
          rw [hey]
          linarith
      _ = eN v * c := by
          rw [hcdef]
          ring
  have hyy : (herm H y' y').re ≤ c * nsq v := by
    calc (herm H y' y').re ≤ ‖herm H y' y'‖ := Complex.re_le_norm _
      _ = ‖herm H y' y‖ := by rw [e1]
      _ ≤ eN y' * eN y := herm_le H hH hHH y' y
      _ ≤ (eN v * c) * eN v := by
          rw [hey]
          exact mul_le_mul_of_nonneg_right hey' (eN_nonneg _)
      _ = c * nsq v := by
          rw [← eN_sq]
          ring
  have hpos : 0 ≤ (herm H ((c : ℂ) • v - y') ((c : ℂ) • v - y')).re := by
    apply hpsd
    intro i
    rw [herm_sub_left H, herm_smul_left H, hv i, hy'q i, mul_zero, sub_zero]
  exact key_ineq H hH c hc v y' hvy hyv hyy hpos
end PI.PolynomialProperness.CoreW
