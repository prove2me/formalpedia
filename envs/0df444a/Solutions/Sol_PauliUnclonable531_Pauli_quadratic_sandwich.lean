-- Prove2me | solution 1 for PauliUnclonable531.Pauli.quadratic_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:11:38.852504+00:00
-- url     : https://prove2.me/submissions/c3f3eeed-e717-434d-bf58-6432cf12ed17

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations
import Theorems.Thm_PauliUnclonable531_Pauli_difference_order
import Theorems.Thm_PauliUnclonable531_Pauli_psd_blocks
import Theorems.Thm_PauliUnclonable531_Pauli_filter_properties

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.Sandwich

open PauliUnclonable531.Pauli

lemma corner_psd {X : Type} [Fintype X] [DecidableEq X] (P : Op X) (hP : P.PosSemidef) :
    (Matrix.fromBlocks (0 : Op X) 0 0 P).PosSemidef := by
  open scoped MatrixOrder in
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  have h := Matrix.posSemidef_conjTranspose_mul_self (Matrix.fromBlocks (0 : Op X) 0 0 S)
  convert h using 1
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.star_eq_conjTranspose]

end PauliUnclonable531.Pauli.Sandwich

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Sandwich in
theorem solution {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) (t : ℝ) (ht : 0 < t) :
    Below ((EB a - EC a) * filterOperator a t * (EB a - EC a))
      ((2 * (t : ℂ)) • disagreement a) := by
  obtain ⟨hZpd, -, -, -, -⟩ := filter_properties n hn a t ht
  obtain ⟨hlow, hup⟩ := difference_order n hn a
  set D := disagreement a
  set T := EB a - EC a
  set Z := (2 * (t : ℂ)) • (1 : Op (Bits n × (B × C))) + D with hZ
  unfold Below at hlow hup
  have h2t : (0 : ℝ) ≤ 2 * t := by linarith
  have hsc : (2 * (t : ℂ)) • (1 : Op (Bits n × (B × C))) = (2 * t : ℝ) • (1 : Op _) := by
    rw [← Complex.coe_smul]; push_cast; rfl
  have hDH : D.IsHermitian := by
    have h1 : ((2 * (t : ℂ)) • (1 : Op (Bits n × (B × C)))).IsHermitian := by
      rw [hsc]; exact (Matrix.PosSemidef.one.smul h2t).isHermitian
    have := hZpd.isHermitian.sub h1
    rwa [hZ, add_sub_cancel_left] at this
  have hplus : (D + T).PosSemidef := by
    rw [sub_neg_eq_add, add_comm] at hlow; exact hlow
  have hTH : T.IsHermitian := by
    have := hplus.isHermitian.sub hDH
    rwa [add_sub_cancel_left] at this
  have hblock := ((psd_blocks D T D hDH hTH hDH).2).mpr ⟨hup, hplus⟩
  have hcorner := corner_psd ((2 * (t : ℂ)) • (1 : Op (Bits n × (B × C))))
    (by rw [hsc]; exact Matrix.PosSemidef.one.smul h2t)
  have hreg : (Matrix.fromBlocks D T T Z).PosSemidef := by
    have := hblock.add hcorner
    rw [Matrix.fromBlocks_add] at this
    simpa [hZ, add_comm] using this
  have hschur := ((psd_blocks D T Z hDH hTH hZpd.isHermitian).1 hZpd).mp hreg
  have hF : filterOperator a t = (2 * (t : ℂ)) • Z⁻¹ := by
    rw [hZ]; rfl
  have heq : (2 * (t : ℂ)) • D - T * filterOperator a t * T = (2 * t : ℝ) • (D - T * Z⁻¹ * T) := by
    rw [hF, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul, smul_sub]
    push_cast
    rfl
  unfold Below
  rw [heq]
  exact hschur.smul h2t
