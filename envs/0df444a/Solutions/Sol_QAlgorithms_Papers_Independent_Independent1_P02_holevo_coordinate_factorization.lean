-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.holevo_coordinate_factorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:00:03.78437+00:00
-- url     : https://prove2.me/submissions/8a9df823-c7ea-49f8-b7d8-c3afd16336e2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P02
/-- Section 4, PDF pp.12–13. Proposed correction T=W U^T replaces the
dimensionally invalid W^T U; the entrywise formula is unchanged.
Pending independent source moderation. -/
theorem gk_herm_im {d : ℕ} (A B : Algebra d) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace.im = 0 := by
  have h : star ((A * B).trace) = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  have := congrArg Complex.im h
  simp at this
  linarith

theorem gk_frame_zero {d : ℕ} (G : HermitianFrame d) (H : Algebra d) (hH : H.IsHermitian)
    (h : ∀ j, (H * G.matrix j).trace.re = 0) : H = 0 := by
  have hs := G.spans H hH
  have key : ∀ Y ∈ Submodule.span ℝ (Set.range G.matrix), (H * Y).trace.re = 0 := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, hx, smul_zero]
  have h1 := key H hs
  have h2 := gk_herm_im H H hH hH
  have h3 : (Hᴴ * H).trace = 0 := by
    rw [hH.eq]; exact Complex.ext h1 h2
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h3

theorem gk_entry {d m : ℕ} (G : HermitianFrame d) (R F : Fin m → Algebra d)
    (hR : ∀ k, (R k).IsHermitian) (hF : ∀ k, (F k).IsHermitian) (j n : Fin (d^2)) :
    coordinateMatrix G (Entanglement.holevoMap R F) j n =
      ∑ k, hermitianCoordinates G (R k) j * hermitianCoordinates G (F k) n := by
  simp only [coordinateMatrix, hermitianCoordinates, Matrix.of_apply, Entanglement.holevoMap,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re]
  apply Finset.sum_congr rfl
  intro k _
  rw [gk_herm_im _ _ (hF k) (G.hermitian n), Matrix.trace_mul_comm (G.matrix j)]
  ring

theorem solution (d m : ℕ) (G : HermitianFrame d)
    (R F : Fin m → Algebra d) (hR : ∀ k, IsDensityMatrix (R k))
    (hF : ∀ k, (F k).PosSemidef) :
    coordinateMatrix G (Entanglement.holevoMap R F) =
      (coordinateFactors G R F).1 * (coordinateFactors G R F).2.transpose ∧
    (∀ j n, coordinateMatrix G (Entanglement.holevoMap R F) j n =
      ∑ k, hermitianCoordinates G (R k) j * hermitianCoordinates G (F k) n) ∧
    (IsPOVM F ↔ ∀ n, coordinateMatrix G (Entanglement.holevoMap R F)
      ⟨0,by have := G.positive; positivity⟩ n = if n.val = 0 then 1 else 0) := by
  have hRh : ∀ k, (R k).IsHermitian := fun k => (hR k).1.isHermitian
  have hFh : ∀ k, (F k).IsHermitian := fun k => (hF k).isHermitian
  have h2 := gk_entry G R F hRh hFh
  refine ⟨?_, h2, ?_⟩
  · ext j n
    rw [h2]
    simp [coordinateFactors, Matrix.mul_apply]
  · have hd := G.positive
    set z : Fin (d^2) := ⟨0, by positivity⟩ with hz
    have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    -- trace of R k is 1
    have hrow : ∀ n, coordinateMatrix G (Entanglement.holevoMap R F) z n =
        (Real.sqrt d)⁻¹ * ((∑ k, F k) * G.matrix n).trace.re := by
      intro n
      rw [h2]
      simp only [hermitianCoordinates, G.identity, hz, Matrix.mul_smul, Matrix.mul_one,
        Matrix.trace_smul, (hR _).2, smul_eq_mul, mul_one, Finset.sum_mul, Matrix.trace_sum,
        Complex.re_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Complex.ofReal_inv, Complex.ofReal_re]
    have hG0 : ∀ n : Fin (d^2), (G.matrix n).trace.re = if n.val = 0 then Real.sqrt d else 0 := by
      intro n
      split_ifs with hn
      · have : n = z := Fin.ext hn
        rw [this, hz, G.identity, Matrix.trace_smul, Matrix.trace_one]
        simp only [Fintype.card_fin, smul_eq_mul]
        rw [← Complex.ofReal_inv, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
          Complex.ofReal_re]
        rw [inv_mul_eq_div, div_eq_iff hsd.ne', Real.mul_self_sqrt (by positivity)]
      · rw [G.traceless n hn]; simp
    constructor
    · intro hP n
      rw [hrow, hP.2, Matrix.one_mul, hG0]
      split_ifs <;> simp [hsd.ne']
    · intro h
      refine ⟨hF, ?_⟩
      have hS : (∑ k, F k).IsHermitian := (Matrix.posSemidef_sum _ (fun k _ => hF k)).isHermitian
      have := gk_frame_zero G (∑ k, F k - 1) (hS.sub Matrix.isHermitian_one) (fun n => ?_)
      · exact sub_eq_zero.1 this
      · have e1 := h n
        rw [hrow] at e1
        rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.one_mul, hG0]
        have e2 : ((∑ k, F k) * G.matrix n).trace.re = if n.val = 0 then Real.sqrt d else 0 := by
          split_ifs at e1 ⊢ with hn
          · field_simp at e1; linarith
          · rcases mul_eq_zero.1 e1 with h | h
            · exact absurd h (inv_ne_zero hsd.ne')
            · exact h
        rw [e2]; ring

