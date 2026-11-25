-- Prove2me | solution 1 for PI.FrameInd.signStep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:42.660609+00:00
-- url     : https://prove2.me/submissions/c3b9a6db-412d-48e1-a161-52d1da152138

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegativeBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_QBuild
import Theorems.Thm_PI_FrameInd_submatrix_conj
import Theorems.Thm_PI_FrameInd_CountsW_diag_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd
namespace PI.FrameInd
theorem _root_.solution (hP : PosCount) (hN : NonposCount) : SignStep := by
  intro k r z z' γ hs hp hdet
  set hA := isHerm k r z z' γ with hhA
  set ev := hA.eigenvalues with hev
  have h1 : Fintype.card {i // 0 < ev i} ≤ r + 1 := hP k r z z' γ hs hp hdet
  have h2 : Fintype.card {i // ¬ 0 < ev i} ≤ r + 1 := hN k r z z' γ hs hp hdet
  have h3 := Fintype.card_subtype_compl (fun i : Fin (r + 1) ⊕ Fin (r + 1) => 0 < ev i)
  have h4 : Fintype.card {i : Fin (r + 1) ⊕ Fin (r + 1) // 0 < ev i} ≤
      Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) := Fintype.card_subtype_le _
  simp only [Fintype.card_sum, Fintype.card_fin] at h3 h4
  have hcP : Fintype.card {i // 0 < ev i} = r + 1 := by omega
  have hcN : Fintype.card {i // ¬ 0 < ev i} = r + 1 := by omega
  have hne : ∀ i, ev i ≠ 0 := by
    intro i h0
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hev, h0]; simp)
  let eP : {i // 0 < ev i} ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcP
  let eN : {i // ¬ 0 < ev i} ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcN
  let e : Fin (r + 1) ⊕ Fin (r + 1) ≃ Fin (r + 1) ⊕ Fin (r + 1) :=
    (Equiv.sumCongr eP.symm eN.symm).trans (Equiv.sumCompl fun i => 0 < ev i)
  let U : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ := hA.eigenvectorUnitary
  let s : Fin (r + 1) ⊕ Fin (r + 1) → ℂ := fun i => (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)
  let f : Fin (r + 1) ⊕ Fin (r + 1) → ℂ := fun i => if 0 < ev i then 1 else -1
  have hW : (U * diagonal s)ᴴ * gramM k r z z' γ * (U * diagonal s) = diagonal f := by
    have hd : Uᴴ * gramM k r z z' γ * U = diagonal (fun i => ((ev i : ℝ) : ℂ)) := CountsW.diag_eq hA
    rw [conjTranspose_mul, diagonal_conjTranspose]
    calc (star s |> diagonal) * Uᴴ * gramM k r z z' γ * (U * diagonal s)
        = diagonal (star s) * (Uᴴ * gramM k r z z' γ * U) * diagonal s := by simp only [Matrix.mul_assoc]
      _ = diagonal f := by
        rw [hd, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        have hpos : 0 < |ev i| := abs_pos.2 (hne i)
        have hsq : Real.sqrt |ev i| * Real.sqrt |ev i| = |ev i| := Real.mul_self_sqrt hpos.le
        have hsq0 : Real.sqrt |ev i| ≠ 0 := by positivity
        simp only [s, f, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
        have : (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = if 0 < ev i then 1 else -1 := by
          rw [mul_comm, ← mul_assoc, ← mul_inv, hsq]
          split_ifs with h
          · rw [abs_of_pos h, inv_mul_cancel₀ (hne i)]
          · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hne i)), inv_neg, neg_mul,
              inv_mul_cancel₀ (hne i)]
        rw [this]; split_ifs <;> simp
  have hfe : f ∘ e = Sum.elim (fun _ => 1) (fun _ => -1) := by
    funext i
    rcases i with a | a
    · simp [f, e, Equiv.sumCompl_apply_inl, (eP.symm a).2]
    · simp [f, e, Equiv.sumCompl_apply_inr, (eN.symm a).2]
  have hD : ((U * diagonal s).submatrix id e)ᴴ * gramM k r z z' γ * (U * diagonal s).submatrix id e =
      diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    rw [submatrix_conj, hW, submatrix_diagonal_equiv, hfe]
  refine ⟨(U * diagonal s).submatrix id e, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det hD
    rw [det_mul, det_mul, h0, mul_zero, det_diagonal] at this
    refine (Finset.prod_ne_zero_iff.2 fun i _ => ?_) this.symm
    rcases i with a | a <;> simp
  · rw [hD]
    ext i j
    rcases i with a | a <;> rcases j with b | b <;> simp [diagonal_apply, one_apply] <;> split_ifs <;> simp
end PI.FrameInd
