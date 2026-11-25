-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.adapted_basis_instance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:38.114469+00:00
-- url     : https://prove2.me/submissions/33995e74-917f-400d-a399-fc8c9b73777b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstAdapt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_AdaptedBasisInstance
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_gram_entry
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_qfamily
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_rank_add_le
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
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution : InstAdaptBasis := by
  intro n ε ι _ _ B hG
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJs : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  set J := Formalism.REAL.Jm ε with hJdef
  set G := Bᴴ * J * B with hGdef
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
  have hGi : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have hGh : Gᴴ = G := by
    rw [hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hJs, Matrix.mul_assoc]
  have hGih : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  set Q := B * G⁻¹ * Bᴴ * J with hQdef
  have hQB : Q * B = B := by
    calc Q * B = B * (G⁻¹ * (Bᴴ * J * B)) := by simp only [hQdef, Matrix.mul_assoc]
      _ = B := by rw [← hGdef, hGi, Matrix.mul_one]
  have hQQ : Q * Q = Q := by
    calc Q * Q = (Q * B) * (G⁻¹ * Bᴴ * J) := by simp only [hQdef, Matrix.mul_assoc]
      _ = Q := by rw [hQB]; simp only [hQdef, Matrix.mul_assoc]
  have hQJ : Qᴴ * J = J * Q := by
    simp only [hQdef, Matrix.conjTranspose_mul, hJs, hGih, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  set P := 1 - Q with hPdef
  have hPP : P * P = P := by
    simp only [hPdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQQ]
    abel
  have hPJ : Pᴴ * J = J * P := by
    rw [hPdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, hQJ,
      Matrix.one_mul, Matrix.mul_one]
  have hQP : Q * P = 0 := by rw [hPdef, Matrix.mul_sub, Matrix.mul_one, hQQ, sub_self]
  have hPQ : P * Q = 0 := by rw [hPdef, Matrix.sub_mul, Matrix.one_mul, hQQ, sub_self]
  obtain ⟨W1, l1, hW1J, hQW1, hsp1, hcard1, -⟩ := inst_qfamily ε Q hQQ hQJ
  obtain ⟨W2, l2, hW2J, hPW2, -, hcard2, -⟩ := inst_qfamily ε P hPP hPJ
  have hcross : W1ᴴ * J * W2 = 0 := by
    calc W1ᴴ * J * W2 = (Q * W1)ᴴ * J * (P * W2) := by rw [hQW1, hPW2]
      _ = W1ᴴ * (Qᴴ * J) * P * W2 := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
        rw [hQJ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Q P, hQP]
        simp
  have hcross' : W2ᴴ * J * W1 = 0 := by
    calc W2ᴴ * J * W1 = (P * W2)ᴴ * J * (Q * W1) := by rw [hQW1, hPW2]
      _ = W2ᴴ * (Pᴴ * J) * Q * W1 := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
        rw [hPJ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P Q, hPQ]
        simp
  have hrk : Q.rank + P.rank = n := by
    apply le_antisymm
    · have h1 : LinearMap.range P.mulVecLin ≤ LinearMap.ker Q.mulVecLin := by
        rintro _ ⟨x, rfl⟩
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
          hQP, Matrix.zero_mulVec]
      have h2 := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
      have h3 := Submodule.finrank_mono h1
      have h4 : Module.finrank ℂ (Fin n → ℂ) = n := by
        first
          | exact Module.finrank_fin_fun ℂ
          | simp
      unfold Matrix.rank
      omega
    · have h := inst_rank_add_le Q P
      have hsum : Q + P = 1 := by rw [hPdef]; abel
      rw [hsum, Matrix.rank_one, Fintype.card_fin] at h
      exact h
  have hcardsum : Fintype.card ({i // l1 i ≠ 0} ⊕ {i // l2 i ≠ 0}) = n := by
    refine Eq.trans ?_ hrk
    rw [Fintype.card_sum]
    convert congrArg₂ (· + ·) hcard1 hcard2 using 2
  obtain ⟨e⟩ : Nonempty (Fin n ≃ ({i // l1 i ≠ 0} ⊕ {i // l2 i ≠ 0})) :=
    ⟨(Fintype.equivFinOfCardEq hcardsum).symm⟩
  obtain ⟨A, hAe⟩ : ∃ A : Matrix (Fin n) (Fin n) ℂ, ∀ r k, A r k =
      Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j) (fun j : {i // l2 i ≠ 0} => W2 r j) (e k) :=
    ⟨Matrix.of fun r k =>
      Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j) (fun j : {i // l2 i ≠ 0} => W2 r j) (e k),
      fun _ _ => rfl⟩
  obtain ⟨ε', hε'⟩ : ∃ ε' : Fin n → Bool, ∀ k, ε' k =
      Sum.elim (fun j : {i // l1 i ≠ 0} => decide (0 < l1 j))
        (fun j : {i // l2 i ≠ 0} => decide (0 < l2 j)) (e k) :=
    ⟨fun k => Sum.elim (fun j : {i // l1 i ≠ 0} => decide (0 < l1 j))
        (fun j : {i // l2 i ≠ 0} => decide (0 < l2 j)) (e k), fun _ => rfl⟩
  have hcol : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin n), M *ᵥ Pi.single k 1 = fun r => M r k := by
    intro M k
    funext r
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨A, ε', Finset.univ.filter (fun k => (e k).isLeft = true), ?_, ?_, ?_⟩
  · ext k k'
    rw [inst_gram_entry]
    simp only [Formalism.REAL.Jm, Matrix.diagonal_apply, hAe, hε']
    rcases hk : e k with j | j <;> rcases hk' : e k' with j' | j' <;>
      simp only [Sum.elim_inl, Sum.elim_inr]
    · rw [← inst_gram_entry W1 J W1 (j : Fin n) j', hW1J, Matrix.diagonal_apply]
      have hkk : k = k' ↔ (j : Fin n) = j' := by
        rw [← e.apply_eq_iff_eq, hk, hk', Sum.inl.injEq, Subtype.ext_iff]
      by_cases h : (j : Fin n) = j'
      · rw [if_pos h, if_pos (hkk.mpr h), if_neg j.2]
        by_cases hp : 0 < l1 j <;> simp [hp]
      · rw [if_neg h, if_neg (fun h' => h (hkk.mp h'))]
    · rw [← inst_gram_entry W1 J W2 (j : Fin n) j', hcross, Matrix.zero_apply, if_neg]
      intro h
      subst h
      rw [hk] at hk'
      exact Sum.inl_ne_inr hk'
    · rw [← inst_gram_entry W2 J W1 (j : Fin n) j', hcross', Matrix.zero_apply, if_neg]
      intro h
      subst h
      rw [hk] at hk'
      exact Sum.inr_ne_inl hk'
    · rw [← inst_gram_entry W2 J W2 (j : Fin n) j', hW2J, Matrix.diagonal_apply]
      have hkk : k = k' ↔ (j : Fin n) = j' := by
        rw [← e.apply_eq_iff_eq, hk, hk', Sum.inr.injEq, Subtype.ext_iff]
      by_cases h : (j : Fin n) = j'
      · rw [if_pos h, if_pos (hkk.mpr h), if_neg j.2]
        by_cases hp : 0 < l2 j <;> simp [hp]
      · rw [if_neg h, if_neg (fun h' => h (hkk.mp h'))]
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hk : e i with j | j
    · refine ⟨G⁻¹ *ᵥ (Bᴴ *ᵥ (J *ᵥ (W1 *ᵥ Pi.single (j : Fin n) 1))), ?_⟩
      have h1 : A *ᵥ Pi.single i 1 = W1 *ᵥ Pi.single (j : Fin n) 1 := by
        rw [hcol, hcol]
        funext r
        show A r i = W1 r (j : Fin n)
        rw [hAe, hk, Sum.elim_inl]
      rw [h1]
      calc W1 *ᵥ Pi.single (j : Fin n) 1 = (Q * W1) *ᵥ Pi.single (j : Fin n) 1 := by rw [hQW1]
        _ = _ := by simp only [hQdef, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · rw [hk] at hi
      simp at hi
  · intro j
    have hb : Q *ᵥ (B *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by rw [Matrix.mulVec_mulVec, hQB]
    obtain ⟨y, hy0, hy⟩ := hsp1 _ hb
    refine ⟨fun k => Sum.elim (fun j' : {i // l1 i ≠ 0} => y j') (fun _ => (0 : ℂ)) (e k), ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases he : e k with j' | j'
      · rw [he] at hk
        simp at hk
      · simp only [he, Sum.elim_inr]
    · rw [hy]
      funext r
      simp only [Matrix.mulVec, dotProduct, hAe]
      symm
      rw [Fintype.sum_equiv e _ (fun x => Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j)
        (fun j : {i // l2 i ≠ 0} => W2 r j) x *
          Sum.elim (fun j' : {i // l1 i ≠ 0} => y j') (fun _ => (0 : ℂ)) x) (fun k => rfl)]
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i => l1 i ≠ 0) (fun i => W1 r i * y i)]
      have h0 : ∑ i : {i // ¬ l1 i ≠ 0}, W1 r i * y i = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hy0 i (not_not.mp i.2), mul_zero]
      rw [h0, add_zero]
end PI.ScMuExists.UnitaryGroupMassFormula
