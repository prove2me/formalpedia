-- Prove2me | solution 1 for QAmpEst.Est.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:21:40.863991+00:00
-- url     : https://prove2.me/submissions/eca1439a-b5f7-4365-b51d-4eb8acba6f0c

import Mathlib
import Definitions.Def_QAmpEst_Est_Setting

open scoped Real Kronecker

namespace Aux_QAE_L1

open QAmpEst.Est Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma psi_apply (A : Matrix ι ι ℂ) (z0 x : ι) : initState A z0 x = A x z0 := by
  simp [initState, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma Qop_mulVec (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι)
    (v : ι → ℂ) :
    Qop A χ z0 *ᵥ v = (2 * ∑ y, star (A y z0) * (signGood χ *ᵥ v) y) • initState A z0
      - signGood χ *ᵥ v := by
  set w := signGood χ *ᵥ v with hw
  have hAA : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp hA
  have hS0 : ∀ u : ι → ℂ, signZero z0 *ᵥ u = u - (2 * u z0) • Pi.single z0 1 := by
    intro u
    funext y
    rw [signZero, mulVec_diagonal]
    by_cases hy : y = z0
    · subst hy; simp; ring
    · simp [hy, Pi.single_apply]
  unfold Qop
  rw [neg_mulVec, ← mulVec_mulVec, ← hw, ← mulVec_mulVec, ← mulVec_mulVec, hS0, mulVec_sub,
    mulVec_smul, mulVec_mulVec, hAA, one_mulVec]
  have hc : (star A *ᵥ w) z0 = ∑ y, star (A y z0) * w y := by
    simp [Matrix.mulVec, dotProduct, star_apply]
  rw [hc]
  unfold initState
  abel

end Aux_QAE_L1

open QAmpEst.Est Aux_QAE_L1 Matrix in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) :
    let Ψ₁ := goodPart χ (initState A z0)
    let Ψ₀ := badPart χ (initState A z0)
    let a : ℂ := (succProb A χ z0 : ℂ)
    (Qop A χ z0).mulVec Ψ₁ = (1 - 2 * a) • Ψ₁ - (2 * a) • Ψ₀ ∧
      (Qop A χ z0).mulVec Ψ₀ = (2 * (1 - a)) • Ψ₁ + (1 - 2 * a) • Ψ₀ := by
  intro Ψ₁ Ψ₀ a
  set ψ := initState A z0 with hψ
  have hψx : ∀ x, ψ x = A x z0 := psi_apply A z0
  have hsplit : ψ = Ψ₁ + Ψ₀ := by
    funext x; simp only [Ψ₁, Ψ₀, goodPart, badPart, Pi.add_apply]; split_ifs <;> simp [hψ]
  -- total mass one
  have hAA : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  have htot : ∑ x, star (A x z0) * A x z0 = 1 := by
    have := congrFun (congrFun hAA z0) z0
    simpa [Matrix.mul_apply, Matrix.star_apply] using this
  have hnorm : ∀ z : ℂ, star z * z = (Complex.normSq z : ℂ) := fun z => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have ha : a = ∑ x, if χ x then star (A x z0) * A x z0 else 0 := by
    simp only [a, succProb, goodProb]
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : χ x = true
    · rw [if_pos hx, if_pos hx, psi_apply, hnorm]
    · rw [if_neg hx, if_neg hx, Complex.ofReal_zero]
  have hb : (1 : ℂ) - a = ∑ x, if χ x then 0 else star (A x z0) * A x z0 := by
    rw [ha, ← htot, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  -- action of signGood
  have hSG1 : signGood χ *ᵥ Ψ₁ = -Ψ₁ := by
    funext x; rw [signGood, mulVec_diagonal]
    simp only [Ψ₁, goodPart, Pi.neg_apply]; split_ifs <;> simp
  have hSG0 : signGood χ *ᵥ Ψ₀ = Ψ₀ := by
    funext x; rw [signGood, mulVec_diagonal]
    simp only [Ψ₀, badPart]; split_ifs <;> simp
  constructor
  · rw [Qop_mulVec A hA χ z0, hSG1, ← hψ]
    have hc : ∑ y, star (A y z0) * (-Ψ₁) y = -a := by
      rw [ha, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y _
      simp only [Ψ₁, goodPart, Pi.neg_apply, psi_apply]
      split_ifs <;> ring
    rw [hc, hsplit]
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  · rw [Qop_mulVec A hA χ z0, hSG0, ← hψ]
    have hc : ∑ y, star (A y z0) * Ψ₀ y = 1 - a := by
      rw [hb]
      apply Finset.sum_congr rfl
      intro y _
      simp only [Ψ₀, badPart, psi_apply]
      split_ifs <;> ring
    rw [hc, hsplit]
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
