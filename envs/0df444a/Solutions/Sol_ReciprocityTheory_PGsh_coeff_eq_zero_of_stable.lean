-- Prove2me | solution 1 for ReciprocityTheory.PGsh.coeff_eq_zero_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:59:20.520017+00:00
-- url     : https://prove2.me/submissions/46171a78-35b3-4dff-b020-9cf926c700e3

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Theorems.Thm_ReciprocityTheory_PGsh_map_aeval_of_leibniz
import Theorems.Thm_ReciprocityTheory_PGsh_lowRed_mul
import Theorems.Thm_ReciprocityTheory_PGsh_lowRed_pderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d p : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (ε : A →ₐ[R] R) (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (D : Fin d → A →ₗ[R] A) (hD : ∀ i f g, D i (f * g) = f * D i g + g * D i f)
    (hDx : ∀ i j, ε (D i (x j)) = if i = j then 1 else 0)
    (hsurj : Function.Surjective (aeval (R := R) x))
    (hp0 : (p : R) = 0) (hunit : ∀ n, 0 < n → n < p → IsUnit (n : R))
    (K : Set A) (hK : ∀ a ∈ K, ε a = 0) (hKD : ∀ i, ∀ a ∈ K, D i a ∈ K)
    (P : MvPolynomial (Fin d) R) (hP : aeval x P ∈ K) :
    ∀ β : Fin d →₀ ℕ, (∀ j, β j < p) → coeff β P = 0 := by
  classical
  have hε : ∀ Q : MvPolynomial (Fin d) R, ε (aeval x Q) = constantCoeff Q := by
    intro Q
    have e : ε.comp (aeval x) = aeval (fun _ => (0 : R)) := by
      rw [comp_aeval]; congr 1; funext i; exact hx i
    rw [← AlgHom.comp_apply, e, aeval_zero']
    rfl
  have Z : ∀ m, ∀ Q : MvPolynomial (Fin d) R, aeval x Q ∈ K → LowRed p m Q →
      ∀ α : Fin d →₀ ℕ, (∀ j, α j < p) → α.degree = m → coeff α Q = 0 := by
    intro m
    induction m with
    | zero =>
      intro Q hQ _ α _ hα
      have h0 : α = 0 := (Finsupp.degree_eq_zero_iff α).1 hα
      subst h0
      rw [← congrFun constantCoeff_eq Q, ← hε, hK _ hQ]
    | succ m ih =>
      intro Q hQ hlow α hα hdeg
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra h
        push Not at h
        have h0 : α = 0 := Finsupp.ext h
        subst h0
        simp at hdeg
      set β := α - Finsupp.single i 1 with hβdef
      have hαβ : α = β + Finsupp.single i 1 := by
        ext j
        simp only [hβdef, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply,
          Finsupp.single_apply]
        split_ifs with hj
        · subst hj; omega
        · omega
      choose T hT using fun j => hsurj (D i (x j))
      have hTc : ∀ j, constantCoeff (T j) = if i = j then 1 else 0 := fun j => by
        rw [← hε, hT, hDx]
      set Q' : MvPolynomial (Fin d) R := ∑ j, pderiv j Q * T j with hQ'def
      have hQ' : aeval x Q' ∈ K := by
        have e : aeval x Q' = D i (aeval x Q) := by
          rw [map_aeval_of_leibniz (D i) (hD i), hQ'def, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, hT]
        rw [e]; exact hKD i _ hQ
      have hsplit : ∀ j (γ : Fin d →₀ ℕ), γ.degree ≤ m → (∀ l, γ l < p) →
          coeff γ (pderiv j Q * T j) = coeff γ (pderiv j Q) * (if i = j then 1 else 0) := by
        intro j γ hγd hγ
        have e : T j = C (constantCoeff (T j)) + (T j - C (constantCoeff (T j))) := by ring
        rw [e, mul_add, coeff_add, mul_comm (pderiv j Q) (C _), coeff_C_mul,
          lowRed_mul (G := T j - C (constantCoeff (T j))) (lowRed_pderiv hp0 hlow j) (by simp) γ hγ hγd,
          add_zero, hTc, mul_comm]
      have hlow' : LowRed p m Q' := by
        intro γ hγ hγd
        rw [hQ'def, coeff_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hsplit j γ hγd.le hγ, lowRed_pderiv hp0 hlow j γ hγ hγd, zero_mul]
      have hβr : ∀ j, β j < p := fun j =>
        lt_of_le_of_lt (by rw [hβdef]; exact tsub_le_self) (hα j)
      have hβd : β.degree = m := by
        have := congrArg Finsupp.degree hαβ
        rw [map_add, Finsupp.degree_single] at this
        omega
      have h0 := ih Q' hQ' hlow' β hβr hβd
      rw [hQ'def, coeff_sum, Finset.sum_eq_single i] at h0
      · rw [hsplit i β hβd.le hβr, if_pos rfl, mul_one, coeff_pderiv, ← hαβ] at h0
        have hb : α i = β i + 1 := by rw [hαβ]; simp
        have hu : IsUnit ((β i : R) + 1) := by
          have := hunit (α i) (Nat.pos_of_ne_zero hi) (hα i)
          rw [hb] at this
          exact_mod_cast this
        exact (hu.mul_left_eq_zero).1 h0
      · intro j _ hj
        rw [hsplit j β hβd.le hβr, if_neg (Ne.symm hj), mul_zero]
      · simp
  have W : ∀ m, ∀ Q : MvPolynomial (Fin d) R, aeval x Q ∈ K → LowRed p m Q := by
    intro m
    induction m with
    | zero => intro Q _ β _ h; simp at h
    | succ m ih =>
      intro Q hQ β hβ hd
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd with h | h
      · exact ih Q hQ β hβ h
      · exact Z m Q hQ (ih Q hQ) β hβ h
  intro β hβ
  exact W (β.degree + 1) P hP β hβ (Nat.lt_succ_self _)
end ReciprocityTheory.PGsh
