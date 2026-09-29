-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.card_le_sq_of_forall_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/66096514-827e-58cd-b134-9e401c7d90b7

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_card_le_sq_of_forall_nsmul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open Polynomial WeierstrassCurve

namespace P2MKcTorsionCount

variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

def xOf : W.toAffine.Point → F
  | .zero => 0
  | .some x _ _ => x

theorem eq_or_eq_neg_of_xOf_eq {P P' : W.toAffine.Point} (hP : P ≠ 0) (hP' : P' ≠ 0)
    (hx : xOf W P = xOf W P') : P = P' ∨ P = -P' := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  rcases P' with _ | ⟨x', y', h'⟩
  · exact absurd rfl hP'
  simp only [xOf] at hx
  subst hx
  rcases Affine.Y_eq_of_X_eq h.1 h'.1 rfl with hy | hy
  · left; subst hy; rfl
  · right
    rw [Affine.Point.neg_some]
    subst hy; rfl

theorem card_filter_ne_zero_le (p : F[X]) (hp : p ≠ 0) (T : Finset W.toAffine.Point)
    (hT : ∀ P ∈ T, P ≠ 0 → p.eval (xOf W P) = 0) :
    (T.filter (· ≠ 0)).card ≤ 2 * p.roots.toFinset.card := by
  set T' := T.filter (· ≠ 0) with hT'
  have himg : T'.image (xOf W) ⊆ p.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    rw [hT', Finset.mem_filter] at hP
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact hT P hP.1 hP.2
  have hfib : ∀ b ∈ T'.image (xOf W), (T'.filter fun P => xOf W P = b).card ≤ 2 := by
    intro b hb
    set Fb := T'.filter fun P => xOf W P = b with hFb
    rcases Fb.eq_empty_or_nonempty with he | ⟨P₁, hP₁⟩
    · rw [he]; simp
    ·
      have hsub : Fb ⊆ {P₁, -P₁} := by
        intro P hP
        rw [hFb, Finset.mem_filter, hT', Finset.mem_filter] at hP hP₁
        rcases eq_or_eq_neg_of_xOf_eq W hP.1.2 hP₁.1.2 (hP.2.trans hP₁.2.symm) with e | e
        · rw [e]; exact Finset.mem_insert_self _ _
        · rw [e]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
  calc T'.card ≤ 2 * (T'.image (xOf W)).card := Finset.card_le_mul_card_image T' 2 hfib
    _ ≤ 2 * p.roots.toFinset.card := Nat.mul_le_mul_left 2 (Finset.card_le_card himg)

theorem card_le_card_filter_ne_zero_add_one (T : Finset W.toAffine.Point) :
    T.card ≤ (T.filter (· ≠ 0)).card + 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := T) (fun P => P ≠ 0)
  have h1 : (T.filter fun P => ¬ P ≠ 0).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rw [Finset.mem_filter, not_not] at ha hb
    rw [ha.2, hb.2]
  omega

theorem two_torsion_coords {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Affine.Point.some x y h : W.toAffine.Point) = 0) :
    2 * y + W.a₁ * x + W.a₃ = 0 ∧ W.Ψ₂Sq.eval x = 0 := by
  have hneg : (Affine.Point.some x y h : W.toAffine.Point) = -Affine.Point.some x y h := by
    rw [two_nsmul] at h2
    exact eq_neg_of_add_eq_zero_left h2
  rw [Affine.Point.neg_some, Affine.Point.some.injEq] at hneg
  have hy : y = -y - W.a₁ * x - W.a₃ := hneg.2
  have h2y : 2 * y + W.a₁ * x + W.a₃ = 0 := by linear_combination hy
  refine ⟨h2y, ?_⟩
  have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (Affine.equation_iff x y).mp h.1
  simp only [Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  linear_combination (-4 : F) * heq + (2 * y + W.a₁ * x + W.a₃) * h2y

theorem card_le_four_of_two_torsion (h2 : (2 : F) ≠ 0) (T : Finset W.toAffine.Point)
    (hT : ∀ P ∈ T, (2 : ℕ) • P = 0) : T.card ≤ 4 := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  set T' := T.filter (· ≠ 0) with hT'

  have himg : T'.image (xOf W) ⊆ W.Ψ₂Sq.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    rw [hT', Finset.mem_filter] at hP
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (W.Ψ₂Sq_ne_zero h4)]
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd rfl hP.2
    · exact (two_torsion_coords W h (hT _ hP.1)).2
  have hinj : Set.InjOn (xOf W) (T' : Set W.toAffine.Point) := by
    intro P hP P' hP' hx
    rw [Finset.mem_coe, hT', Finset.mem_filter] at hP hP'
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd rfl hP.2
    rcases P' with _ | ⟨x', y', h'⟩
    · exact absurd rfl hP'.2
    simp only [xOf] at hx
    subst hx
    have hy := (two_torsion_coords W h (hT _ hP.1)).1
    have hy' := (two_torsion_coords W h' (hT _ hP'.1)).1
    have : y = y' := by
      have : (2 : F) * (y - y') = 0 := by linear_combination hy - hy'
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2
      · linear_combination h
    subst this
    rfl
  have hcard : T'.card ≤ 3 := by
    calc T'.card = (T'.image (xOf W)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ W.Ψ₂Sq.roots.toFinset.card := Finset.card_le_card himg
      _ ≤ W.Ψ₂Sq.roots.card := Multiset.toFinset_card_le _
      _ ≤ W.Ψ₂Sq.natDegree := Polynomial.card_roots' _
      _ ≤ 3 := W.natDegree_Ψ₂Sq_le
  have := card_le_card_filter_ne_zero_add_one W T
  rw [← hT'] at this
  omega

theorem card_le_sq_of_odd {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0) (S : Finset W.toAffine.Point)
    (hS : ∀ P ∈ S, n • P = 0) : S.card ≤ n ^ 2 := by
  have hp : W.preΨ' n ≠ 0 := W.preΨ'_ne_zero hn
  have hdeg : (W.preΨ' n).natDegree = (n ^ 2 - 1) / 2 := by
    rw [W.natDegree_preΨ' hn, if_neg (Nat.not_even_iff_odd.mpr hodd)]
  have hroots : ∀ P ∈ S, P ≠ 0 → (W.preΨ' n).eval (xOf W P) = 0 := by
    intro P hP hP0
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd rfl hP0
    · exact (Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd h).mp (hS _ hP)
  have h1 := card_filter_ne_zero_le W (W.preΨ' n) hp S hroots
  have h2 := card_le_card_filter_ne_zero_add_one W S
  have h3 : (W.preΨ' n).roots.toFinset.card ≤ (n ^ 2 - 1) / 2 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans hdeg.le)
  have hsq : Odd (n ^ 2) := hodd.pow
  obtain ⟨k, hk⟩ := hsq
  have : S.card ≤ 2 * ((n ^ 2 - 1) / 2) + 1 := by omega
  omega

theorem card_le_sq (n : ℕ) (hn : (n : F) ≠ 0) (S : Finset W.toAffine.Point)
    (hS : ∀ P ∈ S, n • P = 0) : S.card ≤ n ^ 2 := by
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases Nat.even_or_odd n with heven | hodd
    · obtain ⟨m, rfl⟩ := heven
      have hm2 : ((m + m : ℕ) : F) = 2 * (m : F) := by push_cast; ring
      rw [hm2] at hn
      have h2 : (2 : F) ≠ 0 := left_ne_zero_of_mul hn
      have hmF : (m : F) ≠ 0 := right_ne_zero_of_mul hn
      have hm0 : m ≠ 0 := by rintro rfl; exact hmF (by simp)

      have himg : (S.image fun P => (2 : ℕ) • P).card ≤ m ^ 2 := by
        apply ih m (by omega) hmF
        intro Q hQ
        rw [Finset.mem_image] at hQ
        obtain ⟨P, hP, rfl⟩ := hQ
        rw [← mul_nsmul', show m * 2 = m + m by ring]
        exact hS P hP

      have hfib : ∀ b ∈ S.image (fun P => (2 : ℕ) • P), (S.filter fun P => (2 : ℕ) • P = b).card ≤ 4 := by
        intro b hb
        rw [Finset.mem_image] at hb
        obtain ⟨P₀, hP₀, rfl⟩ := hb
        set Fb := S.filter fun P => (2 : ℕ) • P = (2 : ℕ) • P₀ with hFb
        have hinj : Set.InjOn (fun P => P - P₀) (Fb : Set W.toAffine.Point) := fun P _ P' _ h =>
          sub_left_injective h
        rw [← Finset.card_image_of_injOn hinj]
        apply card_le_four_of_two_torsion W h2
        intro Q hQ
        rw [Finset.mem_image] at hQ
        obtain ⟨P, hP, rfl⟩ := hQ
        rw [hFb, Finset.mem_filter] at hP
        rw [nsmul_sub, hP.2, sub_self]
      calc S.card ≤ 4 * (S.image fun P => (2 : ℕ) • P).card := Finset.card_le_mul_card_image S 4 hfib
        _ ≤ 4 * m ^ 2 := Nat.mul_le_mul_left 4 himg
        _ = (m + m) ^ 2 := by ring
    · exact card_le_sq_of_odd W hodd hn S hS

end P2MKcTorsionCount

end

theorem solution
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℕ) (hn : (n : F) ≠ 0) (S : Finset W.toAffine.Point) (hS : ∀ P ∈ S, n • P = 0) :
    S.card ≤ n ^ 2 :=
  P2MKcTorsionCount.card_le_sq W n hn S hS

end S_WeierstrassCurve_Affine_Point_card_le_sq_of_forall_nsmul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_card_le_sq_of_forall_nsmul_eq_zero (solution)
