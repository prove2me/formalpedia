-- Prove2me | solution 1 for WeierstrassCurve.exists_torsion_not_inZeroComponentAt_of_ne_residueChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6b68e3e4-4607-587d-b111-9f7292aae79a

import Theorems.Thm_WeierstrassCurve_exists_reduction_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_mem_valuationSubring_of_nsmul_eq_zero_of_liesOverPrime
import Theorems.Thm_WeierstrassCurve_Affine_Point_finite_and_ncard_torsion_le_of_isNode
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_torsion_not_inZeroComponentAt_of_ne_residueChar
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

namespace M3dS11

open WeierstrassCurve Polynomial

variable {k : Type*} [Field k]

private theorem equation_iff_F (W : WeierstrassCurve k) (x y : k) :
    W.toAffine.Equation x y ↔
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
  WeierstrassCurve.Affine.equation_iff' ..

theorem exists_isNode_of_char_two (W : WeierstrassCurve k) (h2 : (2 : k) = 0)
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) :
    ∃ x₀ y₀ : k, W.toAffine.Equation x₀ y₀ ∧ ¬ W.toAffine.Nonsingular x₀ y₀ ∧
      W.b₂ + 12 * x₀ ≠ 0 := by
  have ha₁ : W.a₁ ≠ 0 := by
    intro h
    apply hc₄
    have : W.c₄ = W.a₁ ^ 4 + 2 * (4 * W.a₁ ^ 2 * W.a₂ + 8 * W.a₂ ^ 2 - 24 * W.a₄ - 12 * W.a₁ * W.a₃) := by
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring
    rw [this, h2, h]; ring
  set x₀ : k := W.a₃ / W.a₁ with hx₀
  set y₀ : k := (x₀ ^ 2 + W.a₄) / W.a₁ with hy₀
  have hax : W.a₁ * x₀ = W.a₃ := by rw [hx₀]; field_simp
  have hay : W.a₁ * y₀ = x₀ ^ 2 + W.a₄ := by rw [hy₀]; field_simp

  have hF : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) = 0 := by
    have key : W.a₁ ^ 6 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ -
        (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) =
        -W.a₁ ^ 6 * W.a₆ + W.a₁ ^ 5 * W.a₃ * W.a₄ - W.a₁ ^ 4 * W.a₂ * W.a₃ ^ 2 +
          W.a₁ ^ 4 * W.a₄ ^ 2 + W.a₁ ^ 3 * W.a₃ ^ 3 + 2 * W.a₁ ^ 2 * W.a₃ ^ 2 * W.a₄ +
          W.a₃ ^ 4 := by
      rw [hy₀, hx₀]; field_simp; ring

    have hΔ' : -W.a₁ ^ 6 * W.a₆ + W.a₁ ^ 5 * W.a₃ * W.a₄ - W.a₁ ^ 4 * W.a₂ * W.a₃ ^ 2 +
          W.a₁ ^ 4 * W.a₄ ^ 2 + W.a₁ ^ 3 * W.a₃ ^ 3 + 2 * W.a₁ ^ 2 * W.a₃ ^ 2 * W.a₄ +
          W.a₃ ^ 4 = W.Δ + 2 * (6*W.a₁^4*W.a₂*W.a₆ - 4*W.a₁^3*W.a₂*W.a₃*W.a₄
          - 18*W.a₁^3*W.a₃*W.a₆ + 4*W.a₁^2*W.a₂^2*W.a₃^2 + 24*W.a₁^2*W.a₂^2*W.a₆
          - 4*W.a₁^2*W.a₂*W.a₄^2 + 16*W.a₁^2*W.a₃^2*W.a₄ - 36*W.a₁^2*W.a₄*W.a₆
          - 8*W.a₁*W.a₂^2*W.a₃*W.a₄ - 18*W.a₁*W.a₂*W.a₃^3 - 72*W.a₁*W.a₂*W.a₃*W.a₆
          + 48*W.a₁*W.a₃*W.a₄^2 + 8*W.a₂^3*W.a₃^2 + 32*W.a₂^3*W.a₆ - 8*W.a₂^2*W.a₄^2
          - 36*W.a₂*W.a₃^2*W.a₄ - 144*W.a₂*W.a₄*W.a₆ + 14*W.a₃^4 + 108*W.a₃^2*W.a₆
          + 32*W.a₄^3 + 216*W.a₆^2) := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]; ring
    rw [hΔ', hΔ, h2, zero_add, zero_mul] at key
    exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero _ ha₁)
  refine ⟨x₀, y₀, (equation_iff_F W x₀ y₀).mpr hF, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.nonsingular_iff']
    push Not
    intro _
    constructor
    · linear_combination hay + (-(x₀ ^ 2) - W.a₂ * x₀) * h2
    · linear_combination hax + (y₀ + W.a₃) * h2
  · intro h
    apply ha₁
    have : W.a₁ ^ 2 = 0 := by
      have hb : W.b₂ + 12 * x₀ = W.a₁ ^ 2 + 2 * (2 * W.a₂ + 6 * x₀) := by
        simp only [WeierstrassCurve.b₂]; ring
      rw [hb, h2, zero_mul, add_zero] at h
      exact h
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this

theorem exists_isNode_of_two_ne_zero [IsAlgClosed k] (W : WeierstrassCurve k) (h2 : (2 : k) ≠ 0)
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) :
    ∃ x₀ y₀ : k, W.toAffine.Equation x₀ y₀ ∧ ¬ W.toAffine.Nonsingular x₀ y₀ ∧
      W.b₂ + 12 * x₀ ≠ 0 := by
  set ψ : k[X] := W.twoTorsionPolynomial.toPoly with hψ
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have ha : W.twoTorsionPolynomial.a ≠ 0 := h4
  have hψ0 : ψ ≠ 0 := Cubic.ne_zero_of_a_ne_zero ha

  have hnotsep : ¬ ψ.Separable := by
    intro hsep
    have hsplit : (W.twoTorsionPolynomial.toPoly.map (RingHom.id k)).Splits := by
      rw [Polynomial.map_id]; exact IsAlgClosed.splits _
    have hnodup : (Cubic.map (RingHom.id k) W.twoTorsionPolynomial).roots.Nodup := by
      rw [Cubic.map_roots, Polynomial.map_id]
      exact (Polynomial.nodup_roots_iff_of_splits hψ0 (IsAlgClosed.splits _)).mpr hsep
    have hdisc := (Cubic.discr_ne_zero_iff_roots_nodup ha hsplit).mpr hnodup
    rw [WeierstrassCurve.twoTorsionPolynomial_discr, hΔ, mul_zero] at hdisc
    exact hdisc rfl

  have hcommon : ∃ x₀ : k, aeval x₀ ψ = 0 ∧ aeval x₀ (derivative ψ) = 0 := by
    by_contra hne
    push Not at hne
    apply hnotsep
    rw [Polynomial.separable_def]
    refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (K := k) (p := ψ)
      (q := derivative ψ)).mpr ?_
    intro a
    by_cases h : aeval a ψ = 0
    · exact Or.inr (hne a h)
    · exact Or.inl h
  obtain ⟨x₀, hψx, hψ'x⟩ := hcommon

  have hψval : 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ = 0 := by
    have h1 : eval x₀ ψ = 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ := by
      simp only [hψ, Cubic.toPoly, WeierstrassCurve.twoTorsionPolynomial, eval_add, eval_mul,
        eval_C, eval_pow, eval_X]
    have h2' : eval x₀ ψ = 0 := by rw [← Polynomial.coe_aeval_eq_eval]; exact hψx
    rw [← h1, h2']
  have hψ'val : 12 * x₀ ^ 2 + 2 * W.b₂ * x₀ + 2 * W.b₄ = 0 := by
    have h1 : eval x₀ (derivative ψ) = 12 * x₀ ^ 2 + 2 * W.b₂ * x₀ + 2 * W.b₄ := by
      simp only [hψ, Cubic.toPoly, WeierstrassCurve.twoTorsionPolynomial, derivative_add,
        derivative_mul, derivative_C, derivative_X_pow, derivative_X, zero_mul, zero_add,
        mul_one, eval_add, eval_mul, eval_C, eval_pow, eval_X, add_zero]
      push_cast
      ring
    have h2' : eval x₀ (derivative ψ) = 0 := by rw [← Polynomial.coe_aeval_eq_eval]; exact hψ'x
    rw [← h1, h2']
  set y₀ : k := -(W.a₁ * x₀ + W.a₃) / 2 with hy₀
  have hy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by rw [hy₀]; field_simp; ring
  refine ⟨x₀, y₀, ?_, ?_, ?_⟩
  · rw [equation_iff_F]

    have h4F : 4 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ -
        (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) = 0 := by
      have hb : 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ =
          4 * x₀ ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x₀ ^ 2 + 2 * (2 * W.a₄ + W.a₁ * W.a₃) * x₀ +
            (W.a₃ ^ 2 + 4 * W.a₆) := by
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      rw [hb] at hψval
      linear_combination (2 * y₀ + W.a₁ * x₀ + W.a₃) * hy - hψval
    exact (mul_eq_zero.mp h4F).resolve_left h4
  · rw [WeierstrassCurve.Affine.nonsingular_iff']
    push Not
    intro _
    constructor
    ·
      have hb : 12 * x₀ ^ 2 + 2 * W.b₂ * x₀ + 2 * W.b₄ =
          12 * x₀ ^ 2 + 2 * (W.a₁ ^ 2 + 4 * W.a₂) * x₀ + 2 * (2 * W.a₄ + W.a₁ * W.a₃) := by
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      rw [hb] at hψ'val
      have h4Fx : 4 * (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) = 0 := by
        linear_combination (2 * W.a₁) * hy - hψ'val
      exact (mul_eq_zero.mp h4Fx).resolve_left h4
    · exact hy
  ·
    intro h
    apply hc₄
    have hb : W.c₄ = (W.b₂ + 12 * x₀) ^ 2 - 12 * (12 * x₀ ^ 2 + 2 * W.b₂ * x₀ + 2 * W.b₄) := by
      simp only [WeierstrassCurve.c₄]; ring
    rw [hb, h, hψ'val]; ring

theorem exists_isNode [IsAlgClosed k] (W : WeierstrassCurve k) (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) :
    ∃ x₀ y₀ : k, W.toAffine.Equation x₀ y₀ ∧ ¬ W.toAffine.Nonsingular x₀ y₀ ∧
      W.b₂ + 12 * x₀ ≠ 0 := by
  by_cases h2 : (2 : k) = 0
  · exact exists_isNode_of_char_two W h2 hΔ hc₄
  · exact exists_isNode_of_two_ne_zero W h2 hΔ hc₄

end M3dS11

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point IsLocalRing

namespace M3dS11

theorem charP_residueField {L : Type*} [Field L] (A : ValuationSubring L) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) : CharP (ResidueField A) q := by
  refine (CharP.charP_iff_prime_eq_zero hq).mpr ?_
  obtain ⟨hqA, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := A)).mp hA
  have : ((q : A) : L) = (q : L) := by push_cast; rfl
  have hqA' : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    have e : (⟨(q : L), hqA⟩ : A) = (q : A) := Subtype.ext (by push_cast; rfl)
    rw [← e]; exact hmax
  have := (IsLocalRing.residue_eq_zero_iff (q : A)).mpr hqA'
  rwa [map_natCast] at this

end M3dS11

theorem solution (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) :
    ∃ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ, ¬ W.InZeroComponentAt A (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by
  by_contra hall
  push Not at hall

  haveI hchar : CharP (ResidueField A) q := M3dS11.charP_residueField A hq hA
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  letI : DecidableEq (ResidueField A) := Classical.decEq _
  have hqℓ : ¬ q ∣ ℓ := fun h => hℓq ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp h).symm

  set Wbar := W.map (Int.castRingHom (ResidueField A)) with hWbar
  obtain ⟨red, h0, hadd, -, -, hker, -⟩ := W.exists_reduction_inZeroComponentAt A

  have hcoe_nsmul : ∀ (n : ℕ)
      (P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ),
      ((n • P : Submodule.torsionBy ℤ _ ℓ) : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
        = n • (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := fun n P =>
    Submodule.coe_smul_of_tower _ _
  have htors : ∀ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ,
      ℓ • (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := by
    intro P
    have h := P.2
    rw [Submodule.mem_torsionBy_iff] at h
    rw [← natCast_zsmul]
    exact h

  have red_nsmul : ∀ (n : ℕ)
      (P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ),
      red (n • (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) = n • red P := by
    intro n P
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      rw [succ_nsmul, succ_nsmul, ← ih]
      refine hadd _ _ ?_ (hall P)
      rw [← hcoe_nsmul]
      exact hall (n • P)

  have red_inj : ∀ P Q : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ,
      red P = red Q → P = Q := by
    intro P Q hPQ
    have hsub : red ((P - Q : Submodule.torsionBy ℤ _ ℓ) :
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := by
      have e : red ((P - Q : Submodule.torsionBy ℤ _ ℓ) :
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) + red Q = red P := by
        rw [← hadd _ _ (hall (P - Q)) (hall Q)]
        congr 1
        push_cast
        abel
      rw [hPQ] at e
      exact add_eq_right.mp e
    rcases hker _ (hall (P - Q)) hsub with hzero | ⟨x, y, h, hxy, hx⟩
    · exact sub_eq_zero.mp (Subtype.ext hzero)
    · exfalso
      apply hx
      refine W.mem_valuationSubring_of_nsmul_eq_zero_of_liesOverPrime A hq hA hqℓ h ?_
      rw [← hxy]
      exact htors (P - Q)

  have hΔbar : Wbar.Δ = 0 := by
    rw [hWbar, map_Δ]
    exact (CharP.intCast_eq_zero_iff (ResidueField A) q W.Δ).mpr hqΔ
  have hc₄bar : Wbar.c₄ ≠ 0 := by
    rw [hWbar, map_c₄]
    exact fun h => hqc₄ ((CharP.intCast_eq_zero_iff (ResidueField A) q W.c₄).mp h)
  obtain ⟨x₀, y₀, he, hs, hnode⟩ := M3dS11.exists_isNode Wbar hΔbar hc₄bar
  obtain ⟨hSfin, hScard⟩ :=
    Point.finite_and_ncard_torsion_le_of_isNode Wbar x₀ y₀ he hs hnode hℓ.pos

  haveI : Finite {Q : Wbar.toAffine.Point | ℓ • Q = 0} := hSfin.to_subtype
  let f : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ →
      {Q : Wbar.toAffine.Point | ℓ • Q = 0} := fun P =>
    ⟨red P, by
      show ℓ • red P = 0
      rw [← red_nsmul, htors P, h0]⟩
  have hf : Function.Injective f := fun P Q h => red_inj P Q (congrArg Subtype.val h)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_coe_set_eq] at hle

  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨by rw [map_Δ, isUnit_iff_ne_zero, eq_intCast]; exact_mod_cast hΔ⟩
  have hℓQ : ((ℓ : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  rw [WeierstrassCurve.card_torsion_of_isAlgClosed (K := AlgebraicClosure ℚ)
    (W.map (Int.castRingHom ℚ)) hℓQ] at hle

  have h2 : 2 ≤ ℓ := hℓ.two_le
  have : ℓ ^ 2 ≤ ℓ := hle.trans hScard
  nlinarith

end S_WeierstrassCurve_exists_torsion_not_inZeroComponentAt_of_ne_residueChar
end P2MW
export P2MW.S_WeierstrassCurve_exists_torsion_not_inZeroComponentAt_of_ne_residueChar (solution)
