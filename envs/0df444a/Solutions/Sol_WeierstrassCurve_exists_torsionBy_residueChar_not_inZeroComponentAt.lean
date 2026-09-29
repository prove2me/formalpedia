-- Prove2me | solution 1 for WeierstrassCurve.exists_torsionBy_residueChar_not_inZeroComponentAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7e0c7196-f7be-5590-a8a4-70f66ebb5fa5

import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_psiSq_ne_zero_of_nodal
import Theorems.Thm_WeierstrassCurve_eval_psiSq_eq_zero_of_singular
import Theorems.Thm_Polynomial_exists_isRoot_and_valuation_lt_one
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_torsionBy_residueChar_not_inZeroComponentAt
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

p2m_open "WeierstrassCurve~evalEval_ψ_sq WeierstrassCurve.Affine WeierstrassCurve.Affine.Point IsLocalRing Polynomial"

namespace M3dS11

theorem charP_residueField {L : Type*} [Field L] (A : ValuationSubring L) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) : CharP (ResidueField A) q := by
  refine (CharP.charP_iff_prime_eq_zero hq).mpr ?_
  obtain ⟨hqA, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := A)).mp hA
  have hqA' : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    have e : (⟨(q : L), hqA⟩ : A) = (q : A) := Subtype.ext (by push_cast; rfl)
    rw [← e]; exact hmax
  have := (IsLocalRing.residue_eq_zero_iff (q : A)).mpr hqA'
  rwa [map_natCast] at this

theorem evalEval_ψ_sq {K : Type*} [Field K] (W : WeierstrassCurve K) {x y : K}
    (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have hmk : AdjoinRoot.mk W.toAffine.polynomial (W.ψ n ^ 2) =
      AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C (W.ΨSq n)) := by
    rw [map_pow, WeierstrassCurve.Affine.CoordinateRing.mk_ψ,
      WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have heq : W.toAffine.polynomial.evalEval x y = 0 := h
  have := congrArg (Polynomial.evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, heq, zero_mul, sub_eq_zero, evalEval_pow, evalEval_C] at this
  exact this

theorem residue_eq_zero_iff_valuation_lt_one {L : Type*} [Field L] (A : ValuationSubring L)
    (a : A) : residue A a = 0 ↔ A.valuation (a : L) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact ValuationSubring.valuation_lt_one_iff A a

end M3dS11

theorem solution
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point q, ¬ W.InZeroComponentAt A (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by

  have hq2 : 2 ≤ q := hq.two_le

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, -⟩ :=
    W.exists_criticalCentre_of_multiplicativeReduction hq hΔ hqΔ hqc₄ A hA

  haveI hchar : CharP (ResidueField A) q := M3dS11.charP_residueField A hq hA
  set k := ResidueField A
  set Wbar : WeierstrassCurve k := W.map (Int.castRingHom k) with hWbar
  have hΔbar : Wbar.Δ = 0 := by
    rw [hWbar, map_Δ]; exact (CharP.intCast_eq_zero_iff k q W.Δ).mpr hqΔ
  have hc₄bar : Wbar.c₄ ≠ 0 := by
    rw [hWbar, map_c₄]; exact fun h => hqc₄ ((CharP.intCast_eq_zero_iff k q W.c₄).mp h)

  set WA : WeierstrassCurve A := W.map (Int.castRingHom A) with hWA
  have hWA_res : WA.map (residue A) = Wbar := by
    rw [hWA, WeierstrassCurve.map_map, hWbar, RingHom.ext_int ((residue A).comp (Int.castRingHom A))
      (Int.castRingHom k)]
  have hE : (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) = WA.map A.subtype := by
    show (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ)) = WA.map A.subtype
    rw [hWA, WeierstrassCurve.map_map, WeierstrassCurve.map_map,
      RingHom.ext_int ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ))
        (A.subtype.comp (Int.castRingHom A))]

  set X0 : A := ⟨x₀, hx₀⟩
  set Y0 : A := ⟨y₀, hy₀⟩
  have hFyA : 2 * Y0 + (W.a₁ : A) * X0 + (W.a₃ : A) = 0 := by
    apply Subtype.ext
    push_cast
    exact hFy
  have hFxA : (W.a₁ : A) * Y0 = 3 * X0 ^ 2 + 2 * (W.a₂ : A) * X0 + (W.a₄ : A) := by
    apply Subtype.ext
    push_cast
    exact hFx
  have hFA : A.valuation ((Y0 ^ 2 + (W.a₁ : A) * X0 * Y0 + (W.a₃ : A) * Y0
      - (X0 ^ 3 + (W.a₂ : A) * X0 ^ 2 + (W.a₄ : A) * X0 + (W.a₆ : A)) : A) : AlgebraicClosure ℚ) < 1 := by
    push_cast
    exact hbad
  have hbFy : 2 * residue A Y0 + Wbar.a₁ * residue A X0 + Wbar.a₃ = 0 := by
    have := congrArg (residue A) hFyA
    simp only [map_add, map_mul, map_ofNat, map_intCast, _root_.map_zero] at this
    simpa [hWbar] using this
  have hbFx : Wbar.a₁ * residue A Y0 = 3 * residue A X0 ^ 2 + 2 * Wbar.a₂ * residue A X0 + Wbar.a₄ := by
    have := congrArg (residue A) hFxA
    simp only [map_add, map_mul, map_ofNat, map_intCast, map_pow] at this
    simpa [hWbar] using this
  have hbeq : Wbar.toAffine.Equation (residue A X0) (residue A Y0) := by
    rw [WeierstrassCurve.Affine.equation_iff']
    have h0 := (M3dS11.residue_eq_zero_iff_valuation_lt_one A _).mpr hFA
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast] at h0
    simpa [hWbar] using h0

  have hΨbar_ne : Wbar.ΨSq q ≠ 0 := Wbar.psiSq_ne_zero_of_nodal hq hΔbar hc₄bar
  have hΨbar_x0 : (Wbar.ΨSq q).eval (residue A X0) = 0 :=
    Wbar.eval_psiSq_eq_zero_of_singular hbeq hbFx hbFy (n := q) (by simp at hq2 ⊢; exact hq2)

  set FA : Polynomial A := WA.ΨSq q with hFAdef
  set GA : Polynomial A := FA.comp (X + C X0) with hGA
  have hFA_res : FA.map (residue A) = Wbar.ΨSq q := by
    rw [hFAdef, ← WeierstrassCurve.map_ΨSq, hWA_res]
  have hGA_res : GA.map (residue A) = (Wbar.ΨSq q).comp (X + C (residue A X0)) := by
    rw [hGA, Polynomial.map_comp, hFA_res]
    simp

  have hGbar_ne : GA.map (residue A) ≠ 0 := by
    rw [hGA_res]
    intro h0
    apply hΨbar_ne
    have : Wbar.ΨSq q = ((Wbar.ΨSq q).comp (X + C (residue A X0))).comp (X - C (residue A X0)) := by
      rw [Polynomial.comp_assoc]
      simp
    rw [this, h0, Polynomial.zero_comp]
  obtain ⟨n, hn⟩ : ∃ n, (GA.map (residue A)).coeff n ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hGbar_ne (Polynomial.ext fun m => by simpa using hall m)
  rw [Polynomial.coeff_map] at hn
  have hunit : A.valuation ((GA.coeff n : A) : AlgebraicClosure ℚ) = 1 := by
    refine le_antisymm (A.valuation_le_one _) ?_
    by_contra hlt
    push Not at hlt
    exact hn ((M3dS11.residue_eq_zero_iff_valuation_lt_one A _).mpr hlt)

  have hG0 : A.valuation ((GA.coeff 0 : A) : AlgebraicClosure ℚ) < 1 := by
    rw [← M3dS11.residue_eq_zero_iff_valuation_lt_one, Polynomial.coeff_zero_eq_eval_zero, hGA,
      Polynomial.eval_comp]
    have : (residue A) (FA.eval ((X + C X0).eval 0)) = (FA.map (residue A)).eval (residue A X0) := by
      rw [Polynomial.eval_map, ← Polynomial.eval₂_at_apply]
      simp
    rw [this, hFA_res, hΨbar_x0]

  set g : Polynomial (AlgebraicClosure ℚ) := GA.map A.subtype with hg
  have hg_coeff : ∀ m, g.coeff m = ((GA.coeff m : A) : AlgebraicClosure ℚ) := fun m => by
    rw [hg, Polynomial.coeff_map]; rfl
  have hg0 : A.valuation (g.coeff 0) < 1 := by rw [hg_coeff]; exact hG0
  have hgn : A.valuation (g.coeff n) = 1 := by rw [hg_coeff]; exact hunit

  obtain ⟨s, hs, hsv⟩ := Polynomial.exists_isRoot_and_valuation_lt_one A hg0 hgn
  set r : AlgebraicClosure ℚ := s + x₀ with hr
  have hΨr : (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).ΨSq q).eval r = 0 := by
    rw [hE, WeierstrassCurve.map_ΨSq]
    have h1 : g.eval s = 0 := hs
    rw [hg, hGA, Polynomial.map_comp, Polynomial.eval_comp] at h1
    have h2 : (Polynomial.map A.subtype (X + C X0)).eval s = r := by
      rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, eval_add, eval_X, eval_C, hr]
      rfl
    rwa [h2, hFAdef] at h1

  have hΔE : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Δ ≠ 0 := by
    rw [hE, map_Δ, hWA, map_Δ]
    simp only [ValuationSubring.coe_subtype, eq_intCast]
    exact_mod_cast hΔ
  obtain ⟨y, hy⟩ : ∃ y, ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Equation r y := by
    set E := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) with hEdef
    set Qy : Polynomial (AlgebraicClosure ℚ) := X ^ 2 + C (E.a₁ * r + E.a₃) * X -
      C (r ^ 3 + E.a₂ * r ^ 2 + E.a₄ * r + E.a₆) with hQy
    have hQdeg : Qy.degree = 2 := by rw [hQy]; compute_degree!
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root Qy (by rw [hQdeg]; norm_num)
    refine ⟨y, ?_⟩
    rw [WeierstrassCurve.Affine.equation_iff']
    have : Qy.eval y = 0 := hy
    simp only [hQy, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at this
    linear_combination this
  have h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular r y :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔE).mp hy
  have hψ : (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).ψ q).evalEval r y = 0 := by
    have := M3dS11.evalEval_ψ_sq _ hy q
    rw [hΨr, sq_eq_zero_iff] at this
    exact this
  have htors : (q : ℤ) • (Point.some r y h) = 0 :=
    (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff _ h q).mpr hψ
  refine ⟨⟨Point.some r y h, (Submodule.mem_torsionBy_iff _ _).mpr htors⟩, ?_⟩

  show ¬ W.InZeroComponentAt A (Point.some r y h)
  refine (W.not_inZeroComponentAt_some_iff_of_criticalCentre A hx₀ hy₀ hFy hFx hnode hbad h).mpr ?_
  have : r - x₀ = s := by rw [hr]; ring
  rw [this]
  exact hsv

end S_WeierstrassCurve_exists_torsionBy_residueChar_not_inZeroComponentAt
end P2MW
export P2MW.S_WeierstrassCurve_exists_torsionBy_residueChar_not_inZeroComponentAt (solution)
