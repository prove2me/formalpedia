-- Prove2me | solution 1 for WeierstrassCurve.exists_torsionBy_residueChar_ne_zero_inZeroComponentAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c8ba8af0-bc87-5726-8428-fdc25b9f3c46

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_psiSq_ne_zero_of_nodal
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_torsionBy_residueChar_ne_zero_inZeroComponentAt
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open Polynomial

namespace NonbotQ

variable {K : Type*} [Field K]

theorem coeff_multiset_prod_X_sub_C_mem (A : ValuationSubring K) (m : Multiset K)
    (hm : ∀ r ∈ m, r ∈ A) (n : ℕ) : ((m.map (X - C ·)).prod).coeff n ∈ A := by
  induction m using Multiset.induction_on generalizing n with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one]
    split_ifs
    · exact one_mem A
    · exact zero_mem A
  | cons a m ih =>
    have ha : a ∈ A := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ r ∈ m, r ∈ A := fun r hr => hm r (Multiset.mem_cons_of_mem hr)
    rw [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine sub_mem ?_ (mul_mem ha (ih hm' n))
    cases n with
    | zero => rw [coeff_X_mul_zero]; exact zero_mem A
    | succ n => rw [coeff_X_mul]; exact ih hm' n

theorem exists_isRoot_and_notMem [IsAlgClosed K] (A : ValuationSubring K) {f : K[X]}
    (hlc : A.valuation f.leadingCoeff < 1) {n : ℕ} (hn : A.valuation (f.coeff n) = 1) :
    ∃ r : K, f.IsRoot r ∧ r ∉ A := by
  by_contra hall
  push Not at hall
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hn

  have hroots : ∀ r ∈ f.roots, r ∈ A := fun r hr =>
    hall r ((mem_roots hf0).mp hr)
  have hsplit := (IsAlgClosed.splits f).eq_prod_roots
  have hcoeff : f.coeff n = f.leadingCoeff * ((f.roots.map (X - C ·)).prod).coeff n := by
    conv_lhs => rw [hsplit]
    rw [coeff_C_mul]
  have hmem := coeff_multiset_prod_X_sub_C_mem A f.roots hroots n
  have : A.valuation (f.coeff n) < 1 := by
    rw [hcoeff, map_mul]
    calc A.valuation f.leadingCoeff * A.valuation ((f.roots.map (X - C ·)).prod.coeff n)
        ≤ A.valuation f.leadingCoeff * 1 := by
          gcongr
          exact (A.valuation_le_one_iff _).mpr hmem
      _ < 1 := by rwa [mul_one]
  exact this.ne hn

end NonbotQ

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace NonbotQ

variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem _root_.NonbotQ.residue_eq_zero_iff (a : A) :
    IsLocalRing.residue A a = 0 ↔ A.valuation (a : L) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

p2m_export "NonbotQ" "residue_eq_zero_iff"

theorem charP_residueField {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) :
    CharP (IsLocalRing.ResidueField A) q := by
  refine (CharP.charP_iff_prime_eq_zero hq).mpr ?_
  have : ((q : A) : L) ∈ A.nonunits := by simp at hA ⊢; exact hA
  rw [ValuationSubring.mem_nonunits_iff] at this
  have h := (residue_eq_zero_iff A (q : A)).mpr this
  simpa using h

end NonbotQ

theorem solution
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point q,
      P ≠ 0 ∧ W.InZeroComponentAt A (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by
  classical
  set E : WeierstrassCurve (AlgebraicClosure ℚ) := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
    with hE

  have hEW : E = W.map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    have : E = (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ)) := rfl
    rw [this, WeierstrassCurve.map_map]
    congr 1

  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ, eq_intCast]; exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hΔ)⟩
  haveI hEll : E.IsElliptic := by
    rw [show E = (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ)) from rfl]
    infer_instance

  set f : (AlgebraicClosure ℚ)[X] := E.ΨSq q with hf
  have hfW : f = (W.ΨSq q).map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    rw [hf, hEW, WeierstrassCurve.map_ΨSq]

  have hcoeffA : ∀ n, f.coeff n ∈ A := by
    intro n; rw [hfW, Polynomial.coeff_map]; exact intCast_mem A _

  have hq0 : ((q : ℤ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hlc : A.valuation f.leadingCoeff < 1 := by
    rw [hf, WeierstrassCurve.leadingCoeff_ΨSq _ hq0]
    have hqA : A.valuation ((q : ℤ) : AlgebraicClosure ℚ) < 1 := by
      have : (q : AlgebraicClosure ℚ) ∈ A.nonunits := hA
      rw [ValuationSubring.mem_nonunits_iff] at this
      exact_mod_cast this
    rw [map_pow]
    exact pow_lt_one₀ zero_le' hqA two_ne_zero

  haveI := NonbotQ.charP_residueField A hq hA
  set k := IsLocalRing.ResidueField A
  have hred : (W.map (Int.castRingHom k)).ΨSq q ≠ 0 := by
    refine WeierstrassCurve.psiSq_ne_zero_of_nodal hq _ ?_ ?_
    · rw [WeierstrassCurve.map_Δ, eq_intCast, (CharP.intCast_eq_zero_iff k q _)]
      exact hqΔ
    · rw [WeierstrassCurve.map_c₄, eq_intCast, Ne, (CharP.intCast_eq_zero_iff k q _)]
      exact hqc₄
  obtain ⟨n, hn⟩ : ∃ n, ((W.map (Int.castRingHom k)).ΨSq q).coeff n ≠ 0 := by
    by_contra h; push Not at h; exact hred (Polynomial.ext fun n => by simpa using h n)
  rw [WeierstrassCurve.map_ΨSq, Polynomial.coeff_map, eq_intCast] at hn
  have hunit : A.valuation (f.coeff n) = 1 := by
    have hle : A.valuation (f.coeff n) ≤ 1 := (A.valuation_le_one_iff _).mpr (hcoeffA n)
    refine le_antisymm hle (not_lt.mp fun hlt => hn ?_)
    have key : IsLocalRing.residue A (((W.ΨSq q).coeff n : ℤ) : A) = 0 := by
      rw [NonbotQ.residue_eq_zero_iff]
      have : (((((W.ΨSq q).coeff n : ℤ) : A) : AlgebraicClosure ℚ)) = f.coeff n := by
        rw [hfW, Polynomial.coeff_map, eq_intCast]; simp
      rw [this]; exact hlt
    simpa using key

  obtain ⟨r, hr, hrA⟩ := NonbotQ.exists_isRoot_and_notMem A hlc hunit

  set g : (AlgebraicClosure ℚ)[X] :=
    X ^ 2 + C (E.a₁ * r + E.a₃) * X - C (r ^ 3 + E.a₂ * r ^ 2 + E.a₄ * r + E.a₆) with hg
  have hgdeg : g.degree = 2 := by
    rw [hg]; compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root g (by rw [hgdeg]; norm_num)
  have heq : E.toAffine.Equation r y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have : g.eval y = 0 := hy
    rw [hg] at this
    simp only [eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at this
    linear_combination this
  have hns : E.toAffine.Nonsingular r y := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq

  have hψ : (E.ψ q).evalEval r y = 0 := by
    have hmk : WeierstrassCurve.Affine.CoordinateRing.mk E ((E.ψ q) ^ 2 - C (E.ΨSq q)) = 0 := by
      rw [map_sub, map_pow, WeierstrassCurve.Affine.CoordinateRing.mk_ψ,
        WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq, sub_self]
    rw [AdjoinRoot.mk_eq_zero] at hmk
    obtain ⟨c, hc⟩ := hmk
    have hev := congrArg (Polynomial.evalEval r y) hc
    rw [Polynomial.evalEval_sub, Polynomial.evalEval_pow, Polynomial.evalEval_C,
      Polynomial.evalEval_mul] at hev
    have hW0 : E.toAffine.polynomial.evalEval r y = 0 := heq
    rw [hW0, zero_mul, sub_eq_zero] at hev
    have hroot : (E.ΨSq q).eval r = 0 := hr
    rw [hroot] at hev
    exact pow_eq_zero_iff two_ne_zero |>.mp hev
  have htor : (q : ℤ) • (Point.some r y hns) = 0 :=
    (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff E hns q).mpr hψ
  refine ⟨⟨Point.some r y hns, (Submodule.mem_torsionBy_iff _ _).mpr htor⟩, ?_, ?_⟩
  · intro h0
    have := congrArg Subtype.val h0
    exact WeierstrassCurve.Affine.Point.some_ne_zero hns this
  · exact Or.inr ⟨r, y, hns, rfl, Or.inl hrA⟩

end S_WeierstrassCurve_exists_torsionBy_residueChar_ne_zero_inZeroComponentAt
end P2MW
export P2MW.S_WeierstrassCurve_exists_torsionBy_residueChar_ne_zero_inZeroComponentAt (solution)
