-- Prove2me | solution 1 for WeierstrassCurve.bijective_reduceHom_restrict_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b5b61d1b-6dda-5a7d-99b1-73f773cea988

import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_eval_psiSq_eq_zero_of_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_bijective_reduceHom_restrict_torsion
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point IsLocalRing Polynomial

namespace TorsEven

private lemma some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

lemma baseChange_self' {R : Type*} [CommRing R] (V : WeierstrassCurve R) : V⁄R = V := by
  rw [show V⁄R = V.map (algebraMap R R) from rfl, Algebra.algebraMap_self,
    WeierstrassCurve.map_id]

lemma residue_eq_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (h : a - b ∈ maximalIdeal R) : residue R a = residue R b := by
  have h0 : residue R (a - b) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal R)).mpr h
  rwa [map_sub, sub_eq_zero] at h0

section TwoTorsion

theorem eval_Ψ₂Sq_eq_sq {R : Type*} [CommRing R] (V : WeierstrassCurve R) {x y : R}
    (heq : V.toAffine.Equation x y) :
    V.Ψ₂Sq.eval x = (y - V.toAffine.negY x y) ^ 2 := by
  rw [WeierstrassCurve.Affine.equation_iff'] at heq
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    WeierstrassCurve.Affine.negY]
  linear_combination -4 * heq

variable {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}

theorem two_zsmul_some_eq_zero_iff_eq_negY {x y : F} (h : V.toAffine.Nonsingular x y) :
    (2 : ℤ) • (Point.some x y h : V.toAffine.Point) = 0 ↔ y = V.toAffine.negY x y := by
  rw [two_zsmul, add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some]
  constructor
  · intro hP
    exact (Point.some.inj hP).2
  · intro hy
    exact some_congr rfl hy _ _

end TwoTorsion

private lemma equation_of_Ψ₂Sq_isRoot {R : Type*} [CommRing R] {W : WeierstrassCurve R}
    {x y : R} (h4 : IsUnit (4 : R)) (hy2 : 2 * y + (W.a₁ * x + W.a₃) = 0)
    (hx : W.Ψ₂Sq.IsRoot x) : W.toAffine.Equation x y := by
  have h : Polynomial.eval x W.Ψ₂Sq = 0 := hx
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X] at h
  rw [WeierstrassCurve.Affine.equation_iff']
  have key : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    apply h4.mul_left_cancel
    rw [mul_zero]
    linear_combination (2 * y + W.a₁ * x + W.a₃) * hy2 - h
  linear_combination key

section Count

variable {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k]
  (V : WeierstrassCurve k) [V.IsElliptic]

theorem card_torsionBy_eq_sq {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ)) = n ^ 2 := by
  have h := WeierstrassCurve.card_torsion_of_isAlgClosed (F := k) (K := k) V (n := n) hn
  rwa [baseChange_self'] at h

omit [IsAlgClosed k] in

theorem preΨ_isRoot_of_smul_eq_zero_of_ne_negY {n : ℤ} {x y : k}
    (h : V.toAffine.Nonsingular x y)
    (hP : n • (Point.some x y h : V.toAffine.Point) = 0) (hy : y ≠ V.toAffine.negY x y) :
    (V.preΨ n).IsRoot x := by
  have hsq := WeierstrassCurve.Affine.Point.eval_psiSq_eq_zero_of_smul_eq_zero h hP
  have heq : V.toAffine.Equation x y := ((V.toAffine.nonsingular_iff x y).mp h).1
  unfold WeierstrassCurve.ΨSq at hsq
  rw [eval_mul, mul_eq_zero, eval_pow, sq_eq_zero_iff] at hsq
  rcases hsq with hsq | hsq
  · exact hsq
  · exfalso
    split_ifs at hsq
    · rw [eval_Ψ₂Sq_eq_sq V heq] at hsq
      exact hy (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq))
    · rw [eval_one] at hsq
      exact one_ne_zero hsq

def twoPart (n : ℕ) : ℕ := if Even n then 4 else 1

omit [DecidableEq k] [IsAlgClosed k] [V.IsElliptic] in
private lemma natDegree_preΨ_eq {n : ℕ} (hn : (n : k) ≠ 0) :
    (V.preΨ (n : ℤ)).natDegree = (n ^ 2 - twoPart n) / 2 := by
  have h := V.natDegree_preΨ (n := (n : ℤ)) (by exact_mod_cast hn)
  rw [Int.natAbs_natCast] at h
  rcases Nat.even_or_odd n with hev | hodd
  · rw [if_pos ((Int.even_coe_nat n).mpr hev)] at h
    rw [h, twoPart, if_pos hev]
  · rw [if_neg (fun he => (Nat.not_even_iff_odd.mpr hodd) ((Int.even_coe_nat n).mp he))] at h
    rw [h, twoPart, if_neg (Nat.not_even_iff_odd.mpr hodd)]

omit [DecidableEq k] [IsAlgClosed k] [V.IsElliptic] in
private lemma preΨ_ne_zero' {n : ℕ} (hn : (n : k) ≠ 0) : V.preΨ (n : ℤ) ≠ 0 :=
  V.preΨ_ne_zero (n := (n : ℤ)) (by exact_mod_cast hn)

private def torsX₂ (n : ℕ) : Set k :=
  {x : k | ∃ y, ∃ h : V.toAffine.Nonsingular x y,
    (n : ℤ) • (Point.some x y h : V.toAffine.Point) = 0 ∧ y ≠ V.toAffine.negY x y}

omit [IsAlgClosed k] in
private lemma isRoot_of_mem_torsX₂ {n : ℕ} {x : k} (hx : x ∈ torsX₂ V n) :
    (V.preΨ (n : ℤ)).IsRoot x := by
  obtain ⟨y, h, hP, hy⟩ := hx
  exact preΨ_isRoot_of_smul_eq_zero_of_ne_negY V h hP hy

omit [IsAlgClosed k] in
private lemma torsX₂_finite {n : ℕ} (hn : (n : k) ≠ 0) : (torsX₂ V n).Finite := by
  refine Set.Finite.subset (V.preΨ (n : ℤ)).roots.finite_toSet fun x hx => ?_
  exact (Polynomial.mem_roots (preΨ_ne_zero' V hn)).mpr (isRoot_of_mem_torsX₂ V hx)

private noncomputable def torsSec {n : ℕ} (z : torsX₂ V n) : V.toAffine.Point :=
  Point.some z.1 z.2.choose z.2.choose_spec.choose

omit [IsAlgClosed k] [V.IsElliptic] in
private lemma torsSec_spec {n : ℕ} (z : torsX₂ V n) : (n : ℤ) • torsSec V z = 0 :=
  z.2.choose_spec.choose_spec.1

omit [IsAlgClosed k] [V.IsElliptic] in
private lemma neg_torsSec {n : ℕ} (z : torsX₂ V n) :
    - torsSec V z = Point.some z.1 (V.toAffine.negY z.1 z.2.choose)
      ((V.toAffine.nonsingular_neg _ _).mpr z.2.choose_spec.choose) := by
  show - Point.some z.1 z.2.choose z.2.choose_spec.choose = _
  rw [WeierstrassCurve.Affine.Point.neg_some]

omit [IsAlgClosed k] [V.IsElliptic] in
private lemma two_zsmul_torsSec_ne_zero {n : ℕ} (z : torsX₂ V n) :
    (2 : ℤ) • torsSec V z ≠ 0 := by
  show (2 : ℤ) • Point.some z.1 z.2.choose z.2.choose_spec.choose ≠ 0
  rw [Ne, two_zsmul_some_eq_zero_iff_eq_negY]
  exact z.2.choose_spec.choose_spec.2

omit [IsAlgClosed k] [V.IsElliptic] in
private lemma two_zsmul_neg_torsSec_ne_zero {n : ℕ} (z : torsX₂ V n) :
    (2 : ℤ) • (- torsSec V z) ≠ 0 := by
  rw [smul_neg, neg_ne_zero]
  exact two_zsmul_torsSec_ne_zero V z

private lemma finite_torsionBy {n : ℕ} (hn : (n : k) ≠ 0) :
    Finite (Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ)) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have hpos : 0 < Nat.card (Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ)) := by
    rw [card_torsionBy_eq_sq V hn]
    exact pow_pos (Nat.pos_of_ne_zero hn0) 2
  exact (Nat.card_pos_iff.mp hpos).2

private lemma card_twoTors_le {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card {P : Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ) //
      (2 : ℤ) • (P : V.toAffine.Point) = 0} ≤ twoPart n := by
  classical
  haveI := finite_torsionBy V hn
  rcases Nat.even_or_odd n with hev | hodd
  · rw [twoPart, if_pos hev]
    have h2 : (2 : k) ≠ 0 := by
      intro h0
      obtain ⟨m, hm⟩ := hev
      apply hn
      rw [hm, Nat.cast_add, ← two_mul, h0, zero_mul]
    have h2' : ((2 : ℕ) : k) ≠ 0 := by exact_mod_cast h2
    haveI := finite_torsionBy V (n := 2) h2'
    calc Nat.card {P : Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ) //
            (2 : ℤ) • (P : V.toAffine.Point) = 0}
        ≤ Nat.card (Submodule.torsionBy ℤ V.toAffine.Point ((2 : ℕ) : ℤ)) :=
          Nat.card_le_card_of_injective
            (fun P : {P : Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ) //
                (2 : ℤ) • (P : V.toAffine.Point) = 0} =>
              (⟨(P.1 : V.toAffine.Point), by
                rw [Submodule.mem_torsionBy_iff]
                exact_mod_cast P.2⟩ : Submodule.torsionBy ℤ V.toAffine.Point ((2 : ℕ) : ℤ)))
            (by
              rintro ⟨⟨P, hP⟩, hP2⟩ ⟨⟨Q, hQ⟩, hQ2⟩ h
              have hPQ : P = Q := by
                have h' := congrArg Subtype.val h
                exact h'
              exact Subtype.ext (Subtype.ext hPQ))
      _ = 4 := by
          rw [card_torsionBy_eq_sq V (n := 2) h2']
          norm_num
  · rw [twoPart, if_neg (Nat.not_even_iff_odd.mpr hodd)]
    refine Finite.card_le_one_iff_subsingleton.mpr ⟨?_⟩
    have hzero : ∀ P : {P : Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ) //
        (2 : ℤ) • (P : V.toAffine.Point) = 0}, (P.1 : V.toAffine.Point) = 0 := by
      rintro ⟨⟨P, hPn⟩, hP2⟩
      rw [Submodule.mem_torsionBy_iff] at hPn
      obtain ⟨m, rfl⟩ := hodd
      have hs : (((2 * m + 1 : ℕ) : ℤ)) = (m : ℤ) * 2 + 1 := by push_cast; ring
      have hP2' : (2 : ℤ) • P = 0 := hP2
      rw [hs, add_smul, mul_smul, hP2', smul_zero, zero_add, one_smul] at hPn
      exact hPn
    intro a b
    exact Subtype.ext (Subtype.ext ((hzero a).trans (hzero b).symm))

private lemma card_nonTwoTors_ge {n : ℕ} (hn : (n : k) ≠ 0) :
    n ^ 2 - twoPart n ≤ Nat.card {P : Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ) //
      (2 : ℤ) • (P : V.toAffine.Point) ≠ 0} := by
  classical
  haveI := finite_torsionBy V hn
  haveI := Fintype.ofFinite (Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ))
  have hT : Fintype.card {P : Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ) //
      (2 : ℤ) • (P : V.toAffine.Point) = 0} ≤ twoPart n := by
    rw [← Nat.card_eq_fintype_card]
    exact card_twoTors_le V hn
  have hcompl := Fintype.card_subtype_compl
    (p := fun P : Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ) =>
      (2 : ℤ) • (P : V.toAffine.Point) = 0)
  have hcard : Fintype.card (Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ)) = n ^ 2 := by
    rw [← Nat.card_eq_fintype_card, card_torsionBy_eq_sq V hn]
  show n ^ 2 - twoPart n ≤ Nat.card {P : Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ) //
    ¬ (2 : ℤ) • (P : V.toAffine.Point) = 0}
  rw [Nat.card_eq_fintype_card, hcompl, hcard]
  omega

omit [IsAlgClosed k] in

private lemma card_nonTwoTors_le {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card {P : Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ) //
      (2 : ℤ) • (P : V.toAffine.Point) ≠ 0} ≤ 2 * Nat.card (torsX₂ V n) := by
  classical
  haveI : Finite (torsX₂ V n) := (torsX₂_finite V hn).to_subtype
  have hG : Function.Surjective
      (fun z : torsX₂ V n × Fin 2 =>
        (⟨⟨if z.2 = 0 then torsSec V z.1 else - torsSec V z.1, by
            rw [Submodule.mem_torsionBy_iff]
            split_ifs
            · exact torsSec_spec V z.1
            · rw [smul_neg, torsSec_spec V z.1, _root_.neg_zero]⟩, by
            show (2 : ℤ) • (if z.2 = 0 then torsSec V z.1 else - torsSec V z.1) ≠ 0
            split_ifs
            · exact two_zsmul_torsSec_ne_zero V z.1
            · exact two_zsmul_neg_torsSec_ne_zero V z.1⟩ :
          {P : Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ) //
            (2 : ℤ) • (P : V.toAffine.Point) ≠ 0})) := by
    rintro ⟨⟨P, hPtors⟩, hPne⟩
    rw [Submodule.mem_torsionBy_iff] at hPtors
    induction P with
    | zero => exact absurd (smul_zero (2 : ℤ)) hPne
    | @some x y h =>
      have hy : y ≠ V.toAffine.negY x y := fun hy =>
        hPne ((two_zsmul_some_eq_zero_iff_eq_negY h).mpr hy)
      have hxX : x ∈ torsX₂ V n := ⟨y, h, hPtors, hy⟩
      have heq₁ : V.toAffine.Equation x y := ((V.toAffine.nonsingular_iff x y).mp h).1
      have heq₀ : V.toAffine.Equation x hxX.choose :=
        ((V.toAffine.nonsingular_iff x hxX.choose).mp hxX.choose_spec.choose).1
      rcases WeierstrassCurve.Affine.Y_eq_of_X_eq heq₁ heq₀ rfl with hy | hy
      · refine ⟨⟨⟨x, hxX⟩, 0⟩, ?_⟩
        refine Subtype.ext (Subtype.ext ?_)
        show (if (0 : Fin 2) = 0 then torsSec V ⟨x, hxX⟩ else - torsSec V ⟨x, hxX⟩) =
          Point.some x y h
        rw [if_pos rfl]
        exact some_congr rfl hy.symm _ h
      · refine ⟨⟨⟨x, hxX⟩, 1⟩, ?_⟩
        refine Subtype.ext (Subtype.ext ?_)
        show (if (1 : Fin 2) = 0 then torsSec V ⟨x, hxX⟩ else - torsSec V ⟨x, hxX⟩) =
          Point.some x y h
        rw [if_neg (by decide : ¬ (1 : Fin 2) = 0), neg_torsSec]
        exact some_congr rfl hy.symm _ h
  calc Nat.card {P : Submodule.torsionBy ℤ V.toAffine.Point (n : ℤ) //
        (2 : ℤ) • (P : V.toAffine.Point) ≠ 0}
      ≤ Nat.card (torsX₂ V n × Fin 2) := Nat.card_le_card_of_surjective _ hG
    _ = 2 * Nat.card (torsX₂ V n) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
          mul_comm]

private lemma roots_nodup_and_mem {n : ℕ} (hn : (n : k) ≠ 0) :
    (V.preΨ (n : ℤ)).roots.Nodup ∧
      ∀ x : k, (V.preΨ (n : ℤ)).IsRoot x → x ∈ torsX₂ V n := by
  classical
  have hp0 : V.preΨ (n : ℤ) ≠ 0 := preΨ_ne_zero' V hn
  have hD : (V.preΨ (n : ℤ)).natDegree = (n ^ 2 - twoPart n) / 2 := natDegree_preΨ_eq V hn
  have hfinX : (torsX₂ V n).Finite := torsX₂_finite V hn
  have hsub : hfinX.toFinset ⊆ (V.preΨ (n : ℤ)).roots.toFinset := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    exact isRoot_of_mem_torsX₂ V hx
  have hcardX : hfinX.toFinset.card = Nat.card (torsX₂ V n) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card (torsX₂ V n) hfinX]
  have hge : (n ^ 2 - twoPart n) / 2 ≤ hfinX.toFinset.card := by
    rw [hcardX]
    have h₁ := card_nonTwoTors_ge V hn
    have h₂ := card_nonTwoTors_le V hn
    omega
  have hchain1 : (V.preΨ (n : ℤ)).roots.toFinset.card ≤ (V.preΨ (n : ℤ)).roots.card :=
    Multiset.toFinset_card_le _
  have hchain2 : (V.preΨ (n : ℤ)).roots.card ≤ (n ^ 2 - twoPart n) / 2 :=
    hD ▸ (V.preΨ (n : ℤ)).card_roots'
  have hchain3 : hfinX.toFinset.card ≤ (V.preΨ (n : ℤ)).roots.toFinset.card :=
    Finset.card_le_card hsub
  have heqFin : hfinX.toFinset = (V.preΨ (n : ℤ)).roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hnodup : (V.preΨ (n : ℤ)).roots.Nodup := by
    have hfc : (V.preΨ (n : ℤ)).roots.toFinset.card =
        (V.preΨ (n : ℤ)).roots.dedup.card :=
      congrArg Multiset.card (Multiset.toFinset_val _)
    have heq : (V.preΨ (n : ℤ)).roots = (V.preΨ (n : ℤ)).roots.dedup :=
      (Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) (by omega)).symm
    rw [heq]
    exact Multiset.nodup_dedup _
  refine ⟨hnodup, fun x hx => ?_⟩
  have hxmem : x ∈ (V.preΨ (n : ℤ)).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    exact hx
  rw [← heqFin, Set.Finite.mem_toFinset] at hxmem
  exact hxmem

theorem exists_smul_eq_zero_of_preΨ_isRoot {n : ℕ} (hn : (n : k) ≠ 0)
    {x : k} (hx : (V.preΨ (n : ℤ)).IsRoot x) :
    ∃ y, ∃ h : V.toAffine.Nonsingular x y,
      (n : ℤ) • (Point.some x y h : V.toAffine.Point) = 0 ∧ y ≠ V.toAffine.negY x y :=
  (roots_nodup_and_mem V hn).2 x hx

theorem eval_derivative_preΨ_ne_zero_of_isRoot {n : ℕ} (hn : (n : k) ≠ 0)
    {x : k} (hx : (V.preΨ (n : ℤ)).IsRoot x) :
    (derivative (V.preΨ (n : ℤ))).eval x ≠ 0 := by
  classical
  have hp0 : V.preΨ (n : ℤ) ≠ 0 := preΨ_ne_zero' V hn
  have hnodup : (V.preΨ (n : ℤ)).roots.Nodup := (roots_nodup_and_mem V hn).1
  have hlc0 : (V.preΨ (n : ℤ)).leadingCoeff⁻¹ ≠ 0 :=
    inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp0)

  set q := V.preΨ (n : ℤ) * C (V.preΨ (n : ℤ)).leadingCoeff⁻¹ with hq
  have hqmonic : q.Monic := Polynomial.monic_mul_leadingCoeff_inv hp0
  have hqroots : q.roots = (V.preΨ (n : ℤ)).roots := by
    rw [hq, mul_comm, Polynomial.roots_C_mul _ hlc0]
  have hprod : q = (q.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits q).eq_prod_roots_of_monic hqmonic
  have hxq : x ∈ q.roots := by
    rw [hqroots, Polynomial.mem_roots hp0]
    exact hx
  have hkey : (derivative q).eval x ≠ 0 := by
    obtain ⟨t, ht⟩ : ∃ t, q.roots = x ::ₘ t :=
      ⟨q.roots.erase x, (Multiset.cons_erase hxq).symm⟩
    have hxt : x ∉ t := by
      have hnd : q.roots.Nodup := hqroots ▸ hnodup
      rw [ht, Multiset.nodup_cons] at hnd
      exact hnd.1
    rw [hprod, ht, Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
      derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, add_zero, Polynomial.eval_multiset_prod,
      Multiset.map_map]
    refine Multiset.prod_ne_zero fun h0 => ?_
    rw [Multiset.mem_map] at h0
    obtain ⟨a, hat, ha⟩ := h0
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at ha
    exact hxt (ha ▸ hat)
  intro hcontra
  apply hkey
  rw [hq, derivative_mul, derivative_C, mul_zero, add_zero, eval_mul, eval_C, hcontra,
    zero_mul]

theorem exists_smul_eq_zero_and_two_smul_ne_zero_of_preΨ_isRoot {n : ℕ} (hn : (n : k) ≠ 0)
    {x : k} (hx : (V.preΨ (n : ℤ)).IsRoot x) :
    ∃ y, ∃ h : V.toAffine.Nonsingular x y,
      (n : ℤ) • (Point.some x y h : V.toAffine.Point) = 0 ∧
        (2 : ℤ) • (Point.some x y h : V.toAffine.Point) ≠ 0 := by
  obtain ⟨y, h, hP, hy⟩ := exists_smul_eq_zero_of_preΨ_isRoot V hn hx
  exact ⟨y, h, hP, fun h2 => hy ((two_zsmul_some_eq_zero_iff_eq_negY h).mp h2)⟩

end Count

section Transfer

variable {L : Type*} [Field L] [DecidableEq L]

theorem smul_eq_zero_of_preΨ_isRoot (V : WeierstrassCurve L) [V.IsElliptic] {n : ℕ}
    (hn : (n : L) ≠ 0) {x y : L} (h : V.toAffine.Nonsingular x y)
    (hx : (V.preΨ (n : ℤ)).IsRoot x) :
    (n : ℤ) • (Point.some x y h : V.toAffine.Point) = 0 := by
  classical
  haveI : DecidableEq (AlgebraicClosure L) := Classical.decEq _
  have hinj : Function.Injective (algebraMap L (AlgebraicClosure L)) :=
    (algebraMap L (AlgebraicClosure L)).injective
  haveI hVK : (V⁄(AlgebraicClosure L)).IsElliptic := by
    refine ⟨?_⟩
    rw [show V⁄(AlgebraicClosure L) = V.map (algebraMap L (AlgebraicClosure L)) from rfl,
      WeierstrassCurve.map_Δ]
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hinj).mpr V.isUnit_Δ.ne_zero)
  have hnK : (n : AlgebraicClosure L) ≠ 0 := by
    intro h0
    apply hn
    apply hinj
    rw [map_natCast, _root_.map_zero, h0]
  have hxK : ((V⁄(AlgebraicClosure L)).preΨ (n : ℤ)).IsRoot
      (algebraMap L (AlgebraicClosure L) x) := by
    rw [show V⁄(AlgebraicClosure L) = V.map (algebraMap L (AlgebraicClosure L)) from rfl,
      WeierstrassCurve.map_preΨ]
    show Polynomial.eval (algebraMap L (AlgebraicClosure L) x)
      ((V.preΨ (n : ℤ)).map (algebraMap L (AlgebraicClosure L))) = 0
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hx.eq_zero, _root_.map_zero]
  obtain ⟨yK, hK, htors, -⟩ :=
    exists_smul_eq_zero_of_preΨ_isRoot (V⁄(AlgebraicClosure L)) hnK hxK
  revert h
  rw [← baseChange_self' V]
  intro h
  have hmap : Point.map (W' := V) (Algebra.ofId L (AlgebraicClosure L))
      ((n : ℤ) • Point.some x y h) = 0 := by
    rw [map_zsmul, WeierstrassCurve.Affine.Point.map_some]
    simp only [Algebra.ofId_apply]
    have heq₁ : (V⁄(AlgebraicClosure L)).toAffine.Equation
        (algebraMap L (AlgebraicClosure L) x) (algebraMap L (AlgebraicClosure L) y) :=
      (((V⁄(AlgebraicClosure L)).toAffine.nonsingular_iff _ _).mp
        ((V.toAffine.baseChange_nonsingular
          (Algebra.ofId L (AlgebraicClosure L)).injective ..).mpr h)).1
    have heq₂ : (V⁄(AlgebraicClosure L)).toAffine.Equation
        (algebraMap L (AlgebraicClosure L) x) yK :=
      (((V⁄(AlgebraicClosure L)).toAffine.nonsingular_iff _ _).mp hK).1
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq heq₁ heq₂ rfl with hy | hy
    · rw [some_congr rfl hy _ hK]
      exact htors
    · have hneg := ((V⁄(AlgebraicClosure L)).toAffine.nonsingular_neg
        (algebraMap L (AlgebraicClosure L) x) yK).mpr hK
      have hpt : (Point.some (algebraMap L (AlgebraicClosure L) x)
          ((V⁄(AlgebraicClosure L)).toAffine.negY
            (algebraMap L (AlgebraicClosure L) x) yK) hneg :
          (V⁄(AlgebraicClosure L)).toAffine.Point) =
          - Point.some (algebraMap L (AlgebraicClosure L) x) yK hK :=
        (WeierstrassCurve.Affine.Point.neg_some hK).symm
      have hzero : ((n : ℤ) • (Point.some (algebraMap L (AlgebraicClosure L) x)
          ((V⁄(AlgebraicClosure L)).toAffine.negY
            (algebraMap L (AlgebraicClosure L) x) yK) hneg) :
          (V⁄(AlgebraicClosure L)).toAffine.Point) = 0 := by
        rw [hpt, zsmul_neg, htors, _root_.neg_zero]
      rw [some_congr rfl hy _ hneg]
      exact hzero
  set S := (n : ℤ) • (Point.some x y h : (V⁄L).toAffine.Point) with hS
  clear_value S
  clear hS
  cases S with
  | zero => rfl
  | @some a b hab =>
    rw [WeierstrassCurve.Affine.Point.map_some] at hmap
    exact absurd hmap (Point.some_ne_zero _)

end Transfer

section Hensel

variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
  [HenselianLocalRing A] [DecidableEq (ResidueField A)]

omit [DecidableEq L] [DecidableEq (ResidueField A)] in

theorem exists_root_lift {f : Polynomial A} (hu : IsUnit f.leadingCoeff)
    {xbar : ResidueField A} (hroot : (f.map (residue A)).IsRoot xbar)
    (hder : (derivative (f.map (residue A))).eval xbar ≠ 0) :
    ∃ xA : A, f.IsRoot xA ∧ residue A xA = xbar := by
  classical
  set u := hu.unit with hu'
  set g := C ((u⁻¹ : Aˣ) : A) * f with hg
  have hgmonic : g.Monic := by
    rw [Polynomial.Monic, hg, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact Units.inv_mul_of_eq hu.unit_spec
  have hfmap : g.map (residue A) =
      C (residue A ((u⁻¹ : Aˣ) : A)) * (f.map (residue A)) := by
    rw [hg, Polynomial.map_mul, Polynomial.map_C]
  obtain ⟨a₀, ha₀⟩ := residue_surjective (R := A) xbar
  have heval : g.eval a₀ ∈ maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal A)]
    show residue A (g.eval a₀) = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hfmap, ha₀, eval_mul, eval_C,
      hroot.eq_zero, mul_zero]
  have hderu : IsUnit ((derivative g).eval a₀) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have h0 : residue A ((derivative g).eval a₀) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal A)).mpr hmem
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← Polynomial.derivative_map,
      hfmap, derivative_C_mul, ha₀, eval_mul, eval_C, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact (RingHom.isUnit_map (residue A) (Units.isUnit u⁻¹)).ne_zero h0
    · exact hder h0
  obtain ⟨xA, hxroot, hxmem⟩ := HenselianLocalRing.is_henselian g hgmonic a₀ heval hderu
  refine ⟨xA, ?_, ?_⟩
  · have h : Polynomial.eval xA g = 0 := hxroot
    rw [hg, eval_mul, eval_C, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h (Units.ne_zero u⁻¹)
    · exact h
  · rw [residue_eq_of_sub_mem hxmem, ha₀]

omit [DecidableEq L] [DecidableEq (ResidueField A)] in

theorem exists_ordinate_lift {W : WeierstrassCurve A} {xA : A} {ybar : ResidueField A}
    (heq : (W.map (residue A)).toAffine.Equation (residue A xA) ybar)
    (hne2 : ybar ≠ (W.map (residue A)).toAffine.negY (residue A xA) ybar) :
    ∃ yA : A, W.toAffine.Equation xA yA ∧ residue A yA = ybar := by
  classical
  set g : Polynomial A :=
    X ^ 2 + (C (W.a₁ * xA + W.a₃) * X +
      C (-(xA ^ 3 + W.a₂ * xA ^ 2 + W.a₄ * xA + W.a₆))) with hg
  have hgmonic : g.Monic := Polynomial.monic_X_pow_add Polynomial.degree_linear_lt
  have hgeval : ∀ yA : A, g.eval yA =
      yA ^ 2 + W.a₁ * xA * yA + W.a₃ * yA -
        (xA ^ 3 + W.a₂ * xA ^ 2 + W.a₄ * xA + W.a₆) := by
    intro yA
    simp only [hg, eval_add, eval_pow, eval_mul, eval_C, eval_X]
    ring
  obtain ⟨b₀, hb₀⟩ := residue_surjective (R := A) ybar
  have heqres := ((W.map (residue A)).toAffine.equation_iff' (residue A xA) ybar).mp heq
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heqres
  have heval : g.eval b₀ ∈ maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal A)]
    show residue A (g.eval b₀) = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hb₀]
    simp only [hg, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, eval_add, eval_pow, eval_mul, eval_C, eval_X]
    simp only [map_add, map_mul, map_pow, map_neg]
    linear_combination heqres
  have hderu : IsUnit ((derivative g).eval b₀) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have h0 : residue A ((derivative g).eval b₀) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal A)).mpr hmem
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← Polynomial.derivative_map,
      hb₀] at h0
    simp only [hg, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X] at h0
    simp only [derivative_add, derivative_X_pow, derivative_mul, derivative_C,
      derivative_X, zero_mul, mul_one, zero_add, add_zero, eval_add, eval_mul, eval_pow,
      eval_C, eval_X] at h0
    simp only [map_add, map_mul] at h0
    apply hne2
    have hnegY : (W.map (residue A)).toAffine.negY (residue A xA) ybar =
        -ybar - residue A W.a₁ * residue A xA - residue A W.a₃ := by
      simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁,
        WeierstrassCurve.map_a₃]
    rw [hnegY]
    push_cast at h0
    linear_combination h0
  obtain ⟨yA, hyroot, hymem⟩ := HenselianLocalRing.is_henselian g hgmonic b₀ heval hderu
  refine ⟨yA, ?_, ?_⟩
  · rw [W.toAffine.equation_iff' xA yA]
    have h : Polynomial.eval yA g = 0 := hyroot
    rw [hgeval] at h
    linear_combination h
  · rw [residue_eq_of_sub_mem hymem, hb₀]

omit [DecidableEq L] [DecidableEq (ResidueField A)] in

theorem exists_preΨ_root_lift {W : WeierstrassCurve A} {N : ℕ}
    (hN : (N : ResidueField A) ≠ 0) {xbar : ResidueField A}
    (hroot : ((W.map (residue A)).preΨ (N : ℤ)).IsRoot xbar)
    (hder : (derivative ((W.map (residue A)).preΨ (N : ℤ))).eval xbar ≠ 0) :
    ∃ xA : A, (W.preΨ (N : ℤ)).IsRoot xA ∧ residue A xA = xbar := by
  have hNA : ((N : ℤ) : A) ≠ 0 := fun h0 => hN (by
    have h1 : residue A ((N : ℤ) : A) = 0 := by rw [h0, _root_.map_zero]
    rwa [map_intCast, Int.cast_natCast] at h1)
  have hlc : IsUnit (W.preΨ (N : ℤ)).leadingCoeff := by
    rw [W.leadingCoeff_preΨ (by exact_mod_cast hNA), ← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have hNmem : ((N : ℤ) : A) ∈ maximalIdeal A := by
      by_cases heven : Even (N : ℤ)
      · rw [if_pos heven] at hmem
        have hfac : ((N : ℤ) : A) = (2 : A) * (((N : ℤ) / 2 : ℤ) : A) := by
          have h2 : (2 : ℤ) * ((N : ℤ) / 2) = (N : ℤ) :=
            Int.mul_ediv_cancel' heven.two_dvd
          calc ((N : ℤ) : A) = ((2 * ((N : ℤ) / 2) : ℤ) : A) := by rw [h2]
            _ = (2 : A) * (((N : ℤ) / 2 : ℤ) : A) := by push_cast; ring
        rw [hfac]
        exact Ideal.mul_mem_left _ _ hmem
      · rwa [if_neg heven] at hmem
    apply hN
    have h0 : residue A ((N : ℤ) : A) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal A)).mpr hNmem
    rwa [map_intCast, Int.cast_natCast] at h0
  rw [WeierstrassCurve.map_preΨ] at hroot hder
  exact exists_root_lift hlc hroot hder

end Hensel

section CountTwo

variable {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k]
  (V : WeierstrassCurve k) [V.IsElliptic]

omit [IsAlgClosed k] [V.IsElliptic] in

theorem negY_eq_of_two_zsmul_eq_zero {x y : k} (h : V.toAffine.Nonsingular x y)
    (hP : (2 : ℤ) • (Point.some x y h : V.toAffine.Point) = 0) :
    y = V.toAffine.negY x y := by
  have hPP : (Point.some x y h : V.toAffine.Point) + Point.some x y h = 0 := by
    rw [← two_zsmul]; exact hP
  have hneg := eq_neg_of_add_eq_zero_left hPP
  rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
    at hneg
  exact hneg.2

omit [IsAlgClosed k] [V.IsElliptic] in

theorem two_zsmul_eq_zero_of_negY_eq {x y : k} (h : V.toAffine.Nonsingular x y)
    (hy : y = V.toAffine.negY x y) :
    (2 : ℤ) • (Point.some x y h : V.toAffine.Point) = 0 := by
  have hQneg : (Point.some x y h : V.toAffine.Point) = - Point.some x y h := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact some_congr rfl hy h _
  rw [two_zsmul]
  nth_rewrite 2 [hQneg]
  exact add_neg_cancel _

omit [IsAlgClosed k] in

theorem Ψ₂Sq_isRoot_of_two_zsmul_eq_zero {x y : k} (h : V.toAffine.Nonsingular x y)
    (hP : (2 : ℤ) • (Point.some x y h : V.toAffine.Point) = 0) :
    V.Ψ₂Sq.IsRoot x := by
  have hsq := WeierstrassCurve.Affine.Point.eval_psiSq_eq_zero_of_smul_eq_zero h hP
  unfold WeierstrassCurve.ΨSq at hsq
  rw [if_pos even_two, WeierstrassCurve.preΨ_two, one_pow, one_mul] at hsq
  exact hsq

omit [IsAlgClosed k] [V.IsElliptic] in

theorem eq_of_X_eq_of_two_zsmul_eq_zero {x y₁ y₂ : k} (h₁ : V.toAffine.Nonsingular x y₁)
    (h₂ : V.toAffine.Nonsingular x y₂)
    (ht₁ : (2 : ℤ) • (Point.some x y₁ h₁ : V.toAffine.Point) = 0) :
    Point.some x y₁ h₁ = Point.some x y₂ h₂ := by
  have hy₁ := negY_eq_of_two_zsmul_eq_zero V h₁ ht₁
  have heq₁ : V.toAffine.Equation x y₁ := ((V.toAffine.nonsingular_iff x y₁).mp h₁).1
  have heq₂ : V.toAffine.Equation x y₂ := ((V.toAffine.nonsingular_iff x y₂).mp h₂).1
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq heq₂ heq₁ rfl with hy | hy
  · exact some_congr rfl hy.symm h₁ h₂
  · exact some_congr rfl (by rw [hy]; exact hy₁) h₁ h₂

private lemma card_torsionBy_two (h2 : (2 : k) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ V.toAffine.Point (2 : ℤ)) = 4 := by
  have hn2 : ((2 : ℕ) : k) ≠ 0 := by exact_mod_cast h2
  have h := card_torsionBy_eq_sq V hn2
  have hcast : (((2 : ℕ) : ℤ)) = (2 : ℤ) := by norm_num
  rw [hcast] at h
  exact h.trans (by norm_num)

private lemma card_torsNZ₂ (h2 : (2 : k) ≠ 0) :
    Nat.card {P : Submodule.torsionBy ℤ V.toAffine.Point (2 : ℤ) //
      (P : V.toAffine.Point) ≠ 0} = 3 := by
  classical
  have hfin : Finite (Submodule.torsionBy ℤ V.toAffine.Point (2 : ℤ)) := by
    have hpos : 0 < Nat.card (Submodule.torsionBy ℤ V.toAffine.Point (2 : ℤ)) := by
      rw [card_torsionBy_two V h2]; norm_num
    exact (Nat.card_pos_iff.mp hpos).2
  haveI := Fintype.ofFinite (Submodule.torsionBy ℤ V.toAffine.Point (2 : ℤ))
  have h0 : Fintype.card
      {P : Submodule.torsionBy ℤ V.toAffine.Point (2 : ℤ) //
        (P : V.toAffine.Point) = 0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, rfl⟩, ?_⟩
    rintro ⟨P, hP⟩
    exact Subtype.ext (Subtype.ext hP)
  have hcompl := Fintype.card_subtype_compl
    (p := fun P : Submodule.torsionBy ℤ V.toAffine.Point (2 : ℤ) =>
      (P : V.toAffine.Point) = 0)
  rw [h0] at hcompl
  have hcard : Fintype.card (Submodule.torsionBy ℤ V.toAffine.Point (2 : ℤ)) = 4 := by
    rw [← Nat.card_eq_fintype_card, card_torsionBy_two V h2]
  show Nat.card {P : Submodule.torsionBy ℤ V.toAffine.Point (2 : ℤ) //
    ¬ (P : V.toAffine.Point) = 0} = 3
  rw [Nat.card_eq_fintype_card, hcompl, hcard]

private def tors2X : Set k :=
  {x : k | ∃ y, ∃ h : V.toAffine.Nonsingular x y,
    (2 : ℤ) • (Point.some x y h : V.toAffine.Point) = 0}

private noncomputable def sec₂ (z : tors2X V) : V.toAffine.Point :=
  Point.some z.1 z.2.choose z.2.choose_spec.choose

omit [IsAlgClosed k] [V.IsElliptic] in
private lemma sec₂_spec (z : tors2X V) : (2 : ℤ) • sec₂ V z = 0 :=
  z.2.choose_spec.choose_spec

omit [IsAlgClosed k] in
private lemma isRoot_of_mem_tors2X {x : k} (hx : x ∈ tors2X V) : V.Ψ₂Sq.IsRoot x := by
  obtain ⟨y, h, hP⟩ := hx
  exact Ψ₂Sq_isRoot_of_two_zsmul_eq_zero V h hP

private lemma Ψ₂Sq_roots_nodup_and_mem (h2 : (2 : k) ≠ 0) :
    V.Ψ₂Sq.roots.Nodup ∧ ∀ x : k, V.Ψ₂Sq.IsRoot x → x ∈ tors2X V := by
  classical
  have h4 : (4 : k) ≠ 0 := by
    have h44 : (4 : k) = 2 * 2 := by norm_num
    rw [h44]; exact mul_ne_zero h2 h2
  have hp0 : V.Ψ₂Sq ≠ 0 := V.Ψ₂Sq_ne_zero h4
  have hD : V.Ψ₂Sq.natDegree = 3 := V.natDegree_Ψ₂Sq h4
  have hfinX : (tors2X V).Finite := by
    refine Set.Finite.subset V.Ψ₂Sq.roots.finite_toSet fun x hx => ?_
    exact (Polynomial.mem_roots hp0).mpr (isRoot_of_mem_tors2X V hx)
  haveI : Finite (tors2X V) := hfinX.to_subtype
  have hG : Function.Surjective
      (fun z : tors2X V =>
        (⟨⟨sec₂ V z, by
            rw [Submodule.mem_torsionBy_iff]
            exact sec₂_spec V z⟩, by
            show sec₂ V z ≠ 0
            exact Point.some_ne_zero _⟩ :
          {P : Submodule.torsionBy ℤ V.toAffine.Point (2 : ℤ) //
            (P : V.toAffine.Point) ≠ 0})) := by
    rintro ⟨⟨P, hPtors⟩, hPne⟩
    rw [Submodule.mem_torsionBy_iff] at hPtors
    induction P with
    | zero => exact absurd rfl hPne
    | @some x y h =>
      have hxX : x ∈ tors2X V := ⟨y, h, hPtors⟩
      refine ⟨⟨x, hxX⟩, ?_⟩
      refine Subtype.ext (Subtype.ext ?_)
      show sec₂ V ⟨x, hxX⟩ = Point.some x y h
      exact eq_of_X_eq_of_two_zsmul_eq_zero V _ h (sec₂_spec V ⟨x, hxX⟩)
  have hcardT := card_torsNZ₂ V h2
  have hle : 3 ≤ Nat.card (tors2X V) := by
    rw [← hcardT]
    exact Nat.card_le_card_of_surjective _ hG
  have hsub : hfinX.toFinset ⊆ V.Ψ₂Sq.roots.toFinset := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    exact isRoot_of_mem_tors2X V hx
  have hcardX : hfinX.toFinset.card = Nat.card (tors2X V) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card (tors2X V) hfinX]
  have hge : 3 ≤ hfinX.toFinset.card := by rw [hcardX]; exact hle
  have hchain1 : V.Ψ₂Sq.roots.toFinset.card ≤ V.Ψ₂Sq.roots.card :=
    Multiset.toFinset_card_le _
  have hchain2 : V.Ψ₂Sq.roots.card ≤ 3 := hD ▸ V.Ψ₂Sq.card_roots'
  have hchain3 : hfinX.toFinset.card ≤ V.Ψ₂Sq.roots.toFinset.card :=
    Finset.card_le_card hsub
  have heqFin : hfinX.toFinset = V.Ψ₂Sq.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hnodup : V.Ψ₂Sq.roots.Nodup := by
    have hfc : V.Ψ₂Sq.roots.toFinset.card = V.Ψ₂Sq.roots.dedup.card :=
      congrArg Multiset.card (Multiset.toFinset_val _)
    have heq : V.Ψ₂Sq.roots = V.Ψ₂Sq.roots.dedup :=
      (Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) (by omega)).symm
    rw [heq]
    exact Multiset.nodup_dedup _
  refine ⟨hnodup, fun x hx => ?_⟩
  have hxmem : x ∈ V.Ψ₂Sq.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    exact hx
  rw [← heqFin, Set.Finite.mem_toFinset] at hxmem
  exact hxmem

omit [DecidableEq k] in

theorem eval_derivative_ne_zero_of_nodup {p : Polynomial k} (hp0 : p ≠ 0)
    (hnodup : p.roots.Nodup) {x : k} (hx : p.IsRoot x) :
    (derivative p).eval x ≠ 0 := by
  classical
  have hlc0 : p.leadingCoeff⁻¹ ≠ 0 :=
    inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  set q := p * C p.leadingCoeff⁻¹ with hq
  have hqmonic : q.Monic := Polynomial.monic_mul_leadingCoeff_inv hp0
  have hqroots : q.roots = p.roots := by
    rw [hq, mul_comm, Polynomial.roots_C_mul _ hlc0]
  have hprod : q = (q.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits q).eq_prod_roots_of_monic hqmonic
  have hxq : x ∈ q.roots := by
    rw [hqroots, Polynomial.mem_roots hp0]
    exact hx
  have hkey : (derivative q).eval x ≠ 0 := by
    obtain ⟨t, ht⟩ : ∃ t, q.roots = x ::ₘ t :=
      ⟨q.roots.erase x, (Multiset.cons_erase hxq).symm⟩
    have hxt : x ∉ t := by
      have hnd : q.roots.Nodup := hqroots ▸ hnodup
      rw [ht, Multiset.nodup_cons] at hnd
      exact hnd.1
    rw [hprod, ht, Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
      derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, add_zero, Polynomial.eval_multiset_prod,
      Multiset.map_map]
    refine Multiset.prod_ne_zero fun h0 => ?_
    rw [Multiset.mem_map] at h0
    obtain ⟨a, hat, ha⟩ := h0
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at ha
    exact hxt (ha ▸ hat)
  intro hcontra
  apply hkey
  rw [hq, derivative_mul, derivative_C, mul_zero, add_zero, eval_mul, eval_C, hcontra,
    zero_mul]

end CountTwo

section R2Main

variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
  [HenselianLocalRing A] [DecidableEq (ResidueField A)] [IsAlgClosed (ResidueField A)]

theorem exists_two_nsmul_eq_zero_and_reduceHom_eq {W : WeierstrassCurve A}
    (hΔ : (W.map (residue A)).Δ ≠ 0) (h2 : (2 : ResidueField A) ≠ 0)
    (Q : (W.map (residue A)).toAffine.Point) (hQ : 2 • Q = 0) :
    ∃ P : (W.map A.subtype).toAffine.Point, 2 • P = 0 ∧ reduceHom hΔ P = Q := by
  classical
  haveI hWbar : (W.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  induction Q with
  | zero => exact ⟨0, by rw [smul_zero], _root_.map_zero _⟩
  | @some xbar ybar hbar =>
    have hQz : (2 : ℤ) • (Point.some xbar ybar hbar :
        (W.map (residue A)).toAffine.Point) = 0 := by
      rw [two_zsmul, ← two_nsmul]
      exact hQ
    have hybar := negY_eq_of_two_zsmul_eq_zero (W.map (residue A)) hbar hQz
    have hroot := Ψ₂Sq_isRoot_of_two_zsmul_eq_zero (W.map (residue A)) hbar hQz
    have h4k : (4 : ResidueField A) ≠ 0 := by
      have h44 : (4 : ResidueField A) = 2 * 2 := by norm_num
      rw [h44]; exact mul_ne_zero h2 h2
    have hder : (derivative ((W.map (residue A)).Ψ₂Sq)).eval xbar ≠ 0 :=
      eval_derivative_ne_zero_of_nodup ((W.map (residue A)).Ψ₂Sq_ne_zero h4k)
        (Ψ₂Sq_roots_nodup_and_mem (W.map (residue A)) h2).1 hroot

    have hu2 : IsUnit (2 : A) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      apply h2
      have h0 : residue A (2 : A) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal A)).mpr hmem
      rwa [map_ofNat] at h0
    have hu4 : IsUnit (4 : A) := by
      have h44 : (4 : A) = 2 * 2 := by norm_num
      rw [h44]; exact hu2.mul hu2
    have hlcu : IsUnit (W.Ψ₂Sq : Polynomial A).leadingCoeff := by
      rw [W.leadingCoeff_Ψ₂Sq hu4.ne_zero]
      exact hu4
    have hrootA : ((W.Ψ₂Sq : Polynomial A).map (residue A)).IsRoot xbar := by
      rw [← WeierstrassCurve.map_Ψ₂Sq]
      exact hroot
    have hderA : (derivative ((W.Ψ₂Sq : Polynomial A).map (residue A))).eval xbar ≠ 0 := by
      rw [← WeierstrassCurve.map_Ψ₂Sq]
      exact hder
    obtain ⟨xA, hxroot, hxres⟩ := exists_root_lift hlcu hrootA hderA

    obtain ⟨yA, hy2⟩ : ∃ yA : A, 2 * yA + (W.a₁ * xA + W.a₃) = 0 := by
      refine ⟨((hu2.unit⁻¹ : Aˣ) : A) * -(W.a₁ * xA + W.a₃), ?_⟩
      have h21 : ((hu2.unit⁻¹ : Aˣ) : A) * (2 : A) = 1 :=
        Units.inv_mul_of_eq hu2.unit_spec
      linear_combination (-(W.a₁ * xA + W.a₃)) * h21
    have hEqA : W.toAffine.Equation xA yA := equation_of_Ψ₂Sq_isRoot hu4 hy2 hxroot

    have hy2k : 2 * ybar + ((W.map (residue A)).a₁ * xbar + (W.map (residue A)).a₃) = 0 := by
      have h := hybar
      rw [WeierstrassCurve.Affine.negY] at h
      linear_combination h
    have hres2 : 2 * residue A yA +
        ((W.map (residue A)).a₁ * xbar + (W.map (residue A)).a₃) = 0 := by
      have h := congrArg (residue A) hy2
      simp only [map_add, map_mul, map_ofNat, _root_.map_zero] at h
      rw [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, ← hxres]
      exact h
    have hyres : residue A yA = ybar := by
      apply mul_left_cancel₀ h2
      linear_combination hres2 - hy2k

    have hΔL : (W.map A.subtype).Δ ≠ 0 := by
      intro h0
      apply hΔ
      rw [WeierstrassCurve.map_Δ] at h0
      have hD0 : W.Δ = 0 := by
        apply Subtype.ext
        show (W.Δ : L) = ((0 : A) : L)
        rw [ZeroMemClass.coe_zero]
        exact h0
      rw [WeierstrassCurve.map_Δ, hD0, _root_.map_zero]
    haveI hWL : (W.map A.subtype).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔL⟩
    have heqL : (W.map A.subtype).toAffine.Equation (xA : L) (yA : L) :=
      (W.toAffine.map_equation (f := A.subtype) (fun _ _ hab => Subtype.ext hab)
        xA yA).mpr hEqA
    have hnsL : (W.map A.subtype).toAffine.Nonsingular (xA : L) (yA : L) :=
      WeierstrassCurve.Affine.equation_iff_nonsingular.mp heqL
    have hynegA : yA = W.toAffine.negY xA yA := by
      rw [WeierstrassCurve.Affine.negY]
      linear_combination hy2
    have hyneg : (yA : L) = (W.map A.subtype).toAffine.negY (xA : L) (yA : L) := by
      have h := congrArg (A.subtype) hynegA
      rw [WeierstrassCurve.Affine.negY, map_sub, map_sub, map_neg, map_mul] at h
      rw [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
      exact h
    have htorsL := two_zsmul_eq_zero_of_negY_eq (W.map A.subtype) hnsL hyneg
    refine ⟨Point.some (xA : L) (yA : L) hnsL, ?_, ?_⟩
    · rw [two_nsmul, ← two_zsmul]
      exact htorsL
    · simp only [WeierstrassCurve.reduceHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [reducePoint_some_of_mem hΔ hnsL xA.2]
      exact some_congr (by rw [Subtype.eta]; exact hxres)
        (by rw [Subtype.eta]; exact hyres) _ hbar

end R2Main

section Main

variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
  [HenselianLocalRing A] [DecidableEq (ResidueField A)] [IsAlgClosed (ResidueField A)]

theorem exists_nsmul_eq_zero_and_reduceHom_eq {W : WeierstrassCurve A}
    (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ}
    (hN : (N : ResidueField A) ≠ 0)
    (Q : (W.map (residue A)).toAffine.Point) (hQ : N • Q = 0) :
    ∃ P : (W.map A.subtype).toAffine.Point, N • P = 0 ∧ reduceHom hΔ P = Q := by
  classical
  haveI hWbar : (W.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  induction Q with
  | zero => exact ⟨0, by rw [smul_zero], _root_.map_zero _⟩
  | @some xbar ybar hbar =>
    by_cases hne2 : ybar = (W.map (residue A)).toAffine.negY xbar ybar
    ·
      have h2Q : 2 • (Point.some xbar ybar hbar :
          (W.map (residue A)).toAffine.Point) = 0 := by
        rw [two_nsmul]
        nth_rewrite 2 [show (Point.some xbar ybar hbar :
            (W.map (residue A)).toAffine.Point) =
            -(Point.some xbar ybar hbar : (W.map (residue A)).toAffine.Point) from ?_]
        · exact add_neg_cancel _
        · rw [WeierstrassCurve.Affine.Point.neg_some]
          exact some_congr rfl hne2 _ _
      have h2N : 2 ∣ N := by
        have hd2 : addOrderOf (Point.some xbar ybar hbar :
            (W.map (residue A)).toAffine.Point) ∣ 2 :=
          addOrderOf_dvd_of_nsmul_eq_zero h2Q
        have hdN : addOrderOf (Point.some xbar ybar hbar :
            (W.map (residue A)).toAffine.Point) ∣ N :=
          addOrderOf_dvd_of_nsmul_eq_zero hQ
        rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
        · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) (Point.some_ne_zero hbar)
        · exact h2 ▸ hdN
      have h2k : (2 : ResidueField A) ≠ 0 := by
        intro h0; apply hN
        obtain ⟨m, rfl⟩ := h2N
        push_cast
        rw [h0, zero_mul]
      obtain ⟨P, hP2, hPQ⟩ :=
        exists_two_nsmul_eq_zero_and_reduceHom_eq hΔ h2k (Point.some xbar ybar hbar) h2Q
      refine ⟨P, ?_, hPQ⟩
      obtain ⟨m, rfl⟩ := h2N
      rw [mul_nsmul, hP2, smul_zero]
    ·
      have hQz : (N : ℤ) • (Point.some xbar ybar hbar :
          (W.map (residue A)).toAffine.Point) = 0 := by
        rw [natCast_zsmul]; exact hQ
      have hroot :=
        preΨ_isRoot_of_smul_eq_zero_of_ne_negY (W.map (residue A)) hbar hQz hne2
      have hder := eval_derivative_preΨ_ne_zero_of_isRoot (W.map (residue A)) hN hroot
      obtain ⟨xA, hxroot, hxres⟩ := exists_preΨ_root_lift hN hroot hder
      have heqbar : (W.map (residue A)).toAffine.Equation (residue A xA) ybar := by
        rw [hxres]
        exact (((W.map (residue A)).toAffine.nonsingular_iff _ _).mp hbar).1
      have hne2' : ybar ≠ (W.map (residue A)).toAffine.negY (residue A xA) ybar := by
        rw [hxres]; exact hne2
      obtain ⟨yA, hyeq, hyres⟩ := exists_ordinate_lift heqbar hne2'
      have hΔL : (W.map A.subtype).Δ ≠ 0 := by
        intro h0
        apply hΔ
        rw [WeierstrassCurve.map_Δ] at h0
        have hD0 : W.Δ = 0 := by
          apply Subtype.ext
          show (W.Δ : L) = ((0 : A) : L)
          rw [ZeroMemClass.coe_zero]; exact h0
        rw [WeierstrassCurve.map_Δ, hD0, _root_.map_zero]
      haveI hWL : (W.map A.subtype).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔL⟩
      have heqL : (W.map A.subtype).toAffine.Equation (xA : L) (yA : L) :=
        (W.toAffine.map_equation (f := A.subtype) (fun _ _ hab => Subtype.ext hab)
          xA yA).mpr hyeq
      have hnsL : (W.map A.subtype).toAffine.Nonsingular (xA : L) (yA : L) :=
        WeierstrassCurve.Affine.equation_iff_nonsingular.mp heqL
      have hrootL : ((W.map A.subtype).preΨ (N : ℤ)).IsRoot (xA : L) := by
        rw [WeierstrassCurve.map_preΨ]
        show Polynomial.eval (A.subtype xA) ((W.preΨ (N : ℤ)).map A.subtype) = 0
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hxroot.eq_zero,
          _root_.map_zero]
      have hNL : (N : L) ≠ 0 := by
        intro h0
        apply hN
        rw [← map_natCast A.subtype N] at h0
        have hN0 : (N : A) = 0 := by
          apply Subtype.ext
          show ((N : A) : L) = ((0 : A) : L)
          rw [ZeroMemClass.coe_zero]; exact h0
        rw [← map_natCast (residue A), hN0, _root_.map_zero]
      have htorsL := smul_eq_zero_of_preΨ_isRoot (W.map A.subtype) hNL hnsL hrootL
      refine ⟨Point.some (xA : L) (yA : L) hnsL, ?_, ?_⟩
      · rw [← natCast_zsmul]; exact htorsL
      · simp only [WeierstrassCurve.reduceHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [reducePoint_some_of_mem hΔ hnsL xA.2]
        exact some_congr (by rw [Subtype.eta]; exact hxres)
          (by rw [Subtype.eta]; exact hyres) _ hbar

end Main

end TorsEven

theorem solution
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
    [HenselianLocalRing A] [DecidableEq (IsLocalRing.ResidueField A)]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (IsLocalRing.residue A)).Δ ≠ 0) {N : ℕ}
    (hN : (N : IsLocalRing.ResidueField A) ≠ 0) :
    Function.Bijective
      (fun P : {P : (W.map A.subtype).toAffine.Point // N • P = 0} =>
        (⟨WeierstrassCurve.reduceHom hΔ P.1, by rw [← map_nsmul, P.2, _root_.map_zero]⟩ :
          {Q : (W.map (IsLocalRing.residue A)).toAffine.Point // N • Q = 0})) := by
  constructor
  · rintro ⟨P₁, h₁⟩ ⟨P₂, h₂⟩ h
    exact Subtype.ext (WeierstrassCurve.eq_of_reduceHom_eq_of_nsmul_eq_zero hΔ hN h₁ h₂
      (congrArg Subtype.val h))
  · rintro ⟨Q, hQ⟩
    obtain ⟨P, hP, hPQ⟩ := TorsEven.exists_nsmul_eq_zero_and_reduceHom_eq hΔ hN Q hQ
    exact ⟨⟨P, hP⟩, Subtype.ext hPQ⟩

end S_WeierstrassCurve_bijective_reduceHom_restrict_torsion
end P2MW
export P2MW.S_WeierstrassCurve_bijective_reduceHom_restrict_torsion (solution)
