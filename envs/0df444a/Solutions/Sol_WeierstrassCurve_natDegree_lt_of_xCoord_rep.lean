-- Prove2me | solution 1 for WeierstrassCurve.natDegree_lt_of_xCoord_rep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6e0db414-f6df-58b8-841e-28210563b11f

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natDegree_lt_of_xCoord_rep
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.CoordinateRing.mk_Ψ_sq natDegree_Φ map Affine.CoordinateRing natDegree_ΨSq_le mk Affine.Point.some Affine.degree_polynomial Affine.Point.some.inj preΨ' ΨSq toAffine Affine.Point Affine.CoordinateRing.mk Affine.CoordinateRing.mk_ψ Affine.monic_polynomial natDegree_preΨ'_pos Affine.Point.some_ne_zero Affine.Point.zsmul_some_eq_some_div Affine.Point.smul_some_eq_zero_iff Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi isCoprime_Phi_PsiSq"
namespace XRepDegree
p2m_open "WeierstrassCurve~evalEval_ψ_sq"

variable {k : Type*} [Field k]

noncomputable def hom (m : ℕ) (u v p : k[X]) : k[X] :=
  ∑ i ∈ Finset.range (m + 1), C (p.coeff i) * u ^ i * v ^ (m - i)

theorem eval_hom {m : ℕ} {u v p : k[X]} (hp : p.natDegree ≤ m) {x x' : k}
    (hx : x' * v.eval x = u.eval x) :
    (hom m u v p).eval x = (v.eval x) ^ m * p.eval x' := by
  simp only [hom, eval_finsetSum, eval_mul, eval_pow, eval_C]
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← hx, mul_pow, show (v.eval x) ^ m = (v.eval x) ^ i * (v.eval x) ^ (m - i) by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hi)]]
  ring

theorem eval_hom_of_root {m : ℕ} {u v : k[X]} (p : k[X]) {x : k} (hx : v.eval x = 0) :
    (hom m u v p).eval x = p.coeff m * (u.eval x) ^ m := by
  simp only [hom, eval_finsetSum, eval_mul, eval_pow, eval_C, hx]
  rw [Finset.sum_eq_single m]
  · simp
  · intro i hi him
    rw [Finset.mem_range] at hi
    rw [zero_pow (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) him)), mul_zero]
  · intro h; exact absurd (Finset.self_mem_range_succ m) h

theorem eval_ne_zero_of_isCoprime {p q : k[X]} (h : IsCoprime p q) {x : k} (hq : q.eval x = 0) :
    p.eval x ≠ 0 := by
  obtain ⟨a, b, hab⟩ := h
  intro hp
  have := congrArg (eval x) hab
  simp [eval_add, eval_mul, hp, hq] at this

variable (W : WeierstrassCurve k)

theorem exists_nonsingular [IsAlgClosed k] [W.IsElliptic] (x : k) :
    ∃ y : k, W.toAffine.Nonsingular x y := by
  have hdeg : (W.toAffine.polynomial.map (evalRingHom x)).degree ≠ 0 := by
    rw [WeierstrassCurve.Affine.monic_polynomial.degree_map,
      WeierstrassCurve.Affine.degree_polynomial]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨y, (W.toAffine.equation_iff_nonsingular).mp ?_⟩
  rw [IsRoot.def, map_evalRingHom_eval] at hy
  exact hy

theorem evalEval_ψ_sq {x y : k} (h : W.toAffine.Equation x y) (n : ℤ) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have hmk : Affine.CoordinateRing.mk W.toAffine (W.ψ n ^ 2) =
      Affine.CoordinateRing.mk W.toAffine (C (W.ΨSq n)) := by
    rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨c, hc⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have h0 : W.toAffine.polynomial.evalEval x y = 0 := h
  have := congrArg (evalEval x y) hc
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_pow, evalEval_C] at this
  exact this

theorem ΨSq_ne_zero' [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) : W.ΨSq n ≠ 0 := by
  intro h0
  have hcop := WeierstrassCurve.isCoprime_Phi_PsiSq W n
  rw [h0, isCoprime_zero_right] at hcop
  have h1 := natDegree_eq_zero_of_isUnit hcop
  rw [WeierstrassCurve.natDegree_Φ] at h1
  exact hn (Int.natAbs_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1))

theorem infinite_torsion_abscissa [DecidableEq k] [IsAlgClosed k] [W.IsElliptic] :
    {e : k | ∃ n : ℕ, Odd n ∧ 1 < n ∧ (W.preΨ' n).eval e = 0}.Infinite := by
  classical

  set G : Set ℕ := {ℓ | ℓ.Prime ∧ ℓ ≠ 2 ∧ (ℓ : k) ≠ 0} with hG
  have hGinf : G.Infinite := by
    have hsub : {p : ℕ | p.Prime} \ {2, ringChar k} ⊆ G := by
      rintro ℓ ⟨hℓ, hnot⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
      refine ⟨hℓ, hnot.1, fun h0 => hnot.2 ?_⟩
      exact (CharP.ringChar_of_prime_eq_zero hℓ h0).symm
    exact (Nat.infinite_setOf_prime.diff (Set.toFinite _)).mono hsub

  let f : ℕ → k := fun ℓ => if h : ∃ e, (W.preΨ' ℓ).IsRoot e then h.choose else 0
  have hroot : ∀ ℓ ∈ G, ∃ e, (W.preΨ' ℓ).IsRoot e := by
    rintro ℓ ⟨hℓ, h2, hk⟩
    apply IsAlgClosed.exists_root
    have hpos := W.natDegree_preΨ'_pos (lt_of_le_of_ne hℓ.two_le (Ne.symm h2)) hk
    exact (natDegree_pos_iff_degree_pos.mp hpos).ne'
  have hf : ∀ ℓ ∈ G, (W.preΨ' ℓ).eval (f ℓ) = 0 := by
    intro ℓ hℓ
    have h := hroot ℓ hℓ
    simp only [f, dif_pos h]
    exact h.choose_spec
  refine Set.infinite_of_injOn_mapsTo (f := f) ?_ ?_ hGinf
  · intro ℓ₁ h₁ ℓ₂ h₂ heq
    by_contra hne
    obtain ⟨y, hy⟩ := exists_nonsingular W (f ℓ₁)
    have hodd₁ : Odd ℓ₁ := h₁.1.odd_of_ne_two h₁.2.1
    have hodd₂ : Odd ℓ₂ := h₂.1.odd_of_ne_two h₂.2.1
    have hT₁ : ℓ₁ • Affine.Point.some (f ℓ₁) y hy = 0 :=
      (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd₁ hy).mpr (hf ℓ₁ h₁)
    have hT₂ : ℓ₂ • Affine.Point.some (f ℓ₁) y hy = 0 :=
      (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd₂ hy).mpr
        (heq ▸ hf ℓ₂ h₂)
    have hd : addOrderOf (Affine.Point.some (f ℓ₁) y hy) ∣ Nat.gcd ℓ₁ ℓ₂ :=
      Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hT₁) (addOrderOf_dvd_of_nsmul_eq_zero hT₂)
    rw [(Nat.coprime_primes h₁.1 h₂.1).mpr hne, Nat.dvd_one, AddMonoid.addOrderOf_eq_one_iff] at hd
    exact Affine.Point.some_ne_zero hy hd
  · rintro ℓ hℓ
    exact ⟨ℓ, hℓ.1.odd_of_ne_two hℓ.2.1, hℓ.1.one_lt, hf ℓ hℓ⟩

variable {W}
variable [DecidableEq k] [IsAlgClosed k] {W₁ W₂ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic]
  (α : W₁.toAffine.Point →+ W₂.toAffine.Point) {u v : Polynomial k} {B : Set k}
  (huv : IsCoprime u v) (hB : B.Finite)
  (hα : ∀ (x y : k) (h : W₁.toAffine.Nonsingular x y), x ∉ B →
    ∃ (x' y' : k) (h' : W₂.toAffine.Nonsingular x' y'),
      α (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some x' y' h' ∧
        x' * v.eval x = u.eval x)

omit [W₂.IsElliptic] in
include huv hα in

theorem eval_v_ne_zero {x : k} (hx : x ∉ B) : v.eval x ≠ 0 := by
  intro hv
  obtain ⟨y, hy⟩ := exists_nonsingular W₁ x
  obtain ⟨x', y', h', -, hx'⟩ := hα x y hy hx
  rw [hv, mul_zero] at hx'
  exact eval_ne_zero_of_isCoprime huv hv hx'.symm

include huv hB hα in

theorem natDegree_lt_of_torsion {n : ℤ} (hn : n ≠ 0) {e yT : k}
    (hT : W₁.toAffine.Nonsingular e yT) (he : e ∉ B)
    (hnT : n • WeierstrassCurve.Affine.Point.some e yT hT = 0) :
    v.natDegree < u.natDegree := by

  set Φ₁ := W₁.Φ n with hΦ₁
  set Ψ₁ := W₁.ΨSq n with hΨ₁
  set Φ₂ := W₂.Φ n with hΦ₂
  set Ψ₂ := W₂.ΨSq n with hΨ₂
  set M := max u.natDegree v.natDegree with hM
  set N' := n.natAbs ^ 2 - 1 with hN'
  have hNpos : 1 ≤ n.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hn)
  have hN : N' + 1 = n.natAbs ^ 2 := Nat.sub_add_cancel hNpos
  have hdegΦ₁ : Φ₁.natDegree = n.natAbs ^ 2 := WeierstrassCurve.natDegree_Φ W₁ n
  have hdegΦ₂ : Φ₂.natDegree ≤ N' + 1 := by rw [hN, hΦ₂, WeierstrassCurve.natDegree_Φ]
  have hdegΨ₁ : Ψ₁.natDegree ≤ N' := WeierstrassCurve.natDegree_ΨSq_le W₁ n
  have hdegΨ₂ : Ψ₂.natDegree ≤ N' := WeierstrassCurve.natDegree_ΨSq_le W₂ n
  have hcop₁ : IsCoprime Φ₁ Ψ₁ := WeierstrassCurve.isCoprime_Phi_PsiSq W₁ n
  have hcop₂ : IsCoprime Φ₂ Ψ₂ := WeierstrassCurve.isCoprime_Phi_PsiSq W₂ n
  have hΨ₁0 : Ψ₁ ≠ 0 := ΨSq_ne_zero' W₁ hn

  set L := hom M Φ₁ Ψ₁ u * hom N' u v Ψ₂ * v with hL
  set R := hom M Φ₁ Ψ₁ v * hom (N' + 1) u v Φ₂ with hR

  set S : Set k := B ∪ {x | Ψ₁.eval x = 0} ∪ ⋃ b ∈ B, {x | (Φ₁ - C b * Ψ₁).eval x = 0} with hS
  have hSfin : S.Finite := by
    refine (hB.union ?_).union (hB.biUnion fun b _ => ?_)
    · exact Polynomial.finite_setOf_isRoot hΨ₁0
    · refine Polynomial.finite_setOf_isRoot ?_
      have hlt : (C b * Ψ₁).natDegree < Φ₁.natDegree := by
        rw [hdegΦ₁, ← hN]
        exact Nat.lt_succ_of_le ((natDegree_C_mul_le _ _).trans hdegΨ₁)
      intro h0
      have := natDegree_sub_eq_left_of_natDegree_lt hlt
      rw [h0, natDegree_zero, hdegΦ₁] at this
      exact absurd this.symm (by positivity)

  have hLR : L = R := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (hSfin.infinite_compl).mono fun x hx => ?_
    simp only [hS, Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion,
      not_or, not_exists] at hx
    obtain ⟨⟨hxB, hxΨ⟩, hxΦ⟩ := hx
    obtain ⟨y, hy⟩ := exists_nonsingular W₁ x
    obtain ⟨x', y', h', hP, hx'⟩ := hα x y hy hxB
    have hvx : v.eval x ≠ 0 := eval_v_ne_zero α huv hα hxB

    have hψ₁ : (W₁.ψ n).evalEval x y ≠ 0 := fun h0 => hxΨ (by
      rw [hΨ₁, ← evalEval_ψ_sq W₁ hy.left n, h0]; ring)
    obtain ⟨y₂, h₂, hnP⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div W₁ hy hψ₁
    set z := Φ₁.eval x / Ψ₁.eval x with hz
    have hzB : z ∉ B := by
      intro hzB
      apply hxΦ z hzB
      rw [eval_sub, eval_mul, eval_C, hz, div_mul_cancel₀ _ hxΨ, sub_self]
    obtain ⟨x'', y'', h'', hQ, hx''⟩ := hα z y₂ h₂ hzB

    have hnQ : n • WeierstrassCurve.Affine.Point.some x' y' h' =
        WeierstrassCurve.Affine.Point.some x'' y'' h'' := by
      rw [← hP, ← map_zsmul, hnP, hQ]
    have hψ₂ : (W₂.ψ n).evalEval x' y' ≠ 0 := by
      intro h0
      have := (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W₂ h' n).mpr h0
      rw [hnQ] at this
      exact WeierstrassCurve.Affine.Point.some_ne_zero h'' this
    have hΨ₂x' : Ψ₂.eval x' ≠ 0 := by
      rw [hΨ₂, ← evalEval_ψ_sq W₂ h'.left n]
      exact pow_ne_zero _ hψ₂
    obtain ⟨y₃, h₃, hnQ'⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div W₂ h' hψ₂
    rw [hnQ] at hnQ'
    have hx''eq : x'' = Φ₂.eval x' / Ψ₂.eval x' :=
      (WeierstrassCurve.Affine.Point.some.inj hnQ').1
    have key : u.eval z * Ψ₂.eval x' = Φ₂.eval x' * v.eval z := by
      rw [← hx'', hx''eq, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hΨ₂x']
    have hzx : z * Ψ₁.eval x = Φ₁.eval x := by rw [hz, div_mul_cancel₀ _ hxΨ]
    show L.eval x = R.eval x
    rw [hL, hR, eval_mul, eval_mul, eval_mul, eval_hom (le_max_left _ _) hzx,
      eval_hom hdegΨ₂ hx', eval_hom (le_max_right _ _) hzx, eval_hom hdegΦ₂ hx']
    linear_combination (Ψ₁.eval x) ^ M * (v.eval x) ^ N' * v.eval x * key

  have hΨ₁e : Ψ₁.eval e = 0 := by
    rw [hΨ₁, ← evalEval_ψ_sq W₁ hT.left n,
      (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W₁ hT n).mp hnT]
    ring
  have hΦ₁e : Φ₁.eval e ≠ 0 := eval_ne_zero_of_isCoprime hcop₁ hΨ₁e
  have hve : v.eval e ≠ 0 := eval_v_ne_zero α huv hα he
  obtain ⟨x', y', h', hαT, hx'⟩ := hα e yT hT he
  have hΨ₂e : Ψ₂.eval x' = 0 := by
    have h0 : n • WeierstrassCurve.Affine.Point.some x' y' h' = 0 := by
      rw [← hαT, ← map_zsmul, hnT, map_zero]
    rw [hΨ₂, ← evalEval_ψ_sq W₂ h'.left n,
      (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W₂ h' n).mp h0]
    ring
  have hΦ₂e : Φ₂.eval x' ≠ 0 := eval_ne_zero_of_isCoprime hcop₂ hΨ₂e
  have hLe : L.eval e = 0 := by
    rw [hL, eval_mul, eval_mul, eval_hom hdegΨ₂ hx', hΨ₂e]
    ring
  have hRe : R.eval e = v.coeff M * (Φ₁.eval e) ^ M * ((v.eval e) ^ (N' + 1) * Φ₂.eval x') := by
    rw [hR, eval_mul, eval_hom_of_root v hΨ₁e, eval_hom hdegΦ₂ hx']
  have hcoeff : v.coeff M = 0 := by
    rw [hLR, hRe] at hLe
    simpa [hΦ₁e, hve, hΦ₂e] using hLe

  by_contra hle
  rw [not_lt] at hle
  have hMv : M = v.natDegree := max_eq_right hle
  have hv0 : v ≠ 0 := by rintro rfl; simp at hve
  rw [hMv, coeff_natDegree, leadingCoeff_eq_zero] at hcoeff
  exact hv0 hcoeff

include huv hB hα in

theorem natDegree_lt : v.natDegree < u.natDegree := by
  obtain ⟨e, ⟨n, hodd, h1, hroot⟩, heB⟩ :=
    ((infinite_torsion_abscissa W₁).diff hB).nonempty
  obtain ⟨yT, hT⟩ := exists_nonsingular W₁ e
  have hnT : (n : ℤ) • WeierstrassCurve.Affine.Point.some e yT hT = 0 := by
    rw [natCast_zsmul]
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W₁ hodd hT).mpr hroot
  exact natDegree_lt_of_torsion α huv hB hα (by exact_mod_cast (by omega : n ≠ 0)) hT heB hnT

end WeierstrassCurve.XRepDegree

theorem solution {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic] (α : W₁.toAffine.Point →+ W₂.toAffine.Point) {u v : Polynomial k} {B : Set k} (huv : IsCoprime u v) (hB : B.Finite) (hα : ∀ (x y : k) (h : W₁.toAffine.Nonsingular x y), x ∉ B → ∃ (x' y' : k) (h' : W₂.toAffine.Nonsingular x' y'), α (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some x' y' h' ∧ x' * v.eval x = u.eval x) : v.natDegree < u.natDegree :=
  WeierstrassCurve.XRepDegree.natDegree_lt α huv hB hα

end S_WeierstrassCurve_natDegree_lt_of_xCoord_rep
end P2MW
export P2MW.S_WeierstrassCurve_natDegree_lt_of_xCoord_rep (solution)
