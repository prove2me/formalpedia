-- Prove2me | solution 1 for WeierstrassCurve.veluY_mem_and_residue_veluY_eq_of_forall_fst_ne_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7bd632c4-e36f-586e-9cb3-f3c38308cbdf

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_veluY_mem_and_residue_veluY_eq_of_forall_fst_ne_residue

set_option autoImplicit false

open IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine mk.injEq a₃ a₁ map map_b₂ b₂ mk a₄ a₂ Affine.Point.some reduction toAffine Affine.Point map_a₁ map_a₄ Δ map_a₂ j b₄ map_a₃ reduceHom X_mem_of_nsmul_eq_zero' Affine.Y_mem_of_X_mem reducePoint reducePoint_some_of_mem veluY veluGx veluGy veluT veluU veluT_eq Affine.Point.coordsOrZero_some oddOrderSummingSet mem_oddOrderSummingSet"
p2m_open "WeierstrassCurve"

namespace VeluReduceY

variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
  [DecidableEq (ResidueField A)]

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

omit [DecidableEq F] in
theorem exists_eq_some_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ x y h, P = Affine.Point.some x y h := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨x, y, h, rfl⟩

variable (W)

theorem injOn_coordsOrZero_nsmul (Q : W.toAffine.Point) (n : ℕ)
    (hQ : addOrderOf Q = 2 * n + 1) :
    Set.InjOn (fun j : ℕ => (j • Q).coordsOrZero) (Finset.Icc 1 n : Set ℕ) := by
  intro j hj l hl hjl
  rw [Finset.coe_Icc, Set.mem_Icc] at hj hl
  have hj0 : j • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  have hl0 : l • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  obtain ⟨x, y, h, hjQ⟩ := exists_eq_some_of_ne_zero hj0
  obtain ⟨x', y', h', hlQ⟩ := exists_eq_some_of_ne_zero hl0
  simp only [hjQ, hlQ, Affine.Point.coordsOrZero_some, Prod.mk.injEq] at hjl
  obtain ⟨rfl, rfl⟩ := hjl
  have heq : j • Q = l • Q := by rw [hjQ, hlQ]
  rw [nsmul_eq_nsmul_iff_modEq, hQ] at heq
  exact Nat.ModEq.eq_of_lt_of_lt heq (by omega) (by omega)

end Field

theorem main {E : WeierstrassCurve A} (hΔ : (E.map (residue A)).Δ ≠ 0) {n : ℕ}
    (hm : ((2 * n + 1 : ℕ) : ResidueField A) ≠ 0)
    (Q : (E.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hQ' : addOrderOf (reduceHom hΔ Q) = 2 * n + 1)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A)
    (hx' : ∀ P ∈ (E.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) n,
      P.1 ≠ residue A ⟨x, hx⟩) :
    ∃ hmem : (E.map A.subtype).veluY ((E.map A.subtype).oddOrderSummingSet Q n) x y ∈ A,
      residue A ⟨_, hmem⟩ =
        (E.map (residue A)).veluY ((E.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) n)
          (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by

  let EL := E.map A.subtype
  let Eb := E.map (residue A)
  let xb := residue A ⟨x, hx⟩
  let yb := residue A ⟨y, hy⟩
  let g : L × L → L := fun P =>
    EL.veluU P.1 P.2 * (2 * y + EL.a₁ * x + EL.a₃) / (x - P.1) ^ 3
      + EL.veluT P.1 P.2 * (EL.a₁ * (x - P.1) + y - P.2) / (x - P.1) ^ 2
      + (EL.a₁ * EL.veluU P.1 P.2 - EL.veluGx P.1 P.2 * EL.veluGy P.1 P.2) / (x - P.1) ^ 2
  let gb : ResidueField A × ResidueField A → ResidueField A := fun P =>
    Eb.veluU P.1 P.2 * (2 * yb + Eb.a₁ * xb + Eb.a₃) / (xb - P.1) ^ 3
      + Eb.veluT P.1 P.2 * (Eb.a₁ * (xb - P.1) + yb - P.2) / (xb - P.1) ^ 2
      + (Eb.a₁ * Eb.veluU P.1 P.2 - Eb.veluGx P.1 P.2 * Eb.veluGy P.1 P.2) / (xb - P.1) ^ 2
  have hsum : EL.veluY (EL.oddOrderSummingSet Q n) x y =
      y - ∑ j ∈ Finset.Icc 1 n, g ((j • Q).coordsOrZero) := by
    rw [veluY, oddOrderSummingSet, Finset.sum_image (injOn_coordsOrZero_nsmul EL Q n hQ)]
  have hsumb : Eb.veluY (Eb.oddOrderSummingSet (reduceHom hΔ Q) n) xb yb =
      yb - ∑ j ∈ Finset.Icc 1 n, gb ((j • (reduceHom hΔ Q)).coordsOrZero) := by
    rw [veluY, oddOrderSummingSet,
      Finset.sum_image (injOn_coordsOrZero_nsmul Eb (reduceHom hΔ Q) n hQ')]

  have hterm : ∀ j ∈ Finset.Icc 1 n, ∃ a : A, (a : L) = g ((j • Q).coordsOrZero) ∧
      residue A a = gb ((j • (reduceHom hΔ Q)).coordsOrZero) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj0 : j • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
    obtain ⟨xj, yj, hxyj, hjQ⟩ := exists_eq_some_of_ne_zero hj0

    have htor : (2 * n + 1) • (Affine.Point.some xj yj hxyj : EL.toAffine.Point) = 0 := by
      rw [← hjQ, ← mul_nsmul', ← hQ, mul_comm, mul_nsmul', addOrderOf_nsmul_eq_zero, nsmul_zero]
    have hxj : xj ∈ A := X_mem_of_nsmul_eq_zero' E hm hxyj htor
    have hyj : yj ∈ A := Affine.Y_mem_of_X_mem E hxyj.1 hxj

    have hjQb : (j • (reduceHom hΔ Q)).coordsOrZero = (residue A ⟨xj, hxj⟩, residue A ⟨yj, hyj⟩) := by
      rw [← map_nsmul, hjQ]
      show (reducePoint hΔ (Affine.Point.some xj yj hxyj)).coordsOrZero = _
      rw [reducePoint_some_of_mem hΔ hxyj hxj]
      rfl
    rw [hjQ, Affine.Point.coordsOrZero_some, hjQb]

    have hmemS : (residue A ⟨xj, hxj⟩, residue A ⟨yj, hyj⟩) ∈
        Eb.oddOrderSummingSet (reduceHom hΔ Q) n := by
      rw [mem_oddOrderSummingSet]
      exact ⟨j, hj.1, hj.2, hjQb⟩
    have hd : x - xj ∈ A := A.toSubring.sub_mem hx hxj
    have hdunit : x - xj ∉ A.nonunits := by
      intro hmem
      apply hx' _ hmemS
      show residue A ⟨xj, hxj⟩ = residue A ⟨x, hx⟩
      symm
      rw [A.residue_eq_residue_iff_sub_mem_nonunits hx hxj]
      exact hmem
    have hdres : residue A ⟨x - xj, hd⟩ = xb - residue A ⟨xj, hxj⟩ := by
      show _ = residue A ⟨x, hx⟩ - _
      rw [← map_sub]; rfl

    let xA : A := ⟨xj, hxj⟩
    let yA : A := ⟨yj, hyj⟩
    let xx : A := ⟨x, hx⟩
    let yy : A := ⟨y, hy⟩
    let dA : A := ⟨x - xj, hd⟩
    have hdU : IsUnit dA := (residue_ne_zero_iff_isUnit dA).mp
      (A.residue_ne_zero_of_notMem_nonunits hd hdunit)
    let iA : A := ↑(hdU.unit⁻¹)
    have hdi : dA * iA = 1 := by
      show (hdU.unit : A) * ↑(hdU.unit⁻¹) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdL : ((dA : A) : L) = x - xj := rfl
    have hiL : (iA : L) = (x - xj)⁻¹ := by
      have h1 : ((dA : A) : L) * (iA : L) = 1 := by
        rw [← Subring.coe_mul]; exact_mod_cast congrArg Subtype.val hdi
      rw [hdL] at h1
      exact (eq_inv_of_mul_eq_one_right h1)
    have hdAres : residue A dA = xb - residue A xA := hdres
    have hires : residue A iA = (xb - residue A xA)⁻¹ := by
      have h1 : residue A dA * residue A iA = 1 := by rw [← map_mul, hdi, map_one]
      rw [hdAres] at h1
      exact eq_inv_of_mul_eq_one_right h1
    let tA : A := 6 * xA ^ 2 + E.b₂ * xA + E.b₄
    let gyA : A := -(2 * yA + E.a₁ * xA + E.a₃)
    let gxA : A := 3 * xA ^ 2 + 2 * E.a₂ * xA + E.a₄ - E.a₁ * yA
    let uA : A := gyA ^ 2
    have htL : (tA : L) = EL.veluT xj yj := by
      rw [veluT_eq]
      show ((6 * xA ^ 2 + E.b₂ * xA + E.b₄ : A) : L) = _
      simp only [EL, map_b₂, map_b₄]
      push_cast
      rfl
    have hgyL : (gyA : L) = EL.veluGy xj yj := by
      simp only [EL, veluGy, map_a₁, map_a₃]
      show (((-(2 * yA + E.a₁ * xA + E.a₃)) : A) : L) = _
      push_cast
      rfl
    have hgxL : (gxA : L) = EL.veluGx xj yj := by
      simp only [EL, veluGx, map_a₁, map_a₂, map_a₄]
      show (((3 * xA ^ 2 + 2 * E.a₂ * xA + E.a₄ - E.a₁ * yA) : A) : L) = _
      push_cast
      rfl
    have huL : (uA : L) = EL.veluU xj yj := by
      show (((gyA ^ 2 : A)) : L) = _
      rw [veluU]; push_cast; rw [hgyL]
    have htres : residue A tA = Eb.veluT (residue A xA) (residue A yA) := by
      rw [veluT_eq]
      show residue A (6 * xA ^ 2 + E.b₂ * xA + E.b₄) = _
      simp only [Eb, map_add, map_mul, map_pow, map_ofNat, map_b₂, map_b₄]
    have hgyres : residue A gyA = Eb.veluGy (residue A xA) (residue A yA) := by
      show residue A (-(2 * yA + E.a₁ * xA + E.a₃)) = _
      simp only [Eb, veluGy, map_a₁, map_a₃, map_neg, map_add, map_mul, map_ofNat]
    have hgxres : residue A gxA = Eb.veluGx (residue A xA) (residue A yA) := by
      show residue A (3 * xA ^ 2 + 2 * E.a₂ * xA + E.a₄ - E.a₁ * yA) = _
      simp only [Eb, veluGx, map_a₁, map_a₂, map_a₄, map_sub, map_add, map_mul, map_pow, map_ofNat]
    have hures : residue A uA = Eb.veluU (residue A xA) (residue A yA) := by
      show residue A (gyA ^ 2) = _
      rw [map_pow, hgyres]; rfl
    have ha₁L : ((E.a₁ : A) : L) = EL.a₁ := (map_a₁ E A.subtype).symm
    have ha₃L : ((E.a₃ : A) : L) = EL.a₃ := (map_a₃ E A.subtype).symm
    have ha₁res : residue A E.a₁ = Eb.a₁ := (map_a₁ E (residue A)).symm
    have ha₃res : residue A E.a₃ = Eb.a₃ := (map_a₃ E (residue A)).symm

    refine ⟨uA * (2 * yy + E.a₁ * xx + E.a₃) * iA ^ 3
      + tA * (E.a₁ * dA + yy - yA) * iA ^ 2 + (E.a₁ * uA - gxA * gyA) * iA ^ 2, ?_, ?_⟩
    · push_cast
      rw [htL, huL, hgxL, hgyL, hiL, ha₁L, ha₃L, hdL]
      simp only [g, div_eq_mul_inv, inv_pow]
      rfl
    · have hxx : residue A xx = xb := rfl
      have hyy : residue A yy = yb := rfl
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, hures, htres, hires, hgxres, hgyres,
        ha₁res, ha₃res, hdAres, hxx, hyy]
      simp only [gb, div_eq_mul_inv, inv_pow]
      rfl

  choose! a ha hres using hterm
  have hcoe : ∑ j ∈ Finset.Icc 1 n, g ((j • Q).coordsOrZero) =
      ((∑ j ∈ Finset.Icc 1 n, a j : A) : L) := by
    push_cast
    exact Finset.sum_congr rfl fun j hj => (ha j hj).symm
  have hmem : EL.veluY (EL.oddOrderSummingSet Q n) x y ∈ A := by
    rw [hsum, hcoe]
    exact A.toSubring.sub_mem hy (SetLike.coe_mem _)
  refine ⟨hmem, ?_⟩
  show _ = Eb.veluY (Eb.oddOrderSummingSet (reduceHom hΔ Q) n) xb yb
  rw [hsumb]
  have hxa : (⟨EL.veluY (EL.oddOrderSummingSet Q n) x y, hmem⟩ : A) =
      ⟨y, hy⟩ - ∑ j ∈ Finset.Icc 1 n, a j := by
    apply Subtype.ext
    push_cast
    rw [hsum, hcoe]
    push_cast
    rfl
  rw [hxa, map_sub, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun j hj => hres j hj

end VeluReduceY

end WeierstrassCurve

theorem solution
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
    [DecidableEq (IsLocalRing.ResidueField A)]
    {E : WeierstrassCurve A} (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) {n : ℕ}
    (hm : ((2 * n + 1 : ℕ) : IsLocalRing.ResidueField A) ≠ 0)
    (Q : (E.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hQ' : addOrderOf (WeierstrassCurve.reduceHom hΔ Q) = 2 * n + 1)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A)
    (hx' : ∀ P ∈ (E.map (IsLocalRing.residue A)).oddOrderSummingSet
      (WeierstrassCurve.reduceHom hΔ Q) n, P.1 ≠ IsLocalRing.residue A ⟨x, hx⟩) :
    ∃ hmem : (E.map A.subtype).veluY ((E.map A.subtype).oddOrderSummingSet Q n) x y ∈ A,
      IsLocalRing.residue A ⟨_, hmem⟩ =
        (E.map (IsLocalRing.residue A)).veluY
          ((E.map (IsLocalRing.residue A)).oddOrderSummingSet (WeierstrassCurve.reduceHom hΔ Q) n)
          (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩) :=
  WeierstrassCurve.VeluReduceY.main hΔ hm Q hQ hQ' hx hy hx'

end S_WeierstrassCurve_veluY_mem_and_residue_veluY_eq_of_forall_fst_ne_residue
end P2MW
export P2MW.S_WeierstrassCurve_veluY_mem_and_residue_veluY_eq_of_forall_fst_ne_residue (solution)
