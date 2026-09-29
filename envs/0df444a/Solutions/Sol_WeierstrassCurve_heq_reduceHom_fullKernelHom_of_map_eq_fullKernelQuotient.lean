-- Prove2me | solution 1 for WeierstrassCurve.heq_reduceHom_fullKernelHom_of_map_eq_fullKernelQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/50da508f-67b3-55bc-8cad-f5dd589cff57

import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_heq_reduceHom_fullKernelHom_of_map_eq_fullKernelQuotient

set_option autoImplicit false

namespace P2MKcA
namespace WidthB2
namespace VeluHomReduction

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

section Cast

variable {R : Type*} [Field R] [DecidableEq R]

def castPt {W₁ W₂ : WeierstrassCurve R} (e : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve R} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (P₂ : W₂.toAffine.Point) : castPt e P = P₂ ↔ HEq P P₂ := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

theorem heq_castPt {W₁ W₂ : WeierstrassCurve R} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq (castPt e P) P := by
  subst e; rfl

theorem coordsOrZero_castPt {W₁ W₂ : WeierstrassCurve R} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    (castPt e P).coordsOrZero = P.coordsOrZero := by
  subst e; rfl

theorem eq_some_of_ne_zero {V : WeierstrassCurve R} {P : V.toAffine.Point} (hP : P ≠ 0) :
    ∃ h : V.toAffine.Nonsingular P.coordsOrZero.1 P.coordsOrZero.2,
      P = .some P.coordsOrZero.1 P.coordsOrZero.2 h := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨h, rfl⟩

end Cast

section Integral

universe u

variable {L : Type u} [Field L] [DecidableEq L] {A : ValuationSubring L}
  [DecidableEq (ResidueField A)] {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)

theorem reduceHom_apply (P : (W.map A.subtype).toAffine.Point) :
    reduceHom hΔ P = reducePoint hΔ P := rfl

theorem exists_coords_of_reduceHom_ne_zero (P : (W.map A.subtype).toAffine.Point)
    (hP : reduceHom hΔ P ≠ 0) :
    ∃ xy : A × A, P.coordsOrZero = ((xy.1 : L), (xy.2 : L)) ∧
      (reduceHom hΔ P).coordsOrZero = (residue A xy.1, residue A xy.2) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd (map_zero (reduceHom hΔ)) hP
  · by_cases hx : x ∈ A
    · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
      refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl, ?_⟩
      rw [reduceHom_apply, reducePoint_some_of_mem hΔ h hx]
      rfl
    · exact absurd (by rw [reduceHom_apply, reducePoint_some_of_notMem hΔ h hx]) hP

theorem notMem_of_reduceHom_eq_zero (P : (W.map A.subtype).toAffine.Point) (hP0 : P ≠ 0)
    (hP : reduceHom hΔ P = 0) : P.coordsOrZero.1 ∉ A := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP0
  · intro hx
    rw [reduceHom_apply, reducePoint_some_of_mem hΔ h hx] at hP
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ hP

theorem reduceHom_some_of_mem {X Y : L} (h : (W.map A.subtype).toAffine.Nonsingular X Y)
    (hX : X ∈ A) (hY : Y ∈ A) :
    reduceHom hΔ (.some X Y h) ≠ 0 ∧
      (reduceHom hΔ (.some X Y h)).coordsOrZero = (residue A ⟨X, hX⟩, residue A ⟨Y, hY⟩) := by
  rw [reduceHom_apply, reducePoint_some_of_mem hΔ h hX]
  exact ⟨WeierstrassCurve.Affine.Point.some_ne_zero _, rfl⟩

theorem reduceHom_some_of_notMem {X Y : L} (h : (W.map A.subtype).toAffine.Nonsingular X Y)
    (hX : X ∉ A) : reduceHom hΔ (.some X Y h) = 0 := by
  rw [reduceHom_apply, reducePoint_some_of_notMem hΔ h hX]

theorem reduceHom_zsmul (Q : (W.map A.subtype).toAffine.Point)
    (m : ℤ) : reduceHom hΔ (m • Q) = m • reduceHom hΔ Q := map_zsmul _ _ _

theorem reduceHom_mem_zmultiples
    (Q : (W.map A.subtype).toAffine.Point) {P : (W.map A.subtype).toAffine.Point}
    (hP : P ∈ AddSubgroup.zmultiples Q) :
    reduceHom hΔ P ∈ AddSubgroup.zmultiples (reduceHom hΔ Q) := by
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
  rw [reduceHom_zsmul]
  exact AddSubgroup.zsmul_mem_zmultiples _ m

theorem integralCoords (R : (W.map A.subtype).toAffine.Point)
    (hR : reduceHom hΔ R ≠ 0) :
    ∃ c : A × A, R.coordsOrZero.1 = A.subtype c.1 ∧ R.coordsOrZero.2 = A.subtype c.2 ∧
      (reduceHom hΔ R).coordsOrZero.1 = residue A c.1 ∧
      (reduceHom hΔ R).coordsOrZero.2 = residue A c.2 := by
  obtain ⟨c, h1, h2⟩ := exists_coords_of_reduceHom_ne_zero hΔ R hR
  exact ⟨c, congrArg Prod.fst h1, congrArg Prod.snd h1, congrArg Prod.fst h2, congrArg Prod.snd h2⟩

end Integral

section Main

universe u

variable {L : Type u} [Field L] [DecidableEq L] {A : ValuationSubring L}
  [DecidableEq (ResidueField A)] {W : WeierstrassCurve A}

structure Setup (hΔ : (W.map (residue A)).Δ ≠ 0) (N : ℕ) (Q : (W.map A.subtype).toAffine.Point)
    where
  W' : WeierstrassCurve A
  hW' : W'.map A.subtype = (W.map A.subtype).fullKernelQuotient Q N
  hW'red : W'.map (residue A) = (W.map (residue A)).fullKernelQuotient (reduceHom hΔ Q) N
  hΔ' : (W'.map (residue A)).Δ ≠ 0
  φ : (W.map A.subtype).toAffine.Point →+
    ((W.map A.subtype).fullKernelQuotient Q N).toAffine.Point
  hφker : φ.ker = AddSubgroup.zmultiples Q
  hφ : ∀ P : (W.map A.subtype).toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
    (φ P).coordsOrZero =
      (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
          ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
       P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
          ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))
  φ₀ : (W.map (residue A)).toAffine.Point →+
    ((W.map (residue A)).fullKernelQuotient (reduceHom hΔ Q) N).toAffine.Point
  hφ₀ker : φ₀.ker = AddSubgroup.zmultiples (reduceHom hΔ Q)
  hφ₀ : ∀ P : (W.map (residue A)).toAffine.Point, P ∉ AddSubgroup.zmultiples (reduceHom hΔ Q) →
    (φ₀ P).coordsOrZero =
      (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
          ((P + k • reduceHom hΔ Q).coordsOrZero.1 - (k • reduceHom hΔ Q).coordsOrZero.1),
       P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
          ((P + k • reduceHom hΔ Q).coordsOrZero.2 - (k • reduceHom hΔ Q).coordsOrZero.2))
  hQ : addOrderOf (reduceHom hΔ Q) = N

variable {hΔ : (W.map (residue A)).Δ ≠ 0} {N : ℕ} {Q : (W.map A.subtype).toAffine.Point}
  (S : Setup hΔ N Q)

include S

noncomputable def redφ (P : (W.map A.subtype).toAffine.Point) :
    ((W.map (residue A)).fullKernelQuotient (reduceHom hΔ Q) N).toAffine.Point :=
  castPt S.hW'red (reduceHom S.hΔ' (castPt S.hW'.symm (S.φ P)))

theorem nsmul_reduce_ne_zero {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ N - 1) :
    k • reduceHom hΔ Q ≠ 0 :=
  nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [S.hQ]; omega)

theorem redφ_eq_zero_of_reduceHom_eq_zero (P : (W.map A.subtype).toAffine.Point)
    (hPQ : P ∉ AddSubgroup.zmultiples Q) (hP : reduceHom hΔ P = 0) :
    redφ S P = 0 := by
  have hP0 : P ≠ 0 := fun h0 => hPQ (by rw [h0]; exact zero_mem _)

  have hx : P.coordsOrZero.1 ∉ A := notMem_of_reduceHom_eq_zero hΔ P hP0 hP

  have hsum : (∑ k ∈ Finset.Icc 1 (N - 1),
      ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1)) ∈ A := by
    refine sum_mem fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hkQ : reduceHom hΔ (k • Q) ≠ 0 := by
      rw [map_nsmul]; exact nsmul_reduce_ne_zero S hk.1 hk.2
    have hPkQ : reduceHom hΔ (P + k • Q) ≠ 0 := by
      rw [map_add, hP, zero_add]; exact hkQ
    obtain ⟨c₁, hc₁, -⟩ := exists_coords_of_reduceHom_ne_zero hΔ _ hPkQ
    obtain ⟨c₂, hc₂, -⟩ := exists_coords_of_reduceHom_ne_zero hΔ _ hkQ
    rw [hc₁, hc₂]
    exact sub_mem c₁.1.2 c₂.1.2

  have hX : (S.φ P).coordsOrZero.1 ∉ A := by
    rw [S.hφ P hPQ]
    intro hmem
    apply hx
    have := sub_mem hmem hsum
    rwa [add_sub_cancel_right] at this

  have hφP0 : S.φ P ≠ 0 := by
    intro h0
    apply hPQ
    rw [← S.hφker]
    exact h0
  have hcP0 : castPt S.hW'.symm (S.φ P) ≠ 0 := by
    intro h0; apply hφP0
    exact (castPt S.hW'.symm).injective (h0.trans (map_zero _).symm)
  obtain ⟨h, heq⟩ := eq_some_of_ne_zero hcP0
  have hX' : (castPt S.hW'.symm (S.φ P)).coordsOrZero.1 ∉ A := by
    rw [coordsOrZero_castPt]; exact hX
  rw [redφ, heq, reduceHom_some_of_notMem S.hΔ' h hX', map_zero]

theorem redφ_eq_of_notMem (P : (W.map A.subtype).toAffine.Point)
    (hPbar : reduceHom hΔ P ∉ AddSubgroup.zmultiples (reduceHom hΔ Q)) :
    redφ S P = S.φ₀ (reduceHom hΔ P) := by
  classical
  have hPQ : P ∉ AddSubgroup.zmultiples Q := fun h => hPbar (reduceHom_mem_zmultiples hΔ Q h)

  have hP : reduceHom hΔ P ≠ 0 := fun h0 => hPbar (by rw [h0]; exact zero_mem _)
  have hPk : ∀ k ∈ Finset.Icc 1 (N - 1), reduceHom hΔ (P + k • Q) ≠ 0 := by
    intro k hk h0
    apply hPbar
    rw [map_add, map_nsmul, add_eq_zero_iff_eq_neg] at h0
    rw [h0]
    exact neg_mem (AddSubgroup.nsmul_mem_zmultiples _ k)
  have hkQ : ∀ k ∈ Finset.Icc 1 (N - 1), reduceHom hΔ (k • Q) ≠ 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [map_nsmul]; exact nsmul_reduce_ne_zero S hk.1 hk.2
  obtain ⟨cP, hcP1, hcP2, hcP3, hcP4⟩ := integralCoords hΔ P hP
  choose! cPk hcPk1 hcPk2 hcPk3 hcPk4 using
    fun k (hk : k ∈ Finset.Icc 1 (N - 1)) => integralCoords hΔ (P + k • Q) (hPk k hk)
  choose! ck hck1 hck2 hck3 hck4 using
    fun k (hk : k ∈ Finset.Icc 1 (N - 1)) => integralCoords hΔ (k • Q) (hkQ k hk)

  set XA : A := cP.1 + ∑ k ∈ Finset.Icc 1 (N - 1), ((cPk k).1 - (ck k).1) with hXA
  set YA : A := cP.2 + ∑ k ∈ Finset.Icc 1 (N - 1), ((cPk k).2 - (ck k).2) with hYA
  have hX : (S.φ P).coordsOrZero.1 = A.subtype XA := by
    rw [S.hφ P hPQ]
    show P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
        ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1) = A.subtype XA
    rw [hXA, map_add, map_sum, hcP1]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hcPk1 k hk, hck1 k hk, map_sub]
  have hY : (S.φ P).coordsOrZero.2 = A.subtype YA := by
    rw [S.hφ P hPQ]
    show P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
        ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2) = A.subtype YA
    rw [hYA, map_add, map_sum, hcP2]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hcPk2 k hk, hck2 k hk, map_sub]

  have hX₀ : (S.φ₀ (reduceHom hΔ P)).coordsOrZero.1 = residue A XA := by
    rw [S.hφ₀ _ hPbar]
    show (reduceHom hΔ P).coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
        ((reduceHom hΔ P + k • reduceHom hΔ Q).coordsOrZero.1 -
          (k • reduceHom hΔ Q).coordsOrZero.1) = residue A XA
    rw [hXA, map_add, map_sum, hcP3]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← map_nsmul, ← map_add, hcPk3 k hk, hck3 k hk, map_sub]
  have hY₀ : (S.φ₀ (reduceHom hΔ P)).coordsOrZero.2 = residue A YA := by
    rw [S.hφ₀ _ hPbar]
    show (reduceHom hΔ P).coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
        ((reduceHom hΔ P + k • reduceHom hΔ Q).coordsOrZero.2 -
          (k • reduceHom hΔ Q).coordsOrZero.2) = residue A YA
    rw [hYA, map_add, map_sum, hcP4]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← map_nsmul, ← map_add, hcPk4 k hk, hck4 k hk, map_sub]

  have hφP0 : S.φ P ≠ 0 := by
    intro h0; apply hPQ; rw [← S.hφker]; exact h0
  have hφ₀P0 : S.φ₀ (reduceHom hΔ P) ≠ 0 := by
    intro h0; apply hPbar; rw [← S.hφ₀ker]; exact h0

  have hcP0 : castPt S.hW'.symm (S.φ P) ≠ 0 := by
    intro h0; apply hφP0
    exact (castPt S.hW'.symm).injective (h0.trans (map_zero _).symm)
  obtain ⟨h, heq⟩ := eq_some_of_ne_zero hcP0
  have hXmem : (castPt S.hW'.symm (S.φ P)).coordsOrZero.1 ∈ A := by
    rw [coordsOrZero_castPt, hX]; exact XA.2
  have hYmem : (castPt S.hW'.symm (S.φ P)).coordsOrZero.2 ∈ A := by
    rw [coordsOrZero_castPt, hY]; exact YA.2
  obtain ⟨hne, hcoords⟩ := reduceHom_some_of_mem S.hΔ' h hXmem hYmem
  have hXA' : (⟨(castPt S.hW'.symm (S.φ P)).coordsOrZero.1, hXmem⟩ : A) = XA :=
    Subtype.ext (show (castPt S.hW'.symm (S.φ P)).coordsOrZero.1 = A.subtype XA by
      rw [coordsOrZero_castPt, hX])
  have hYA' : (⟨(castPt S.hW'.symm (S.φ P)).coordsOrZero.2, hYmem⟩ : A) = YA :=
    Subtype.ext (show (castPt S.hW'.symm (S.φ P)).coordsOrZero.2 = A.subtype YA by
      rw [coordsOrZero_castPt, hY])
  rw [hXA', hYA'] at hcoords

  apply eq_of_coordsOrZero_eq
  · rw [redφ, heq]
    intro h0
    exact hne ((castPt S.hW'red).injective (h0.trans (map_zero _).symm))
  · exact hφ₀P0
  · rw [redφ, heq, coordsOrZero_castPt, hcoords, Prod.ext_iff]
    exact ⟨hX₀.symm, hY₀.symm⟩

theorem redφ_eq (P : (W.map A.subtype).toAffine.Point) : redφ S P = S.φ₀ (reduceHom hΔ P) := by
  by_cases hPQ : P ∈ AddSubgroup.zmultiples Q
  ·
    have h1 : S.φ P = 0 := by rw [← AddMonoidHom.mem_ker, S.hφker]; exact hPQ
    have h2 : S.φ₀ (reduceHom hΔ P) = 0 := by
      rw [← AddMonoidHom.mem_ker, S.hφ₀ker]; exact reduceHom_mem_zmultiples hΔ Q hPQ
    rw [redφ, h1, map_zero, map_zero, map_zero, h2]
  by_cases hPbar : reduceHom hΔ P ∈ AddSubgroup.zmultiples (reduceHom hΔ Q)
  ·
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hPbar
    have h2 : S.φ₀ (reduceHom hΔ P) = 0 := by
      rw [← AddMonoidHom.mem_ker, S.hφ₀ker]; exact hPbar
    set P₁ := P - m • Q with hP₁
    have hP₁Q : P₁ ∉ AddSubgroup.zmultiples Q := by
      intro h; apply hPQ
      have : P = P₁ + m • Q := by rw [hP₁, sub_add_cancel]
      rw [this]
      exact add_mem h (AddSubgroup.zsmul_mem_zmultiples Q m)
    have hP₁red : reduceHom hΔ P₁ = 0 := by
      rw [hP₁, map_sub, reduceHom_zsmul, hm, sub_self]
    have hφP₁ : S.φ P₁ = S.φ P := by
      rw [hP₁, map_sub, sub_eq_self, ← AddMonoidHom.mem_ker, S.hφker]
      exact AddSubgroup.zsmul_mem_zmultiples Q m
    have key := redφ_eq_zero_of_reduceHom_eq_zero S P₁ hP₁Q hP₁red
    rw [redφ, hφP₁] at key
    rw [redφ, key, h2]
  · exact redφ_eq_of_notMem S P hPbar

theorem main (P : (W.map A.subtype).toAffine.Point) (P' : (S.W'.map A.subtype).toAffine.Point)
    (hP' : HEq P' (S.φ P)) :
    HEq (reduceHom S.hΔ' P') (S.φ₀ (reduceHom hΔ P)) := by
  have h1 : castPt S.hW'.symm (S.φ P) = P' := by
    rw [castPt_eq_iff_heq]; exact hP'.symm
  have h2 := redφ_eq S P
  rw [redφ, h1, castPt_eq_iff_heq] at h2
  exact h2

end Main

end P2MKcA.WidthB2.VeluHomReduction

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

universe u in
theorem solution
    {L : Type u} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    (N : ℕ) (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf (reduceHom hΔ Q) = N)
    (W' : WeierstrassCurve A)
    (hW' : W'.map A.subtype = (W.map A.subtype).fullKernelQuotient Q N)
    (hW'red : W'.map (residue A) = (W.map (residue A)).fullKernelQuotient (reduceHom hΔ Q) N)
    (hΔ' : (W'.map (residue A)).Δ ≠ 0)
    (φ : (W.map A.subtype).toAffine.Point →+
      ((W.map A.subtype).fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : (W.map A.subtype).toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (φ₀ : (W.map (residue A)).toAffine.Point →+
      ((W.map (residue A)).fullKernelQuotient (reduceHom hΔ Q) N).toAffine.Point)
    (hφ₀ker : φ₀.ker = AddSubgroup.zmultiples (reduceHom hΔ Q))
    (hφ₀ : ∀ P : (W.map (residue A)).toAffine.Point, P ∉ AddSubgroup.zmultiples (reduceHom hΔ Q) →
      (φ₀ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • reduceHom hΔ Q).coordsOrZero.1 - (k • reduceHom hΔ Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • reduceHom hΔ Q).coordsOrZero.2 - (k • reduceHom hΔ Q).coordsOrZero.2)))
    (P : (W.map A.subtype).toAffine.Point) (P' : (W'.map A.subtype).toAffine.Point)
    (hP' : HEq P' (φ P)) :
    HEq (reduceHom hΔ' P') (φ₀ (reduceHom hΔ P)) :=
  P2MKcA.WidthB2.VeluHomReduction.main
    ⟨W', hW', hW'red, hΔ', φ, hφker, hφ, φ₀, hφ₀ker, hφ₀, hQ⟩ P P' hP'

end S_WeierstrassCurve_heq_reduceHom_fullKernelHom_of_map_eq_fullKernelQuotient
end P2MW
export P2MW.S_WeierstrassCurve_heq_reduceHom_fullKernelHom_of_map_eq_fullKernelQuotient (solution)
