-- Prove2me | solution 1 for WeierstrassCurve.exists_map_residue_eq_and_map_subtype_j_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c8a4760c-fc86-5874-a7fa-8d92e1a15926

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_map_residue_eq_and_map_subtype_j_eq

set_option autoImplicit false

open Polynomial IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "isUnit_Δ map_c₄ a₃ map_map a₁ map b₂ coe_Δ' a₄ a₂ a₆ isIntegral_iff reduction IsIntegral map_injective map_Δ b₆ b₈ Δ c₄ j b₄ Δ'"
namespace LiftJ
p2m_open "WeierstrassCurve"

variable {R : Type*} [CommRing R]

noncomputable def fam (a₂ a₃ a₄ a₆ : R) : WeierstrassCurve R[X] := ⟨X, C a₂, C a₃, C a₄, C a₆⟩

theorem fam_map_eval (a₂ a₃ a₄ a₆ r : R) :
    (fam a₂ a₃ a₄ a₆).map (evalRingHom r) = ⟨r, a₂, a₃, a₄, a₆⟩ := by
  simp [fam, WeierstrassCurve.map]

theorem fam_map_map {S : Type*} [CommRing S] (f : R →+* S) (a₂ a₃ a₄ a₆ : R) :
    (fam a₂ a₃ a₄ a₆).map (mapRingHom f) = fam (f a₂) (f a₃) (f a₄) (f a₆) := by
  simp [fam, WeierstrassCurve.map]

theorem fam_c₄ (a₂ a₃ a₄ a₆ : R) :
    (fam a₂ a₃ a₄ a₆).c₄ = X ^ 4 + C (8 * a₂) * X ^ 2 + C (-(24 * a₃)) * X + C (16 * a₂ ^ 2 - 48 * a₄) := by
  simp only [fam, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, map_mul, map_neg,
    map_sub, map_pow, C_ofNat]
  ring

theorem natDegree_fam_c₄ [Nontrivial R] (a₂ a₃ a₄ a₆ : R) : (fam a₂ a₃ a₄ a₆).c₄.natDegree = 4 := by
  rw [fam_c₄]
  compute_degree!

theorem monic_fam_c₄ [Nontrivial R] (a₂ a₃ a₄ a₆ : R) : (fam a₂ a₃ a₄ a₆).c₄.Monic := by
  rw [fam_c₄]
  monicity!

theorem natDegree_fam_Δ_le (a₂ a₃ a₄ a₆ : R) : (fam a₂ a₃ a₄ a₆).Δ.natDegree ≤ 6 := by
  simp only [fam, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  compute_degree!

noncomputable def G (β a₂ a₃ a₄ a₆ : R) : R[X] :=
  (fam a₂ a₃ a₄ a₆).c₄ ^ 3 - C β * (fam a₂ a₃ a₄ a₆).Δ

theorem monic_G [Nontrivial R] (β a₂ a₃ a₄ a₆ : R) : (G β a₂ a₃ a₄ a₆).Monic := by
  have h1 : ((fam a₂ a₃ a₄ a₆).c₄ ^ 3).Monic := (monic_fam_c₄ a₂ a₃ a₄ a₆).pow 3
  have h2 : ((fam a₂ a₃ a₄ a₆).c₄ ^ 3).natDegree = 12 := by
    rw [(monic_fam_c₄ a₂ a₃ a₄ a₆).natDegree_pow, natDegree_fam_c₄]
  apply h1.sub_of_left
  have hq : (C β * (fam a₂ a₃ a₄ a₆).Δ).natDegree ≤ 6 :=
    (natDegree_C_mul_le _ _).trans (natDegree_fam_Δ_le a₂ a₃ a₄ a₆)
  calc (C β * (fam a₂ a₃ a₄ a₆).Δ).degree ≤ (6 : ℕ) := natDegree_le_iff_degree_le.mp hq
    _ < (12 : ℕ) := by exact_mod_cast (by norm_num : (6 : ℕ) < 12)
    _ = ((fam a₂ a₃ a₄ a₆).c₄ ^ 3).degree := by rw [degree_eq_natDegree h1.ne_zero, h2]

theorem natDegree_G [Nontrivial R] (β a₂ a₃ a₄ a₆ : R) : (G β a₂ a₃ a₄ a₆).natDegree = 12 := by
  have h1 : ((fam a₂ a₃ a₄ a₆).c₄ ^ 3).Monic := (monic_fam_c₄ a₂ a₃ a₄ a₆).pow 3
  have h2 : ((fam a₂ a₃ a₄ a₆).c₄ ^ 3).natDegree = 12 := by
    rw [(monic_fam_c₄ a₂ a₃ a₄ a₆).natDegree_pow, natDegree_fam_c₄]
  have hq : (C β * (fam a₂ a₃ a₄ a₆).Δ).natDegree ≤ 6 :=
    (natDegree_C_mul_le _ _).trans (natDegree_fam_Δ_le a₂ a₃ a₄ a₆)
  rw [G, natDegree_sub_eq_left_of_natDegree_lt (by omega), h2]

theorem G_map {S : Type*} [CommRing S] (f : R →+* S) (β a₂ a₃ a₄ a₆ : R) :
    (G β a₂ a₃ a₄ a₆).map f = G (f β) (f a₂) (f a₃) (f a₄) (f a₆) := by
  simp only [G, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_C]
  rw [← coe_mapRingHom, ← WeierstrassCurve.map_c₄, ← WeierstrassCurve.map_Δ, fam_map_map]

theorem G_eval (β a₂ a₃ a₄ a₆ r : R) :
    (G β a₂ a₃ a₄ a₆).eval r =
      (⟨r, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve R).c₄ ^ 3 - β * (⟨r, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve R).Δ := by
  simp only [G, eval_sub, eval_mul, eval_pow, eval_C]
  rw [← coe_evalRingHom, ← WeierstrassCurve.map_c₄, ← WeierstrassCurve.map_Δ, fam_map_eval]

section Valuation

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem exists_coe_eq_of_monic_of_isRoot {P : A[X]} (hP : P.Monic) {z : L}
    (hz : (P.map A.subtype).IsRoot z) : ∃ a : A, (a : L) = z := by
  have hint : _root_.IsIntegral A z := ⟨P, hP, by rwa [IsRoot.def, eval_map] at hz⟩
  exact IsIntegrallyClosed.isIntegral_iff.mp hint

theorem exists_multiset_eq_prod [IsAlgClosed L] {P : A[X]} (hP : P.Monic) :
    ∃ s : Multiset A, P = (s.map fun a => X - C a).prod := by
  classical
  have hsplit : (P.map A.subtype).Splits := IsAlgClosed.splits _
  have hmon : (P.map A.subtype).Monic := hP.map _
  have hprod := hsplit.eq_prod_roots_of_monic hmon

  have hroots : ∀ z ∈ (P.map A.subtype).roots, ∃ a : A, (a : L) = z := fun z hz =>
    exists_coe_eq_of_monic_of_isRoot A hP ((mem_roots hmon.ne_zero).mp hz)
  choose f hf using hroots
  refine ⟨(P.map A.subtype).roots.attach.map fun z => f z.1 z.2, ?_⟩
  apply Polynomial.map_injective A.subtype Subtype.coe_injective
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  conv_lhs => rw [hprod]
  congr 1
  have h1 : Multiset.map ((Polynomial.map A.subtype ∘ fun a : A => X - C a) ∘ fun z => f z.1 z.2)
      (P.map A.subtype).roots.attach =
      Multiset.map ((fun x : L => X - C x) ∘ Subtype.val) (P.map A.subtype).roots.attach :=
    Multiset.map_congr rfl fun z _ => by simp [hf]
  rw [h1, ← Multiset.map_map, Multiset.attach_map_val]

end Valuation

theorem j_mul_Δ_eq {F : Type*} [Field F] (V : WeierstrassCurve F) [V.IsElliptic] :
    V.j * V.Δ = V.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← V.coe_Δ', mul_comm ((↑V.Δ'⁻¹ : F)) _, mul_assoc, Units.inv_mul, mul_one]

theorem exists_model {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (W : WeierstrassCurve (ResidueField A)) [W.IsElliptic]
    (β : A) (hres : residue A β = W.j) :
    ∃ (E : WeierstrassCurve A) (_ : (E.map A.subtype).IsElliptic),
      E.map (residue A) = W ∧ (E.map A.subtype).j = (β : L) := by
  classical

  obtain ⟨a₂, ha₂⟩ := residue_surjective W.a₂
  obtain ⟨a₃, ha₃⟩ := residue_surjective W.a₃
  obtain ⟨a₄, ha₄⟩ := residue_surjective W.a₄
  obtain ⟨a₆, ha₆⟩ := residue_surjective W.a₆

  obtain ⟨s, hs⟩ := exists_multiset_eq_prod A (monic_G β a₂ a₃ a₄ a₆)

  have hred : ((G β a₂ a₃ a₄ a₆).map (residue A)).eval W.a₁ = 0 := by
    rw [G_map, G_eval, ha₂, ha₃, ha₄, ha₆, hres]
    have hW : (⟨W.a₁, W.a₂, W.a₃, W.a₄, W.a₆⟩ : WeierstrassCurve (ResidueField A)) = W := rfl
    rw [hW, ← j_mul_Δ_eq W, sub_self]

  rw [hs, Polynomial.map_multiset_prod, Multiset.map_map, eval_multiset_prod, Multiset.map_map,
    Multiset.prod_eq_zero_iff, Multiset.mem_map] at hred
  obtain ⟨r, hr, hr0⟩ := hred
  simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C, eval_sub, eval_X, eval_C,
    sub_eq_zero] at hr0

  set E : WeierstrassCurve A := ⟨r, a₂, a₃, a₄, a₆⟩ with hE
  have hEred : E.map (residue A) = W := by
    rw [hE]
    ext <;> simp [WeierstrassCurve.map, hr0, ha₂, ha₃, ha₄, ha₆]

  have hGr : (G β a₂ a₃ a₄ a₆).eval r = 0 := by
    rw [hs, eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff, Multiset.mem_map]
    exact ⟨r, hr, by simp⟩
  rw [G_eval] at hGr
  have hc4 : E.c₄ ^ 3 = β * E.Δ := sub_eq_zero.mp hGr

  have hΔres : residue A E.Δ = W.Δ := by
    rw [← hEred, WeierstrassCurve.map_Δ]
  have hΔunit : IsUnit E.Δ := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hΔres]
    exact W.isUnit_Δ.ne_zero
  have hΔL : (E.map A.subtype).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    intro h0
    have : E.Δ = 0 := Subtype.ext (by simpa using h0)
    exact hΔunit.ne_zero this
  haveI hEll : (E.map A.subtype).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔL⟩
  refine ⟨E, hEll, hEred, ?_⟩

  have hc4L : (E.map A.subtype).c₄ ^ 3 = (β : L) * (E.map A.subtype).Δ := by
    rw [WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ]
    have := congrArg (fun x : A => (x : L)) hc4
    simpa using this
  have hj := j_mul_Δ_eq (E.map A.subtype)
  rw [hc4L] at hj
  exact mul_right_cancel₀ hΔL hj

end WeierstrassCurve.LiftJ

theorem solution {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) (W : WeierstrassCurve (IsLocalRing.ResidueField A)) [W.IsElliptic] (β : A) (hres : IsLocalRing.residue A β = W.j) : ∃ (E : WeierstrassCurve A) (_ : (E.map A.subtype).IsElliptic), E.map (IsLocalRing.residue A) = W ∧ (E.map A.subtype).j = (β : L) :=
  WeierstrassCurve.LiftJ.exists_model A W β hres

end S_WeierstrassCurve_exists_map_residue_eq_and_map_subtype_j_eq
end P2MW
export P2MW.S_WeierstrassCurve_exists_map_residue_eq_and_map_subtype_j_eq (solution)
