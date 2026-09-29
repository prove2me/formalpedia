-- Prove2me | solution 1 for TwoChartCech.finrank_H0_sub_finrank_H1_gluedLinesSections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1e0ecc83-842a-57a3-830b-44d17e44fed2

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import Theorems.Thm_TwoChartCech_finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

p2m_open "TwoChartCech P2MW.S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections.TwoChartCech LaurentPolynomial"

universe u v

namespace TwoChartCech
p2m_export "TwoChartCech" "levalUnit polyPart invPolyPart mem_invPolyPart_iff GluedCond gluedLinesM01 gluedLinesM0 gluedLinesM1 gluedLinesSections Sections Sections.cechDiff_apply finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1"
p2m_open "TwoChartCech"
namespace GluedLinesMain

variable {k : Type u} [Field k] {s : ℕ}

theorem T_eq_single (j : ℤ) : (T j : k[T;T⁻¹]) = AddMonoidAlgebra.single j 1 := rfl

theorem support_mul_T (f : k[T;T⁻¹]) (j : ℤ) :
    (f * T j).coeff.support = f.coeff.support.map (addRightEmbedding j) := by
  rw [T_eq_single]
  exact AddMonoidAlgebra.support_coeff_mul_single (k := k) (G := ℤ) f (1 : k) (fun y => by simp) j

theorem mul_T_mem_invPolyPart_iff (f : k[T;T⁻¹]) (j : ℤ) :
    f * T j ∈ invPolyPart k ↔ ∀ n ∈ f.coeff.support, n + j ≤ 0 := by
  rw [mem_invPolyPart_iff, support_mul_T]
  constructor
  · intro h n hn
    exact h (n + j) (Finset.mem_map_of_mem _ hn)
  · intro h n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hn
    exact h m hm

theorem toLaurent_mem_polyPart (p : Polynomial k) : Polynomial.toLaurent p ∈ polyPart k := by
  intro n hn
  rw [LaurentPolynomial.support_coeff_toLaurent] at hn
  obtain ⟨m, -, rfl⟩ := Finset.mem_map.mp hn
  exact Int.natCast_nonneg m

theorem toLaurent_trunc_apply (f : k[T;T⁻¹]) (n : ℤ) :
    (Polynomial.toLaurent (LaurentPolynomial.trunc f)).coeff n = if 0 ≤ n then f.coeff n else 0 := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [hp, hq]
    split_ifs
    · rfl
    · exact add_zero 0
  | C_mul_T m r =>
    rw [LaurentPolynomial.trunc_C_mul_T]
    have hcoef : ∀ j : ℤ, (LaurentPolynomial.C r * T m : k[T;T⁻¹]).coeff j = if m = j then r else 0 := fun j => by
      rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]; exact Finsupp.single_apply
    split_ifs with hm hn hn
    · rw [Polynomial.toLaurent_C_mul_T, Int.toNat_of_nonneg hm, hcoef]
    · rw [Polynomial.toLaurent_C_mul_T, Int.toNat_of_nonneg hm, hcoef, if_neg]
      rintro rfl; exact hn hm
    · rw [map_zero, hcoef, if_neg]
      · rfl
      · rintro rfl; exact hm hn
    · rw [map_zero]; rfl

theorem toLaurent_trunc_of_mem_polyPart {f : k[T;T⁻¹]} (hf : f ∈ polyPart k) :
    Polynomial.toLaurent (LaurentPolynomial.trunc f) = f := by
  apply LaurentPolynomial.ext
  intro n
  rw [toLaurent_trunc_apply]
  split_ifs with h
  · rfl
  · symm
    by_contra hne
    exact h (hf n (Finsupp.mem_support_iff.mpr hne))

theorem toLaurent_mul_T_mem_invPolyPart_iff_degree_lt (p : Polynomial k) (d : ℕ) :
    Polynomial.toLaurent p * T (-((d : ℤ) - 1)) ∈ invPolyPart k ↔ p.degree < d := by
  rw [mul_T_mem_invPolyPart_iff, Polynomial.degree_lt_iff_coeff_zero]
  constructor
  · intro h m hm
    by_contra hne
    have hmem : (m : ℤ) ∈ (Polynomial.toLaurent p).coeff.support := by
      rw [LaurentPolynomial.support_coeff_toLaurent]
      exact Finset.mem_map.mpr ⟨m, Polynomial.mem_support_iff.mpr hne, rfl⟩
    have hle := h _ hmem
    omega
  · intro h n hn
    rw [LaurentPolynomial.support_coeff_toLaurent] at hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hn
    have hlt : m < d := lt_of_not_ge fun hge => (Polynomial.mem_support_iff.mp hm) (h m hge)
    change (m : ℤ) + -((d : ℤ) - 1) ≤ 0
    omega

theorem eval_toLaurent (u : kˣ) (p : Polynomial k) : levalUnit k u (Polynomial.toLaurent p) = p.eval (u : k) := by
  rw [levalUnit, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id]

theorem eval_C (u : kˣ) (c : k) : levalUnit k u (LaurentPolynomial.C c) = c := by
  simp [LaurentPolynomial.eval₂_C]

theorem C_mem_polyPart (c : k) : (LaurentPolynomial.C c : k[T;T⁻¹]) ∈ polyPart k := by
  intro n hn
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single] at hn
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hn)]

theorem C_mem_invPolyPart (c : k) : (LaurentPolynomial.C c : k[T;T⁻¹]) ∈ invPolyPart k := by
  intro n hn
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single] at hn
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hn)]

theorem eq_C_of_mem_polyPart_of_mem_invPolyPart {f : k[T;T⁻¹]} (h0 : f ∈ polyPart k) (h1 : f ∈ invPolyPart k) :
    f = LaurentPolynomial.C (f.coeff 0) := by
  apply LaurentPolynomial.ext
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hn)]
    by_contra hne
    have hmem : n ∈ f.coeff.support := Finsupp.mem_support_iff.mpr hne
    exact hn (le_antisymm (h1 n hmem) (h0 n hmem))

noncomputable def lpos (f : k[T;T⁻¹]) : k[T;T⁻¹] := Polynomial.toLaurent (LaurentPolynomial.trunc f)

noncomputable def lneg (f : k[T;T⁻¹]) : k[T;T⁻¹] := f - lpos f

theorem lpos_add_lneg (f : k[T;T⁻¹]) : lpos f + lneg f = f := add_sub_cancel (lpos f) f

theorem lpos_mem_polyPart (f : k[T;T⁻¹]) : lpos f ∈ polyPart k := toLaurent_mem_polyPart _

theorem lneg_mul_T_mem_invPolyPart (f : k[T;T⁻¹]) {j : ℤ} (hj : j ≤ 1) : lneg f * T j ∈ invPolyPart k := by
  rw [mul_T_mem_invPolyPart_iff]
  intro n hn
  have hneg : ¬ 0 ≤ n := fun h0 => by
    apply Finsupp.mem_support_iff.mp hn
    rw [lneg, lpos, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, toLaurent_trunc_apply, if_pos h0, sub_self]
  omega

theorem injOn_val (a : Fin s → kˣ) (ha : Function.Injective a) :
    Set.InjOn (fun i => (a i : k)) ↑(Finset.univ : Finset (Fin s)) :=
  fun _ _ _ _ h => ha (Units.ext h)

variable (a b lam : Fin s → kˣ)

def coeffSnd (n m : ℤ) : ↥(gluedLinesSections k a b lam n m).H0 →ₗ[k] k where
  toFun x := x.1.1.1.2.coeff 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem H0_shape (x : ↥(gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H0) :
    x.1.2.1 = x.1.1.1 ∧
    x.1.1.1.2 = LaurentPolynomial.C (x.1.1.1.2.coeff 0) ∧
    Polynomial.toLaurent (LaurentPolynomial.trunc x.1.1.1.1) = x.1.1.1.1 ∧
    (LaurentPolynomial.trunc x.1.1.1.1).degree < s ∧
    (∀ i, (LaurentPolynomial.trunc x.1.1.1.1).eval (a i : k) = lam i * x.1.1.1.2.coeff 0) := by
  have hH := ((gluedLinesSections k a b lam ((s : ℤ) - 1) 0).mem_H0_iff x.1).mp x.2
  have heq : x.1.2.1 = x.1.1.1 := (congrArg Subtype.val hH).symm
  obtain ⟨hcond, hpoly⟩ := x.1.1.2
  obtain ⟨-, hinv1, hinv2⟩ := x.1.2.2
  rw [heq] at hinv1 hinv2
  rw [neg_zero, LaurentPolynomial.T_zero, mul_one] at hinv2
  obtain ⟨hp1, hp2⟩ := Subalgebra.mem_prod.mp hpoly
  have h2 := eq_C_of_mem_polyPart_of_mem_invPolyPart hp2 hinv2
  have h1 := toLaurent_trunc_of_mem_polyPart hp1
  have hdeg : (LaurentPolynomial.trunc x.1.1.1.1).degree < s := by
    rw [← toLaurent_mul_T_mem_invPolyPart_iff_degree_lt, h1]; exact hinv1
  refine ⟨heq, h2, h1, hdeg, fun i => ?_⟩
  have hc := hcond i
  rw [← h1, h2, eval_toLaurent, eval_C] at hc
  exact hc

theorem coeffSnd_bijective (ha : Function.Injective a) :
    Function.Bijective (coeffSnd a b lam ((s : ℤ) - 1) 0) := by
  classical
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨heq, h2, h1, hdeg, hev⟩ := H0_shape a b lam x
    have hx2 : x.1.1.1.2.coeff 0 = 0 := hx

    have hp0 : LaurentPolynomial.trunc x.1.1.1.1 = 0 :=
      Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ (injOn_val a ha)
        (by simpa using hdeg) (fun i _ => by rw [hev i, hx2, mul_zero])
    have hv : x.1.1.1 = 0 := by
      apply Prod.ext
      · rw [← h1, hp0, map_zero]; rfl
      · rw [h2, hx2, map_zero]; rfl
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext hv
    · exact Subtype.ext (heq.trans hv)
  · intro c

    set p : Polynomial k := Lagrange.interpolate Finset.univ (fun i => (a i : k)) (fun i => (lam i : k) * c) with hp
    have hdeg : p.degree < s := by
      have h := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := fun i => (a i : k))
        (fun i => (lam i : k) * c) (injOn_val a ha)
      rwa [Finset.card_univ, Fintype.card_fin] at h
    have hev : ∀ i, p.eval (a i : k) = lam i * c := fun i =>
      Lagrange.eval_interpolate_at_node _ (injOn_val a ha) (Finset.mem_univ i)
    have hcond : GluedCond a b lam (Polynomial.toLaurent p, LaurentPolynomial.C c) := fun i => by
      change levalUnit k (a i) (Polynomial.toLaurent p) = lam i * levalUnit k (b i) (LaurentPolynomial.C c)
      rw [eval_toLaurent, eval_C, hev]
    let v0 : (gluedLinesSections k a b lam ((s : ℤ) - 1) 0).M0 :=
      ⟨(Polynomial.toLaurent p, LaurentPolynomial.C c), hcond,
        Subalgebra.mem_prod.mpr ⟨toLaurent_mem_polyPart p, C_mem_polyPart c⟩⟩
    let v1 : (gluedLinesSections k a b lam ((s : ℤ) - 1) 0).M1 :=
      ⟨(Polynomial.toLaurent p, LaurentPolynomial.C c), hcond,
        (toLaurent_mul_T_mem_invPolyPart_iff_degree_lt p s).mpr hdeg, by
        rw [neg_zero, LaurentPolynomial.T_zero, mul_one]; exact C_mem_invPolyPart c⟩
    have hmem : (v0, v1) ∈ (gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H0 :=
      ((gluedLinesSections k a b lam ((s : ℤ) - 1) 0).mem_H0_iff (v0, v1)).mpr rfl
    refine ⟨⟨(v0, v1), hmem⟩, ?_⟩
    change (LaurentPolynomial.C c : k[T;T⁻¹]).coeff 0 = c
    rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

theorem cechDiff_surjective (ha : Function.Injective a) :
    Function.Surjective (gluedLinesSections k a b lam ((s : ℤ) - 1) 0).cechDiff := by
  classical
  intro w
  set P := w.1.1 with hP
  set Q := w.1.2 with hQ

  set r : Polynomial k := Lagrange.interpolate Finset.univ (fun i => (a i : k))
    (fun i => levalUnit k (a i) (lpos P) - lam i * levalUnit k (b i) (lpos Q)) with hr
  have hdeg : r.degree < s := by
    have h := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := fun i => (a i : k))
      (fun i => levalUnit k (a i) (lpos P) - lam i * levalUnit k (b i) (lpos Q)) (injOn_val a ha)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hev : ∀ i, r.eval (a i : k) = levalUnit k (a i) (lpos P) - lam i * levalUnit k (b i) (lpos Q) :=
    fun i => Lagrange.eval_interpolate_at_node _ (injOn_val a ha) (Finset.mem_univ i)

  set u : k[T;T⁻¹] × k[T;T⁻¹] := (-lpos P + Polynomial.toLaurent r, -lpos Q) with hu
  have hucond : GluedCond a b lam u := fun i => by
    change levalUnit k (a i) (-lpos P + Polynomial.toLaurent r) = lam i * levalUnit k (b i) (-lpos Q)
    rw [map_add, map_neg, map_neg, eval_toLaurent, hev]
    ring
  have hu0 : u ∈ (polyPart k).prod (polyPart k) :=
    Subalgebra.mem_prod.mpr ⟨Subalgebra.add_mem _ (Subalgebra.neg_mem _ (lpos_mem_polyPart P)) (toLaurent_mem_polyPart r),
      Subalgebra.neg_mem _ (lpos_mem_polyPart Q)⟩

  set v : k[T;T⁻¹] × k[T;T⁻¹] := w.1 + u with hv
  have hvcond : GluedCond a b lam v := w.2.add hucond
  have hv1 : v.1 * T (-((s : ℤ) - 1)) ∈ invPolyPart k := by
    have hsplit : v.1 = lneg P + Polynomial.toLaurent r := by
      change P + (-lpos P + Polynomial.toLaurent r) = (P - lpos P) + Polynomial.toLaurent r
      abel
    rw [hsplit, add_mul]
    refine Subalgebra.add_mem _ (lneg_mul_T_mem_invPolyPart P (by omega)) ?_
    exact (toLaurent_mul_T_mem_invPolyPart_iff_degree_lt r s).mpr hdeg
  have hv2 : v.2 * T (-(0 : ℤ)) ∈ invPolyPart k := by
    have hsplit : v.2 = lneg Q := by
      change Q + -lpos Q = Q - lpos Q
      abel
    rw [hsplit, neg_zero]
    simpa using lneg_mul_T_mem_invPolyPart Q (show (0 : ℤ) ≤ 1 by omega)
  refine ⟨(⟨u, hucond, hu0⟩, ⟨v, hvcond, hv1, hv2⟩), ?_⟩
  rw [Sections.cechDiff_apply]
  apply Subtype.ext
  change v - u = w.1
  rw [hv, add_sub_cancel_right]

end GluedLinesMain
end TwoChartCech

namespace TwoChartCech
p2m_export "TwoChartCech" "levalUnit polyPart invPolyPart mem_invPolyPart_iff GluedCond gluedLinesM01 gluedLinesM0 gluedLinesM1 gluedLinesSections Sections Sections.cechDiff_apply finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1"
p2m_open "TwoChartCech"
namespace ChiStep

open Module Submodule

variable {k : Type u} [Field k] {F : Type v} [AddCommGroup F] [Module k F]
variable (A B B' W : Submodule k F)

abbrev Q : Type v := ↥B' ⧸ (B.comap B'.subtype)

def ψ : ↥(A ⊓ B') →ₗ[k] Q B B' := (mkQ _).comp (Submodule.inclusion inf_le_right)

def φbar (hB'W : B' ≤ W) : Q B B' →ₗ[k] ↥W ⧸ ((A ⊔ B).comap W.subtype) :=
  (B.comap B'.subtype).liftQ ((mkQ _).comp (Submodule.inclusion hB'W)) (by
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.comp_apply, mkQ_apply, Quotient.mk_eq_zero, mem_comap]
    exact mem_sup_right hv)

def π (hBB' : B ≤ B') : (↥W ⧸ ((A ⊔ B).comap W.subtype)) →ₗ[k] ↥W ⧸ ((A ⊔ B').comap W.subtype) :=
  Submodule.factor (comap_mono (sup_le_sup_left hBB' A))

theorem ker_ψ : LinearMap.ker (ψ A B B') = (A ⊓ B).comap (A ⊓ B').subtype := by
  ext v
  simp only [ψ, LinearMap.mem_ker, LinearMap.comp_apply, mkQ_apply, Quotient.mk_eq_zero, mem_comap,
    Submodule.subtype_apply, Submodule.coe_inclusion, mem_inf]
  exact ⟨fun h => ⟨v.2.1, h⟩, fun h => h.2⟩

theorem range_ψ_eq_ker_φbar (hBB' : B ≤ B') (hB'W : B' ≤ W) :
    LinearMap.range (ψ A B B') = LinearMap.ker (φbar A B B' W hB'W) := by
  ext q
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    simp only [LinearMap.mem_range, LinearMap.mem_ker, φbar, liftQ_apply, LinearMap.comp_apply, mkQ_apply,
      Quotient.mk_eq_zero, mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion]
    constructor
    · rintro ⟨w, hw⟩

      have hvw : (v : F) - w ∈ B := by
        have := (Submodule.Quotient.eq _).mp hw.symm
        simpa [ψ, mem_comap] using this
      have : (v : F) = w + ((v : F) - w) := by abel
      rw [this]
      exact add_mem (mem_sup_left w.2.1) (mem_sup_right hvw)
    · intro hv
      obtain ⟨a, ha, b, hb, hab⟩ := mem_sup.mp hv
      have haB' : a ∈ B' := by
        have : a = (v : F) - b := by rw [← hab]; abel
        rw [this]; exact sub_mem v.2 (hBB' hb)
      refine ⟨⟨a, ha, haB'⟩, ?_⟩
      simp only [ψ, LinearMap.comp_apply, mkQ_apply]
      apply (Submodule.Quotient.eq _).mpr
      simp only [mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion]
      have : a - (v : F) = -b := by rw [← hab]; abel
      rw [this]; exact neg_mem hb

theorem range_φbar_eq_ker_π (hBB' : B ≤ B') (hB'W : B' ≤ W) :
    LinearMap.range (φbar A B B' W hB'W) = LinearMap.ker (π A B B' W hBB') := by
  ext q
  induction q using Submodule.Quotient.induction_on with
  | _ w =>
    simp only [LinearMap.mem_range, LinearMap.mem_ker, π, Submodule.factor, mapQ_apply, LinearMap.id_apply,
      Quotient.mk_eq_zero, mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with
      | _ v =>
        simp only [φbar, liftQ_apply, LinearMap.comp_apply, mkQ_apply] at hq
        have hvw : (v : F) - w ∈ A ⊔ B := by
          have := (Submodule.Quotient.eq _).mp hq
          simpa [mem_comap] using this
        have : (w : F) = v - ((v : F) - w) := by abel
        rw [this]
        exact sub_mem (mem_sup_right v.2) (sup_le_sup_left hBB' A hvw)
    · intro hw
      obtain ⟨a, ha, b, hb, hab⟩ := mem_sup.mp hw
      refine ⟨Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
      simp only [φbar, liftQ_apply, LinearMap.comp_apply, mkQ_apply]
      apply (Submodule.Quotient.eq _).mpr
      simp only [mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion]
      have : b - (w : F) = -a := by rw [← hab]; abel
      rw [this]; exact neg_mem (mem_sup_left ha)

theorem finite_forward (hBB' : B ≤ B') (hB'W : B' ≤ W) (hcodim : Module.finrank k (Q B B') = 1)
    [Module.Finite k ↥(A ⊓ B)] [Module.Finite k (↥W ⧸ ((A ⊔ B).comap W.subtype))] :
    Module.Finite k ↥(A ⊓ B') ∧ Module.Finite k (↥W ⧸ ((A ⊔ B').comap W.subtype)) := by
  haveI : Module.Finite k (Q B B') := Module.finite_of_finrank_eq_succ hcodim
  haveI hfinK : Module.Finite k ↥(LinearMap.ker (ψ A B B')) := by
    rw [ker_ψ]
    exact Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (inf_le_inf_left A hBB')).symm
  haveI : Module.Finite k (↥(A ⊓ B') ⧸ LinearMap.ker (ψ A B B')) :=
    Module.Finite.equiv (LinearMap.quotKerEquivRange (ψ A B B')).symm
  exact ⟨Module.Finite.of_submodule_quotient (LinearMap.ker (ψ A B B')),
    Module.Finite.of_surjective (π A B B' W hBB') (Submodule.factor_surjective (comap_mono (sup_le_sup_left hBB' A)))⟩

theorem finite_backward (hBB' : B ≤ B') (hB'W : B' ≤ W) (hcodim : Module.finrank k (Q B B') = 1)
    [Module.Finite k ↥(A ⊓ B')] [Module.Finite k (↥W ⧸ ((A ⊔ B').comap W.subtype))] :
    Module.Finite k ↥(A ⊓ B) ∧ Module.Finite k (↥W ⧸ ((A ⊔ B).comap W.subtype)) := by
  haveI : Module.Finite k (Q B B') := Module.finite_of_finrank_eq_succ hcodim
  refine ⟨Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (inf_le_inf_left A hBB'))
      (M := ↥((A ⊓ B).comap (A ⊓ B').subtype)), ?_⟩

  haveI hker : Module.Finite k ↥(LinearMap.ker (π A B B' W hBB')) := by
    rw [← range_φbar_eq_ker_π A B B' W hBB' hB'W]
    exact Module.Finite.range (φbar A B B' W hB'W)
  haveI : Module.Finite k ((↥W ⧸ ((A ⊔ B).comap W.subtype)) ⧸ LinearMap.ker (π A B B' W hBB')) :=
    Module.Finite.equiv
      (LinearMap.quotKerEquivOfSurjective (π A B B' W hBB')
        (Submodule.factor_surjective (comap_mono (sup_le_sup_left hBB' A)))).symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (π A B B' W hBB'))

theorem finrank_step (hBB' : B ≤ B') (hB'W : B' ≤ W) (hcodim : Module.finrank k (Q B B') = 1)
    [Module.Finite k ↥(A ⊓ B)] [Module.Finite k (↥W ⧸ ((A ⊔ B).comap W.subtype))]
    [Module.Finite k ↥(A ⊓ B')] [Module.Finite k (↥W ⧸ ((A ⊔ B').comap W.subtype))] :
    (Module.finrank k ↥(A ⊓ B') : ℤ) - Module.finrank k (↥W ⧸ ((A ⊔ B').comap W.subtype)) =
      (Module.finrank k ↥(A ⊓ B) : ℤ) - Module.finrank k (↥W ⧸ ((A ⊔ B).comap W.subtype)) + 1 := by
  haveI : Module.Finite k (Q B B') := Module.finite_of_finrank_eq_succ hcodim
  have h1 := LinearMap.finrank_range_add_finrank_ker (ψ A B B')
  have h2 := LinearMap.finrank_range_add_finrank_ker (φbar A B B' W hB'W)
  have h3 := LinearMap.finrank_range_add_finrank_ker (π A B B' W hBB')
  rw [hcodim] at h2
  have hkψ : Module.finrank k ↥(LinearMap.ker (ψ A B B')) = Module.finrank k ↥(A ⊓ B) := by
    rw [ker_ψ]; exact (Submodule.comapSubtypeEquivOfLe (inf_le_inf_left A hBB')).finrank_eq
  have hrψ : Module.finrank k ↥(LinearMap.range (ψ A B B')) = Module.finrank k ↥(LinearMap.ker (φbar A B B' W hB'W)) := by
    rw [range_ψ_eq_ker_φbar A B B' W hBB' hB'W]
  have hrφ : Module.finrank k ↥(LinearMap.range (φbar A B B' W hB'W)) =
      Module.finrank k ↥(LinearMap.ker (π A B B' W hBB')) := by
    rw [range_φbar_eq_ker_π A B B' W hBB' hB'W]
  have hrπ : Module.finrank k ↥(LinearMap.range (π A B B' W hBB')) =
      Module.finrank k (↥W ⧸ ((A ⊔ B').comap W.subtype)) := by
    have hsurj : Function.Surjective (π A B B' W hBB') := Submodule.factor_surjective (comap_mono (sup_le_sup_left hBB' A))
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
  omega

end ChiStep
end TwoChartCech

noncomputable section

namespace TwoChartCech
p2m_export "TwoChartCech" "levalUnit polyPart invPolyPart mem_invPolyPart_iff GluedCond gluedLinesM01 gluedLinesM0 gluedLinesM1 gluedLinesSections Sections Sections.cechDiff_apply finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1"
p2m_open "TwoChartCech"
namespace GluedLinesChi

open Module Submodule

variable {k : Type u} [Field k] {s : ℕ} (a b lam : Fin s → kˣ)

abbrev Amb (k : Type u) [Field k] : Type u := k[T;T⁻¹] × k[T;T⁻¹]

def Asub : Submodule k (Amb k) := (gluedLinesM0 k a b lam).restrictScalars k

def Bsub (n m : ℤ) : Submodule k (Amb k) := (gluedLinesM1 k a b lam n m).restrictScalars k

def Wsub : Submodule k (Amb k) := (gluedLinesM01 k a b lam).restrictScalars k

theorem A_le_W : Asub a b lam ≤ Wsub a b lam := fun _ hv => hv.1
theorem B_le_W (n m : ℤ) : Bsub a b lam n m ≤ Wsub a b lam := fun _ hv => hv.1

theorem mul_T_mem_invPolyPart_mono {f : k[T;T⁻¹]} {j j' : ℤ} (hj : j' ≤ j) (h : f * T j ∈ invPolyPart k) :
    f * T j' ∈ invPolyPart k := by
  rw [GluedLinesMain.mul_T_mem_invPolyPart_iff] at h ⊢
  intro n hn; have := h n hn; omega

theorem B_mono_fst (n m : ℤ) : Bsub a b lam (n - 1) m ≤ Bsub a b lam n m :=
  fun _ hv => ⟨hv.1, mul_T_mem_invPolyPart_mono (by omega) hv.2.1, hv.2.2⟩

theorem B_mono_snd (n m : ℤ) : Bsub a b lam n (m - 1) ≤ Bsub a b lam n m :=
  fun _ hv => ⟨hv.1, hv.2.1, mul_T_mem_invPolyPart_mono (by omega) hv.2.2⟩

def H0equiv (n m : ℤ) : ↥(gluedLinesSections k a b lam n m).H0 ≃ₗ[k] ↥(Asub a b lam ⊓ Bsub a b lam n m) where
  toFun x := ⟨x.1.1.1, x.1.1.2, by
    have hH := ((gluedLinesSections k a b lam n m).mem_H0_iff x.1).mp x.2
    have heq : x.1.2.1 = x.1.1.1 := (congrArg Subtype.val hH).symm
    rw [← heq]; exact x.1.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨(⟨v.1, v.2.1⟩, ⟨v.1, v.2.2⟩), ((gluedLinesSections k a b lam n m).mem_H0_iff _).mpr rfl⟩
  left_inv x := by
    have hH := ((gluedLinesSections k a b lam n m).mem_H0_iff x.1).mp x.2
    have heq : x.1.2.1 = x.1.1.1 := (congrArg Subtype.val hH).symm
    apply Subtype.ext; apply Prod.ext
    · rfl
    · exact Subtype.ext heq.symm
  right_inv v := rfl

def M01equiv : (gluedLinesSections k a b lam 0 0).M01 ≃ₗ[k] ↥(Wsub a b lam) where
  toFun w := ⟨w.1, w.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨w.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem map_range_cechDiff (n m : ℤ) :
    (LinearMap.range (gluedLinesSections k a b lam n m).cechDiff).map (M01equiv a b lam).toLinearMap =
      (Asub a b lam ⊔ Bsub a b lam n m).comap (Wsub a b lam).subtype := by
  ext w
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_comap, Submodule.subtype_apply,
    LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, ⟨⟨u, v⟩, rfl⟩, rfl⟩
    rw [Sections.cechDiff_apply]
    change (v.1 - u.1 : Amb k) ∈ Asub a b lam ⊔ Bsub a b lam n m
    rw [sub_eq_add_neg]
    exact add_mem (mem_sup_right v.2) (mem_sup_left (neg_mem u.2))
  · intro hw
    obtain ⟨u, hu, v, hv, huv⟩ := mem_sup.mp hw
    refine ⟨⟨w.1, w.2⟩, ⟨(⟨-u, neg_mem (show u ∈ gluedLinesM0 k a b lam from hu)⟩, ⟨v, hv⟩), ?_⟩, rfl⟩
    rw [Sections.cechDiff_apply]
    apply Subtype.ext
    change v - -u = (w : Amb k)
    rw [sub_neg_eq_add, add_comm]; exact huv

def H1equiv (n m : ℤ) :
    (gluedLinesSections k a b lam n m).H1 ≃ₗ[k] ↥(Wsub a b lam) ⧸ (Asub a b lam ⊔ Bsub a b lam n m).comap (Wsub a b lam).subtype :=
  Submodule.Quotient.equiv _ _ (M01equiv a b lam) (map_range_cechDiff a b lam n m)

end GluedLinesChi
end TwoChartCech

end

noncomputable section

namespace TwoChartCech
p2m_export "TwoChartCech" "levalUnit polyPart invPolyPart mem_invPolyPart_iff GluedCond gluedLinesM01 gluedLinesM0 gluedLinesM1 gluedLinesSections Sections Sections.cechDiff_apply finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1"
p2m_open "TwoChartCech"
namespace GluedLinesChi

open Module Submodule GluedLinesMain

variable {k : Type u} [Field k] {s : ℕ}

theorem levalUnit_invert (u : kˣ) (f : k[T;T⁻¹]) :
    levalUnit k u (LaurentPolynomial.invert f) = levalUnit k u⁻¹ f := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | C_mul_T n c =>
    have hinv : LaurentPolynomial.invert (LaurentPolynomial.C c * T n : k[T;T⁻¹]) = LaurentPolynomial.C c * T (-n) := by
      simp
    rw [hinv, levalUnit, LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.eval₂_C_mul_T, inv_zpow']

theorem mul_T_apply (f : k[T;T⁻¹]) (j m : ℤ) : (f * T j : k[T;T⁻¹]).coeff m = f.coeff (m - j) := by
  rw [T_eq_single, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, sub_eq_add_neg]

theorem T_apply_self (j : ℤ) : (T j : k[T;T⁻¹]).coeff j = 1 := by
  rw [T_eq_single, AddMonoidAlgebra.coeff_single]; exact Finsupp.single_eq_same

theorem toLaurent_apply_neg (r : Polynomial k) {j : ℤ} (hj : j < 0) : (Polynomial.toLaurent r).coeff j = 0 := by
  by_contra hne
  have := toLaurent_mem_polyPart r j (Finsupp.mem_support_iff.mpr hne)
  omega

theorem exists_laurent_eval_eq (a : Fin s → kˣ) (ha : Function.Injective a) (n : ℤ) (t : Fin s → k) :
    ∃ p : k[T;T⁻¹], p * T (-(n - 1)) ∈ invPolyPart k ∧ p.coeff n = 0 ∧ ∀ i, levalUnit k (a i) p = t i := by
  classical
  have hInj : Set.InjOn (fun i => (((a i)⁻¹ : kˣ) : k)) ↑(Finset.univ : Finset (Fin s)) :=
    fun i _ j _ h => ha (inv_injective (Units.ext h))
  set r : Polynomial k := Lagrange.interpolate Finset.univ (fun i => (((a i)⁻¹ : kˣ) : k))
    (fun i => t i * ((a i ^ (1 - n) : kˣ) : k)) with hr
  have hev : ∀ i, r.eval (((a i)⁻¹ : kˣ) : k) = t i * ((a i ^ (1 - n) : kˣ) : k) := fun i =>
    Lagrange.eval_interpolate_at_node _ hInj (Finset.mem_univ i)
  refine ⟨T (n - 1) * LaurentPolynomial.invert (Polynomial.toLaurent r), ?_, ?_, ?_⟩
  · rw [mul_comm (T (n - 1)), mul_assoc, ← T_add, show (n - 1) + -(n - 1) = 0 by ring, T_zero, mul_one]
    intro j hj
    have hne : (LaurentPolynomial.invert (Polynomial.toLaurent r)).coeff j ≠ 0 := Finsupp.mem_support_iff.mp hj
    rw [LaurentPolynomial.invert_apply] at hne
    have := toLaurent_mem_polyPart r (-j) (Finsupp.mem_support_iff.mpr hne)
    omega
  · rw [mul_comm, mul_T_apply, LaurentPolynomial.invert_apply]
    exact toLaurent_apply_neg r (by omega)
  · intro i
    rw [map_mul, levalUnit_invert, eval_toLaurent, hev i]
    change LaurentPolynomial.eval₂ (RingHom.id k) (a i) (T (n - 1)) * _ = _
    rw [LaurentPolynomial.eval₂_T]
    have hu : ((a i ^ (n - 1) : kˣ) : k) * ((a i ^ (1 - n) : kˣ) : k) = 1 := by
      rw [← Units.val_mul, ← zpow_add, show n - 1 + (1 - n) = 0 by ring, zpow_zero, Units.val_one]
    linear_combination (t i) * hu

variable (a b lam : Fin s → kˣ)

def lead (n m : ℤ) : ↥(Bsub a b lam n m) →ₗ[k] k where
  toFun v := v.1.1.coeff n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_lead (n m : ℤ) : LinearMap.ker (lead a b lam n m) = (Bsub a b lam (n - 1) m).comap (Bsub a b lam n m).subtype := by
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  change v.1.1.coeff n = 0 ↔ (v : Amb k) ∈ gluedLinesM1 k a b lam (n - 1) m
  obtain ⟨hcond, h1, h2⟩ := v.2
  rw [mul_T_mem_invPolyPart_iff] at h1
  constructor
  · intro h0
    refine ⟨hcond, ?_, h2⟩
    rw [mul_T_mem_invPolyPart_iff]
    intro j hj
    have hle := h1 j hj
    have hne : j ≠ n := fun hjn => (Finsupp.mem_support_iff.mp hj) (hjn ▸ h0)
    omega
  · rintro ⟨-, h1', -⟩
    rw [mul_T_mem_invPolyPart_iff] at h1'
    by_contra hne
    have := h1' n (Finsupp.mem_support_iff.mpr hne)
    omega

theorem lead_surjective (ha : Function.Injective a) (n m : ℤ) : Function.Surjective (lead a b lam n m) := by
  obtain ⟨p, hp, hp0, hpev⟩ := exists_laurent_eval_eq a ha n (fun i => -((a i ^ n : kˣ) : k))
  have hcond : GluedCond a b lam (T n + p, 0) := fun i => by
    change levalUnit k (a i) (T n + p) = lam i * levalUnit k (b i) 0
    rw [map_add, map_zero, mul_zero, hpev]
    change LaurentPolynomial.eval₂ (RingHom.id k) (a i) (T n) + _ = 0
    rw [LaurentPolynomial.eval₂_T, add_neg_cancel]
  have hmem : ((T n + p, 0) : Amb k) ∈ Bsub a b lam n m := by
    refine ⟨hcond, ?_, ?_⟩
    · change (T n + p) * T (-n) ∈ invPolyPart k
      rw [add_mul, ← T_add, add_neg_cancel, T_zero]
      exact Subalgebra.add_mem _ (Subalgebra.one_mem _) (mul_T_mem_invPolyPart_mono (by omega) hp)
    · change (0 : k[T;T⁻¹]) * T (-m) ∈ invPolyPart k
      rw [zero_mul]; exact Subalgebra.zero_mem _
  have hlead : lead a b lam n m ⟨_, hmem⟩ = 1 := by
    change (T n + p : k[T;T⁻¹]).coeff n = 1
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp0, add_zero, T_apply_self]
  intro c
  exact ⟨c • ⟨_, hmem⟩, by rw [map_smul, hlead, smul_eq_mul, mul_one]⟩

theorem codim_fst (ha : Function.Injective a) (n m : ℤ) :
    Module.finrank k (↥(Bsub a b lam n m) ⧸ (Bsub a b lam (n - 1) m).comap (Bsub a b lam n m).subtype) = 1 := by
  rw [← ker_lead]
  exact ((lead a b lam n m).quotKerEquivOfSurjective (lead_surjective a b lam ha n m)).finrank_eq.trans
    (Module.finrank_self k)

def lead₂ (n m : ℤ) : ↥(Bsub a b lam n m) →ₗ[k] k where
  toFun v := v.1.2.coeff m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_lead₂ (n m : ℤ) : LinearMap.ker (lead₂ a b lam n m) = (Bsub a b lam n (m - 1)).comap (Bsub a b lam n m).subtype := by
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  change v.1.2.coeff m = 0 ↔ (v : Amb k) ∈ gluedLinesM1 k a b lam n (m - 1)
  obtain ⟨hcond, h1, h2⟩ := v.2
  rw [mul_T_mem_invPolyPart_iff] at h2
  constructor
  · intro h0
    refine ⟨hcond, h1, ?_⟩
    rw [mul_T_mem_invPolyPart_iff]
    intro j hj
    have hle := h2 j hj
    have hne : j ≠ m := fun hjm => (Finsupp.mem_support_iff.mp hj) (hjm ▸ h0)
    omega
  · rintro ⟨-, -, h2'⟩
    rw [mul_T_mem_invPolyPart_iff] at h2'
    by_contra hne
    have := h2' m (Finsupp.mem_support_iff.mpr hne)
    omega

theorem lead₂_surjective (ha : Function.Injective a) (n m : ℤ) : Function.Surjective (lead₂ a b lam n m) := by
  obtain ⟨p, hp, -, hpev⟩ := exists_laurent_eval_eq a ha n (fun i => lam i * ((b i ^ m : kˣ) : k))
  have hcond : GluedCond a b lam (p, T m) := fun i => by
    change levalUnit k (a i) p = lam i * levalUnit k (b i) (T m)
    rw [hpev]
    change _ = (lam i : k) * LaurentPolynomial.eval₂ (RingHom.id k) (b i) (T m)
    rw [LaurentPolynomial.eval₂_T]
  have hmem : ((p, T m) : Amb k) ∈ Bsub a b lam n m := by
    refine ⟨hcond, mul_T_mem_invPolyPart_mono (by omega) hp, ?_⟩
    change T m * T (-m) ∈ invPolyPart k
    rw [← T_add, add_neg_cancel, T_zero]; exact Subalgebra.one_mem _
  have hlead : lead₂ a b lam n m ⟨_, hmem⟩ = 1 := T_apply_self m
  intro c
  exact ⟨c • ⟨_, hmem⟩, by rw [map_smul, hlead, smul_eq_mul, mul_one]⟩

theorem codim_snd (ha : Function.Injective a) (n m : ℤ) :
    Module.finrank k (↥(Bsub a b lam n m) ⧸ (Bsub a b lam n (m - 1)).comap (Bsub a b lam n m).subtype) = 1 := by
  rw [← ker_lead₂]
  exact ((lead₂ a b lam n m).quotKerEquivOfSurjective (lead₂_surjective a b lam ha n m)).finrank_eq.trans
    (Module.finrank_self k)

def Claim (n m : ℤ) : Prop :=
  Module.Finite k ↥(Asub a b lam ⊓ Bsub a b lam n m) ∧
  Module.Finite k (↥(Wsub a b lam) ⧸ (Asub a b lam ⊔ Bsub a b lam n m).comap (Wsub a b lam).subtype) ∧
  (Module.finrank k ↥(Asub a b lam ⊓ Bsub a b lam n m) : ℤ)
    - Module.finrank k (↥(Wsub a b lam) ⧸ (Asub a b lam ⊔ Bsub a b lam n m).comap (Wsub a b lam).subtype) = n + m + 2 - s

theorem claim_step_fst (ha : Function.Injective a) (n m : ℤ) : Claim a b lam (n - 1) m ↔ Claim a b lam n m := by
  have hBB' := B_mono_fst a b lam n m
  have hB'W := B_le_W a b lam n m
  have hcod := codim_fst a b lam ha n m
  constructor
  · rintro ⟨hf0, hf1, hχ⟩
    haveI := hf0; haveI := hf1
    obtain ⟨hf0', hf1'⟩ := ChiStep.finite_forward (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    haveI := hf0'; haveI := hf1'
    refine ⟨hf0', hf1', ?_⟩
    have := ChiStep.finrank_step (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    omega
  · rintro ⟨hf0', hf1', hχ⟩
    haveI := hf0'; haveI := hf1'
    obtain ⟨hf0, hf1⟩ := ChiStep.finite_backward (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    haveI := hf0; haveI := hf1
    refine ⟨hf0, hf1, ?_⟩
    have := ChiStep.finrank_step (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    omega

theorem claim_step_snd (ha : Function.Injective a) (n m : ℤ) : Claim a b lam n (m - 1) ↔ Claim a b lam n m := by
  have hBB' := B_mono_snd a b lam n m
  have hB'W := B_le_W a b lam n m
  have hcod := codim_snd a b lam ha n m
  constructor
  · rintro ⟨hf0, hf1, hχ⟩
    haveI := hf0; haveI := hf1
    obtain ⟨hf0', hf1'⟩ := ChiStep.finite_forward (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    haveI := hf0'; haveI := hf1'
    refine ⟨hf0', hf1', ?_⟩
    have := ChiStep.finrank_step (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    omega
  · rintro ⟨hf0', hf1', hχ⟩
    haveI := hf0'; haveI := hf1'
    obtain ⟨hf0, hf1⟩ := ChiStep.finite_backward (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    haveI := hf0; haveI := hf1
    refine ⟨hf0, hf1, ?_⟩
    have := ChiStep.finrank_step (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    omega

theorem claim_base (ha : Function.Injective a)
    (hmain : Module.finrank k ↥(gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H0 = 1 ∧
      Subsingleton (gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H1) :
    Claim a b lam ((s : ℤ) - 1) 0 := by
  obtain ⟨h0, h1⟩ := hmain
  have e0 := H0equiv a b lam ((s : ℤ) - 1) 0
  have e1 := H1equiv a b lam ((s : ℤ) - 1) 0
  have hr0 : Module.finrank k ↥(Asub a b lam ⊓ Bsub a b lam ((s : ℤ) - 1) 0) = 1 := by rw [← e0.finrank_eq, h0]
  haveI : Subsingleton (↥(Wsub a b lam) ⧸ (Asub a b lam ⊔ Bsub a b lam ((s : ℤ) - 1) 0).comap (Wsub a b lam).subtype) :=
    e1.symm.toEquiv.subsingleton
  refine ⟨Module.finite_of_finrank_eq_succ hr0, Module.Finite.of_finite, ?_⟩
  rw [hr0, Module.finrank_zero_of_subsingleton]
  push_cast
  ring

theorem claim_all (ha : Function.Injective a)
    (hmain : Module.finrank k ↥(gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H0 = 1 ∧
      Subsingleton (gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H1)
    (n m : ℤ) : Claim a b lam n m := by
  have hbase := claim_base a b lam ha hmain

  have hm : Claim a b lam ((s : ℤ) - 1) m := by
    induction m using Int.induction_on with
    | zero => exact hbase
    | succ j ih => exact (claim_step_snd a b lam ha _ ((j : ℤ) + 1)).mp (by rwa [add_sub_cancel_right])
    | pred j ih => exact (claim_step_snd a b lam ha _ (-(j : ℤ))).mpr ih

  have hd : ∀ d : ℤ, Claim a b lam ((s : ℤ) - 1 + d) m := by
    intro d
    induction d using Int.induction_on with
    | zero => rwa [add_zero]
    | succ j ih =>
      refine (claim_step_fst a b lam ha ((s : ℤ) - 1 + ((j : ℤ) + 1)) m).mp ?_
      rwa [show (s : ℤ) - 1 + ((j : ℤ) + 1) - 1 = (s : ℤ) - 1 + j by ring]
    | pred j ih =>
      have h := (claim_step_fst a b lam ha ((s : ℤ) - 1 + -(j : ℤ)) m).mpr ih
      rwa [show (s : ℤ) - 1 + -(j : ℤ) - 1 = (s : ℤ) - 1 + (-(j : ℤ) - 1) by ring] at h
  have h := hd (n - ((s : ℤ) - 1))
  rwa [show (s : ℤ) - 1 + (n - ((s : ℤ) - 1)) = n by ring] at h

end GluedLinesChi
end TwoChartCech

end

open _root_.TwoChartCech _root_.P2MW.S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections.TwoChartCech TwoChartCech.GluedLinesChi in
theorem solution
    (k : Type u) [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (ha : Function.Injective a) (n m : ℤ) :
    Module.Finite k ↥(gluedLinesSections k a b lam n m).H0 ∧
      Module.Finite k (gluedLinesSections k a b lam n m).H1 ∧
      (Module.finrank k ↥(gluedLinesSections k a b lam n m).H0 : ℤ)
        - Module.finrank k (gluedLinesSections k a b lam n m).H1 = n + m + 2 - s := by
  obtain ⟨hf0, hf1, hχ⟩ := claim_all a b lam ha (TwoChartCech.finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1 k a b lam ha) n m
  haveI := hf0; haveI := hf1
  have e0 := H0equiv a b lam n m
  have e1 := H1equiv a b lam n m
  refine ⟨Module.Finite.equiv e0.symm, Module.Finite.equiv e1.symm, ?_⟩
  rw [e0.finrank_eq, e1.finrank_eq]
  exact hχ

end S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections
end P2MW
export P2MW.S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections (solution)
