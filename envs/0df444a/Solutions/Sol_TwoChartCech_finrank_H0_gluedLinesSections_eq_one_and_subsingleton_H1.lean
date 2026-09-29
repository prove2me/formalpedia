-- Prove2me | solution 1 for TwoChartCech.finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/39797b4c-165b-5e8d-8980-4c1b83a656e4

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

p2m_open "TwoChartCech P2MW.S_TwoChartCech_finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1.TwoChartCech LaurentPolynomial"

universe u

namespace TwoChartCech
p2m_export "TwoChartCech" "levalUnit polyPart invPolyPart mem_invPolyPart_iff GluedCond gluedLinesSections Sections Sections.cechDiff_apply"
p2m_open "TwoChartCech"
namespace GluedLinesMain

variable {k : Type u} [Field k] {s : ℕ}

theorem T_eq_single (j : ℤ) : (T j : k[T;T⁻¹]) = AddMonoidAlgebra.single j 1 := rfl

theorem support_mul_T (f : k[T;T⁻¹]) (j : ℤ) :
    (f * T j).coeff.support = f.coeff.support.map (addRightEmbedding j) := by
  rw [T_eq_single]
  exact AddMonoidAlgebra.support_coeff_mul_single f (1 : k) (fun y => by simp) j

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
    change (Polynomial.toLaurent (LaurentPolynomial.trunc p)).coeff n + (Polynomial.toLaurent (LaurentPolynomial.trunc q)).coeff n = _
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
    change f.coeff n - (Polynomial.toLaurent (LaurentPolynomial.trunc f)).coeff n = 0
    rw [toLaurent_trunc_apply, if_pos h0, sub_self]
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

open TwoChartCech.GluedLinesMain in
theorem solution
    (k : Type u) [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (ha : Function.Injective a) :
    Module.finrank k ↥(gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H0 = 1 ∧
      Subsingleton (gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H1 := by
  refine ⟨?_, ?_⟩
  · have e := LinearEquiv.ofBijective (coeffSnd a b lam ((s : ℤ) - 1) 0) (coeffSnd_bijective a b lam ha)
    rw [e.finrank_eq, Module.finrank_self]
  · rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
    exact cechDiff_surjective a b lam ha

end S_TwoChartCech_finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1
end P2MW
export P2MW.S_TwoChartCech_finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1 (solution)
