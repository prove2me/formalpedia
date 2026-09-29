-- Prove2me | solution 1 for TwoChartCech.finrank_H0_gluedLinesSections_of_sub_one_le_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/dec9e68a-d65b-5855-95e4-4383949ae7d4

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_finrank_H0_gluedLinesSections_of_sub_one_le_of_neg
set_option autoImplicit false
open LaurentPolynomial TwoChartCech Polynomial

universe u

namespace GLH0Neg

variable {k : Type u} [Field k]

theorem support_mul_T (f : k[T;T⁻¹]) (e : ℤ) : (f * T e).coeff.support = f.coeff.support.map (addRightEmbedding e) := by
  have : (T e : k[T;T⁻¹]) = AddMonoidAlgebra.single e 1 := rfl
  rw [this]
  exact AddMonoidAlgebra.support_coeff_mul_single f 1 (fun y => by simp) e

theorem le_of_mul_T_mem_invPolyPart {f : k[T;T⁻¹]} {m : ℤ} (h : f * T (-m) ∈ invPolyPart k) :
    ∀ d ∈ f.coeff.support, d ≤ m := by
  intro d hd
  have : d + -m ∈ (f * T (-m)).coeff.support := by
    rw [support_mul_T]; exact Finset.mem_map_of_mem _ hd
  have := (mem_invPolyPart_iff k).mp h _ this
  omega

theorem eq_zero_of_neg {f : k[T;T⁻¹]} {m : ℤ} (hm : m < 0) (h0 : f ∈ polyPart k)
    (h1 : f * T (-m) ∈ invPolyPart k) : f = 0 := by
  by_contra hf
  obtain ⟨d, hd⟩ := Finsupp.support_nonempty_iff.mpr (AddMonoidAlgebra.coeff_injective.ne hf)
  have h0' := (mem_polyPart_iff k).mp h0 d hd
  have h1' := le_of_mul_T_mem_invPolyPart h1 d hd
  omega

theorem exists_eq_toLaurent {f : k[T;T⁻¹]} {N : ℕ} (h : ∀ d ∈ f.coeff.support, 0 ≤ d ∧ d < N) :
    ∃ p : k[X], p ∈ degreeLT k N ∧ toLaurent p = f := by
  classical
  refine ⟨∑ d ∈ f.coeff.support, monomial d.toNat (f.coeff d), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun d hd => ?_
    rw [mem_degreeLT]
    refine (degree_monomial_le _ _).trans_lt ?_
    have := h d hd
    exact_mod_cast (show d.toNat < N by omega)
  · rw [map_sum]
    conv_rhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Polynomial.toLaurent_C_mul_T]
    have := (h d hd).1
    rw [show ((d.toNat : ℕ) : ℤ) = d from Int.toNat_of_nonneg this, ← single_eq_C_mul_T]

theorem toLaurent_support_bound {p : k[X]} {N : ℕ} (hp : p ∈ degreeLT k N) :
    ∀ d ∈ (toLaurent p).coeff.support, 0 ≤ d ∧ d < N := by
  intro d hd
  rw [toLaurent_support, Finset.mem_map] at hd
  obtain ⟨e, he, rfl⟩ := hd
  refine ⟨by simp, ?_⟩
  have : e < N := by
    rw [mem_degreeLT] at hp
    by_contra hcon
    push Not at hcon
    have : (p.coeff e) = 0 := coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast hcon))
    exact (mem_support_iff.mp he) this
  show (e : ℤ) < N
  exact_mod_cast this

noncomputable def evalAt {s : ℕ} (a : Fin s → kˣ) (N : ℕ) : ↥(degreeLT k N) →ₗ[k] (Fin s → k) where
  toFun p := fun i => (p.1).eval (a i : k)
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

theorem evalAt_surjective {s : ℕ} (a : Fin s → kˣ) (ha : Function.Injective a) (N : ℕ) (hN : s ≤ N) :
    Function.Surjective (evalAt a N) := by
  classical
  intro r
  have hinj : Set.InjOn (fun i : Fin s => (a i : k)) (Finset.univ : Finset (Fin s)) :=
    fun i _ j _ hij => ha (Units.ext hij)
  refine ⟨⟨Lagrange.interpolate Finset.univ (fun i => (a i : k)) r, ?_⟩, ?_⟩
  · rw [mem_degreeLT]
    refine (Lagrange.degree_interpolate_lt _ hinj).trans_le ?_
    exact_mod_cast (by simpa using hN)
  · ext i
    simp only [evalAt, LinearMap.coe_mk, AddHom.coe_mk]
    exact Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)

theorem finrank_ker_evalAt {s : ℕ} (a : Fin s → kˣ) (ha : Function.Injective a) (N : ℕ) (hN : s ≤ N) :
    Module.finrank k (LinearMap.ker (evalAt a N)) = N - s := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (evalAt a N)
  rw [LinearMap.range_eq_top.mpr (evalAt_surjective a ha N hN), finrank_top, Module.finrank_fin_fun] at h1
  have h2 : Module.finrank k ↥(degreeLT k N) = N := by
    rw [LinearEquiv.finrank_eq (degreeLTEquiv k N), Module.finrank_fin_fun]
  omega

end GLH0Neg

namespace GLH0Neg

variable {k : Type u} [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (n m : ℤ)

def fstL (x : ↥(gluedLinesSections k a b lam n m).H0) : k[T;T⁻¹] := ((x.1).1 : ↥(gluedLinesM0 k a b lam)).1.1

def sndL (x : ↥(gluedLinesSections k a b lam n m).H0) : k[T;T⁻¹] := ((x.1).1 : ↥(gluedLinesM0 k a b lam)).1.2

theorem fstL_add (x y : ↥(gluedLinesSections k a b lam n m).H0) : fstL a b lam n m (x + y) = fstL a b lam n m x + fstL a b lam n m y := rfl
theorem sndL_add (x y : ↥(gluedLinesSections k a b lam n m).H0) : sndL a b lam n m (x + y) = sndL a b lam n m x + sndL a b lam n m y := rfl
theorem fstL_smul (c : k) (x : ↥(gluedLinesSections k a b lam n m).H0) : fstL a b lam n m (c • x) = c • fstL a b lam n m x := rfl
theorem sndL_smul (c : k) (x : ↥(gluedLinesSections k a b lam n m).H0) : sndL a b lam n m (c • x) = c • sndL a b lam n m x := rfl

theorem val_M1_eq (x : ↥(gluedLinesSections k a b lam n m).H0) :
    ((x.1).2 : ↥(gluedLinesM1 k a b lam n m)).1 = ((x.1).1 : ↥(gluedLinesM0 k a b lam)).1 := by
  have hx := (Sections.mem_H0_iff _ x.1).mp x.2

  exact (congrArg Subtype.val hx).symm

theorem fst_mem_polyPart (x : ↥(gluedLinesSections k a b lam n m).H0) : fstL a b lam n m x ∈ polyPart k :=
  (Subalgebra.mem_prod.mp ((x.1).1).2.2).1
theorem snd_mem_polyPart (x : ↥(gluedLinesSections k a b lam n m).H0) : sndL a b lam n m x ∈ polyPart k :=
  (Subalgebra.mem_prod.mp ((x.1).1).2.2).2
theorem fst_mul_T_mem (x : ↥(gluedLinesSections k a b lam n m).H0) : fstL a b lam n m x * T (-n) ∈ invPolyPart k := by
  have h := ((x.1).2).2.2.1
  rw [val_M1_eq] at h
  exact h
theorem snd_mul_T_mem (x : ↥(gluedLinesSections k a b lam n m).H0) : sndL a b lam n m x * T (-m) ∈ invPolyPart k := by
  have h := ((x.1).2).2.2.2
  rw [val_M1_eq] at h
  exact h
theorem gluedCond (x : ↥(gluedLinesSections k a b lam n m).H0) :
    GluedCond a b lam (fstL a b lam n m x, sndL a b lam n m x) := ((x.1).1).2.1

theorem fst_support (x : ↥(gluedLinesSections k a b lam n m).H0) :
    ∀ d ∈ (fstL a b lam n m x).coeff.support, 0 ≤ d ∧ d < n + 1 := fun d hd =>
  ⟨(mem_polyPart_iff k).mp (fst_mem_polyPart a b lam n m x) d hd,
    by have := le_of_mul_T_mem_invPolyPart (fst_mul_T_mem a b lam n m x) d hd; omega⟩

theorem ext_of_fst_snd {x y : ↥(gluedLinesSections k a b lam n m).H0}
    (h1 : fstL a b lam n m x = fstL a b lam n m y) (h2 : sndL a b lam n m x = sndL a b lam n m y) : x = y := by
  have hp : ((x.1).1 : ↥(gluedLinesM0 k a b lam)).1 = ((y.1).1 : ↥(gluedLinesM0 k a b lam)).1 := Prod.ext h1 h2
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hp
  · apply Subtype.ext
    rw [val_M1_eq, val_M1_eq]; exact hp

def mkH0 (f : k[T;T⁻¹] × k[T;T⁻¹]) (hc : GluedCond a b lam f) (hp : f ∈ (polyPart k).prod (polyPart k))
    (h1 : f.1 * T (-n) ∈ invPolyPart k) (h2 : f.2 * T (-m) ∈ invPolyPart k) :
    ↥(gluedLinesSections k a b lam n m).H0 :=
  ⟨(⟨f, hc, hp⟩, ⟨f, hc, h1, h2⟩), (Sections.mem_H0_iff _ _).mpr rfl⟩

@[scoped simp] theorem fstL_mkH0 (f : k[T;T⁻¹] × k[T;T⁻¹]) (hc hp h1 h2) : fstL a b lam n m (mkH0 a b lam n m f hc hp h1 h2) = f.1 := rfl
@[scoped simp] theorem sndL_mkH0 (f : k[T;T⁻¹] × k[T;T⁻¹]) (hc hp h1 h2) : sndL a b lam n m (mkH0 a b lam n m f hc hp h1 h2) = f.2 := rfl

theorem toLaurent_conds {p : k[X]} {N : ℕ} (hp : p ∈ degreeLT k N) (hN : (N : ℤ) ≤ n + 1) :
    toLaurent p ∈ polyPart k ∧ toLaurent p * T (-n) ∈ invPolyPart k := by
  have hb := toLaurent_support_bound hp
  refine ⟨(mem_polyPart_iff k).mpr fun d hd => (hb d hd).1, (mem_invPolyPart_iff k).mpr fun d hd => ?_⟩
  rw [support_mul_T, Finset.mem_map] at hd
  obtain ⟨e, he, rfl⟩ := hd
  have := (hb e he).2
  show e + -n ≤ 0
  omega

theorem levalUnit_toLaurent (u : kˣ) (p : k[X]) : levalUnit k u (toLaurent p) = p.eval (u : k) := by
  show LaurentPolynomial.eval₂ (RingHom.id k) u (toLaurent p) = _
  rw [eval₂_toLaurent, Polynomial.eval₂_id]

theorem finrank_H0_of_neg (ha : Function.Injective a) (hn : (s : ℤ) - 1 ≤ n) (hm : m < 0) :
    Module.finrank k ↥(gluedLinesSections k a b lam n m).H0 = (n + 1 - s).toNat := by
  classical
  set N : ℕ := (n + 1).toNat with hN
  have hNle : (N : ℤ) ≤ n + 1 := by omega
  have hsN : s ≤ N := by omega

  let V := LinearMap.ker (evalAt a N)
  have cond : ∀ p : V, GluedCond a b lam (toLaurent (p.1.1), 0) := by
    intro p i
    have hp : (p.1.1).eval (a i : k) = 0 := congrFun (LinearMap.mem_ker.mp p.2) i
    simp only [levalUnit_toLaurent, hp, map_zero, mul_zero]
  let Ψ : V →ₗ[k] ↥(gluedLinesSections k a b lam n m).H0 :=
    { toFun := fun p => mkH0 a b lam n m (toLaurent p.1.1, 0) (cond p)
        (Subalgebra.mem_prod.mpr ⟨(toLaurent_conds n p.1.2 hNle).1, Subalgebra.zero_mem _⟩)
        (toLaurent_conds n p.1.2 hNle).2 (by rw [zero_mul]; exact Subalgebra.zero_mem _)
      map_add' := fun p q => by
        apply ext_of_fst_snd
        · simp [fstL_add, map_add]
        · simp [sndL_add]
      map_smul' := fun c p => by
        apply ext_of_fst_snd
        · simp only [fstL_mkH0, RingHom.id_apply, fstL_smul]
          show toLaurent (c • p.1.1) = c • toLaurent p.1.1
          rw [Polynomial.smul_eq_C_mul, map_mul, Polynomial.toLaurent_C, LaurentPolynomial.smul_eq_C_mul]
        · simp only [sndL_mkH0, RingHom.id_apply, sndL_smul, smul_zero] }
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro p q hpq
      have := congrArg (fstL a b lam n m) hpq
      simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, fstL_mkH0] at this
      exact Subtype.ext (Subtype.ext (Polynomial.toLaurent_injective this))
    · intro x
      have h2 : sndL a b lam n m x = 0 := eq_zero_of_neg hm (snd_mem_polyPart a b lam n m x) (snd_mul_T_mem a b lam n m x)
      obtain ⟨p, hp, hpx⟩ := exists_eq_toLaurent (N := N) (fun d hd => by
        have := fst_support a b lam n m x d hd; exact ⟨this.1, by omega⟩)
      have hpV : (⟨p, hp⟩ : ↥(degreeLT k N)) ∈ V := by
        rw [LinearMap.mem_ker]
        ext i
        have hc := gluedCond a b lam n m x i
        rw [h2, map_zero, mul_zero, ← hpx, levalUnit_toLaurent] at hc
        exact hc
      refine ⟨⟨⟨p, hp⟩, hpV⟩, ?_⟩
      apply ext_of_fst_snd
      · simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, fstL_mkH0]; exact hpx
      · simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, sndL_mkH0]; exact h2.symm
  rw [← (LinearEquiv.ofBijective Ψ hΨ).finrank_eq, finrank_ker_evalAt a ha N hsN]
  omega

end GLH0Neg
p2m_reactivate "P2MW.S_TwoChartCech_finrank_H0_gluedLinesSections_of_sub_one_le_of_neg.GLH0Neg"

theorem solution
    (k : Type u) [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (ha : Function.Injective a) (n m : ℤ)
    (hn : (s : ℤ) - 1 ≤ n) (hm : m < 0) :
    Module.finrank k ↥(gluedLinesSections k a b lam n m).H0 = (n + 1 - s).toNat :=
  GLH0Neg.finrank_H0_of_neg a b lam n m ha hn hm

end S_TwoChartCech_finrank_H0_gluedLinesSections_of_sub_one_le_of_neg
end P2MW
export P2MW.S_TwoChartCech_finrank_H0_gluedLinesSections_of_sub_one_le_of_neg (solution)
