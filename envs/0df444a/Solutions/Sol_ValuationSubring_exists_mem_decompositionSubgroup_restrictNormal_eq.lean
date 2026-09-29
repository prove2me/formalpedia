-- Prove2me | solution 1 for ValuationSubring.exists_mem_decompositionSubgroup_restrictNormal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/beb012e8-ace2-5469-9b35-659cff73718b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq

open scoped Pointwise

set_option autoImplicit false

namespace CTap

universe u v

section Conj

variable {M : Type u} {L : Type v} [Field M] [Field L] [Algebra M L]

abbrev baseRing (A₀ : ValuationSubring M) : Subring L := A₀.toSubring.map (algebraMap M L)

abbrev intCl (A₀ : ValuationSubring M) : Subalgebra (baseRing (L := L) A₀) L :=
  integralClosure (baseRing (L := L) A₀) L

def LiesOverVal (V : ValuationSubring L) (A₀ : ValuationSubring M) : Prop :=
  V.comap (algebraMap M L) = A₀

variable {A₀ : ValuationSubring M}

theorem LiesOverVal.mem_iff {V : ValuationSubring L} (h : LiesOverVal V A₀) (m : M) :
    algebraMap M L m ∈ V ↔ m ∈ A₀ := by
  rw [← h]; rfl

theorem LiesOverVal.baseRing_le {V : ValuationSubring L} (h : LiesOverVal V A₀) :
    baseRing (L := L) A₀ ≤ V.toSubring := by
  rintro _ ⟨m, hm, rfl⟩
  exact (h.mem_iff m).2 hm

end Conj

section Trunc

open Polynomial

variable {R : Type*} [CommRing R]

noncomputable def truncQ (p : R[X]) (k : ℕ) : R[X] := divX^[k] p

@[scoped simp] theorem truncQ_zero (p : R[X]) : truncQ p 0 = p := rfl

theorem truncQ_succ (p : R[X]) (k : ℕ) : truncQ p (k + 1) = divX (truncQ p k) := by
  simp [truncQ, Function.iterate_succ_apply']

theorem coeff_truncQ (p : R[X]) (k i : ℕ) : (truncQ p k).coeff i = p.coeff (i + k) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih => rw [truncQ_succ, coeff_divX, ih, Nat.add_right_comm, Nat.add_assoc]

theorem truncQ_succ_mul_X_add (p : R[X]) (k : ℕ) :
    truncQ p (k + 1) * X + C (p.coeff k) = truncQ p k := by
  rw [truncQ_succ]
  conv_rhs => rw [← divX_mul_X_add (truncQ p k)]
  rw [coeff_truncQ, Nat.zero_add]

theorem natDegree_truncQ_le (p : R[X]) (k : ℕ) : (truncQ p k).natDegree ≤ p.natDegree - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [truncQ_succ, natDegree_divX_eq_natDegree_tsub_one]
    omega

theorem X_pow_mul_truncQ_add_sum (p : R[X]) (k : ℕ) :
    X ^ k * truncQ p k + ∑ i ∈ Finset.range k, C (p.coeff i) * X ^ i = p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    calc X ^ (k + 1) * truncQ p (k + 1) + (∑ i ∈ Finset.range k, C (p.coeff i) * X ^ i + C (p.coeff k) * X ^ k)
        = X ^ k * (truncQ p (k + 1) * X + C (p.coeff k)) + ∑ i ∈ Finset.range k, C (p.coeff i) * X ^ i := by ring
      _ = p := by rw [truncQ_succ_mul_X_add, ih]

variable {A : Type*} [Field A] [Algebra R A]

theorem aeval_mem_span_pow_of_natDegree_le (x : A) (n : ℕ) (q : R[X]) (hq : q.natDegree ≤ n) :
    aeval x q ∈ Submodule.span R (Set.range fun i : Fin (n + 1) => x ^ (i : ℕ)) := by
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hq)]
  refine Submodule.sum_mem _ fun i hi => ?_
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩

theorem aeval_truncQ_succ (p : R[X]) (x : A) (k : ℕ) :
    x * aeval x (truncQ p (k + 1)) + algebraMap R A (p.coeff k) = aeval x (truncQ p k) := by
  have := congrArg (aeval x) (truncQ_succ_mul_X_add p k)
  simpa [mul_comm] using this

theorem X_pow_mul_aeval_truncQ (p : R[X]) (x : A) (hp : aeval x p = 0) (k : ℕ) :
    x ^ k * aeval x (truncQ p k) = - ∑ i ∈ Finset.range k, algebraMap R A (p.coeff i) * x ^ i := by
  have := congrArg (aeval x) (X_pow_mul_truncQ_add_sum p k)
  rw [hp, map_add, map_mul, map_pow, aeval_X, map_sum] at this
  simp only [map_mul, map_pow, aeval_X, aeval_C] at this
  linear_combination this

theorem isIntegral_aeval_truncQ (p : R[X]) (x : A) (hp : aeval x p = 0) (k : ℕ) :
    IsIntegral R (aeval x (truncQ p k)) := by
  classical
  set n := p.natDegree
  set N : Submodule R A := Submodule.span R (Set.range fun i : Fin (n + 1) => x ^ (i : ℕ)) with hN
  have h1 : (1 : A) ∈ N := Submodule.subset_span ⟨⟨0, Nat.succ_pos n⟩, by simp⟩
  have hNbot : N ≠ ⊥ := fun h => one_ne_zero ((Submodule.eq_bot_iff N).mp h 1 h1)
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)

  have key : ∀ j : Fin (n + 1), aeval x (truncQ p k) * x ^ (j : ℕ) ∈ N := by
    intro j
    have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
    rcases le_or_gt (j : ℕ) k with hjk | hjk
    ·
      have : aeval x (truncQ p k) * x ^ (j : ℕ) = aeval x (truncQ p k * X ^ (j : ℕ)) := by simp
      rw [this]
      apply aeval_mem_span_pow_of_natDegree_le
      calc (truncQ p k * X ^ (j : ℕ)).natDegree
          ≤ (truncQ p k).natDegree + (X ^ (j : ℕ) : R[X]).natDegree := natDegree_mul_le
        _ ≤ (n - k) + (j : ℕ) := by
            gcongr
            · exact natDegree_truncQ_le p k
            · exact natDegree_X_pow_le _
        _ ≤ n := by omega
    ·
      have hsplit : aeval x (truncQ p k) * x ^ (j : ℕ) = x ^ ((j : ℕ) - k) * (x ^ k * aeval x (truncQ p k)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjk.le, mul_comm]
      rw [hsplit, X_pow_mul_aeval_truncQ p x hp k]
      have : x ^ ((j : ℕ) - k) * -∑ i ∈ Finset.range k, algebraMap R A (p.coeff i) * x ^ i
          = -aeval x (X ^ ((j : ℕ) - k) * ∑ i ∈ Finset.range k, C (p.coeff i) * X ^ i) := by
        rw [map_mul, map_pow, aeval_X, map_sum, mul_neg]
        congr 2
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_pow, aeval_X, aeval_C]
      rw [this]
      refine Submodule.neg_mem _ (aeval_mem_span_pow_of_natDegree_le x n _ ?_)
      calc (X ^ ((j : ℕ) - k) * ∑ i ∈ Finset.range k, C (p.coeff i) * X ^ i).natDegree
          ≤ (X ^ ((j : ℕ) - k) : R[X]).natDegree + (∑ i ∈ Finset.range k, C (p.coeff i) * X ^ i).natDegree :=
            natDegree_mul_le
        _ ≤ ((j : ℕ) - k) + (k - 1) := by
            gcongr
            · exact natDegree_X_pow_le _
            · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
              calc (C (p.coeff i) * X ^ i).natDegree ≤ i := natDegree_C_mul_X_pow_le _ _
                _ ≤ k - 1 := by have := Finset.mem_range.mp hi; omega
        _ ≤ n := by omega
  have hle : N ≤ N.comap (LinearMap.mulLeft R (aeval x (truncQ p k))) := by
    rw [hN]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact key j
  exact isIntegral_of_smul_mem_submodule N hNbot hNfg _ fun m hm => hle hm

end Trunc

section Conj2

variable {M : Type u} {L : Type v} [Field M] [Field L] [Algebra M L]
variable {A₀ : ValuationSubring M}

open Polynomial

theorem mem_nonunits_iff_eq_zero_or_inv_not_mem (V : ValuationSubring L) (x : L) :
    x ∈ V.nonunits ↔ x = 0 ∨ x⁻¹ ∉ V := by
  rw [ValuationSubring.mem_nonunits_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← V.valuation_le_one_iff, map_inv₀, not_le]
    simp only [hx, false_or]
    have h0 : 0 < V.valuation x := by
      rw [zero_lt_iff]; exact (_root_.map_ne_zero V.valuation).mpr hx
    constructor
    · intro h; exact (one_lt_inv₀ h0).mpr h
    · intro h; exact (one_lt_inv₀ h0).mp h

theorem LiesOverVal.valuation_le_one_of_mem_baseRing {V : ValuationSubring L} (h : LiesOverVal V A₀)
    {s : L} (hs : s ∈ baseRing (L := L) A₀) : V.valuation s ≤ 1 :=
  (V.valuation_le_one_iff s).mpr (h.baseRing_le hs)

theorem LiesOverVal.intCl_le {V : ValuationSubring L} (h : LiesOverVal V A₀) {r : L}
    (hr : r ∈ intCl (L := L) A₀) : r ∈ V := by

  obtain ⟨p, hpm, hp⟩ : IsIntegral (baseRing (L := L) A₀) r := hr
  by_contra hrV
  have hr0 : r ≠ 0 := by rintro rfl; exact hrV V.zero_mem
  have hy : V.valuation r⁻¹ < 1 := by
    have hx : ¬ V.valuation r ≤ 1 := by rwa [V.valuation_le_one_iff]
    rw [map_inv₀]; push_neg at hx
    exact inv_lt_one_of_one_lt₀ hx

  set n := p.natDegree
  have heval : r ^ n + ∑ i ∈ Finset.range n, algebraMap _ L (p.coeff i) * r ^ i = 0 := by
    have : Polynomial.eval₂ (algebraMap _ L) r p = 0 := hp
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at this
    simp only [Polynomial.coeff_natDegree, hpm.leadingCoeff, map_one, one_mul] at this
    rw [add_comm] at this; exact this
  have key : (1 : L) = - ∑ i ∈ Finset.range n, algebraMap _ L (p.coeff i) * r⁻¹ ^ (n - i) := by
    have hrn : r ^ n ≠ 0 := pow_ne_zero _ hr0
    have h2 : ∑ i ∈ Finset.range n, algebraMap _ L (p.coeff i) * r⁻¹ ^ (n - i)
        = (∑ i ∈ Finset.range n, algebraMap _ L (p.coeff i) * r ^ i) * r⁻¹ ^ n := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := (Finset.mem_range.mp hi).le
      rw [mul_assoc]; congr 1
      calc r⁻¹ ^ (n - i) = (r * r⁻¹) ^ i * r⁻¹ ^ (n - i) := by rw [mul_inv_cancel₀ hr0, one_pow, one_mul]
        _ = r ^ i * r⁻¹ ^ n := by rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' hi']
    rw [h2, eq_neg_iff_add_eq_zero]
    have h3 := congrArg (· * r⁻¹ ^ n) heval
    simp only [add_mul, zero_mul] at h3
    rwa [← mul_pow, mul_inv_cancel₀ hr0, one_pow] at h3
  have hlt : V.valuation (∑ i ∈ Finset.range n, algebraMap _ L (p.coeff i) * r⁻¹ ^ (n - i)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
    have hi' : 1 ≤ n - i := by have := Finset.mem_range.mp hi; omega
    rw [map_mul, map_pow]
    calc V.valuation (algebraMap _ L (p.coeff i)) * V.valuation r⁻¹ ^ (n - i)
        ≤ 1 * V.valuation r⁻¹ ^ (n - i) := by
          gcongr; exact h.valuation_le_one_of_mem_baseRing (p.coeff i).2
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le' hy (by omega)
  have : V.valuation (1 : L) < 1 := by rw [key, Valuation.map_neg]; exact hlt
  simp at this

theorem exists_poly_unit_coeff [Algebra.IsAlgebraic M L] (A₀ : ValuationSubring M) (x : L) :
    ∃ p : Polynomial (baseRing (L := L) A₀), aeval x p = 0 ∧ ∃ j, p.coeff j = 1 := by
  classical
  set f := minpoly M x with hf
  have hfx : aeval x f = 0 := minpoly.aeval M x
  have hfm : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)

  obtain ⟨j, hjmem, hjmax⟩ := Finset.exists_max_image (Finset.range (f.natDegree + 1))
    (fun i => A₀.valuation (f.coeff i)) ⟨f.natDegree, Finset.mem_range.mpr (Nat.lt_succ_self _)⟩
  have hcn : A₀.valuation (f.coeff f.natDegree) = 1 := by
    rw [Polynomial.coeff_natDegree, hfm.leadingCoeff, map_one]
  have hcj0 : f.coeff j ≠ 0 := by
    intro h0
    have := hjmax f.natDegree (Finset.mem_range.mpr (Nat.lt_succ_self _))
    rw [h0, map_zero, hcn] at this
    exact not_lt.mpr this zero_lt_one

  set g : M[X] := C (f.coeff j)⁻¹ * f with hg
  have hgcoeff : ∀ i, g.coeff i ∈ A₀ := by
    intro i
    rw [hg, coeff_C_mul, ← A₀.valuation_le_one_iff, map_mul, map_inv₀]
    rcases lt_or_ge i (f.natDegree + 1) with hi | hi
    · have := hjmax i (Finset.mem_range.mpr hi)
      have hvj : A₀.valuation (f.coeff j) ≠ 0 := (_root_.map_ne_zero _).mpr hcj0
      calc (A₀.valuation (f.coeff j))⁻¹ * A₀.valuation (f.coeff i)
          ≤ (A₀.valuation (f.coeff j))⁻¹ * A₀.valuation (f.coeff j) := by gcongr
        _ = 1 := inv_mul_cancel₀ hvj
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := f) (n := i) (by omega), map_zero, mul_zero]
      exact zero_le'
  have hgj : g.coeff j = 1 := by rw [hg, coeff_C_mul, inv_mul_cancel₀ hcj0]
  have hgx : aeval x g = 0 := by rw [hg, map_mul, hfx, mul_zero]

  set g' : L[X] := g.map (algebraMap M L) with hg'
  have hlift : g' ∈ Polynomial.lifts (baseRing (L := L) A₀).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [hg', Polynomial.coeff_map]
    exact ⟨⟨algebraMap M L (g.coeff i), ⟨g.coeff i, hgcoeff i, rfl⟩⟩, rfl⟩
  obtain ⟨p, hp⟩ := hlift
  have hp' : p.map (baseRing (L := L) A₀).subtype = g' := hp
  refine ⟨p, ?_, j, ?_⟩
  · have : aeval x p = (p.map (baseRing (L := L) A₀).subtype).eval x := by
      rw [Polynomial.eval_map]; rfl
    rw [this, hp', hg', Polynomial.eval_map, ← Polynomial.aeval_def, hgx]
  · have := congrArg (fun q : L[X] => q.coeff j) hp'
    simp only [Polynomial.coeff_map, hg', hgj, map_one, Subring.coe_subtype] at this
    exact Subtype.ext (by simpa using this)

theorem eq_of_center_eq [Algebra.IsAlgebraic M L] {V V' : ValuationSubring L}
    (hV : LiesOverVal V A₀) (hV' : LiesOverVal V' A₀)
    (hc : ∀ r : L, r ∈ intCl (L := L) A₀ → (r ∈ V.nonunits ↔ r ∈ V'.nonunits)) : V = V' := by
  suffices key : ∀ {V V' : ValuationSubring L}, LiesOverVal V A₀ → LiesOverVal V' A₀ →
      (∀ r : L, r ∈ intCl (L := L) A₀ → (r ∈ V.nonunits ↔ r ∈ V'.nonunits)) → V ≤ V' from
    le_antisymm (key hV hV' hc) (key hV' hV fun r hr => (hc r hr).symm)
  intro V V' hV hV' hc x hxV
  by_contra hxV'
  have hx0 : x ≠ 0 := by rintro rfl; exact hxV' V'.zero_mem

  have hy : V'.valuation x⁻¹ < 1 := by
    have hx : ¬ V'.valuation x ≤ 1 := by rwa [V'.valuation_le_one_iff]
    rw [map_inv₀]; push_neg at hx
    exact inv_lt_one_of_one_lt₀ hx
  obtain ⟨p, hp, j, hj⟩ := exists_poly_unit_coeff (L := L) A₀ x

  have hu_int : ∀ k, aeval x (truncQ p k) ∈ intCl (L := L) A₀ := fun k => isIntegral_aeval_truncQ p x hp k

  have hA : ∀ k, 1 ≤ k → V'.valuation (aeval x (truncQ p k)) < 1 := by
    intro k hk
    have h := X_pow_mul_aeval_truncQ p x hp k
    have hxk : x ^ k ≠ 0 := pow_ne_zero _ hx0
    have huk : aeval x (truncQ p k) = - ∑ i ∈ Finset.range k, algebraMap _ L (p.coeff i) * x⁻¹ ^ (k - i) := by
      have h1 : aeval x (truncQ p k) = (x ^ k * aeval x (truncQ p k)) * x⁻¹ ^ k := by
        rw [inv_pow, mul_comm (x ^ k), mul_assoc, mul_inv_cancel₀ hxk, mul_one]
      rw [h1, h, neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ k := (Finset.mem_range.mp hi).le
      rw [mul_assoc]; congr 1
      calc x ^ i * x⁻¹ ^ k = x ^ i * (x⁻¹ ^ i * x⁻¹ ^ (k - i)) := by rw [← pow_add, Nat.add_sub_cancel' hi']
        _ = (x * x⁻¹) ^ i * x⁻¹ ^ (k - i) := by rw [mul_pow, mul_assoc]
        _ = x⁻¹ ^ (k - i) := by rw [mul_inv_cancel₀ hx0, one_pow, one_mul]
    rw [huk, Valuation.map_neg]
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
    have hi' : 1 ≤ k - i := by have := Finset.mem_range.mp hi; omega
    rw [map_mul, map_pow]
    calc V'.valuation (algebraMap _ L (p.coeff i)) * V'.valuation x⁻¹ ^ (k - i)
        ≤ 1 * V'.valuation x⁻¹ ^ (k - i) := by
          gcongr; exact hV'.valuation_le_one_of_mem_baseRing (p.coeff i).2
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le' hy (by omega)

  have hA' : ∀ k, 1 ≤ k → V.valuation (aeval x (truncQ p k)) < 1 := by
    intro k hk
    rw [← ValuationSubring.mem_nonunits_iff, hc _ (hu_int k), ValuationSubring.mem_nonunits_iff]
    exact hA k hk

  have hB : ∀ k, V.valuation (algebraMap _ L (p.coeff k)) < 1 := by
    intro k
    have hrec := aeval_truncQ_succ p x k
    have : algebraMap _ L (p.coeff k) = aeval x (truncQ p k) - x * aeval x (truncQ p (k + 1)) := by
      rw [← hrec]; ring
    rw [this, sub_eq_add_neg]
    refine Valuation.map_add_lt _ ?_ ?_
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [truncQ_zero, hp, map_zero]; exact zero_lt_one
      · exact hA' k hk
    · rw [Valuation.map_neg, map_mul]
      calc V.valuation x * V.valuation (aeval x (truncQ p (k + 1)))
          ≤ 1 * V.valuation (aeval x (truncQ p (k + 1))) := by
            gcongr; exact (V.valuation_le_one_iff x).mpr hxV
        _ < 1 := by rw [one_mul]; exact hA' (k + 1) (Nat.succ_pos k)
  have := hB j
  rw [hj, map_one, map_one] at this
  exact lt_irrefl _ this

end Conj2

section Galois

open scoped IntermediateField

set_option synthInstance.maxHeartbeats 800000

variable {M : Type u} {L : Type v} [Field M] [Field L] [Algebra M L]
variable (A₀ : ValuationSubring M)

def algHomBase (g : L ≃ₐ[M] L) : L →ₐ[baseRing (L := L) A₀] L :=
  { g.toAlgHom.toRingHom with
    commutes' := by
      rintro ⟨_, m, hm, rfl⟩
      exact g.commutes m }

theorem algHomBase_apply (g : L ≃ₐ[M] L) (x : L) : algHomBase A₀ g x = g x := rfl

theorem smul_mem_intCl {r : L} (hr : r ∈ intCl (L := L) A₀) (g : L ≃ₐ[M] L) :
    g r ∈ intCl (L := L) A₀ := by
  have : IsIntegral _ (algHomBase A₀ g r) := IsIntegral.map (algHomBase A₀ g) hr
  exact this

noncomputable scoped instance galAction : MulSemiringAction (L ≃ₐ[M] L) (intCl (L := L) A₀) where
  smul g r := ⟨g r, smul_mem_intCl A₀ r.2 g⟩
  one_smul r := Subtype.ext rfl
  mul_smul g h r := Subtype.ext rfl
  smul_zero g := Subtype.ext (map_zero g)
  smul_add g r s := Subtype.ext (map_add g _ _)
  smul_one g := Subtype.ext (map_one g)
  smul_mul g r s := Subtype.ext (map_mul g _ _)

@[scoped simp] theorem coe_galSmul (g : L ≃ₐ[M] L) (r : intCl (L := L) A₀) :
    ((g • r : intCl (L := L) A₀) : L) = g r := rfl

theorem gal_apply_baseRing (g : L ≃ₐ[M] L) (s : baseRing (L := L) A₀) : g (s : L) = s := by
  obtain ⟨m, -, hs⟩ := s.2
  rw [← hs]; exact g.commutes m

scoped instance galSMulCommClass :
    SMulCommClass (L ≃ₐ[M] L) (baseRing (L := L) A₀) (intCl (L := L) A₀) where
  smul_comm g s r := by
    apply Subtype.ext
    change g (((s • r : intCl (L := L) A₀) : L)) = (((s • (g • r) : intCl (L := L) A₀)) : L)
    rw [Subalgebra.coe_smul, Subalgebra.coe_smul, coe_galSmul, Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact gal_apply_baseRing A₀ g s

def fixedSubring : Subring (intCl (L := L) A₀) where
  carrier := {r | ∀ g : L ≃ₐ[M] L, g • r = r}
  mul_mem' {a b} ha hb g := by rw [smul_mul', ha g, hb g]
  one_mem' g := smul_one g
  add_mem' {a b} ha hb g := by rw [smul_add, ha g, hb g]
  zero_mem' g := smul_zero g
  neg_mem' {a} ha g := by rw [smul_neg, ha g]

noncomputable scoped instance fixedAlgebra : Algebra (fixedSubring (L := L) A₀) (intCl (L := L) A₀) :=
  (fixedSubring (L := L) A₀).subtype.toAlgebra

theorem fixedAlgebra_algebraMap (a : fixedSubring (L := L) A₀) :
    algebraMap (fixedSubring (L := L) A₀) (intCl (L := L) A₀) a = a.1 := by
  rw [show algebraMap (fixedSubring (L := L) A₀) (intCl (L := L) A₀) = (fixedSubring (L := L) A₀).subtype from
    RingHom.algebraMap_toAlgebra _]
  rfl

scoped instance fixedSMulCommClass :
    SMulCommClass (L ≃ₐ[M] L) (fixedSubring (L := L) A₀) (intCl (L := L) A₀) where
  smul_comm g a r := by
    rw [Algebra.smul_def, Algebra.smul_def, fixedAlgebra_algebraMap, smul_mul', a.2 g]

scoped instance fixedIsInvariant :
    Algebra.IsInvariant (fixedSubring (L := L) A₀) (intCl (L := L) A₀) (L ≃ₐ[M] L) :=
  ⟨fun r hr => ⟨⟨r, hr⟩, fixedAlgebra_algebraMap A₀ _⟩⟩

theorem continuousSMul_gal [Algebra.IsAlgebraic M L] :
    @ContinuousSMul (L ≃ₐ[M] L) (intCl (L := L) A₀) _ _ ⊥ := by
  letI : TopologicalSpace (intCl (L := L) A₀) := ⊥
  haveI : DiscreteTopology (intCl (L := L) A₀) := ⟨rfl⟩
  refine ⟨?_⟩
  rw [continuous_prod_of_discrete_right]
  intro r
  rw [continuous_discrete_rng]
  intro b
  rw [isOpen_iff_mem_nhds]
  intro g₀ hg₀

  haveI : FiniteDimensional M M⟮(r : L)⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (r : L))
  have hH : IsOpen ((M⟮(r : L)⟯.fixingSubgroup : Subgroup (L ≃ₐ[M] L)) : Set (L ≃ₐ[M] L)) :=
    IntermediateField.fixingSubgroup_isOpen _
  set U : Set (L ≃ₐ[M] L) := (fun g => g₀⁻¹ * g) ⁻¹' (M⟮(r : L)⟯.fixingSubgroup : Set (L ≃ₐ[M] L)) with hU
  have hUo : IsOpen U := hH.preimage (continuous_mul_left g₀⁻¹)
  have hg₀U : g₀ ∈ U := by
    change g₀⁻¹ * g₀ ∈ (M⟮(r : L)⟯.fixingSubgroup : Set (L ≃ₐ[M] L))
    rw [inv_mul_cancel]; exact Subgroup.one_mem _
  refine Filter.mem_of_superset (hUo.mem_nhds hg₀U) fun g hg => ?_
  change g₀⁻¹ * g ∈ (M⟮(r : L)⟯.fixingSubgroup : Set (L ≃ₐ[M] L)) at hg
  have hfix : (g₀⁻¹ * g) • (r : L) = r :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ (IntermediateField.mem_adjoin_simple_self M (r : L))
  change g • r = b
  change g₀ • r = b at hg₀
  rw [← hg₀]
  apply Subtype.ext
  change g (r : L) = g₀ (r : L)
  have : g = g₀ * (g₀⁻¹ * g) := by group
  conv_lhs => rw [this]
  change g₀ ((g₀⁻¹ * g) (r : L)) = _
  rw [show (g₀⁻¹ * g) (r : L) = (g₀⁻¹ * g) • (r : L) from rfl, hfix]

variable {A₀}

def center {V : ValuationSubring L} (h : LiesOverVal V A₀) : Ideal (intCl (L := L) A₀) where
  carrier := {r | V.valuation (r : L) < 1}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    change V.valuation ((a : L) + b) < 1
    exact Valuation.map_add_lt _ ha hb
  smul_mem' c r hr := by
    change V.valuation ((c : L) * r) < 1
    rw [map_mul]
    calc V.valuation (c : L) * V.valuation (r : L) ≤ 1 * V.valuation (r : L) := by
          gcongr; exact (V.valuation_le_one_iff _).mpr (h.intCl_le c.2)
      _ < 1 := by rwa [one_mul]

theorem mem_center_iff {V : ValuationSubring L} (h : LiesOverVal V A₀) (r : intCl (L := L) A₀) :
    r ∈ center h ↔ (r : L) ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]; rfl

scoped instance center_isPrime {V : ValuationSubring L} (h : LiesOverVal V A₀) : (center h).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    change ¬ V.valuation ((1 : intCl (L := L) A₀) : L) < 1
    simp
  · intro r s hrs
    change V.valuation ((r : L) * s) < 1 at hrs
    rw [map_mul] at hrs
    by_contra hcon
    push_neg at hcon
    obtain ⟨hr, hs⟩ := hcon
    change ¬ V.valuation (r : L) < 1 at hr
    change ¬ V.valuation (s : L) < 1 at hs
    have hr1 : V.valuation (r : L) = 1 :=
      le_antisymm ((V.valuation_le_one_iff _).mpr (h.intCl_le r.2)) (not_lt.mp hr)
    have hs1 : V.valuation (s : L) = 1 :=
      le_antisymm ((V.valuation_le_one_iff _).mpr (h.intCl_le s.2)) (not_lt.mp hs)
    rw [hr1, hs1, one_mul] at hrs
    exact lt_irrefl _ hrs

theorem LiesOverVal.smul {B : ValuationSubring L} (h : LiesOverVal B A₀) (g : L ≃ₐ[M] L) :
    LiesOverVal (g • B) A₀ := by
  unfold LiesOverVal at *
  ext m
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    AlgEquiv.commutes, ← ValuationSubring.mem_comap (A := B), h]

theorem mem_nonunits_smul_iff (B : ValuationSubring L) (g : L ≃ₐ[M] L) (x : L) :
    x ∈ (g • B).nonunits ↔ g⁻¹ x ∈ B.nonunits := by
  rw [mem_nonunits_iff_eq_zero_or_inv_not_mem, mem_nonunits_iff_eq_zero_or_inv_not_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀,
    map_eq_zero_iff _ (g⁻¹).injective]

theorem under_center_eq [IsGalois M L] {B B' : ValuationSubring L}
    (hB : LiesOverVal B A₀) (hB' : LiesOverVal B' A₀) :
    (center hB).under (fixedSubring (L := L) A₀) = (center hB').under (fixedSubring (L := L) A₀) := by

  have hfix : ∀ x : L, (∀ g : L ≃ₐ[M] L, g x = x) → ∃ m : M, algebraMap M L m = x := by
    intro x hx
    have h := InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField M L)
    rw [IntermediateField.fixingSubgroup_bot] at h
    have : x ∈ (⊥ : IntermediateField M L) := by
      rw [← h, IntermediateField.mem_fixedField_iff]
      exact fun g _ => hx g
    rwa [IntermediateField.mem_bot] at this
  have key : ∀ m : M, (algebraMap M L m ∈ B.nonunits ↔ algebraMap M L m ∈ B'.nonunits) := by
    intro m
    rw [mem_nonunits_iff_eq_zero_or_inv_not_mem, mem_nonunits_iff_eq_zero_or_inv_not_mem, ← map_inv₀,
      hB.mem_iff, hB'.mem_iff]
  ext ⟨a, ha⟩
  rw [Ideal.mem_comap, Ideal.mem_comap, fixedAlgebra_algebraMap, mem_center_iff, mem_center_iff]
  obtain ⟨m, hm⟩ := hfix (a : L) fun g => congrArg Subtype.val (ha g)
  rw [← hm]
  exact key m

theorem exists_smul_eq_of_liesOverVal [IsGalois M L] {B B' : ValuationSubring L}
    (hB : LiesOverVal B A₀) (hB' : LiesOverVal B' A₀) :
    ∃ ρ : L ≃ₐ[M] L, ρ • B = B' := by
  letI : TopologicalSpace (intCl (L := L) A₀) := ⊥
  haveI : DiscreteTopology (intCl (L := L) A₀) := ⟨rfl⟩
  haveI : ContinuousSMul (L ≃ₐ[M] L) (intCl (L := L) A₀) := continuousSMul_gal A₀
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := fixedSubring (L := L) A₀) (G := L ≃ₐ[M] L) (center hB) (center hB') (under_center_eq hB hB')
  refine ⟨g, eq_of_center_eq (hB.smul g) hB' fun r hr => ?_⟩
  rw [mem_nonunits_smul_iff, ← mem_center_iff hB' ⟨r, hr⟩, hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    mem_center_iff hB]
  rfl

end Galois

end CTap
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq.CTap"

open CTap in

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) [Normal K M]
    (A : ValuationSubring L) (τ : M ≃ₐ[K] M)
    (hτ : τ • (A.comap (algebraMap M L)) = A.comap (algebraMap M L)) :
    ∃ σ : L ≃ₐ[K] L, σ ∈ A.decompositionSubgroup K ∧ σ.restrictNormal M = τ := by

  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) L τ
  have hσ₀' : σ₀.restrictNormal M = τ := hσ₀
  have hres : ∀ m : M, σ₀ (algebraMap M L m) = algebraMap M L (τ m) := fun m => by
    rw [← hσ₀', AlgEquiv.restrictNormal_commutes]

  haveI : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  have h1 : LiesOverVal (σ₀ • A) (A.comap (algebraMap M L)) := by
    ext m
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_comap]
    have : σ₀⁻¹ • (algebraMap M L m) = algebraMap M L (τ⁻¹ m) := by
      rw [AlgEquiv.smul_def]
      apply σ₀.injective
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, hres, ← AlgEquiv.mul_apply,
        mul_inv_cancel, AlgEquiv.one_apply]
    rw [this]
    have hτ' := congrArg (fun S : ValuationSubring M => m ∈ S) hτ
    simp only [eq_iff_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ValuationSubring.mem_comap] at hτ'
    exact hτ'
  have h2 : LiesOverVal A (A.comap (algebraMap M L)) := rfl
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_liesOverVal h1 h2
  refine ⟨(ρ.restrictScalars K) * σ₀, ?_, ?_⟩
  ·
    show ((ρ.restrictScalars K) * σ₀) • A = A
    rw [mul_smul]
    have : (ρ.restrictScalars K) • (σ₀ • A) = ρ • (σ₀ • A) := by
      ext x
      simp only [ValuationSubring.mem_smul_pointwise_iff_exists, AlgEquiv.smul_def]
      rfl
    rw [this, hρ]
  ·
    apply AlgEquiv.ext
    intro m
    apply (algebraMap M L).injective
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.mul_apply]
    change ρ (σ₀ (algebraMap M L m)) = _
    rw [hres, ρ.commutes]

end S_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq
end P2MW
export P2MW.S_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq (solution)
