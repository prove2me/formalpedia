-- Prove2me | solution 1 for WeilConjectures.exists_qladic_interior_cohomology_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:37:43.601622+00:00
-- url     : https://prove2.me/submissions/64ee9cd6-7e50-4576-97b7-80507728057b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_qladic_lower_half_cohomology_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

section LowerHalfDualityBridge

private abbrev UpperDualAux (W D : Type) : Bool → Type
  | true => D
  | false => W

private instance upperDualAuxAddCommGroup (W D : Type) [AddCommGroup W] [AddCommGroup D] :
    ∀ b : Bool, AddCommGroup (UpperDualAux W D b)
  | true => inferInstance
  | false => inferInstance

private instance upperDualAuxModule (K W D : Type) [Field K]
    [AddCommGroup W] [Module K W] [AddCommGroup D] [Module K D] :
    ∀ b : Bool, Module K (UpperDualAux W D b)
  | true => inferInstance
  | false => inferInstance

private instance upperDualAuxFinite (K W D : Type) [Field K]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    [AddCommGroup D] [Module K D] [Module.Finite K D] :
    ∀ b : Bool, Module.Finite K (UpperDualAux W D b)
  | true => inferInstance
  | false => inferInstance

private abbrev UpperDualObj (K : Type) [Field K] (V : ℕ → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (n i : ℕ) : Type :=
  UpperDualAux (V i) (Module.Dual K (V (2 * n - i))) (decide (n < i ∧ i < 2 * n))

private def upperDualAuxEquivTrue {K W D : Type} [Field K]
    [AddCommGroup W] [Module K W] [AddCommGroup D] [Module K D]
    {b : Bool} (hb : b = true) :
    UpperDualAux W D b ≃ₗ[K] D := by
  cases hb
  exact LinearEquiv.refl K D

private def upperDualAuxEquivFalse {K W D : Type} [Field K]
    [AddCommGroup W] [Module K W] [AddCommGroup D] [Module K D]
    {b : Bool} (hb : b = false) :
    UpperDualAux W D b ≃ₗ[K] W := by
  cases hb
  exact LinearEquiv.refl K W

private def upperDualEquivDual {K : Type} [Field K] {V : ℕ → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] {n i : ℕ}
    (hi : n < i ∧ i < 2 * n) :
    UpperDualObj K V n i ≃ₗ[K] Module.Dual K (V (2 * n - i)) :=
  upperDualAuxEquivTrue (decide_eq_true hi)

private def upperDualEquivV {K : Type} [Field K] {V : ℕ → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] {n i : ℕ}
    (hi : ¬(n < i ∧ i < 2 * n)) :
    UpperDualObj K V n i ≃ₗ[K] V i :=
  upperDualAuxEquivFalse (decide_eq_false hi)

private def idxEquiv {K : Type} [Field K] {V : ℕ → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] {a b : ℕ} (h : a = b) :
    V a ≃ₗ[K] V b :=
  h ▸ LinearEquiv.refl K (V a)

private lemma idxEquiv_map_F {K : Type} [Field K] {V : ℕ → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (F : ∀ i, V i ≃ₗ[K] V i) {a b : ℕ} (h : a = b) (x : V a) :
    idxEquiv (K := K) (V := V) h (F a x) = F b (idxEquiv (K := K) (V := V) h x) := by
  cases h; rfl

private lemma dualMap_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (c : K) (f : V →ₗ[K] V) : (c • f).dualMap = c • f.dualMap := by
  ext φ x; simp

private lemma dualMap_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V] :
    (0 : V →ₗ[K] V).dualMap = 0 := by
  ext φ x; simp

private lemma linearEquiv_conj_pow {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) (f : V →ₗ[K] V) (m : ℕ) :
    (e.conj f) ^ m = e.conj (f ^ m) := by
  induction m with
  | zero =>
    ext x
    simp
  | succ m ih =>
    rw [pow_succ, pow_succ, ih]
    ext x
    simp [LinearEquiv.conj_apply]

private lemma aeval_linearEquiv_conj {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) (f : V →ₗ[K] V) (P : ℤ[X]) :
    aeval (e.conj f) P = e.conj (aeval f P) := by
  induction P using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rw [map_add, map_add, ihp, ihq, map_add]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, linearEquiv_conj_pow]
    ext x
    simp [LinearEquiv.conj_apply]

private lemma dualMap_pow {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] V) (m : ℕ) :
    (f.dualMap) ^ m = (f ^ m).dualMap := by
  induction m with
  | zero =>
    ext φ x
    simp
  | succ m ih =>
    rw [pow_succ', pow_succ, ih, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.dualMap_comp_dualMap]

private lemma aeval_dualMap {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] V) (P : ℤ[X]) :
    aeval f.dualMap P = (aeval f P).dualMap := by
  induction P using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rw [map_add, map_add, ihp, ihq]
    ext φ x
    simp
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, dualMap_pow]
    ext φ x
    simp

private lemma eq_zero_of_forall_dual_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] {x : V} (hx : ∀ φ : Module.Dual K V, φ x = 0) : x = 0 := by
  let b := Module.finBasis K V
  apply b.repr.injective
  rw [map_zero]
  ext j
  simpa [Module.Basis.coord_apply] using hx (b.coord j)

private noncomputable def scalePoly (W : ℤ[X]) (c : ℤ) : ℤ[X] :=
  ∑ r ∈ Finset.range (W.natDegree + 1), C (W.coeff r * c ^ (W.natDegree - r)) * Polynomial.X ^ r

private noncomputable def recipTwistedPoly (W : ℤ[X]) (c : ℤ) : ℤ[X] :=
  ∑ r ∈ Finset.range (W.natDegree + 1), C (W.coeff r * c ^ r) * Polynomial.X ^ (W.natDegree - r)

private lemma coeff_scalePoly (W : ℤ[X]) (c : ℤ) (m : ℕ) :
    (scalePoly W c).coeff m = if m ≤ W.natDegree then W.coeff m * c ^ (W.natDegree - m) else 0 := by
  rw [scalePoly, Polynomial.finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  by_cases hm : m ≤ W.natDegree <;> simp [hm]

private lemma monic_scalePoly {W : ℤ[X]} (hW : W.Monic) (c : ℤ) :
    (scalePoly W c).Monic := by
  have hdeg_le : (scalePoly W c).natDegree ≤ W.natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_scalePoly, if_neg (not_le.mpr hm)]
  have hlead : (scalePoly W c).coeff W.natDegree = 1 := by
    rw [coeff_scalePoly, if_pos le_rfl, Nat.sub_self, pow_zero, mul_one]
    exact hW.leadingCoeff
  have hdeg_ge : W.natDegree ≤ (scalePoly W c).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hlead]; exact one_ne_zero)
  have hdeg_eq : (scalePoly W c).natDegree = W.natDegree := le_antisymm hdeg_le hdeg_ge
  rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg_eq, hlead]

private lemma aeval_scalePoly_complex (W : ℤ[X]) (c : ℤ) (hc : (c : ℂ) ≠ 0) (z : ℂ) :
    aeval z (scalePoly W c) = (c : ℂ) ^ W.natDegree * aeval (z / (c : ℂ)) W := by
  rw [scalePoly, map_sum]
  conv_rhs => arg 2; rw [Polynomial.as_sum_range_C_mul_X_pow W, map_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr_le : r ≤ W.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [map_mul, aeval_C, map_pow, aeval_X]
  conv_rhs => arg 2; rw [map_mul, aeval_C, map_pow, aeval_X]
  simp only [eq_intCast, Int.cast_mul, Int.cast_pow, div_pow]
  have hpow : (c : ℂ) ^ W.natDegree = (c : ℂ) ^ (W.natDegree - r) * (c : ℂ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr_le]
  rw [hpow]
  have hcr : (c : ℂ) ^ r ≠ 0 := pow_ne_zero r hc
  field_simp [hcr]

private lemma multiset_prod_const_mul {α R : Type*} [CommRing R]
    (s : Multiset α) (c : R) (f : α → R) :
    c ^ s.card * (s.map f).prod = (s.map (fun a => c * f a)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.card_cons, pow_succ', Multiset.map_cons, Multiset.prod_cons]
    rw [← ih]
    ring

private lemma multiset_prod_mul {α R : Type*} [CommRing R]
    (s : Multiset α) (f g : α → R) :
    (s.map f).prod * (s.map g).prod = (s.map (fun a => f a * g a)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← ih]
    ring

private lemma coeff_zero_mul_scalePoly_eq_recipTwistedPoly {q n j : ℕ} (hq : 0 < q)
    (hj : j < n) {W : ℤ[X]} (hW : W.Monic)
    (hnorm : ∀ z : ℂ, aeval z W = 0 → ‖z‖ = (q : ℝ) ^ ((j : ℝ) / 2)) :
    C (W.coeff 0) * scalePoly W ((q : ℤ) ^ (n - j)) = recipTwistedPoly W ((q : ℤ) ^ n) ∧
      W.coeff 0 ≠ 0 := by
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq)
  let WC : ℂ[X] := W.map (Int.castRingHom ℂ)
  have hWC_mon : WC.Monic := hW.map (Int.castRingHom ℂ)
  have hWC_deg : WC.natDegree = W.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
  have hWC_splits : WC.Splits := IsAlgClosed.splits WC
  let s : Multiset ℂ := WC.roots
  have hs_card : s.card = W.natDegree := by
    rw [← hWC_deg]
    exact (Polynomial.splits_iff_card_roots.mp hWC_splits)
  have hWC_prod : WC = (s.map (fun a => Polynomial.X - C a)).prod := by
    simpa [s] using hWC_splits.eq_prod_roots_of_monic hWC_mon
  have hWC_conj_prod : WC = (s.map (fun a => Polynomial.X - C (starRingEnd ℂ a))).prod := by
    have hmap : WC.map (starRingEnd ℂ) = WC := by
      dsimp only [WC]
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext_int _ _
    rw [← hmap]
    conv_lhs => rw [hWC_prod]
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp
  have ha_mul : ∀ a ∈ s, a * ((q : ℂ) ^ (n - j) * starRingEnd ℂ a) = (q : ℂ) ^ n := by
    intro a ha
    have hroot : WC.IsRoot a := Polynomial.isRoot_of_mem_roots ha
    have haeval : aeval a W = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact hroot
    have hna : ‖a‖ = (q : ℝ) ^ ((j : ℝ) / 2) := hnorm a haeval
    have hnsq : a * starRingEnd ℂ a = (q : ℂ) ^ j := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hna, ← Real.rpow_natCast,
        ← Real.rpow_mul (le_of_lt hqR)]
      have hexp : ((j : ℝ) / 2) * (2 : ℕ) = (j : ℝ) := by push_cast; ring
      rw [hexp, Real.rpow_natCast]
      push_cast
      rfl
    calc
      a * ((q : ℂ) ^ (n - j) * starRingEnd ℂ a)
          = (q : ℂ) ^ (n - j) * (a * starRingEnd ℂ a) := by ring
      _ = (q : ℂ) ^ (n - j) * (q : ℂ) ^ j := by rw [hnsq]
      _ = (q : ℂ) ^ n := by rw [← pow_add, Nat.sub_add_cancel (le_of_lt hj)]
  have hW0_eq : (W.coeff 0 : ℂ) = (s.map (fun a => -a)).prod := by
    have h1 : WC.eval 0 = (W.coeff 0 : ℂ) := by
      dsimp only [WC]
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, eq_intCast]
    rw [← h1]
    conv_lhs => rw [hWC_prod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp
  have hW0_ne : W.coeff 0 ≠ 0 := by
    intro h0
    have h0C : (W.coeff 0 : ℂ) = 0 := by rw [h0, Int.cast_zero]
    rw [hW0_eq] at h0C
    have hmem0 : (0 : ℂ) ∈ s.map (fun a => -a) := Multiset.prod_eq_zero_iff.mp h0C
    rcases Multiset.mem_map.mp hmem0 with ⟨a, ha, ha0⟩
    have ha_eq : a = 0 := neg_eq_zero.mp ha0
    have hm := ha_mul a ha
    rw [ha_eq, zero_mul] at hm
    exact pow_ne_zero n hqC hm.symm
  refine ⟨?_, hW0_ne⟩
  apply Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
  apply Polynomial.funext
  intro z
  have hlhs : ((C (W.coeff 0) * scalePoly W ((q : ℤ) ^ (n - j))).map (Int.castRingHom ℂ)).eval z =
      (s.map (fun a => (q : ℂ) ^ n - a * z)).prod := by
    rw [Polynomial.map_mul, Polynomial.eval_mul, Polynomial.map_C, Polynomial.eval_C, eq_intCast]
    have hscale : ((scalePoly W ((q : ℤ) ^ (n - j))).map (Int.castRingHom ℂ)).eval z =
        (s.map (fun a => z - (q : ℂ) ^ (n - j) * starRingEnd ℂ a)).prod := by
      have h1 : ((scalePoly W ((q : ℤ) ^ (n - j))).map (Int.castRingHom ℂ)).eval z =
          aeval z (scalePoly W ((q : ℤ) ^ (n - j))) := by
        rw [Polynomial.aeval_def, ← Polynomial.eval_map,
          show Int.castRingHom ℂ = algebraMap ℤ ℂ from RingHom.ext_int _ _]
      rw [h1, aeval_scalePoly_complex W ((q : ℤ) ^ (n - j))
        (by push_cast; exact pow_ne_zero _ hqC)]
      have h2 : aeval (z / (((q : ℤ) ^ (n - j) : ℤ) : ℂ)) W =
          WC.eval (z / (q : ℂ) ^ (n - j)) := by
        rw [Polynomial.aeval_def, ← Polynomial.eval_map]
        push_cast; rfl
      rw [h2, ← hs_card]
      conv_lhs => rw [hWC_conj_prod]
      rw [Polynomial.eval_multiset_prod, Multiset.map_map]
      have hcast : ((((q : ℤ) ^ (n - j) : ℤ) : ℂ)) = (q : ℂ) ^ (n - j) := by push_cast; rfl
      rw [hcast, multiset_prod_const_mul]
      congr 1
      refine Multiset.map_congr rfl fun a _ => ?_
      simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      have hqnj : (q : ℂ) ^ (n - j) ≠ 0 := pow_ne_zero _ hqC
      field_simp [hqnj]
    rw [hW0_eq, hscale, multiset_prod_mul]
    congr 1
    refine Multiset.map_congr rfl fun a ha => ?_
    have hmul := ha_mul a ha
    calc
      (-a) * (z - (q : ℂ) ^ (n - j) * starRingEnd ℂ a)
          = a * ((q : ℂ) ^ (n - j) * starRingEnd ℂ a) - a * z := by ring
      _ = (q : ℂ) ^ n - a * z := by rw [hmul]
  have hrhs : ((recipTwistedPoly W ((q : ℤ) ^ n)).map (Int.castRingHom ℂ)).eval z =
      (s.map (fun a => (q : ℂ) ^ n - a * z)).prod := by
    rw [recipTwistedPoly, Polynomial.map_sum, Polynomial.eval_finsetSum]
    by_cases hz : z = 0
    · subst hz
      have hsum0 : ∑ r ∈ Finset.range (W.natDegree + 1),
          ((C (W.coeff r * ((q : ℤ) ^ n) ^ r) * Polynomial.X ^ (W.natDegree - r)).map
            (Int.castRingHom ℂ)).eval 0 =
          ((q : ℂ) ^ n) ^ W.natDegree := by
        rw [Finset.sum_range_succ]
        have hlt : ∑ r ∈ Finset.range W.natDegree,
            ((C (W.coeff r * ((q : ℤ) ^ n) ^ r) * Polynomial.X ^ (W.natDegree - r)).map
              (Int.castRingHom ℂ)).eval 0 = 0 := by
          refine Finset.sum_eq_zero fun r hr => ?_
          have hpos : W.natDegree - r ≠ 0 := Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hr)
          simp [zero_pow hpos]
        rw [hlt, zero_add, Nat.sub_self]
        simp [hW.leadingCoeff]
      rw [hsum0, ← hs_card]
      have hprod0 : (s.map (fun a => (q : ℂ) ^ n - a * 0)).prod = ((q : ℂ) ^ n) ^ s.card := by
        have hconst : s.map (fun a => (q : ℂ) ^ n - a * 0) = Multiset.replicate s.card ((q : ℂ) ^ n) := by
          simp [Multiset.map_const']
        rw [hconst, Multiset.prod_replicate]
      rw [hprod0]
    · have hsum_nz : ∑ r ∈ Finset.range (W.natDegree + 1),
          ((C (W.coeff r * ((q : ℤ) ^ n) ^ r) * Polynomial.X ^ (W.natDegree - r)).map
            (Int.castRingHom ℂ)).eval z =
          z ^ W.natDegree * WC.eval ((q : ℂ) ^ n / z) := by
        conv_rhs => rw [show WC = (∑ r ∈ Finset.range (W.natDegree + 1),
            C (W.coeff r) * Polynomial.X ^ r).map (Int.castRingHom ℂ) by
              rw [← Polynomial.as_sum_range_C_mul_X_pow W],
          Polynomial.map_sum, Polynomial.eval_finsetSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        have hr_le : r ≤ W.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        conv_rhs => arg 2; rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X]
        simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast, div_pow]
        have hpow : z ^ W.natDegree = z ^ (W.natDegree - r) * z ^ r := by
          rw [← pow_add, Nat.sub_add_cancel hr_le]
        rw [hpow]
        have hzr : z ^ r ≠ 0 := pow_ne_zero r hz
        field_simp [hzr]
      rw [hsum_nz, ← hs_card]
      conv_lhs => rw [hWC_prod]
      rw [Polynomial.eval_multiset_prod, Multiset.map_map, multiset_prod_const_mul]
      congr 1
      refine Multiset.map_congr rfl fun a _ => ?_
      simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      field_simp [hz]
  rw [hlhs, hrhs]

private lemma aeval_scalePoly_inv_eq_zero {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] {q n j : ℕ} (hq : 0 < q) (hj : j < n)
    (F : V ≃ₗ[K] V) {W : ℤ[X]} (hW : W.Monic)
    (hWF : aeval (F : V →ₗ[K] V) W = 0)
    (hnorm : ∀ z : ℂ, aeval z W = 0 → ‖z‖ = (q : ℝ) ^ ((j : ℝ) / 2)) :
    aeval (((q : K) ^ n) • (F.symm : V →ₗ[K] V)) (scalePoly W ((q : ℤ) ^ (n - j))) = 0 := by
  obtain ⟨hpoly, hW0_ne⟩ := coeff_zero_mul_scalePoly_eq_recipTwistedPoly hq hj hW hnorm
  let g : V →ₗ[K] V := ((q : K) ^ n) • (F.symm : V →ₗ[K] V)
  let f : V →ₗ[K] V := (F : V →ₗ[K] V)
  have hfg : ∀ (r : ℕ), r ≤ W.natDegree →
      f ^ W.natDegree * ((((q : K) ^ n) ^ r) • (g ^ (W.natDegree - r))) =
        (((q : K) ^ n) ^ W.natDegree) • (f ^ r) := by
    intro r hr
    have hmul1 : f * g = ((q : K) ^ n) • (1 : Module.End K V) := by
      ext x
      simp [f, g, Module.End.mul_apply]
    have hmul_pow : ∀ m : ℕ, f ^ m * g ^ m = (((q : K) ^ n) ^ m) • (1 : Module.End K V) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        calc
          f ^ (m + 1) * g ^ (m + 1)
              = (f ^ m * f) * (g * g ^ m) := by rw [pow_succ, pow_succ']
          _ = f ^ m * (f * g) * g ^ m := by simp only [mul_assoc]
          _ = ((q : K) ^ n) • (f ^ m * g ^ m) := by
            rw [hmul1, mul_smul_comm, smul_mul_assoc, mul_one]
          _ = (((q : K) ^ n) ^ (m + 1)) • (1 : Module.End K V) := by
            rw [ih, smul_smul, pow_succ']
    calc
      f ^ W.natDegree * ((((q : K) ^ n) ^ r) • (g ^ (W.natDegree - r)))
          = (((q : K) ^ n) ^ r) • (f ^ (r + (W.natDegree - r)) * g ^ (W.natDegree - r)) := by
            rw [Nat.add_sub_of_le hr, mul_smul_comm]
      _ = (((q : K) ^ n) ^ r) • (f ^ r * (f ^ (W.natDegree - r) * g ^ (W.natDegree - r))) := by
            rw [pow_add, mul_assoc]
      _ = (((q : K) ^ n) ^ r) • (f ^ r * ((((q : K) ^ n) ^ (W.natDegree - r)) • (1 : Module.End K V))) := by
            rw [hmul_pow]
      _ = ((((q : K) ^ n) ^ r) * (((q : K) ^ n) ^ (W.natDegree - r))) • (f ^ r) := by
            rw [mul_smul_comm, mul_one, smul_smul]
      _ = (((q : K) ^ n) ^ W.natDegree) • (f ^ r) := by
            rw [← pow_add, Nat.add_sub_of_le hr]
  have hrecip_mul : f ^ W.natDegree * aeval g (recipTwistedPoly W ((q : ℤ) ^ n)) = 0 := by
    rw [recipTwistedPoly, map_sum, Finset.mul_sum]
    have hterm : ∀ r ∈ Finset.range (W.natDegree + 1),
        f ^ W.natDegree * aeval g (C (W.coeff r * ((q : ℤ) ^ n) ^ r) * Polynomial.X ^ (W.natDegree - r)) =
        (((q : K) ^ n) ^ W.natDegree) • aeval f (C (W.coeff r) * Polynomial.X ^ r) := by
      intro r hr
      have hr_le : r ≤ W.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      rw [map_mul, aeval_C, aeval_X_pow]
      conv_rhs => arg 2; rw [map_mul, aeval_C, aeval_X_pow]
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      have hz1 : ((W.coeff r * ((q : ℤ) ^ n) ^ r : ℤ) • (1 : Module.End K V)) * g ^ (W.natDegree - r) =
          (W.coeff r : ℤ) • ((((q : K) ^ n) ^ r) • (g ^ (W.natDegree - r))) := by
        ext x
        simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
          ← Int.cast_smul_eq_zsmul K, Int.cast_mul, Int.cast_pow, Int.cast_natCast, smul_smul]
      have hz2 : ((W.coeff r : ℤ) • (1 : Module.End K V)) * f ^ r = (W.coeff r : ℤ) • (f ^ r) := by
        ext x
        simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply]
      rw [hz1, hz2, mul_smul_comm, hfg r hr_le, smul_comm]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← map_sum,
      ← Polynomial.as_sum_range_C_mul_X_pow W, hWF, smul_zero]
  have hrecip0 : aeval g (recipTwistedPoly W ((q : ℤ) ^ n)) = 0 := by
    ext x
    have hx := congrArg (fun h : Module.End K V => h x) hrecip_mul
    simp only [Module.End.mul_apply, LinearMap.zero_apply] at hx
    have hfinj : Function.Injective (f ^ W.natDegree) := by
      have : ∀ m : ℕ, Function.Injective (f ^ m) := by
        intro m
        induction m with
        | zero => exact Function.injective_id
        | succ m ih =>
          rw [pow_succ', Module.End.mul_eq_comp]
          exact F.injective.comp ih
      exact this W.natDegree
    exact hfinj (by rw [hx, LinearMap.zero_apply, map_zero])
  have hmul0 : ((W.coeff 0 : ℤ) : K) • aeval g (scalePoly W ((q : ℤ) ^ (n - j))) = 0 := by
    have h1 := congrArg (aeval g) hpoly
    rw [hrecip0, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one] at h1
    ext x
    have hx := congrArg (fun h : Module.End K V => h x) h1
    simpa only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
      LinearMap.zero_apply, ← Int.cast_smul_eq_zsmul K] using hx
  exact (smul_eq_zero.mp hmul0).resolve_left (Int.cast_ne_zero.mpr hW0_ne)

end LowerHalfDualityBridge

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ (V : ℕ → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module (Padic ℓ) (V i))
      (_ : ∀ i, Module.Finite (Padic ℓ) (V i))
      (F : ∀ i, V i →ₗ[Padic ℓ] V i)
      (B : ∀ i, 1 ≤ i → i ≤ n → V i →ₗ[Padic ℓ] V (2 * n - i) →ₗ[Padic ℓ] Padic ℓ),
      (∀ m : ℕ, 0 < m →
        (pointCount p f m : Padic ℓ) =
          1 + ((Nat.card k : Padic ℓ) ^ n) ^ m +
            ∑ i ∈ Finset.Ico 1 (2 * n),
              (-1 : Padic ℓ) ^ i * LinearMap.trace (Padic ℓ) (V i) ((F i) ^ m)) ∧
      (∀ i (h1 : 1 ≤ i) (hi : i ≤ n) (x : V i) (y : V (2 * n - i)),
        B i h1 hi (F i x) (F (2 * n - i) y) = (Nat.card k : Padic ℓ) ^ n * B i h1 hi x y) ∧
      (∀ i (h1 : 1 ≤ i) (hi : i ≤ n),
        (∀ x : V i, (∀ y : V (2 * n - i), B i h1 hi x y = 0) → x = 0) ∧
        (∀ y : V (2 * n - i), (∀ x : V i, B i h1 hi x y = 0) → y = 0)) ∧
      (∀ i, 1 ≤ i → i < 2 * n → ∃ W : ℤ[X], W.Monic ∧ aeval (F i) W = 0 ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  obtain ⟨V, hVAdd, hVMod, hVFin, F, Bmid, htr, hBmid_eq, hBmid_nondeg, hWlow, hWmid⟩ :=
    WeilConjectures.exists_qladic_lower_half_cohomology_of_ge_two p k n hn X f hproj ℓ hℓp
  let _ : ∀ i, AddCommGroup (V i) := hVAdd
  let _ : ∀ i, Module (Padic ℓ) (V i) := hVMod
  let _ : ∀ i, Module.Finite (Padic ℓ) (V i) := hVFin
  let K := Padic ℓ
  let qK : K := (Nat.card k : K) ^ n
  let V' : ℕ → Type := UpperDualObj K V n
  let F' : ∀ i, V' i →ₗ[K] V' i := fun i =>
    if h : n < i ∧ i < 2 * n then
      (upperDualEquivDual (K := K) (V := V) (n := n) h).symm.conj
        ((qK • ((F (2 * n - i)).symm : V (2 * n - i) →ₗ[K] V (2 * n - i))).dualMap)
    else
      (upperDualEquivV (K := K) (V := V) (n := n) h).symm.conj (F i : V i →ₗ[K] V i)
  let B' : ∀ i, 1 ≤ i → i ≤ n → V' i →ₗ[K] V' (2 * n - i) →ₗ[K] K := fun i h1 hi =>
    if hlt : i < n then
      have hlo : ¬(n < i ∧ i < 2 * n) := by omega
      have hhi : n < 2 * n - i ∧ 2 * n - i < 2 * n := by omega
      let ei : V' i ≃ₗ[K] V i := upperDualEquivV (K := K) (V := V) (n := n) hlo
      let ej : V' (2 * n - i) ≃ₗ[K] Module.Dual K (V (2 * n - (2 * n - i))) :=
        upperDualEquivDual (K := K) (V := V) (n := n) hhi
      have heq_idx : 2 * n - (2 * n - i) = i := by omega
      let eidx : V i ≃ₗ[K] V (2 * n - (2 * n - i)) := idxEquiv (K := K) (V := V) heq_idx.symm
      { toFun := fun x =>
          { toFun := fun y => ej y (eidx (ei x))
            map_add' := fun y₁ y₂ => by simp [map_add]
            map_smul' := fun c y => by simp [map_smul] }
        map_add' := fun x₁ x₂ => by
          ext y
          change ej y (eidx (ei (x₁ + x₂))) = ej y (eidx (ei x₁)) + ej y (eidx (ei x₂))
          simp [map_add]
        map_smul' := fun c x => by
          ext y
          change ej y (eidx (ei (c • x))) = c * ej y (eidx (ei x))
          simp [map_smul] }
    else
      have hin : i = n := by omega
      have hlo : ¬(n < i ∧ i < 2 * n) := by omega
      have hlo2 : ¬(n < 2 * n - i ∧ 2 * n - i < 2 * n) := by omega
      let ei : V' i ≃ₗ[K] V i := upperDualEquivV (K := K) (V := V) (n := n) hlo
      let ej : V' (2 * n - i) ≃ₗ[K] V (2 * n - i) :=
        upperDualEquivV (K := K) (V := V) (n := n) hlo2
      have h2ni : 2 * n - i = n := by omega
      let e1 : V i ≃ₗ[K] V n := idxEquiv (K := K) (V := V) hin
      let e2 : V (2 * n - i) ≃ₗ[K] V n := idxEquiv (K := K) (V := V) h2ni
      { toFun := fun x =>
          { toFun := fun y => Bmid (e1 (ei x)) (e2 (ej y))
            map_add' := fun y₁ y₂ => by
              change Bmid (e1 (ei x)) (e2 (ej (y₁ + y₂))) =
                Bmid (e1 (ei x)) (e2 (ej y₁)) + Bmid (e1 (ei x)) (e2 (ej y₂))
              simp [map_add]
            map_smul' := fun c y => by
              change Bmid (e1 (ei x)) (e2 (ej (c • y))) = c * Bmid (e1 (ei x)) (e2 (ej y))
              simp [map_smul] }
        map_add' := fun x₁ x₂ => by
          ext y
          change Bmid (e1 (ei (x₁ + x₂))) (e2 (ej y)) =
            Bmid (e1 (ei x₁)) (e2 (ej y)) + Bmid (e1 (ei x₂)) (e2 (ej y))
          simp [map_add]
        map_smul' := fun c x => by
          ext y
          change Bmid (e1 (ei (c • x))) (e2 (ej y)) = c * Bmid (e1 (ei x)) (e2 (ej y))
          simp [map_smul] }
  have hq_pos : 0 < Nat.card k := Nat.card_pos
  refine ⟨V', inferInstance, inferInstance, inferInstance, F', B', ?_, ?_, ?_, ?_⟩
  · intro m hm
    rw [htr m hm]
    have hsplit : ∑ i ∈ Finset.Ico 1 (2 * n), (-1 : K) ^ i * LinearMap.trace K (V' i) ((F' i) ^ m) =
        (-1 : K) ^ n * LinearMap.trace K (V' n) ((F' n) ^ m) +
        ∑ i ∈ Finset.Ico 1 n, (-1 : K) ^ i * LinearMap.trace K (V' i) ((F' i) ^ m) +
        ∑ i ∈ Finset.Ico (n + 1) (2 * n), (-1 : K) ^ i * LinearMap.trace K (V' i) ((F' i) ^ m) := by
      have h1 : Finset.Ico 1 (2 * n) = Finset.Ico 1 n ∪ Finset.Ico n (2 * n) :=
        (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
      have hd1 : Disjoint (Finset.Ico 1 n) (Finset.Ico n (2 * n)) :=
        Finset.Ico_disjoint_Ico_consecutive 1 n (2 * n)
      rw [h1, Finset.sum_union hd1, Finset.sum_eq_sum_Ico_succ_bot (by omega : n < 2 * n)]
      ring
    rw [hsplit]
    have htr_mid : LinearMap.trace K (V' n) ((F' n) ^ m) =
        LinearMap.trace K (V n) ((F n : V n →ₗ[K] V n) ^ m) := by
      have hnot : ¬(n < n ∧ n < 2 * n) := by omega
      simp only [F', dif_neg hnot, linearEquiv_conj_pow, LinearMap.trace_conj']
    have htr_low : ∀ i ∈ Finset.Ico 1 n,
        LinearMap.trace K (V' i) ((F' i) ^ m) =
        LinearMap.trace K (V i) ((F i : V i →ₗ[K] V i) ^ m) := by
      intro i hi
      have hnot : ¬(n < i ∧ i < 2 * n) := by
        have := (Finset.mem_Ico.mp hi).2; omega
      simp only [F', dif_neg hnot, linearEquiv_conj_pow, LinearMap.trace_conj']
    have htr_high : ∑ i ∈ Finset.Ico (n + 1) (2 * n),
          (-1 : K) ^ i * LinearMap.trace K (V' i) ((F' i) ^ m) =
        ∑ j ∈ Finset.Ico 1 n,
          (-1 : K) ^ j * (qK ^ m * LinearMap.trace K (V j) (((F j).symm : V j →ₗ[K] V j) ^ m)) := by
      refine Finset.sum_bij (fun i _ => 2 * n - i) ?_ ?_ ?_ ?_
      · intro i hi
        rcases Finset.mem_Ico.mp hi with ⟨h1, h2⟩
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · intro i₁ hi₁ i₂ hi₂ heq
        rcases Finset.mem_Ico.mp hi₁ with ⟨_, h1b⟩
        rcases Finset.mem_Ico.mp hi₂ with ⟨_, h2b⟩
        omega
      · intro j hj
        rcases Finset.mem_Ico.mp hj with ⟨h1, h2⟩
        exact ⟨2 * n - j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro i hi
        rcases Finset.mem_Ico.mp hi with ⟨h1, h2⟩
        have hhi : n < i ∧ i < 2 * n := ⟨by omega, h2⟩
        have hsign : (-1 : K) ^ i = (-1 : K) ^ (2 * n - i) := by
          have hmul : (-1 : K) ^ i * (-1 : K) ^ (2 * n - i) = 1 := by
            rw [← pow_add, Nat.add_sub_of_le (le_of_lt h2), pow_mul]
            norm_num
          calc
            (-1 : K) ^ i = (-1 : K) ^ i * ((-1 : K) ^ (2 * n - i) * (-1 : K) ^ (2 * n - i)) := by
              rw [← mul_pow]; norm_num
            _ = ((-1 : K) ^ i * (-1 : K) ^ (2 * n - i)) * (-1 : K) ^ (2 * n - i) := by ring
            _ = (-1 : K) ^ (2 * n - i) := by rw [hmul, one_mul]
        rw [hsign]
        congr 1
        simp only [F', dif_pos hhi, linearEquiv_conj_pow, LinearMap.trace_conj', dualMap_pow]
        have hspow : (qK • ((F (2 * n - i)).symm : V (2 * n - i) →ₗ[K] V (2 * n - i))) ^ m =
            (qK ^ m) • (((F (2 * n - i)).symm : V (2 * n - i) →ₗ[K] V (2 * n - i)) ^ m) := by
          exact _root_.smul_pow qK ((F (2 * n - i)).symm : V (2 * n - i) →ₗ[K] V (2 * n - i)) m
        rw [hspow, dualMap_smul, map_smul, smul_eq_mul]
        congr 1
        exact LinearMap.trace_transpose' (((F (2 * n - i)).symm : V (2 * n - i) →ₗ[K] V (2 * n - i)) ^ m)
    have htr_low_sum : ∑ i ∈ Finset.Ico 1 n,
          (-1 : K) ^ i * LinearMap.trace K (V' i) ((F' i) ^ m) =
        ∑ i ∈ Finset.Ico 1 n,
          (-1 : K) ^ i * LinearMap.trace K (V i) ((F i : V i →ₗ[K] V i) ^ m) :=
      Finset.sum_congr rfl fun i hi => by rw [htr_low i hi]
    rw [htr_mid, htr_low_sum, htr_high]
    rw [show ∑ i ∈ Finset.Ico 1 n, (-1 : K) ^ i *
          (LinearMap.trace K (V i) ((F i : V i →ₗ[K] V i) ^ m) +
           qK ^ m * LinearMap.trace K (V i) (((F i).symm : V i →ₗ[K] V i) ^ m)) =
        (∑ i ∈ Finset.Ico 1 n, (-1 : K) ^ i * LinearMap.trace K (V i) ((F i : V i →ₗ[K] V i) ^ m)) +
        (∑ i ∈ Finset.Ico 1 n, (-1 : K) ^ i *
          (qK ^ m * LinearMap.trace K (V i) (((F i).symm : V i →ₗ[K] V i) ^ m))) by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring]
    ring
  · intro i h1 hi x y
    by_cases hlt : i < n
    · have hlo : ¬(n < i ∧ i < 2 * n) := by omega
      have hhi : n < 2 * n - i ∧ 2 * n - i < 2 * n := by omega
      have heq_idx : 2 * n - (2 * n - i) = i := by omega
      simp only [B', dif_pos hlt, LinearMap.coe_mk, AddHom.coe_mk, F', dif_neg hlo, dif_pos hhi,
        LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm]
      rw [(upperDualEquivV (K := K) (V := V) (n := n) hlo).apply_symm_apply,
        (upperDualEquivDual (K := K) (V := V) (n := n) hhi).apply_symm_apply]
      set φ := upperDualEquivDual (K := K) (V := V) (n := n) hhi y
      set v := upperDualEquivV (K := K) (V := V) (n := n) hlo x
      change ((qK • ((F (2 * n - (2 * n - i))).symm : V (2 * n - (2 * n - i)) →ₗ[K]
          V (2 * n - (2 * n - i)))).dualMap φ)
          (idxEquiv (K := K) (V := V) heq_idx.symm ((F i) v)) =
        qK * φ (idxEquiv (K := K) (V := V) heq_idx.symm v)
      rw [idxEquiv_map_F F heq_idx.symm v]
      simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, map_smul, smul_eq_mul]
    · have hin : i = n := by omega
      have hlo : ¬(n < i ∧ i < 2 * n) := by omega
      have hlo2 : ¬(n < 2 * n - i ∧ 2 * n - i < 2 * n) := by omega
      have h2ni : 2 * n - i = n := by omega
      simp only [B', dif_neg hlt, LinearMap.coe_mk, AddHom.coe_mk, F', dif_neg hlo, dif_neg hlo2,
        LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm]
      rw [(upperDualEquivV (K := K) (V := V) (n := n) hlo).apply_symm_apply,
        (upperDualEquivV (K := K) (V := V) (n := n) hlo2).apply_symm_apply]
      set u := upperDualEquivV (K := K) (V := V) (n := n) hlo x
      set w := upperDualEquivV (K := K) (V := V) (n := n) hlo2 y
      change Bmid (idxEquiv (K := K) (V := V) hin ((F i) u))
          (idxEquiv (K := K) (V := V) h2ni ((F (2 * n - i)) w)) =
        qK * Bmid (idxEquiv (K := K) (V := V) hin u) (idxEquiv (K := K) (V := V) h2ni w)
      rw [idxEquiv_map_F F hin u, idxEquiv_map_F F h2ni w]
      exact hBmid_eq _ _
  · intro i h1 hi
    by_cases hlt : i < n
    · have hlo : ¬(n < i ∧ i < 2 * n) := by omega
      have hhi : n < 2 * n - i ∧ 2 * n - i < 2 * n := by omega
      have heq_idx : 2 * n - (2 * n - i) = i := by omega
      constructor
      · intro x hx
        apply (upperDualEquivV (K := K) (V := V) (n := n) hlo).injective
        rw [map_zero]
        apply (idxEquiv (K := K) (V := V) heq_idx.symm).injective
        rw [map_zero]
        apply eq_zero_of_forall_dual_eq_zero (K := K)
        intro ψ
        have hy := hx ((upperDualEquivDual (K := K) (V := V) (n := n) hhi).symm ψ)
        simpa only [B', dif_pos hlt, LinearMap.coe_mk, AddHom.coe_mk,
          LinearEquiv.apply_symm_apply] using hy
      · intro y hy
        apply (upperDualEquivDual (K := K) (V := V) (n := n) hhi).injective
        rw [map_zero]
        apply LinearMap.ext
        intro v
        have hx := hy ((upperDualEquivV (K := K) (V := V) (n := n) hlo).symm
          ((idxEquiv (K := K) (V := V) heq_idx.symm).symm v))
        simpa only [B', dif_pos hlt, LinearMap.coe_mk, AddHom.coe_mk,
          LinearEquiv.apply_symm_apply, LinearMap.zero_apply] using hx
    · have hin : i = n := by omega
      have hlo : ¬(n < i ∧ i < 2 * n) := by omega
      have hlo2 : ¬(n < 2 * n - i ∧ 2 * n - i < 2 * n) := by omega
      have h2ni : 2 * n - i = n := by omega
      constructor
      · intro x hx
        apply (upperDualEquivV (K := K) (V := V) (n := n) hlo).injective
        rw [map_zero]
        apply (idxEquiv (K := K) (V := V) hin).injective
        rw [map_zero]
        apply hBmid_nondeg.1
        intro w
        have hw := hx ((upperDualEquivV (K := K) (V := V) (n := n) hlo2).symm
          ((idxEquiv (K := K) (V := V) h2ni).symm w))
        simpa only [B', dif_neg hlt, LinearMap.coe_mk, AddHom.coe_mk,
          LinearEquiv.apply_symm_apply] using hw
      · intro y hy
        apply (upperDualEquivV (K := K) (V := V) (n := n) hlo2).injective
        rw [map_zero]
        apply (idxEquiv (K := K) (V := V) h2ni).injective
        rw [map_zero]
        apply hBmid_nondeg.2
        intro u
        have hu := hy ((upperDualEquivV (K := K) (V := V) (n := n) hlo).symm
          ((idxEquiv (K := K) (V := V) hin).symm u))
        simpa only [B', dif_neg hlt, LinearMap.coe_mk, AddHom.coe_mk,
          LinearEquiv.apply_symm_apply] using hu
  · intro i h1 h2
    by_cases hlt : i < n
    · have hnot : ¬(n < i ∧ i < 2 * n) := by omega
      obtain ⟨W, hWmon, hWF, hWnorm⟩ := hWlow i h1 hlt
      refine ⟨W, hWmon, ?_, fun z hz => le_of_eq (hWnorm z hz)⟩
      simp only [F', dif_neg hnot, aeval_linearEquiv_conj, hWF, map_zero]
    · by_cases heq : i = n
      · subst i
        have hnot : ¬(n < n ∧ n < 2 * n) := by omega
        obtain ⟨W, hWmon, hWF, hWnorm⟩ := hWmid
        refine ⟨W, hWmon, ?_, hWnorm⟩
        simp only [F', dif_neg hnot, aeval_linearEquiv_conj, hWF, map_zero]
      · have hhi : n < i ∧ i < 2 * n := ⟨by omega, h2⟩
        let j := 2 * n - i
        have hj1 : 1 ≤ j := by omega
        have hjlt : j < n := by omega
        obtain ⟨W, hWmon, hWF, hWnorm⟩ := hWlow j hj1 hjlt
        refine ⟨scalePoly W ((Nat.card k : ℤ) ^ (n - j)), monic_scalePoly hWmon _, ?_, ?_⟩
        · simp only [F', dif_pos hhi, aeval_linearEquiv_conj, aeval_dualMap]
          have hzero : aeval (qK • ((F j).symm : V j →ₗ[K] V j))
              (scalePoly W ((Nat.card k : ℤ) ^ (n - j))) = 0 :=
            aeval_scalePoly_inv_eq_zero hq_pos hjlt (F j) hWmon hWF hWnorm
          change (upperDualEquivDual (K := K) (V := V) (n := n) hhi).symm.conj
            ((aeval (qK • ((F j).symm : V j →ₗ[K] V j))
              (scalePoly W ((Nat.card k : ℤ) ^ (n - j)))).dualMap) = 0
          rw [hzero, dualMap_zero, map_zero]
        · intro z hz
          have hqR : (0 : ℝ) < (Nat.card k : ℝ) := Nat.cast_pos.mpr hq_pos
          have hqC : (Nat.card k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq_pos)
          have hqnjC : (((Nat.card k : ℤ) ^ (n - j) : ℤ) : ℂ) ≠ 0 := by
            push_cast; exact pow_ne_zero _ hqC
          rw [aeval_scalePoly_complex W ((Nat.card k : ℤ) ^ (n - j)) hqnjC z] at hz
          have hWz : aeval (z / (((Nat.card k : ℤ) ^ (n - j) : ℤ) : ℂ)) W = 0 :=
            (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hqnjC)
          have hnz := hWnorm _ hWz
          have hcastC : (((Nat.card k : ℤ) ^ (n - j) : ℤ) : ℂ) = (Nat.card k : ℂ) ^ (n - j) := by
            push_cast; rfl
          rw [hcastC, norm_div, norm_pow, Complex.norm_natCast] at hnz
          have hpos_pow : (0 : ℝ) < (Nat.card k : ℝ) ^ (n - j) := pow_pos hqR _
          have hnorm_eq : ‖z‖ = (Nat.card k : ℝ) ^ (n - j) * (Nat.card k : ℝ) ^ ((j : ℝ) / 2) := by
            have := (div_eq_iff (ne_of_gt hpos_pow)).mp hnz
            linarith
          rw [hnorm_eq, ← Real.rpow_natCast, ← Real.rpow_add hqR]
          have hexp : ((n - j : ℕ) : ℝ) + (j : ℝ) / 2 = (i : ℝ) / 2 := by
            have hji : 2 * (n - j) + j = i := by omega
            have hjiR : (2 : ℝ) * ((n - j : ℕ) : ℝ) + (j : ℝ) = (i : ℝ) := by exact_mod_cast hji
            linarith
          rw [hexp]
