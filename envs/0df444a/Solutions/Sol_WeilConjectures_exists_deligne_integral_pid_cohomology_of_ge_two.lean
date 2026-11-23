-- Prove2me | solution 1 for WeilConjectures.exists_deligne_integral_pid_cohomology_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T21:08:45.053799+00:00
-- url     : https://prove2.me/submissions/6c77e1b2-15f3-4545-88cb-d88a77ab2cdf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_deligne_fg_pid_cohomology_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open scoped TensorProduct
open WeilConjectures

section TorsionQuotientAndCharpolyLift

private lemma mem_torsion_iff_exists_ne_zero {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] (x : M) :
    x ∈ Submodule.torsion R M ↔ ∃ r : R, r ≠ 0 ∧ r • x = 0 := by
  constructor
  · rintro ⟨⟨r, hr⟩, hrx⟩
    exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, hrx⟩
  · rintro ⟨r, hr, hrx⟩
    exact ⟨⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr⟩, hrx⟩

private lemma exists_denom_smul_tmul {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] (u : TensorProduct R (FractionRing R) M) :
    ∃ (d : R) (x : M), d ≠ 0 ∧
      u = (algebraMap R (FractionRing R) d)⁻¹ • ((1 : FractionRing R) ⊗ₜ[R] x) := by
  induction u using TensorProduct.induction_on with
  | zero =>
    refine ⟨1, 0, one_ne_zero, ?_⟩
    simp
  | tmul c x =>
    obtain ⟨⟨a, s⟩, hcs⟩ := IsLocalization.surj (nonZeroDivisors R) c
    have hs_ne : (s : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.2
    have hsg_ne : algebraMap R (FractionRing R) (s : R) ≠ 0 :=
      (map_ne_zero_iff (algebraMap R (FractionRing R))
        (IsFractionRing.injective R (FractionRing R))).mpr hs_ne
    have hc_eq : c = (algebraMap R (FractionRing R) (s : R))⁻¹ * algebraMap R (FractionRing R) a := by
      have hmul : algebraMap R (FractionRing R) (s : R) * c = algebraMap R (FractionRing R) a := by
        rw [mul_comm]; exact hcs
      calc
        c = (algebraMap R (FractionRing R) (s : R))⁻¹ *
              (algebraMap R (FractionRing R) (s : R) * c) := by
            rw [← mul_assoc, inv_mul_cancel₀ hsg_ne, one_mul]
        _ = (algebraMap R (FractionRing R) (s : R))⁻¹ * algebraMap R (FractionRing R) a := by
            rw [hmul]
    refine ⟨(s : R), a • x, hs_ne, ?_⟩
    calc
      c ⊗ₜ[R] x
          = ((algebraMap R (FractionRing R) (s : R))⁻¹ * algebraMap R (FractionRing R) a) ⊗ₜ[R] x := by
            rw [hc_eq]
      _ = (algebraMap R (FractionRing R) (s : R))⁻¹ •
            ((algebraMap R (FractionRing R) a) ⊗ₜ[R] x) := by
            rw [← smul_eq_mul, TensorProduct.smul_tmul']
      _ = (algebraMap R (FractionRing R) (s : R))⁻¹ •
            ((a • (1 : FractionRing R)) ⊗ₜ[R] x) := by
            rw [Algebra.smul_def, mul_one]
      _ = (algebraMap R (FractionRing R) (s : R))⁻¹ • ((1 : FractionRing R) ⊗ₜ[R] (a • x)) := by
            rw [TensorProduct.smul_tmul]
  | add u₁ u₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨d₁, x₁, hd₁, rfl⟩
    rcases ih₂ with ⟨d₂, x₂, hd₂, rfl⟩
    have hd12 : d₁ * d₂ ≠ 0 := mul_ne_zero hd₁ hd₂
    have hdg1 : algebraMap R (FractionRing R) d₁ ≠ 0 :=
      (map_ne_zero_iff (algebraMap R (FractionRing R))
        (IsFractionRing.injective R (FractionRing R))).mpr hd₁
    have hdg2 : algebraMap R (FractionRing R) d₂ ≠ 0 :=
      (map_ne_zero_iff (algebraMap R (FractionRing R))
        (IsFractionRing.injective R (FractionRing R))).mpr hd₂
    refine ⟨d₁ * d₂, d₂ • x₁ + d₁ • x₂, hd12, ?_⟩
    rw [TensorProduct.tmul_add, smul_add, map_mul, mul_inv]
    congr 1
    · calc
        (algebraMap R (FractionRing R) d₁)⁻¹ • ((1 : FractionRing R) ⊗ₜ[R] x₁)
            = ((algebraMap R (FractionRing R) d₁)⁻¹ * (algebraMap R (FractionRing R) d₂)⁻¹ *
                algebraMap R (FractionRing R) d₂) • ((1 : FractionRing R) ⊗ₜ[R] x₁) := by
              rw [mul_assoc, inv_mul_cancel₀ hdg2, mul_one]
        _ = ((algebraMap R (FractionRing R) d₁)⁻¹ * (algebraMap R (FractionRing R) d₂)⁻¹) •
              ((algebraMap R (FractionRing R) d₂) • ((1 : FractionRing R) ⊗ₜ[R] x₁)) := by
              rw [mul_smul]
        _ = ((algebraMap R (FractionRing R) d₁)⁻¹ * (algebraMap R (FractionRing R) d₂)⁻¹) •
              ((d₂ • (1 : FractionRing R)) ⊗ₜ[R] x₁) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
        _ = ((algebraMap R (FractionRing R) d₁)⁻¹ * (algebraMap R (FractionRing R) d₂)⁻¹) •
              ((1 : FractionRing R) ⊗ₜ[R] (d₂ • x₁)) := by
              rw [TensorProduct.smul_tmul]
    · calc
        (algebraMap R (FractionRing R) d₂)⁻¹ • ((1 : FractionRing R) ⊗ₜ[R] x₂)
            = ((algebraMap R (FractionRing R) d₁)⁻¹ * (algebraMap R (FractionRing R) d₂)⁻¹ *
                algebraMap R (FractionRing R) d₁) • ((1 : FractionRing R) ⊗ₜ[R] x₂) := by
              rw [mul_comm (algebraMap R (FractionRing R) d₁)⁻¹, mul_assoc,
                inv_mul_cancel₀ hdg1, mul_one]
        _ = ((algebraMap R (FractionRing R) d₁)⁻¹ * (algebraMap R (FractionRing R) d₂)⁻¹) •
              ((algebraMap R (FractionRing R) d₁) • ((1 : FractionRing R) ⊗ₜ[R] x₂)) := by
              rw [mul_smul]
        _ = ((algebraMap R (FractionRing R) d₁)⁻¹ * (algebraMap R (FractionRing R) d₂)⁻¹) •
              ((d₁ • (1 : FractionRing R)) ⊗ₜ[R] x₂) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
        _ = ((algebraMap R (FractionRing R) d₁)⁻¹ * (algebraMap R (FractionRing R) d₂)⁻¹) •
              ((1 : FractionRing R) ⊗ₜ[R] (d₁ • x₂)) := by
              rw [TensorProduct.smul_tmul]

private lemma baseChange_pow {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K : Type*) [CommRing K] [Algebra R K] (f : M →ₗ[R] M) (m : ℕ) :
    (f.baseChange K) ^ m = (f ^ m).baseChange K := by
  induction m with
  | zero =>
    ext x
    simp
  | succ m ih =>
    rw [pow_succ, pow_succ, ih, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.baseChange_comp]

private lemma one_tmul_eq_zero_of_free {R N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup N] [Module R N] [Module.Free R N] (y : N)
    (h : ((1 : FractionRing R) ⊗ₜ[R] y) = 0) : y = 0 := by
  let b := Module.Free.chooseBasis R N
  have hb := congrArg (b.baseChange (FractionRing R)).repr h
  rw [map_zero] at hb
  apply b.repr.injective
  rw [map_zero]
  ext j
  have hj := congrArg (fun v => v j) hb
  simp only [Finsupp.zero_apply] at hj
  have hrepr : (b.baseChange (FractionRing R)).repr ((1 : FractionRing R) ⊗ₜ[R] y) j =
      algebraMap R (FractionRing R) (b.repr y j) := by
    have hsum : (1 : FractionRing R) ⊗ₜ[R] y =
        (b.repr y).sum (fun i r => (algebraMap R (FractionRing R) r) •
          (b.baseChange (FractionRing R) i)) := by
      conv_lhs => rw [← b.linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum]
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, Module.Basis.baseChange_apply,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsum, map_finsuppSum]
    simp only [Finsupp.sum_apply, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero]
    simp only [Finsupp.sum, Finset.sum_ite_eq']
    split_ifs with h0
    · rfl
    · rw [Finsupp.notMem_support_iff.mp h0, map_zero]
  rw [hrepr] at hj
  exact IsFractionRing.injective R (FractionRing R) (by simpa using hj)

private noncomputable def baseChangeTorsionQuotEquiv {R M : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (FractionRing R ⊗[R] M) ≃ₗ[FractionRing R]
      (FractionRing R ⊗[R] (M ⧸ Submodule.torsion R M)) := by
  let K := FractionRing R
  let T := Submodule.torsion R M
  let _ : Module.Free R (M ⧸ T) := Module.free_of_finite_type_torsion_free'
  let f : (K ⊗[R] M) →ₗ[K] (K ⊗[R] (M ⧸ T)) := (T.mkQ).baseChange K
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    obtain ⟨d, x, hd_ne, rfl⟩ := exists_denom_smul_tmul u
    have hdg_ne : algebraMap R K d ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hd_ne
    have hfu : f ((algebraMap R K d)⁻¹ • ((1 : K) ⊗ₜ[R] x)) = 0 := LinearMap.mem_ker.mp hu
    rw [map_smul, smul_eq_zero] at hfu
    have htmul0 : (1 : K) ⊗ₜ[R] (T.mkQ x) = 0 := by
      have h1 := hfu.resolve_left (inv_ne_zero hdg_ne)
      simpa [f, LinearMap.baseChange_tmul] using h1
    have hmk0 : T.mkQ x = 0 := one_tmul_eq_zero_of_free (T.mkQ x) htmul0
    have hxT : x ∈ T := (Submodule.Quotient.mk_eq_zero T).mp hmk0
    obtain ⟨r, hr_ne, hrx⟩ := (mem_torsion_iff_exists_ne_zero x).mp hxT
    have hrg_ne : algebraMap R K r ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hr_ne
    have hx_tmul0 : (1 : K) ⊗ₜ[R] x = 0 := by
      calc
        (1 : K) ⊗ₜ[R] x
            = (algebraMap R K r)⁻¹ • ((algebraMap R K r) • ((1 : K) ⊗ₜ[R] x)) := by
              rw [← mul_smul, inv_mul_cancel₀ hrg_ne, one_smul]
        _ = (algebraMap R K r)⁻¹ • ((r • (1 : K)) ⊗ₜ[R] x) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
        _ = (algebraMap R K r)⁻¹ • ((1 : K) ⊗ₜ[R] (r • x)) := by
              rw [TensorProduct.smul_tmul]
        _ = 0 := by rw [hrx, TensorProduct.tmul_zero, smul_zero]
    rw [hx_tmul0, smul_zero]
  have hsurj : Function.Surjective f := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero f⟩
    | tmul c q =>
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective T q
      exact ⟨c ⊗ₜ[R] x, by simp [f, LinearMap.baseChange_tmul]⟩
    | add v₁ v₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨u₁, rfl⟩
      rcases ih₂ with ⟨u₂, rfl⟩
      exact ⟨u₁ + u₂, map_add f u₁ u₂⟩
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

private lemma aeval_mkQ_comm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (T : Submodule R M) (f : M →ₗ[R] M) (hT : T ≤ T.comap f) (W : ℤ[X]) (x : M) :
    T.mkQ (aeval f W x) = aeval (T.mapQ T f hT) W (T.mkQ x) := by
  induction W using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [map_add, LinearMap.add_apply, ihp, ihq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply,
      map_zsmul]
    congr 1
    clear a
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
      rfl

private lemma aeval_baseChange_tmul {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] (f : N →ₗ[R] N) (W : ℤ[X]) (c : S) (y : N) :
    aeval (f.baseChange S) W (c ⊗ₜ[R] y) = c ⊗ₜ[R] (aeval f W y) := by
  induction W using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [map_add, LinearMap.add_apply, TensorProduct.tmul_add, ihp, ihq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply,
      baseChange_pow, LinearMap.baseChange_tmul, TensorProduct.tmul_smul]

private lemma prod_X_sub_C_dvd_pow {L : Type*} [Field L] (P : L[X]) (s : Multiset L)
    (h : ∀ a ∈ s, Polynomial.X - Polynomial.C a ∣ P) :
    (s.map fun a => Polynomial.X - Polynomial.C a).prod ∣ P ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact mul_dvd_mul (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

private lemma charpoly_dvd_pow_of_aeval_int_eq_zero {R N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]
    (f : N →ₗ[R] N) (W : ℤ[X]) (hW : aeval f W = 0) :
    ∃ d : ℕ, f.charpoly ∣ (W ^ d).map (Int.castRingHom R) := by
  let K := FractionRing R
  let L := AlgebraicClosure K
  let fK : (K ⊗[R] N) →ₗ[K] (K ⊗[R] N) := f.baseChange K
  let fL : (L ⊗[K] (K ⊗[R] N)) →ₗ[L] (L ⊗[K] (K ⊗[R] N)) := fK.baseChange L
  have hfK_zero : aeval fK W = 0 := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c y
    change aeval (f.baseChange K) W (c ⊗ₜ[R] y) = 0
    rw [aeval_baseChange_tmul, hW, LinearMap.zero_apply, TensorProduct.tmul_zero]
  have hfL_zero : aeval fL W = 0 := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c u
    change aeval (fK.baseChange L) W (c ⊗ₜ[K] u) = 0
    rw [aeval_baseChange_tmul, hfK_zero, LinearMap.zero_apply, TensorProduct.tmul_zero]
  have hfL_map_zero : aeval fL (W.map (Int.castRingHom L)) = 0 := by
    have hcomp : aeval fL (W.map (Int.castRingHom L)) = aeval fL W := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map]
      congr 1
      exact RingHom.ext_int _ _
    rw [hcomp, hfL_zero]
  have hmin_dvd : minpoly L fL ∣ W.map (Int.castRingHom L) :=
    minpoly.dvd L fL hfL_map_zero
  have hsplit : fL.charpoly =
      (fL.charpoly.roots.map fun a => Polynomial.X - Polynomial.C a).prod :=
    (IsAlgClosed.splits fL.charpoly).eq_prod_roots_of_monic (LinearMap.charpoly_monic fL)
  let d := fL.charpoly.roots.card
  refine ⟨d, ?_⟩
  have hdvdL : fL.charpoly ∣ (W ^ d).map (Int.castRingHom L) := by
    rw [Polynomial.map_pow]
    conv_lhs => rw [hsplit]
    apply prod_X_sub_C_dvd_pow
    intro a ha
    have hroot_cp : fL.charpoly.IsRoot a := Polynomial.isRoot_of_mem_roots ha
    have heig : Module.End.HasEigenvalue fL a :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly fL a).mpr hroot_cp
    have hroot_min : (minpoly L fL).IsRoot a :=
      (Module.End.hasEigenvalue_iff_isRoot (f := fL) (μ := a)).mp heig
    have hroot_W : (W.map (Int.castRingHom L)).IsRoot a := by
      rcases hmin_dvd with ⟨Q, hQ⟩
      rw [Polynomial.IsRoot.def, hQ, Polynomial.eval_mul, hroot_min, zero_mul]
    exact Polynomial.dvd_iff_isRoot.mpr hroot_W
  have hdvdK : fK.charpoly ∣ (W ^ d).map (Int.castRingHom K) := by
    have hmapL : fK.charpoly.map (algebraMap K L) ∣
        ((W ^ d).map (Int.castRingHom K)).map (algebraMap K L) := by
      rw [← LinearMap.charpoly_baseChange (f := fK) (A := L), Polynomial.map_map]
      have hring : (algebraMap K L).comp (Int.castRingHom K) = Int.castRingHom L :=
        RingHom.ext_int _ _
      rw [hring]
      exact hdvdL
    exact (Polynomial.map_dvd_map (algebraMap K L) (algebraMap K L).injective
      (LinearMap.charpoly_monic fK)).mp hmapL
  have hmapK : f.charpoly.map (algebraMap R K) ∣
      ((W ^ d).map (Int.castRingHom R)).map (algebraMap R K) := by
    rw [← LinearMap.charpoly_baseChange (f := f) (A := K), Polynomial.map_map]
    have hring : (algebraMap R K).comp (Int.castRingHom R) = Int.castRingHom K :=
      RingHom.ext_int _ _
    rw [hring]
    exact hdvdK
  exact (Polynomial.map_dvd_map (algebraMap R K) (IsFractionRing.injective R K)
    (LinearMap.charpoly_monic f)).mp hmapK

end TorsionQuotientAndCharpolyLift

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsPrincipalIdealRing R) (_ : CharZero R)
      (M : ℕ → Type) (_ : ∀ i, AddCommGroup (M i)) (_ : ∀ i, Module R (M i))
      (_ : ∀ i, Module.Finite R (M i)) (_ : ∀ i, Module.Free R (M i))
      (F : ∀ i, M i →ₗ[R] M i)
      (cup : ∀ i, i ≤ n → M i →ₗ[R] M (2 * n - i) →ₗ[R] M (2 * n))
      (tr : M (2 * n) →ₗ[R] R),
      (∀ m : ℕ, 0 < m →
        (pointCount p f m : R) =
          ∑ i ∈ Finset.range (2 * n + 1), (-1 : R) ^ i * LinearMap.trace R (M i) (F i ^ m)) ∧
      (∀ z : M (2 * n), tr (F (2 * n) z) = (Nat.card k : R) ^ n * tr z) ∧
      (∀ i (hi : i ≤ n) (x : M i) (y : M (2 * n - i)),
        cup i hi (F i x) (F (2 * n - i) y) = F (2 * n) (cup i hi x y)) ∧
      (∀ i (hi : i ≤ n),
        (∀ x : M i, (∀ y : M (2 * n - i), tr (cup i hi x y) = 0) → x = 0) ∧
        (∀ y : M (2 * n - i), (∀ x : M i, tr (cup i hi x y) = 0) → y = 0)) ∧
      Module.finrank R (M 0) = 1 ∧
      F 0 = LinearMap.id ∧
      (∀ i ≤ 2 * n, ∃ W : ℤ[X], W ≠ 0 ∧ (F i).charpoly ∣ W.map (Int.castRingHom R) ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  obtain ⟨R, hRComm, hRDom, hRPID, hRChar0, M, hMAdd, hMMod, hMFin, F, cup, tr,
      htr, htopF, hcupF, hnondeg, hfin0, hF0, hW⟩ :=
    WeilConjectures.exists_deligne_fg_pid_cohomology_of_ge_two p k n hn X f hproj
  let _ : CommRing R := hRComm
  let _ : IsDomain R := hRDom
  let _ : IsPrincipalIdealRing R := hRPID
  let _ : CharZero R := hRChar0
  let _ : ∀ i, AddCommGroup (M i) := hMAdd
  let _ : ∀ i, Module R (M i) := hMMod
  let _ : ∀ i, Module.Finite R (M i) := hMFin
  let T : ∀ i, Submodule R (M i) := fun i => Submodule.torsion R (M i)
  let N : ℕ → Type := fun i => M i ⧸ T i
  let _ : ∀ i, Module.Finite R (N i) := fun _ => inferInstance
  let _ : ∀ i, Module.IsTorsionFree R (N i) := fun _ => inferInstance
  let _ : ∀ i, Module.Free R (N i) := fun _ => Module.free_of_finite_type_torsion_free'
  have hFT : ∀ i, T i ≤ (T i).comap (F i) := by
    intro i x hx
    obtain ⟨r, hr, hrx⟩ := (mem_torsion_iff_exists_ne_zero x).mp hx
    exact (mem_torsion_iff_exists_ne_zero (F i x)).mpr ⟨r, hr, by rw [← map_smul, hrx, map_zero]⟩
  let FN : ∀ i, N i →ₗ[R] N i := fun i => (T i).mapQ (T i) (F i) (hFT i)
  have htr_ker : T (2 * n) ≤ LinearMap.ker tr := by
    intro z hz
    obtain ⟨r, hr, hrz⟩ := (mem_torsion_iff_exists_ne_zero z).mp hz
    have hmul : r * tr z = 0 := by
      have h1 := congrArg tr hrz
      rw [map_smul, smul_eq_mul, map_zero] at h1
      exact h1
    exact (mul_eq_zero.mp hmul).resolve_left hr
  let trN : N (2 * n) →ₗ[R] R := (T (2 * n)).liftQ tr htr_ker
  let cupN : ∀ i, i ≤ n → N i →ₗ[R] N (2 * n - i) →ₗ[R] N (2 * n) := fun i hi =>
    let raw : M i →ₗ[R] M (2 * n - i) →ₗ[R] N (2 * n) := (cup i hi).compr₂ (T (2 * n)).mkQ
    have hL : T i ≤ LinearMap.ker raw := by
      intro x hx
      obtain ⟨r, hr, hrx⟩ := (mem_torsion_iff_exists_ne_zero x).mp hx
      ext y
      change Submodule.Quotient.mk (p := T (2 * n)) (cup i hi x y) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact (mem_torsion_iff_exists_ne_zero _).mpr
        ⟨r, hr, by rw [← LinearMap.map_smul₂, hrx, map_zero, LinearMap.zero_apply]⟩
    have hR : T (2 * n - i) ≤ LinearMap.ker raw.flip := by
      intro y hy
      obtain ⟨r, hr, hry⟩ := (mem_torsion_iff_exists_ne_zero y).mp hy
      ext x
      change Submodule.Quotient.mk (p := T (2 * n)) (cup i hi x y) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact (mem_torsion_iff_exists_ne_zero _).mpr
        ⟨r, hr, by rw [← map_smul, hry, map_zero]⟩
    raw.liftQ₂ (T i) (T (2 * n - i)) hL hR
  refine ⟨R, hRComm, hRDom, hRPID, hRChar0, N, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, FN, cupN, trN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_natCast, htr m hm, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [map_mul, map_pow, map_neg, map_one]
    congr 1
    let K := FractionRing R
    let e := baseChangeTorsionQuotEquiv (R := R) (M := M i)
    have hconj : e.conj (((F i).baseChange K) ^ m) = ((FN i).baseChange K) ^ m := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro c q
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (T i) q
      have he_eq : c ⊗ₜ[R] Submodule.Quotient.mk (p := T i) x = e (c ⊗ₜ[R] x) := by
        change c ⊗ₜ[R] (T i).mkQ x = ((T i).mkQ).baseChange K (c ⊗ₜ[R] x)
        rw [LinearMap.baseChange_tmul]
      rw [he_eq]
      change e (((F i).baseChange K ^ m) (e.symm (e (c ⊗ₜ[R] x)))) =
        (((FN i).baseChange K) ^ m) (e (c ⊗ₜ[R] x))
      rw [e.symm_apply_apply, baseChange_pow, baseChange_pow, LinearMap.baseChange_tmul, ← he_eq,
        LinearMap.baseChange_tmul]
      change (T i).mkQ.baseChange K (c ⊗ₜ[R] (F i ^ m) x) =
        c ⊗ₜ[R] (FN i ^ m) (Submodule.Quotient.mk (p := T i) x)
      rw [LinearMap.baseChange_tmul]
      congr 1
      clear c he_eq e hm
      induction m generalizing x with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
        rfl
    rw [← LinearMap.trace_conj' (((F i).baseChange K) ^ m) e, hconj, baseChange_pow,
      LinearMap.trace_baseChange]
  · intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (T (2 * n)) q
    exact htopF z
  · intro i hi qx qy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (T i) qx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (T (2 * n - i)) qy
    change (T (2 * n)).mkQ (cup i hi (F i x) (F (2 * n - i) y)) =
      (T (2 * n)).mkQ (F (2 * n) (cup i hi x y))
    rw [hcupF i hi x y]
  · intro i hi
    refine ⟨?_, ?_⟩
    · intro qx hqx
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (T i) qx
      rw [Submodule.Quotient.mk_eq_zero]
      apply (mem_torsion_iff_exists_ne_zero x).mpr
      apply (hnondeg i hi).1 x
      intro y
      exact hqx (Submodule.Quotient.mk (p := T (2 * n - i)) y)
    · intro qy hqy
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (T (2 * n - i)) qy
      rw [Submodule.Quotient.mk_eq_zero]
      apply (mem_torsion_iff_exists_ne_zero y).mpr
      apply (hnondeg i hi).2 y
      intro x
      exact hqy (Submodule.Quotient.mk (p := T i) x)
  · dsimp only [N, T]
    rw [finrank_quotient_eq_of_le_torsion le_rfl, hfin0]
  · ext x
    change Submodule.Quotient.mk (p := T 0) (F 0 x) = Submodule.Quotient.mk (p := T 0) x
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    exact (mem_torsion_iff_exists_ne_zero _).mpr (hF0 x)
  · intro i hi
    obtain ⟨W, hWne, hWann, hWnorm⟩ := hW i hi
    have hFN_ann : aeval (FN i) W = 0 := by
      ext x
      change aeval (FN i) W ((T i).mkQ x) = 0
      rw [← aeval_mkQ_comm (T i) (F i) (hFT i) W x]
      change Submodule.Quotient.mk (p := T i) (aeval (F i) W x) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact (mem_torsion_iff_exists_ne_zero _).mpr (hWann x)
    obtain ⟨d, hdvd⟩ := charpoly_dvd_pow_of_aeval_int_eq_zero (FN i) W hFN_ann
    refine ⟨W ^ d, pow_ne_zero d hWne, hdvd, ?_⟩
    intro z hz
    rw [map_pow] at hz
    exact hWnorm z (eq_zero_of_pow_eq_zero hz)
