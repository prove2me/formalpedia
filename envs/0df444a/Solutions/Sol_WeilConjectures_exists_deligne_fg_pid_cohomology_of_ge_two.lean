-- Prove2me | solution 1 for WeilConjectures.exists_deligne_fg_pid_cohomology_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T21:25:34.866954+00:00
-- url     : https://prove2.me/submissions/17f5e519-103b-4cfa-9488-757926219b39
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_ladic_cohomology_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open scoped TensorProduct
open WeilConjectures

section PadicFractionTransfer

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
    rcases hxT with ⟨⟨r, hr⟩, hrx⟩
    have hr_ne : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
    have hrx' : r • x = 0 := hrx
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
        _ = 0 := by rw [hrx', TensorProduct.tmul_zero, smul_zero]
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

private lemma trace_baseChange_of_algEquiv {R K₁ K₂ M : Type*} [CommRing R]
    [Field K₁] [Field K₂] [Algebra R K₁] [Algebra R K₂] (eF : K₁ ≃ₐ[R] K₂)
    [AddCommGroup M] [Module R M] [Module.Finite R M] (f : M →ₗ[R] M) :
    LinearMap.trace K₂ (K₂ ⊗[R] M) (f.baseChange K₂) =
      eF (LinearMap.trace K₁ (K₁ ⊗[R] M) (f.baseChange K₁)) := by
  let _ : Algebra K₁ K₂ := eF.toRingHom.toAlgebra
  let _ : IsScalarTower R K₁ K₂ := IsScalarTower.of_algebraMap_eq (fun r => (eF.commutes r).symm)
  let Ψ := TensorProduct.AlgebraTensorModule.cancelBaseChange R K₁ K₂ K₂ M
  have hconj : Ψ.conj ((f.baseChange K₁).baseChange K₂) = f.baseChange K₂ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c₂ x
    change Ψ (((f.baseChange K₁).baseChange K₂) (Ψ.symm (c₂ ⊗ₜ[R] x))) =
      (f.baseChange K₂) (c₂ ⊗ₜ[R] x)
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  rw [← hconj, LinearMap.trace_conj', LinearMap.trace_baseChange]
  rfl

private lemma finrank_baseChange_of_algEquiv {R K₁ K₂ M : Type*} [CommRing R]
    [Field K₁] [Field K₂] [Algebra R K₁] [Algebra R K₂] (eF : K₁ ≃ₐ[R] K₂)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.finrank K₂ (K₂ ⊗[R] M) = Module.finrank K₁ (K₁ ⊗[R] M) := by
  let _ : Algebra K₁ K₂ := eF.toRingHom.toAlgebra
  let _ : IsScalarTower R K₁ K₂ := IsScalarTower.of_algebraMap_eq (fun r => (eF.commutes r).symm)
  let Ψ := TensorProduct.AlgebraTensorModule.cancelBaseChange R K₁ K₂ K₂ M
  rw [← Ψ.finrank_eq, Module.finrank_baseChange]

private lemma exists_ne_zero_of_pow_prime_smul {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*}
    [AddCommGroup M] [Module (PadicInt ℓ) M] {x : M}
    (h : ∃ t : ℕ, ℓ ^ t • x = 0) :
    ∃ r : PadicInt ℓ, r ≠ 0 ∧ r • x = 0 := by
  obtain ⟨t, ht⟩ := h
  refine ⟨((ℓ ^ t : ℕ) : PadicInt ℓ), ?_, ?_⟩
  · exact Nat.cast_ne_zero.mpr (pow_ne_zero t (Fact.out : ℓ.Prime).ne_zero)
  · rwa [Nat.cast_smul_eq_nsmul]

end PadicFractionTransfer

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsPrincipalIdealRing R) (_ : CharZero R)
      (M : ℕ → Type) (_ : ∀ i, AddCommGroup (M i)) (_ : ∀ i, Module R (M i))
      (_ : ∀ i, Module.Finite R (M i))
      (F : ∀ i, M i →ₗ[R] M i)
      (cup : ∀ i, i ≤ n → M i →ₗ[R] M (2 * n - i) →ₗ[R] M (2 * n))
      (tr : M (2 * n) →ₗ[R] R),
      (∀ m : ℕ, 0 < m →
        (pointCount p f m : FractionRing R) =
          ∑ i ∈ Finset.range (2 * n + 1),
            (-1 : FractionRing R) ^ i *
              LinearMap.trace (FractionRing R) (FractionRing R ⊗[R] M i)
                (((F i).baseChange (FractionRing R)) ^ m)) ∧
      (∀ z : M (2 * n), tr (F (2 * n) z) = (Nat.card k : R) ^ n * tr z) ∧
      (∀ i (hi : i ≤ n) (x : M i) (y : M (2 * n - i)),
        cup i hi (F i x) (F (2 * n - i) y) = F (2 * n) (cup i hi x y)) ∧
      (∀ i (hi : i ≤ n),
        (∀ x : M i, (∀ y : M (2 * n - i), tr (cup i hi x y) = 0) →
          ∃ r : R, r ≠ 0 ∧ r • x = 0) ∧
        (∀ y : M (2 * n - i), (∀ x : M i, tr (cup i hi x y) = 0) →
          ∃ r : R, r ≠ 0 ∧ r • y = 0)) ∧
      Module.finrank R (M 0) = 1 ∧
      (∀ x : M 0, ∃ r : R, r ≠ 0 ∧ r • (F 0 x - x) = 0) ∧
      (∀ i ≤ 2 * n, ∃ W : ℤ[X], W ≠ 0 ∧
        (∀ x : M i, ∃ r : R, r ≠ 0 ∧ r • (aeval (F i) W x) = 0) ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  let ℓ : ℕ := if p = 2 then 3 else 2
  have hℓ_prime : ℓ.Prime := by
    dsimp only [ℓ]
    split_ifs
    · exact Nat.prime_three
    · exact Nat.prime_two
  let _ : Fact ℓ.Prime := ⟨hℓ_prime⟩
  have hℓp : ℓ ≠ p := by
    dsimp only [ℓ]
    split_ifs with hp2
    · omega
    · exact Ne.symm hp2
  obtain ⟨M, hMAdd, hMMod, hMFin, F, cup, tr, htr, htopF, hcupF, hnondeg, hfin0, hF0, hW⟩ :=
    WeilConjectures.exists_ladic_cohomology_of_ge_two p k n hn X f hproj ℓ hℓp
  let _ : ∀ i, AddCommGroup (M i) := hMAdd
  let _ : ∀ i, Module (PadicInt ℓ) (M i) := hMMod
  let _ : ∀ i, Module.Finite (PadicInt ℓ) (M i) := hMFin
  let eF : Padic ℓ ≃ₐ[PadicInt ℓ] FractionRing (PadicInt ℓ) :=
    IsLocalization.algEquiv (nonZeroDivisors (PadicInt ℓ)) (Padic ℓ) (FractionRing (PadicInt ℓ))
  refine ⟨PadicInt ℓ, inferInstance, inferInstance, inferInstance, inferInstance,
    M, hMAdd, hMMod, hMFin, F, cup, tr, ?_, htopF, hcupF, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have h1 := congrArg eF (htr m hm)
    rw [map_natCast, map_sum] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_neg, map_one]
    congr 1
    rw [baseChange_pow, baseChange_pow, trace_baseChange_of_algEquiv eF (F i ^ m)]
  · intro i hi
    exact ⟨fun x hx => exists_ne_zero_of_pow_prime_smul ((hnondeg i hi).1 x hx),
      fun y hy => exists_ne_zero_of_pow_prime_smul ((hnondeg i hi).2 y hy)⟩
  · let T0 := Submodule.torsion (PadicInt ℓ) (M 0)
    let _ : Module.Free (PadicInt ℓ) (M 0 ⧸ T0) := Module.free_of_finite_type_torsion_free'
    have hq := finrank_quotient_eq_of_le_torsion (R := PadicInt ℓ) (M := M 0) (M' := T0) le_rfl
    have heq := (baseChangeTorsionQuotEquiv (R := PadicInt ℓ) (M := M 0)).finrank_eq
    rw [← hq, ← Module.finrank_baseChange (R := FractionRing (PadicInt ℓ)) (S := PadicInt ℓ),
      ← heq, finrank_baseChange_of_algEquiv eF, hfin0]
  · intro x
    exact exists_ne_zero_of_pow_prime_smul (hF0 x)
  · intro i hi
    obtain ⟨W, hWne, hWann, hWnorm⟩ := hW i hi
    exact ⟨W, hWne, fun x => exists_ne_zero_of_pow_prime_smul (hWann x), hWnorm⟩
