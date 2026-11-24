-- Prove2me | solution 1 for WeilConjectures.exists_ladic_cohomology_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T22:35:05.996082+00:00
-- url     : https://prove2.me/submissions/4eae5d61-b5b5-4a25-82cc-3a2331103c23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_qladic_weil_cohomology_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open scoped TensorProduct
open WeilConjectures

section QladicLatticeConstruction

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

private lemma exists_denom_smul_tmul_of_isFractionRing {R K M : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup M] [Module R M]
    (u : TensorProduct R K M) :
    ∃ (d : R) (x : M), d ≠ 0 ∧ u = (algebraMap R K d)⁻¹ • ((1 : K) ⊗ₜ[R] x) := by
  induction u using TensorProduct.induction_on with
  | zero =>
    refine ⟨1, 0, one_ne_zero, ?_⟩
    simp
  | tmul c x =>
    obtain ⟨⟨a, s⟩, hcs⟩ := IsLocalization.surj (nonZeroDivisors R) c
    have hs_ne : (s : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.2
    have hsg_ne : algebraMap R K (s : R) ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hs_ne
    have hc_eq : c = (algebraMap R K (s : R))⁻¹ * algebraMap R K a := by
      have hmul : algebraMap R K (s : R) * c = algebraMap R K a := by
        rw [mul_comm]; exact hcs
      calc
        c = (algebraMap R K (s : R))⁻¹ * (algebraMap R K (s : R) * c) := by
            rw [← mul_assoc, inv_mul_cancel₀ hsg_ne, one_mul]
        _ = (algebraMap R K (s : R))⁻¹ * algebraMap R K a := by rw [hmul]
    refine ⟨(s : R), a • x, hs_ne, ?_⟩
    calc
      c ⊗ₜ[R] x
          = ((algebraMap R K (s : R))⁻¹ * algebraMap R K a) ⊗ₜ[R] x := by rw [hc_eq]
      _ = (algebraMap R K (s : R))⁻¹ • ((algebraMap R K a) ⊗ₜ[R] x) := by
            rw [← smul_eq_mul, TensorProduct.smul_tmul']
      _ = (algebraMap R K (s : R))⁻¹ • ((a • (1 : K)) ⊗ₜ[R] x) := by
            rw [Algebra.smul_def, mul_one]
      _ = (algebraMap R K (s : R))⁻¹ • ((1 : K) ⊗ₜ[R] (a • x)) := by
            rw [TensorProduct.smul_tmul]
  | add u₁ u₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨d₁, x₁, hd₁, rfl⟩
    rcases ih₂ with ⟨d₂, x₂, hd₂, rfl⟩
    have hd12 : d₁ * d₂ ≠ 0 := mul_ne_zero hd₁ hd₂
    have hdg1 : algebraMap R K d₁ ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hd₁
    have hdg2 : algebraMap R K d₂ ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hd₂
    refine ⟨d₁ * d₂, d₂ • x₁ + d₁ • x₂, hd12, ?_⟩
    rw [TensorProduct.tmul_add, smul_add, map_mul, mul_inv]
    congr 1
    · calc
        (algebraMap R K d₁)⁻¹ • ((1 : K) ⊗ₜ[R] x₁)
            = ((algebraMap R K d₁)⁻¹ * (algebraMap R K d₂)⁻¹ * algebraMap R K d₂) •
                ((1 : K) ⊗ₜ[R] x₁) := by
              rw [mul_assoc, inv_mul_cancel₀ hdg2, mul_one]
        _ = ((algebraMap R K d₁)⁻¹ * (algebraMap R K d₂)⁻¹) •
              ((algebraMap R K d₂) • ((1 : K) ⊗ₜ[R] x₁)) := by rw [mul_smul]
        _ = ((algebraMap R K d₁)⁻¹ * (algebraMap R K d₂)⁻¹) •
              ((d₂ • (1 : K)) ⊗ₜ[R] x₁) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
        _ = ((algebraMap R K d₁)⁻¹ * (algebraMap R K d₂)⁻¹) •
              ((1 : K) ⊗ₜ[R] (d₂ • x₁)) := by rw [TensorProduct.smul_tmul]
    · calc
        (algebraMap R K d₂)⁻¹ • ((1 : K) ⊗ₜ[R] x₂)
            = ((algebraMap R K d₁)⁻¹ * (algebraMap R K d₂)⁻¹ * algebraMap R K d₁) •
                ((1 : K) ⊗ₜ[R] x₂) := by
              rw [mul_comm (algebraMap R K d₁)⁻¹, mul_assoc, inv_mul_cancel₀ hdg1, mul_one]
        _ = ((algebraMap R K d₁)⁻¹ * (algebraMap R K d₂)⁻¹) •
              ((algebraMap R K d₁) • ((1 : K) ⊗ₜ[R] x₂)) := by rw [mul_smul]
        _ = ((algebraMap R K d₁)⁻¹ * (algebraMap R K d₂)⁻¹) •
              ((d₁ • (1 : K)) ⊗ₜ[R] x₂) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
        _ = ((algebraMap R K d₁)⁻¹ * (algebraMap R K d₂)⁻¹) •
              ((1 : K) ⊗ₜ[R] (d₁ • x₂)) := by rw [TensorProduct.smul_tmul]

private noncomputable def latticeSpanEquiv {R K V : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (L : Submodule R V)
    (hspan : ∀ v : V, v ∈ Submodule.span K (L : Set V)) :
    (K ⊗[R] L) ≃ₗ[K] V := by
  let Φ : (K ⊗[R] L) →ₗ[K] V :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun c =>
          { toFun := fun x => c • (x : V)
            map_add' := fun x₁ x₂ => by simp [smul_add]
            map_smul' := fun r x => by
              change c • (r • (x : V)) = r • (c • (x : V))
              rw [← IsScalarTower.algebraMap_smul K r (x : V),
                ← IsScalarTower.algebraMap_smul K r (c • (x : V)),
                smul_comm] }
        map_add' := fun c₁ c₂ => by
          ext x; simp [add_smul]
        map_smul' := fun k c => by
          ext x; simp [mul_smul] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    obtain ⟨d, x, hd_ne, rfl⟩ := exists_denom_smul_tmul_of_isFractionRing u
    have hdg_ne : algebraMap R K d ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hd_ne
    have h0 : Φ ((algebraMap R K d)⁻¹ • ((1 : K) ⊗ₜ[R] x)) = 0 := LinearMap.mem_ker.mp hu
    rw [map_smul, smul_eq_zero] at h0
    have hxV : (x : V) = 0 := by
      have h1 := h0.resolve_left (inv_ne_zero hdg_ne)
      simpa [Φ] using h1
    have hx0 : x = 0 := Subtype.ext hxV
    rw [hx0, TensorProduct.tmul_zero, smul_zero]
  have hsurj : Function.Surjective Φ := by
    intro v
    have hv := hspan v
    induction hv using Submodule.span_induction with
    | mem x hx =>
      exact ⟨(1 : K) ⊗ₜ[R] ⟨x, hx⟩, by simp [Φ]⟩
    | zero => exact ⟨0, map_zero Φ⟩
    | add x y _ _ ihx ihy =>
      rcases ihx with ⟨ux, rfl⟩
      rcases ihy with ⟨uy, rfl⟩
      exact ⟨ux + uy, map_add Φ ux uy⟩
    | smul c x _ ihx =>
      rcases ihx with ⟨ux, rfl⟩
      exact ⟨c • ux, map_smul Φ c ux⟩
  exact LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩

private lemma exists_frob_stable_lattice {R K V : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] [Module R V] [IsScalarTower R K V]
    (F : V →ₗ[K] V) (W : ℤ[X]) (hW : W.Monic) (hWF : aeval F W = 0) :
    ∃ (S : Finset V),
      (∀ j, Module.finBasis K V j ∈ S) ∧
      (∀ x ∈ Submodule.span R (S : Set V), F x ∈ Submodule.span R (S : Set V)) := by
  classical
  let b := Module.finBasis K V
  let deg := max 1 W.natDegree
  let S : Finset V :=
    (Finset.univ : Finset (Fin (Module.finrank K V) × Fin deg)).image
      (fun p => (F ^ (p.2 : ℕ)) (b p.1))
  refine ⟨S, ?_, ?_⟩
  · intro j
    have h0 : (0 : ℕ) < deg := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 W.natDegree)
    exact Finset.mem_image.mpr ⟨(j, ⟨0, h0⟩), Finset.mem_univ _, by simp [b]⟩
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases Finset.mem_image.mp hy with ⟨⟨j, ⟨k, hk⟩⟩, _, rfl⟩
      by_cases hdeg0 : W.natDegree = 0
      · have hW1 : W = 1 := by
          rw [Polynomial.as_sum_range_C_mul_X_pow W, hdeg0, Finset.range_one,
            Finset.sum_singleton, pow_zero, mul_one]
          have hc0 : W.coeff 0 = 1 := by
            simpa [Polynomial.leadingCoeff, hdeg0] using hW.leadingCoeff
          rw [hc0, map_one]
        have h10 : (1 : Module.End K V) = 0 := by
          simpa [hW1] using hWF
        have hzero : F ((F ^ k) (b j)) = 0 := by
          have hv : (F ^ k) (b j) = 0 := by
            have := congrArg (fun g : Module.End K V => g ((F ^ k) (b j))) h10
            simpa [Module.End.one_apply] using this
          rw [hv, map_zero]
        rw [hzero]
        exact Submodule.zero_mem _
      · have hdeg_pos : 0 < W.natDegree := Nat.pos_of_ne_zero hdeg0
        have hdeg_eq : deg = W.natDegree := max_eq_right hdeg_pos
        have hk_lt : k < W.natDegree := hdeg_eq ▸ hk
        have hFpow : F ((F ^ k) (b j)) = (F ^ (k + 1)) (b j) := by
          rw [pow_succ', Module.End.mul_apply]
        rw [hFpow]
        by_cases hk1 : k + 1 < W.natDegree
        · apply Submodule.subset_span
          exact Finset.mem_image.mpr
            ⟨(j, ⟨k + 1, hdeg_eq.symm ▸ hk1⟩), Finset.mem_univ _, rfl⟩
        · have hk1_eq : k + 1 = W.natDegree := by omega
          rw [hk1_eq]
          have hWsum : W =
              (∑ t ∈ Finset.range W.natDegree, C (W.coeff t) * X ^ t) + X ^ W.natDegree := by
            conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow W]
            rw [Finset.sum_range_succ, show W.coeff W.natDegree = 1 from hW.leadingCoeff,
              map_one, one_mul]
          have hEv0 : aeval F W (b j) = 0 := by rw [hWF]; rfl
          rw [hWsum, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply,
            aeval_X_pow] at hEv0
          have hpow_eq : (F ^ W.natDegree) (b j) =
              - ∑ t ∈ Finset.range W.natDegree, ((W.coeff t : ℤ) : R) • ((F ^ t) (b j)) := by
            have hterm : ∀ t ∈ Finset.range W.natDegree,
                aeval F (C (W.coeff t) * X ^ t) (b j) = ((W.coeff t : ℤ) : R) • ((F ^ t) (b j)) := by
              intro t _
              rw [map_mul, aeval_C, aeval_X_pow, Module.End.mul_apply]
              change ((W.coeff t : ℤ) • (1 : Module.End K V)) ((F ^ t) (b j)) =
                ((W.coeff t : ℤ) : R) • ((F ^ t) (b j))
              rw [LinearMap.smul_apply, Module.End.one_apply,
                ← IsScalarTower.algebraMap_smul K ((W.coeff t : ℤ) : R), map_intCast,
                Int.cast_smul_eq_zsmul]
            rw [Finset.sum_congr rfl hterm] at hEv0
            exact eq_neg_of_add_eq_zero_right hEv0
          rw [hpow_eq]
          refine Submodule.neg_mem _ (Submodule.sum_mem _ fun t ht => ?_)
          have ht_lt : t < deg := hdeg_eq.symm ▸ Finset.mem_range.mp ht
          refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
          exact Finset.mem_image.mpr ⟨(j, ⟨t, ht_lt⟩), Finset.mem_univ _, rfl⟩
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add y z _ _ ihy ihz =>
      rw [map_add]
      exact Submodule.add_mem _ ihy ihz
    | smul r y _ ihy =>
      rw [← IsScalarTower.algebraMap_smul K r y, map_smul, IsScalarTower.algebraMap_smul K r (F y)]
      exact Submodule.smul_mem _ r ihy

private lemma restrict_pow_val {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (F : V →ₗ[K] V) (L : Submodule R V) (hL : ∀ x ∈ L, F x ∈ L)
    (m : ℕ) (x : L) :
    ((((F.restrictScalars R).restrict hL ^ m) x : L) : V) = (F ^ m) (x : V) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    change F ((((F.restrictScalars R).restrict hL ^ m) x : L) : V) = F ((F ^ m) (x : V))
    rw [ih]

private lemma aeval_restrict_val {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (F : V →ₗ[K] V) (L : Submodule R V) (hL : ∀ x ∈ L, F x ∈ L)
    (P : ℤ[X]) (x : L) :
    ((aeval ((F.restrictScalars R).restrict hL) P x : L) : V) = aeval F P (x : V) := by
  induction P using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, ihp, ihq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply,
      Submodule.coe_smul_of_tower, restrict_pow_val]

private lemma exists_scaled_integral_tr {R K V : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (S : Finset V) (tr : V →ₗ[K] K) :
    ∃ (r : R) (trL : Submodule.span R (S : Set V) →ₗ[R] R),
      r ≠ 0 ∧ ∀ z : Submodule.span R (S : Set V),
        algebraMap R K (trL z) = algebraMap R K r * tr (z : V) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun s : S => tr s.1)
  have hb_ne : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
  have hint : ∀ z ∈ Submodule.span R (S : Set V),
      ∃ a : R, algebraMap R K a = algebraMap R K (b : R) * tr z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha⟩ := hb ⟨x, hx⟩
      refine ⟨a, ?_⟩
      simpa [Algebra.smul_def] using ha
    | zero =>
      exact ⟨0, by simp⟩
    | add x y _ _ ihx ihy =>
      rcases ihx with ⟨ax, hax⟩
      rcases ihy with ⟨ay, hay⟩
      exact ⟨ax + ay, by rw [map_add, map_add, mul_add, hax, hay]⟩
    | smul r x _ ihx =>
      rcases ihx with ⟨ax, hax⟩
      refine ⟨r * ax, ?_⟩
      rw [map_mul, hax, ← IsScalarTower.algebraMap_smul K r x, map_smul, smul_eq_mul]
      ring
  let f : Submodule.span R (S : Set V) → R := fun z => (hint z.1 z.2).choose
  have hf : ∀ z : Submodule.span R (S : Set V),
      algebraMap R K (f z) = algebraMap R K (b : R) * tr (z : V) :=
    fun z => (hint z.1 z.2).choose_spec
  let trL : Submodule.span R (S : Set V) →ₗ[R] R :=
    { toFun := f
      map_add' := fun x y => IsFractionRing.injective R K <| by
        rw [map_add, hf, hf, hf, Submodule.coe_add, map_add, mul_add]
      map_smul' := fun r x => IsFractionRing.injective R K <| by
        rw [RingHom.id_apply, smul_eq_mul, map_mul, hf, hf, Submodule.coe_smul_of_tower,
          ← IsScalarTower.algebraMap_smul K r (x : V), map_smul, smul_eq_mul]
        ring }
  exact ⟨(b : R), trL, hb_ne, hf⟩

private lemma exists_scaled_integral_cup {R K V₁ V₂ V₃ : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V₁] [Module K V₁] [Module R V₁] [IsScalarTower R K V₁]
    [AddCommGroup V₂] [Module K V₂] [Module R V₂] [IsScalarTower R K V₂]
    [AddCommGroup V₃] [Module K V₃] [Module.Finite K V₃] [Module R V₃] [IsScalarTower R K V₃]
    (S₁ : Finset V₁) (S₂ : Finset V₂) (S₃ : Finset V₃)
    (hb₃ : ∀ j, Module.finBasis K V₃ j ∈ S₃)
    (cup : V₁ →ₗ[K] V₂ →ₗ[K] V₃) :
    ∃ (r : R) (cupL : Submodule.span R (S₁ : Set V₁) →ₗ[R]
        Submodule.span R (S₂ : Set V₂) →ₗ[R] Submodule.span R (S₃ : Set V₃)),
      r ≠ 0 ∧ ∀ (x : Submodule.span R (S₁ : Set V₁)) (y : Submodule.span R (S₂ : Set V₂)),
        ((cupL x y : Submodule.span R (S₃ : Set V₃)) : V₃) =
          (algebraMap R K r) • cup (x : V₁) (y : V₂) := by
  let b₃ := Module.finBasis K V₃
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : (S₁ × S₂) × Fin (Module.finrank K V₃) => b₃.repr (cup p.1.1.1 p.1.2.1) p.2)
  have hb_ne : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
  have hmem_gen : ∀ x ∈ S₁, ∀ y ∈ S₂,
      (algebraMap R K (b : R)) • cup x y ∈ Submodule.span R (S₃ : Set V₃) := by
    intro x hx y hy
    have hsum : (algebraMap R K (b : R)) • cup x y =
        ∑ j : Fin (Module.finrank K V₃),
          ((hb ((⟨x, hx⟩, ⟨y, hy⟩), j)).choose : R) • b₃ j := by
      conv_lhs => rw [← b₃.sum_repr (cup x y), Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj := (hb ((⟨x, hx⟩, ⟨y, hy⟩), j)).choose_spec
      rw [← IsScalarTower.algebraMap_smul K ((hb ((⟨x, hx⟩, ⟨y, hy⟩), j)).choose : R),
        hj, Algebra.smul_def, smul_smul]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hb₃ j))
  have hmem : ∀ x ∈ Submodule.span R (S₁ : Set V₁), ∀ y ∈ Submodule.span R (S₂ : Set V₂),
      (algebraMap R K (b : R)) • cup x y ∈ Submodule.span R (S₃ : Set V₃) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hmem_gen x hx y hy
      | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
      | add y₁ y₂ _ _ ih₁ ih₂ =>
        rw [map_add, smul_add]; exact Submodule.add_mem _ ih₁ ih₂
      | smul r y _ ih =>
        rw [← IsScalarTower.algebraMap_smul K r y, map_smul, smul_comm,
          IsScalarTower.algebraMap_smul K r _]
        exact Submodule.smul_mem _ r ih
    | zero =>
      intro y _; rw [map_zero, LinearMap.zero_apply, smul_zero]; exact Submodule.zero_mem _
    | add x₁ x₂ _ _ ih₁ ih₂ =>
      intro y hy
      rw [map_add, LinearMap.add_apply, smul_add]
      exact Submodule.add_mem _ (ih₁ y hy) (ih₂ y hy)
    | smul r x _ ih =>
      intro y hy
      rw [← IsScalarTower.algebraMap_smul K r x, map_smul, LinearMap.smul_apply, smul_comm,
        IsScalarTower.algebraMap_smul K r _]
      exact Submodule.smul_mem _ r (ih y hy)
  let cupL : Submodule.span R (S₁ : Set V₁) →ₗ[R]
      Submodule.span R (S₂ : Set V₂) →ₗ[R] Submodule.span R (S₃ : Set V₃) :=
    { toFun := fun x =>
        { toFun := fun y => ⟨(algebraMap R K (b : R)) • cup x.1 y.1, hmem x.1 x.2 y.1 y.2⟩
          map_add' := fun y₁ y₂ => Subtype.ext <| by simp [map_add, smul_add]
          map_smul' := fun r y => Subtype.ext <| by
            change (algebraMap R K (b : R)) • cup x.1 (r • y.1) =
              r • ((algebraMap R K (b : R)) • cup x.1 y.1)
            rw [← IsScalarTower.algebraMap_smul K r y.1, map_smul, smul_comm,
              IsScalarTower.algebraMap_smul K r _] }
      map_add' := fun x₁ x₂ => by
        ext y; simp [map_add, smul_add]
      map_smul' := fun r x => by
        ext y
        change (algebraMap R K (b : R)) • cup (r • x.1) y.1 =
          r • ((algebraMap R K (b : R)) • cup x.1 y.1)
        rw [← IsScalarTower.algebraMap_smul K r x.1, map_smul, LinearMap.smul_apply, smul_comm,
          IsScalarTower.algebraMap_smul K r _] }
  exact ⟨(b : R), cupL, hb_ne, fun _ _ => rfl⟩

end QladicLatticeConstruction

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ (M : ℕ → Type) (_ : ∀ i, AddCommGroup (M i)) (_ : ∀ i, Module (PadicInt ℓ) (M i))
      (_ : ∀ i, Module.Finite (PadicInt ℓ) (M i))
      (F : ∀ i, M i →ₗ[PadicInt ℓ] M i)
      (cup : ∀ i, i ≤ n → M i →ₗ[PadicInt ℓ] M (2 * n - i) →ₗ[PadicInt ℓ] M (2 * n))
      (tr : M (2 * n) →ₗ[PadicInt ℓ] PadicInt ℓ),
      (∀ m : ℕ, 0 < m →
        (pointCount p f m : Padic ℓ) =
          ∑ i ∈ Finset.range (2 * n + 1),
            (-1 : Padic ℓ) ^ i *
              LinearMap.trace (Padic ℓ) (Padic ℓ ⊗[PadicInt ℓ] M i)
                (((F i).baseChange (Padic ℓ)) ^ m)) ∧
      (∀ z : M (2 * n), tr (F (2 * n) z) = (Nat.card k : PadicInt ℓ) ^ n * tr z) ∧
      (∀ i (hi : i ≤ n) (x : M i) (y : M (2 * n - i)),
        cup i hi (F i x) (F (2 * n - i) y) = F (2 * n) (cup i hi x y)) ∧
      (∀ i (hi : i ≤ n),
        (∀ x : M i, (∀ y : M (2 * n - i), tr (cup i hi x y) = 0) →
          ∃ t : ℕ, ℓ ^ t • x = 0) ∧
        (∀ y : M (2 * n - i), (∀ x : M i, tr (cup i hi x y) = 0) →
          ∃ t : ℕ, ℓ ^ t • y = 0)) ∧
      Module.finrank (Padic ℓ) (Padic ℓ ⊗[PadicInt ℓ] M 0) = 1 ∧
      (∀ x : M 0, ∃ t : ℕ, ℓ ^ t • (F 0 x - x) = 0) ∧
      (∀ i ≤ 2 * n, ∃ W : ℤ[X], W ≠ 0 ∧
        (∀ x : M i, ∃ t : ℕ, ℓ ^ t • (aeval (F i) W x) = 0) ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  obtain ⟨V, hVAdd, hVMod, hVFin, F, cup, tr, htr, htopF, hcupF, hnondeg, hfin0, hF0, hW⟩ :=
    WeilConjectures.exists_qladic_weil_cohomology_of_ge_two p k n hn X f hproj ℓ hℓp
  let _ : ∀ i, AddCommGroup (V i) := hVAdd
  let _ : ∀ i, Module (Padic ℓ) (V i) := hVMod
  let _ : ∀ i, Module.Finite (Padic ℓ) (V i) := hVFin
  let _ : ∀ i, Module (PadicInt ℓ) (V i) :=
    fun i => Module.compHom (V i) (algebraMap (PadicInt ℓ) (Padic ℓ))
  let _ : ∀ i, IsScalarTower (PadicInt ℓ) (Padic ℓ) (V i) :=
    fun _ => IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hlat : ∀ i : ℕ, ∃ (S : Finset (V i)),
      (i ≤ 2 * n → ∀ j, Module.finBasis (Padic ℓ) (V i) j ∈ S) ∧
      (∀ x ∈ Submodule.span (PadicInt ℓ) (S : Set (V i)),
        F i x ∈ Submodule.span (PadicInt ℓ) (S : Set (V i))) := by
    intro i
    by_cases hi : i ≤ 2 * n
    · obtain ⟨W, hWmon, hWF, _⟩ := hW i hi
      obtain ⟨S, hSb, hSF⟩ := exists_frob_stable_lattice (R := PadicInt ℓ) (F i) W hWmon hWF
      exact ⟨S, fun _ => hSb, hSF⟩
    · refine ⟨∅, fun h => False.elim (hi h), ?_⟩
      intro x hx
      rw [Finset.coe_empty, Submodule.span_empty] at hx ⊢
      rw [Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact Submodule.zero_mem _
  let S : ∀ i : ℕ, Finset (V i) := fun i => (hlat i).choose
  have hSb : ∀ i, i ≤ 2 * n → ∀ j, Module.finBasis (Padic ℓ) (V i) j ∈ S i :=
    fun i => (hlat i).choose_spec.1
  have hSF : ∀ i, ∀ x ∈ Submodule.span (PadicInt ℓ) (S i : Set (V i)),
      F i x ∈ Submodule.span (PadicInt ℓ) (S i : Set (V i)) :=
    fun i => (hlat i).choose_spec.2
  let L : ∀ i : ℕ, Submodule (PadicInt ℓ) (V i) :=
    fun i => Submodule.span (PadicInt ℓ) (S i : Set (V i))
  let M : ℕ → Type := fun i => ↥(L i)
  have hMFin : ∀ i, Module.Finite (PadicInt ℓ) (M i) :=
    fun i => Module.Finite.iff_fg.mpr (Submodule.fg_span (S i).finite_toSet)
  let FL : ∀ i, M i →ₗ[PadicInt ℓ] M i :=
    fun i => ((F i).restrictScalars (PadicInt ℓ)).restrict (hSF i)
  have hLspan : ∀ i, i ≤ 2 * n → ∀ v : V i, v ∈ Submodule.span (Padic ℓ) (L i : Set (V i)) := by
    intro i hi v
    rw [← (Module.finBasis (Padic ℓ) (V i)).sum_repr v]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Submodule.subset_span (hSb i hi j)
  let Φ : ∀ i, i ≤ 2 * n → (Padic ℓ ⊗[PadicInt ℓ] M i) ≃ₗ[Padic ℓ] V i :=
    fun i hi => latticeSpanEquiv (L i) (hLspan i hi)
  obtain ⟨r_tr, trL, hr_tr_ne, htrL⟩ := exists_scaled_integral_tr (R := PadicInt ℓ) (S (2 * n)) tr
  have hcup_ex : ∀ i (hi : i ≤ n),
      ∃ (r : PadicInt ℓ) (cupL : M i →ₗ[PadicInt ℓ] M (2 * n - i) →ₗ[PadicInt ℓ] M (2 * n)),
        r ≠ 0 ∧ ∀ (x : M i) (y : M (2 * n - i)),
          ((cupL x y : M (2 * n)) : V (2 * n)) =
            (algebraMap (PadicInt ℓ) (Padic ℓ) r) • cup i hi (x : V i) (y : V (2 * n - i)) :=
    fun i hi => exists_scaled_integral_cup (R := PadicInt ℓ) (S i) (S (2 * n - i)) (S (2 * n))
      (hSb (2 * n) le_rfl) (cup i hi)
  let r_cup : ∀ i, i ≤ n → PadicInt ℓ := fun i hi => (hcup_ex i hi).choose
  let cupL : ∀ i, i ≤ n → M i →ₗ[PadicInt ℓ] M (2 * n - i) →ₗ[PadicInt ℓ] M (2 * n) :=
    fun i hi => (hcup_ex i hi).choose_spec.choose
  have hr_cup_ne : ∀ i (hi : i ≤ n), r_cup i hi ≠ 0 :=
    fun i hi => (hcup_ex i hi).choose_spec.choose_spec.1
  have hcupL : ∀ i (hi : i ≤ n) (x : M i) (y : M (2 * n - i)),
      ((cupL i hi x y : M (2 * n)) : V (2 * n)) =
        (algebraMap (PadicInt ℓ) (Padic ℓ) (r_cup i hi)) • cup i hi (x : V i) (y : V (2 * n - i)) :=
    fun i hi => (hcup_ex i hi).choose_spec.choose_spec.2
  refine ⟨M, inferInstance, inferInstance, hMFin, FL, cupL, trL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    rw [htr m hm]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    congr 1
    have hconj : (Φ i hi').conj (((FL i).baseChange (Padic ℓ)) ^ m) = (F i) ^ m := by
      rw [baseChange_pow]
      apply LinearMap.ext
      intro v
      obtain ⟨u, rfl⟩ := (Φ i hi').surjective v
      change (Φ i hi') (((FL i ^ m).baseChange (Padic ℓ)) ((Φ i hi').symm ((Φ i hi') u))) =
        (F i ^ m) ((Φ i hi') u)
      rw [(Φ i hi').symm_apply_apply]
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul c x =>
        rw [LinearMap.baseChange_tmul]
        change c • (((FL i ^ m) x : M i) : V i) = (F i ^ m) (c • (x : V i))
        rw [restrict_pow_val, map_smul]
      | add u₁ u₂ ih₁ ih₂ =>
        simp only [map_add, ih₁, ih₂]
    rw [← hconj, LinearMap.trace_conj']
  · intro z
    apply IsFractionRing.injective (PadicInt ℓ) (Padic ℓ)
    rw [htrL, map_mul, map_pow, map_natCast, htrL]
    change algebraMap (PadicInt ℓ) (Padic ℓ) r_tr * tr (F (2 * n) (z : V (2 * n))) =
      (Nat.card k : Padic ℓ) ^ n * (algebraMap (PadicInt ℓ) (Padic ℓ) r_tr * tr (z : V (2 * n)))
    rw [htopF]
    ring
  · intro i hi x y
    apply Subtype.ext
    rw [hcupL]
    change (algebraMap (PadicInt ℓ) (Padic ℓ) (r_cup i hi)) •
        cup i hi (F i (x : V i)) (F (2 * n - i) (y : V (2 * n - i))) =
      F (2 * n) ((cupL i hi x y : M (2 * n)) : V (2 * n))
    rw [hcupL, hcupF, map_smul]
  · intro i hi
    have hrg_tr : algebraMap (PadicInt ℓ) (Padic ℓ) r_tr ≠ 0 :=
      (map_ne_zero_iff (algebraMap (PadicInt ℓ) (Padic ℓ))
        (IsFractionRing.injective (PadicInt ℓ) (Padic ℓ))).mpr hr_tr_ne
    have hrg_cup : algebraMap (PadicInt ℓ) (Padic ℓ) (r_cup i hi) ≠ 0 :=
      (map_ne_zero_iff (algebraMap (PadicInt ℓ) (Padic ℓ))
        (IsFractionRing.injective (PadicInt ℓ) (Padic ℓ))).mpr (hr_cup_ne i hi)
    constructor
    · intro x hx
      have hxV : (x : V i) = 0 := by
        apply (hnondeg i hi).1 (x : V i)
        intro y
        have hy_span := hLspan (2 * n - i) (by omega) y
        induction hy_span using Submodule.span_induction with
        | mem y0 hy0 =>
          have h0 := congrArg (algebraMap (PadicInt ℓ) (Padic ℓ)) (hx ⟨y0, hy0⟩)
          rw [map_zero, htrL, hcupL, map_smul, smul_eq_mul, ← mul_assoc] at h0
          exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hrg_tr hrg_cup)
        | zero => simp
        | add y₁ y₂ _ _ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
        | smul c y₀ _ ih => simp [map_smul, ih]
      have hx0 : x = 0 := Subtype.ext hxV
      exact ⟨0, by rw [hx0, smul_zero]⟩
    · intro y hy
      have hyV : (y : V (2 * n - i)) = 0 := by
        apply (hnondeg i hi).2 (y : V (2 * n - i))
        intro x
        have hx_span := hLspan i (by omega) x
        induction hx_span using Submodule.span_induction with
        | mem x0 hx0 =>
          have h0 := congrArg (algebraMap (PadicInt ℓ) (Padic ℓ)) (hy ⟨x0, hx0⟩)
          rw [map_zero, htrL, hcupL, map_smul, smul_eq_mul, ← mul_assoc] at h0
          exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hrg_tr hrg_cup)
        | zero => simp
        | add x₁ x₂ _ _ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
        | smul c x₀ _ ih => simp [map_smul, ih]
      have hy0 : y = 0 := Subtype.ext hyV
      exact ⟨0, by rw [hy0, smul_zero]⟩
  · rw [(Φ 0 (Nat.zero_le _)).finrank_eq, hfin0]
  · intro x
    refine ⟨0, ?_⟩
    have hx : FL 0 x - x = 0 := Subtype.ext <| by
      change F 0 (x : V 0) - (x : V 0) = 0
      rw [hF0, LinearMap.id_apply, sub_self]
    rw [hx, smul_zero]
  · intro i hi
    obtain ⟨W, hWmon, hWF, hWnorm⟩ := hW i hi
    refine ⟨W, hWmon.ne_zero, ?_, hWnorm⟩
    intro x
    refine ⟨0, ?_⟩
    have hx : aeval (FL i) W x = 0 := Subtype.ext <| by
      rw [aeval_restrict_val, hWF]; rfl
    rw [hx, smul_zero]
