-- Prove2me | solution 1 for WeilConjectures.exists_deligne_weight_bound_cohomology_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T20:47:42.495979+00:00
-- url     : https://prove2.me/submissions/4a56074d-fdce-4364-9654-c8d22d4617b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_deligne_integral_pid_cohomology_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open scoped TensorProduct
open WeilConjectures

section DeligneBaseChangeAndDuality

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

private noncomputable def baseChangeBilin {R K U W Z : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [AddCommGroup U] [Module R U] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z] (B : U →ₗ[R] W →ₗ[R] Z) :
    TensorProduct R K U →ₗ[K] TensorProduct R K W →ₗ[K] TensorProduct R K Z :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun c =>
        { toFun := fun u =>
            TensorProduct.AlgebraTensorModule.lift
              { toFun := fun d =>
                  { toFun := fun w => (c * d) ⊗ₜ[R] B u w
                    map_add' := fun w₁ w₂ => by rw [map_add, TensorProduct.tmul_add]
                    map_smul' := fun r w => by
                      simp [map_smul, TensorProduct.tmul_smul] }
                map_add' := fun d₁ d₂ => by
                  ext w; simp [mul_add, TensorProduct.add_tmul]
                map_smul' := fun k d => by
                  ext w
                  simp [TensorProduct.smul_tmul', mul_left_comm] }
          map_add' := fun u₁ u₂ => by
            apply TensorProduct.AlgebraTensorModule.ext
            intro d w
            simp [TensorProduct.tmul_add]
          map_smul' := fun r u => by
            apply TensorProduct.AlgebraTensorModule.ext
            intro d w
            simp [TensorProduct.tmul_smul] }
      map_add' := fun c₁ c₂ => by
        ext u w
        simp [add_mul, TensorProduct.add_tmul]
      map_smul' := fun k c => by
        ext u w
        simp [TensorProduct.smul_tmul', mul_assoc] }

private lemma baseChangeBilin_tmul {R K U W Z : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [AddCommGroup U] [Module R U] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z] (B : U →ₗ[R] W →ₗ[R] Z)
    (c d : K) (u : U) (w : W) :
    baseChangeBilin (K := K) B (c ⊗ₜ[R] u) (d ⊗ₜ[R] w) = (c * d) ⊗ₜ[R] B u w := by
  simp [baseChangeBilin]

private noncomputable def baseChangeTrace {R K Z : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [AddCommGroup Z] [Module R Z] (tr : Z →ₗ[R] R) :
    TensorProduct R K Z →ₗ[K] K :=
  (TensorProduct.AlgebraTensorModule.rid R K K).toLinearMap.comp (tr.baseChange K)

private lemma baseChangeTrace_tmul {R K Z : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [AddCommGroup Z] [Module R Z] (tr : Z →ₗ[R] R) (c : K) (z : Z) :
    baseChangeTrace (K := K) tr (c ⊗ₜ[R] z) = c * algebraMap R K (tr z) := by
  simp [baseChangeTrace, Algebra.smul_def, mul_comm]

private lemma exists_dualEquiv_of_nondeg {K U W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [Module.Finite K U]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (FU : U →ₗ[K] U) (FW : W →ₗ[K] W) (a : K)
    (B : U →ₗ[K] W →ₗ[K] K)
    (hL : ∀ x : U, (∀ y : W, B x y = 0) → x = 0)
    (hR : ∀ y : W, (∀ x : U, B x y = 0) → y = 0)
    (hF : ∀ (x : U) (y : W), B (FU x) (FW y) = a * B x y) :
    ∃ e : U ≃ₗ[K] Module.Dual K W, ∀ (x : U) (y : W), e (FU x) (FW y) = a * e x y := by
  have hinjL : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    apply hL x
    intro y
    exact congrArg (fun φ : Module.Dual K W => φ y) (LinearMap.mem_ker.mp hx)
  have hinjR : Function.Injective B.flip := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    apply hR y
    intro x
    exact congrArg (fun φ : Module.Dual K U => φ x) (LinearMap.mem_ker.mp hy)
  have hle1 : Module.finrank K U ≤ Module.finrank K W := by
    have h1 := LinearMap.finrank_le_finrank_of_injective hinjL
    rwa [Subspace.dual_finrank_eq] at h1
  have hle2 : Module.finrank K W ≤ Module.finrank K U := by
    have h2 := LinearMap.finrank_le_finrank_of_injective hinjR
    rwa [Subspace.dual_finrank_eq] at h2
  have hfin : Module.finrank K U = Module.finrank K (Module.Dual K W) := by
    rw [Subspace.dual_finrank_eq]
    exact le_antisymm hle1 hle2
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinjL
  exact ⟨LinearEquiv.ofBijective B ⟨hinjL, hsurj⟩, hF⟩

end DeligneBaseChangeAndDuality

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (V : ℕ → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module K (V i))
      (_ : ∀ i, Module.Finite K (V i))
      (F : ∀ i, V i →ₗ[K] V i),
      (∀ m : ℕ, 0 < m →
        (pointCount p f m : K) =
          ∑ i ∈ Finset.range (2 * n + 1), (-1 : K) ^ i * LinearMap.trace K (V i) (F i ^ m)) ∧
      (∀ i ≤ 2 * n, ∃ e : V i ≃ₗ[K] Module.Dual K (V (2 * n - i)),
        ∀ (x : V i) (y : V (2 * n - i)),
          e (F i x) (F (2 * n - i) y) = (Nat.card k : K) ^ n * e x y) ∧
      Module.finrank K (V 0) = 1 ∧
      F 0 = LinearMap.id ∧
      (∀ i ≤ 2 * n, ∃ W : ℚ[X], W ≠ 0 ∧ (F i).charpoly ∣ W.map (algebraMap ℚ K) ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  obtain ⟨R, hRComm, hRDom, hRPID, hRChar0, M, hMAdd, hMMod, hMFin, hMFree, F, cup, tr,
      htr, htopF, hcupF, hnondeg, hfin0, hF0, hW⟩ :=
    WeilConjectures.exists_deligne_integral_pid_cohomology_of_ge_two p k n hn X f hproj
  let _ : CommRing R := hRComm
  let _ : IsDomain R := hRDom
  let _ : IsPrincipalIdealRing R := hRPID
  let _ : CharZero R := hRChar0
  let _ : ∀ i, AddCommGroup (M i) := hMAdd
  let _ : ∀ i, Module R (M i) := hMMod
  let _ : ∀ i, Module.Finite R (M i) := hMFin
  let _ : ∀ i, Module.Free R (M i) := hMFree
  let K : Type := FractionRing R
  let _ : CharZero K :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  let V : ℕ → Type := fun i => TensorProduct R K (M i)
  let FK : ∀ i, V i →ₗ[K] V i := fun i => (F i).baseChange K
  let cupK : ∀ i, i ≤ n → V i →ₗ[K] V (2 * n - i) →ₗ[K] V (2 * n) :=
    fun i hi => baseChangeBilin (K := K) (cup i hi)
  let trK : V (2 * n) →ₗ[K] K := baseChangeTrace (K := K) tr
  have htopFK : ∀ z : V (2 * n), trK (FK (2 * n) z) = (Nat.card k : K) ^ n * trK z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c z =>
      change baseChangeTrace (K := K) tr ((F (2 * n)).baseChange K (c ⊗ₜ[R] z)) =
        (Nat.card k : K) ^ n * baseChangeTrace (K := K) tr (c ⊗ₜ[R] z)
      rw [LinearMap.baseChange_tmul, baseChangeTrace_tmul, baseChangeTrace_tmul, htopF z,
        map_mul, map_pow, map_natCast]
      ring
    | add z₁ z₂ ih₁ ih₂ =>
      rw [map_add, map_add, map_add, ih₁, ih₂, mul_add]
  have hcupFK : ∀ i (hi : i ≤ n) (u : V i) (v : V (2 * n - i)),
      cupK i hi (FK i u) (FK (2 * n - i) v) = FK (2 * n) (cupK i hi u v) := by
    intro i hi u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul d y =>
        change baseChangeBilin (K := K) (cup i hi)
            ((F i).baseChange K (c ⊗ₜ[R] x)) ((F (2 * n - i)).baseChange K (d ⊗ₜ[R] y)) =
          (F (2 * n)).baseChange K (baseChangeBilin (K := K) (cup i hi) (c ⊗ₜ[R] x) (d ⊗ₜ[R] y))
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, baseChangeBilin_tmul,
          baseChangeBilin_tmul, LinearMap.baseChange_tmul, hcupF i hi x y]
      | add v₁ v₂ ih₁ ih₂ =>
        rw [map_add, map_add, map_add, map_add, ih₁, ih₂]
    | add u₁ u₂ ih₁ ih₂ =>
      rw [map_add, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, map_add, ih₁, ih₂]
  have hnondegK : ∀ i (hi : i ≤ n),
      (∀ u : V i, (∀ v : V (2 * n - i), trK (cupK i hi u v) = 0) → u = 0) ∧
      (∀ v : V (2 * n - i), (∀ u : V i, trK (cupK i hi u v) = 0) → v = 0) := by
    intro i hi
    refine ⟨?_, ?_⟩
    · intro u hu
      obtain ⟨d, x, hd_ne, rfl⟩ := exists_denom_smul_tmul u
      have hdg_ne : algebraMap R K d ≠ 0 :=
        (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hd_ne
      have hx0 : x = 0 := by
        apply (hnondeg i hi).1 x
        intro y
        have hval := hu ((1 : K) ⊗ₜ[R] y)
        rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul] at hval
        have hinner : trK (cupK i hi ((1 : K) ⊗ₜ[R] x) ((1 : K) ⊗ₜ[R] y)) = 0 :=
          (mul_eq_zero.mp hval).resolve_left (inv_ne_zero hdg_ne)
        change baseChangeTrace (K := K) tr
            (baseChangeBilin (K := K) (cup i hi) ((1 : K) ⊗ₜ[R] x) ((1 : K) ⊗ₜ[R] y)) = 0 at hinner
        rw [baseChangeBilin_tmul, one_mul, baseChangeTrace_tmul, one_mul] at hinner
        exact IsFractionRing.injective R K (by simpa using hinner)
      simp [hx0]
    · intro v hv
      obtain ⟨d, y, hd_ne, rfl⟩ := exists_denom_smul_tmul v
      have hdg_ne : algebraMap R K d ≠ 0 :=
        (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hd_ne
      have hy0 : y = 0 := by
        apply (hnondeg i hi).2 y
        intro x
        have hval := hv ((1 : K) ⊗ₜ[R] x)
        rw [map_smul, map_smul, smul_eq_mul] at hval
        have hinner : trK (cupK i hi ((1 : K) ⊗ₜ[R] x) ((1 : K) ⊗ₜ[R] y)) = 0 :=
          (mul_eq_zero.mp hval).resolve_left (inv_ne_zero hdg_ne)
        change baseChangeTrace (K := K) tr
            (baseChangeBilin (K := K) (cup i hi) ((1 : K) ⊗ₜ[R] x) ((1 : K) ⊗ₜ[R] y)) = 0 at hinner
        rw [baseChangeBilin_tmul, one_mul, baseChangeTrace_tmul, one_mul] at hinner
        exact IsFractionRing.injective R K (by simpa using hinner)
      simp [hy0]
  refine ⟨K, inferInstance, inferInstance, V, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, FK, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have hR := congrArg (algebraMap R K) (htr m hm)
    simp only [map_natCast, map_sum, map_mul, map_pow, map_neg, map_one] at hR
    rw [hR]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [baseChange_pow, LinearMap.trace_baseChange]
  · intro i hi2n
    let pair : ∀ j (hj : j ≤ n), V j →ₗ[K] V (2 * n - j) →ₗ[K] K :=
      fun j hj => (cupK j hj).compr₂ trK
    have hpair_eq : ∀ j (hj : j ≤ n) (x : V j) (y : V (2 * n - j)),
        pair j hj x y = trK (cupK j hj x y) := fun _ _ _ _ => rfl
    have hpair_F : ∀ j (hj : j ≤ n) (x : V j) (y : V (2 * n - j)),
        pair j hj (FK j x) (FK (2 * n - j) y) = (Nat.card k : K) ^ n * pair j hj x y := by
      intro j hj x y
      rw [hpair_eq, hpair_eq, hcupFK j hj x y, htopFK]
    by_cases hi : i ≤ n
    · exact exists_dualEquiv_of_nondeg (FK i) (FK (2 * n - i)) ((Nat.card k : K) ^ n)
        (pair i hi) (hnondegK i hi).1 (hnondegK i hi).2 (hpair_F i hi)
    · generalize hj_def : 2 * n - i = j
      have hj : j ≤ n := by omega
      have hi_eq : i = 2 * n - j := by omega
      clear hj_def
      subst hi_eq
      exact exists_dualEquiv_of_nondeg (FK (2 * n - j)) (FK j) ((Nat.card k : K) ^ n)
        (pair j hj).flip (hnondegK j hj).2 (hnondegK j hj).1 (fun x y => hpair_F j hj y x)
  · dsimp only [V]
    rw [Module.finrank_baseChange, hfin0]
  · dsimp only [FK]
    rw [hF0, LinearMap.baseChange_id]
  · intro i hi
    obtain ⟨W, hWne, hWdvd, hWnorm⟩ := hW i hi
    let WQ : ℚ[X] := W.map (Int.castRingHom ℚ)
    refine ⟨WQ, ?_, ?_, ?_⟩
    · intro h0
      apply hWne
      exact Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective (by simpa [WQ] using h0)
    · rcases hWdvd with ⟨Q, hQ⟩
      refine ⟨Q.map (algebraMap R K), ?_⟩
      have hmap_eq : WQ.map (algebraMap ℚ K) = (W.map (Int.castRingHom R)).map (algebraMap R K) := by
        dsimp only [WQ]
        rw [Polynomial.map_map, Polynomial.map_map]
        congr 1
        exact RingHom.ext_int _ _
      rw [hmap_eq, hQ, Polynomial.map_mul, LinearMap.charpoly_baseChange]
    · intro z hz
      apply hWnorm z
      have hz' : aeval z W = aeval z WQ := by
        dsimp only [WQ]
        rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map]
        congr 1
      rw [hz', hz]
