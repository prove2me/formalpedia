-- Prove2me | solution 1 for WeilConjectures.exists_qladic_weil_cohomology_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T22:53:19.166501+00:00
-- url     : https://prove2.me/submissions/b351f875-7816-4f3c-9e3a-4cdd4c2759db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_qladic_interior_cohomology_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

section InteriorCohomologyBridge

private abbrev CohObjAux (K W : Type) : Bool → Type
  | true => K
  | false => W

private instance cohObjAuxAddCommGroup (K W : Type) [AddCommGroup K] [AddCommGroup W] :
    ∀ b : Bool, AddCommGroup (CohObjAux K W b)
  | true => inferInstance
  | false => inferInstance

private instance cohObjAuxModule (K W : Type) [Field K] [AddCommGroup W] [Module K W] :
    ∀ b : Bool, Module K (CohObjAux K W b)
  | true => inferInstance
  | false => inferInstance

private instance cohObjAuxFinite (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    [Module.Finite K W] :
    ∀ b : Bool, Module.Finite K (CohObjAux K W b)
  | true => inferInstance
  | false => inferInstance

private abbrev CohObj (K : Type) (V : ℕ → Type) (n i : ℕ) : Type :=
  CohObjAux K (V i) (decide (i = 0 ∨ i = 2 * n))

private def cohObjAuxEquivTrue {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    {b : Bool} (hb : b = true) :
    CohObjAux K W b ≃ₗ[K] K := by
  cases hb
  exact LinearEquiv.refl K K

private def cohObjAuxEquivFalse {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    {b : Bool} (hb : b = false) :
    CohObjAux K W b ≃ₗ[K] W := by
  cases hb
  exact LinearEquiv.refl K W

private def cohObjEquivK {K : Type} [Field K] {V : ℕ → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] {n i : ℕ}
    (hi : i = 0 ∨ i = 2 * n) :
    CohObj K V n i ≃ₗ[K] K :=
  cohObjAuxEquivTrue (decide_eq_true hi)

private def cohObjEquivV {K : Type} [Field K] {V : ℕ → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] {n i : ℕ}
    (hi : ¬(i = 0 ∨ i = 2 * n)) :
    CohObj K V n i ≃ₗ[K] V i :=
  cohObjAuxEquivFalse (decide_eq_false hi)

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

end InteriorCohomologyBridge

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ (V : ℕ → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module (Padic ℓ) (V i))
      (_ : ∀ i, Module.Finite (Padic ℓ) (V i))
      (F : ∀ i, V i →ₗ[Padic ℓ] V i)
      (cup : ∀ i, i ≤ n → V i →ₗ[Padic ℓ] V (2 * n - i) →ₗ[Padic ℓ] V (2 * n))
      (tr : V (2 * n) →ₗ[Padic ℓ] Padic ℓ),
      (∀ m : ℕ, 0 < m →
        (pointCount p f m : Padic ℓ) =
          ∑ i ∈ Finset.range (2 * n + 1),
            (-1 : Padic ℓ) ^ i * LinearMap.trace (Padic ℓ) (V i) ((F i) ^ m)) ∧
      (∀ z : V (2 * n), tr (F (2 * n) z) = (Nat.card k : Padic ℓ) ^ n * tr z) ∧
      (∀ i (hi : i ≤ n) (x : V i) (y : V (2 * n - i)),
        cup i hi (F i x) (F (2 * n - i) y) = F (2 * n) (cup i hi x y)) ∧
      (∀ i (hi : i ≤ n),
        (∀ x : V i, (∀ y : V (2 * n - i), tr (cup i hi x y) = 0) → x = 0) ∧
        (∀ y : V (2 * n - i), (∀ x : V i, tr (cup i hi x y) = 0) → y = 0)) ∧
      Module.finrank (Padic ℓ) (V 0) = 1 ∧
      F 0 = LinearMap.id ∧
      (∀ i ≤ 2 * n, ∃ W : ℤ[X], W.Monic ∧ aeval (F i) W = 0 ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  obtain ⟨V, hVAdd, hVMod, hVFin, F, B, htr, hB_eq, hB_nondeg, hW⟩ :=
    WeilConjectures.exists_qladic_interior_cohomology_of_ge_two p k n hn X f hproj ℓ hℓp
  let _ : ∀ i, AddCommGroup (V i) := hVAdd
  let _ : ∀ i, Module (Padic ℓ) (V i) := hVMod
  let _ : ∀ i, Module.Finite (Padic ℓ) (V i) := hVFin
  let K := Padic ℓ
  let qK : K := (Nat.card k : K) ^ n
  let V' : ℕ → Type := CohObj K V n
  let e0 : V' 0 ≃ₗ[K] K := cohObjEquivK (Or.inl rfl)
  let eTop : V' (2 * n) ≃ₗ[K] K := cohObjEquivK (Or.inr rfl)
  let F' : ∀ i, V' i →ₗ[K] V' i := fun i =>
    if h0 : i = 0 then LinearMap.id
    else if htop : i = 2 * n then qK • LinearMap.id
    else (cohObjEquivV (by tauto)).symm.conj (F i)
  have hF'0 : F' 0 = LinearMap.id := dif_pos rfl
  have hF'top : F' (2 * n) = qK • LinearMap.id := by
    have h2n0 : 2 * n ≠ 0 := by omega
    simp only [F', dif_neg h2n0, ↓reduceDIte]
  have hF'mid : ∀ i (h : ¬(i = 0 ∨ i = 2 * n)),
      F' i = (cohObjEquivV h).symm.conj (F i) := by
    intro i h
    have h0 : i ≠ 0 := fun hi => h (Or.inl hi)
    have htop : i ≠ 2 * n := fun hi => h (Or.inr hi)
    simp only [F', dif_neg h0, dif_neg htop]
  let tr' : V' (2 * n) →ₗ[K] K := eTop.toLinearMap
  let cup' : ∀ i, i ≤ n → V' i →ₗ[K] V' (2 * n - i) →ₗ[K] V' (2 * n) := fun i hi =>
    if h0 : i = 0 then
      let ei : V' i ≃ₗ[K] K := cohObjEquivK (Or.inl h0)
      let ej : V' (2 * n - i) ≃ₗ[K] K := cohObjEquivK (Or.inr (by omega))
      { toFun := fun x =>
          { toFun := fun y => eTop.symm (ei x * ej y)
            map_add' := fun y₁ y₂ => by simp [mul_add]
            map_smul' := fun c y => by
              change eTop.symm (ei x * ej (c • y)) = c • eTop.symm (ei x * ej y)
              rw [map_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul c (ei x * ej y),
                map_smul eTop.symm c] }
        map_add' := fun x₁ x₂ => by ext y; simp [add_mul]
        map_smul' := fun c x => by
          ext y
          change eTop.symm (ei (c • x) * ej y) = c • eTop.symm (ei x * ej y)
          rw [map_smul, smul_eq_mul, mul_assoc, ← smul_eq_mul c (ei x * ej y),
            map_smul eTop.symm c] }
    else
      have h1 : 1 ≤ i := by omega
      have hmid_i : ¬(i = 0 ∨ i = 2 * n) := by omega
      have hmid_j : ¬(2 * n - i = 0 ∨ 2 * n - i = 2 * n) := by omega
      let ei : V' i ≃ₗ[K] V i := cohObjEquivV hmid_i
      let ej : V' (2 * n - i) ≃ₗ[K] V (2 * n - i) := cohObjEquivV hmid_j
      { toFun := fun x =>
          { toFun := fun y => eTop.symm (B i h1 hi (ei x) (ej y))
            map_add' := fun y₁ y₂ => by simp [map_add]
            map_smul' := fun c y => by
              change eTop.symm (B i h1 hi (ei x) (ej (c • y))) =
                c • eTop.symm (B i h1 hi (ei x) (ej y))
              rw [map_smul, map_smul, map_smul] }
        map_add' := fun x₁ x₂ => by ext y; simp [map_add]
        map_smul' := fun c x => by
          ext y
          change eTop.symm (B i h1 hi (ei (c • x)) (ej y)) =
            c • eTop.symm (B i h1 hi (ei x) (ej y))
          rw [map_smul, map_smul, LinearMap.smul_apply, map_smul] }
  refine ⟨V', inferInstance, inferInstance, inferInstance, F', cup', tr',
    ?_, ?_, ?_, ?_, ?_, hF'0, ?_⟩
  · intro m hm
    rw [htr m hm]
    have hsplit : ∑ i ∈ Finset.range (2 * n + 1),
        (-1 : K) ^ i * LinearMap.trace K (V' i) ((F' i) ^ m) =
        ((-1 : K) ^ 0 * LinearMap.trace K (V' 0) ((F' 0) ^ m)) +
        ((-1 : K) ^ (2 * n) * LinearMap.trace K (V' (2 * n)) ((F' (2 * n)) ^ m)) +
        ∑ i ∈ Finset.Ico 1 (2 * n),
          (-1 : K) ^ i * LinearMap.trace K (V' i) ((F' i) ^ m) := by
      rw [Finset.sum_range_succ, Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < 2 * n)]
      ring
    rw [hsplit]
    have htr0 : (-1 : K) ^ 0 * LinearMap.trace K (V' 0) ((F' 0) ^ m) = 1 := by
      rw [pow_zero, one_mul, hF'0]
      change LinearMap.trace K (V' 0) ((1 : Module.End K (V' 0)) ^ m) = 1
      rw [one_pow]
      change LinearMap.trace K (V' 0) LinearMap.id = 1
      rw [LinearMap.trace_id, e0.finrank_eq, Module.finrank_self, Nat.cast_one]
    have htrTop : (-1 : K) ^ (2 * n) * LinearMap.trace K (V' (2 * n)) ((F' (2 * n)) ^ m) =
        qK ^ m := by
      have hsign : (-1 : K) ^ (2 * n) = 1 := by rw [pow_mul]; norm_num
      have hpow : (qK • (LinearMap.id : V' (2 * n) →ₗ[K] V' (2 * n))) ^ m =
          (qK ^ m) • LinearMap.id := by
        change (qK • (1 : Module.End K (V' (2 * n)))) ^ m = (qK ^ m) • (1 : Module.End K (V' (2 * n)))
        rw [_root_.smul_pow, one_pow]
      rw [hsign, one_mul, hF'top, hpow, map_smul, LinearMap.trace_id, eTop.finrank_eq,
        Module.finrank_self, Nat.cast_one, smul_eq_mul, mul_one]
    rw [htr0, htrTop]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have h2 : i < 2 * n := (Finset.mem_Ico.mp hi).2
    have hmid : ¬(i = 0 ∨ i = 2 * n) := by omega
    rw [hF'mid i hmid, linearEquiv_conj_pow, LinearMap.trace_conj']
  · intro z
    rw [hF'top, LinearMap.smul_apply, LinearMap.id_apply, map_smul, smul_eq_mul]
  · intro i hi x y
    by_cases h0 : i = 0
    · subst h0
      simp only [cup', ↓reduceDIte, LinearMap.coe_mk, AddHom.coe_mk, hF'0, LinearMap.id_apply,
        Nat.sub_zero, hF'top, LinearMap.smul_apply]
      rw [map_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul qK _, map_smul eTop.symm qK]
    · have h1 : 1 ≤ i := by omega
      have hmid_i : ¬(i = 0 ∨ i = 2 * n) := by omega
      have hmid_j : ¬(2 * n - i = 0 ∨ 2 * n - i = 2 * n) := by omega
      simp only [cup', dif_neg h0, LinearMap.coe_mk, AddHom.coe_mk,
        hF'mid i hmid_i, hF'mid (2 * n - i) hmid_j, hF'top, LinearMap.smul_apply,
        LinearMap.id_apply, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_symm]
      rw [(cohObjEquivV (K := K) (V := V) (n := n) hmid_i).apply_symm_apply,
        (cohObjEquivV (K := K) (V := V) (n := n) hmid_j).apply_symm_apply,
        hB_eq i h1 hi, ← smul_eq_mul qK _, map_smul eTop.symm qK]
  · intro i hi
    by_cases h0 : i = 0
    · subst h0
      constructor
      · intro x hx
        have h1 := hx (eTop.symm 1)
        simp only [cup', ↓reduceDIte, tr', LinearMap.coe_mk, AddHom.coe_mk,
          LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1
        have h1' : e0 x = 0 := by
          simpa [e0, eTop] using h1
        exact e0.injective (by rw [h1', map_zero])
      · intro y hy
        have h1 := hy (e0.symm 1)
        simp only [cup', ↓reduceDIte, tr', LinearMap.coe_mk, AddHom.coe_mk,
          LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1
        have h1' : eTop y = 0 := by
          simpa [e0, eTop] using h1
        exact eTop.injective (by rw [h1', map_zero])
    · have h1 : 1 ≤ i := by omega
      have hmid_i : ¬(i = 0 ∨ i = 2 * n) := by omega
      have hmid_j : ¬(2 * n - i = 0 ∨ 2 * n - i = 2 * n) := by omega
      constructor
      · intro x hx
        apply (cohObjEquivV hmid_i).injective
        rw [map_zero]
        apply (hB_nondeg i h1 hi).1
        intro y
        have hy := hx ((cohObjEquivV hmid_j).symm y)
        simpa only [cup', dif_neg h0, tr', LinearMap.coe_mk, AddHom.coe_mk,
          LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hy
      · intro y hy
        apply (cohObjEquivV hmid_j).injective
        rw [map_zero]
        apply (hB_nondeg i h1 hi).2
        intro x
        have hx := hy ((cohObjEquivV hmid_i).symm x)
        simpa only [cup', dif_neg h0, tr', LinearMap.coe_mk, AddHom.coe_mk,
          LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hx
  · rw [e0.finrank_eq, Module.finrank_self]
  · intro i hi
    by_cases h0 : i = 0
    · subst h0
      refine ⟨Polynomial.X - C (1 : ℤ), Polynomial.monic_X_sub_C (1 : ℤ), ?_, ?_⟩
      · rw [map_sub, aeval_X, aeval_C, map_one, hF'0]; exact sub_self _
      · intro z hz
        rw [map_sub, aeval_X, aeval_C, map_one, sub_eq_zero] at hz
        rw [hz, norm_one]
        simp
    · by_cases htop : i = 2 * n
      · subst htop
        refine ⟨Polynomial.X - C ((Nat.card k : ℤ) ^ n), Polynomial.monic_X_sub_C _, ?_, ?_⟩
        · rw [map_sub, aeval_X, aeval_C, hF'top, Algebra.algebraMap_eq_smul_one]
          ext x
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
            Module.End.one_apply, LinearMap.zero_apply, qK]
          rw [← Int.cast_smul_eq_zsmul K, Int.cast_pow, Int.cast_natCast, sub_self]
        · intro z hz
          rw [map_sub, aeval_X, aeval_C, sub_eq_zero] at hz
          rw [hz]
          have hcast : ((algebraMap ℤ ℂ) ((Nat.card k : ℤ) ^ n)) = ((Nat.card k : ℂ) ^ n) := by
            push_cast; rfl
          rw [hcast, norm_pow, Complex.norm_natCast]
          have hexp : ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) := by push_cast; ring
          rw [hexp, Real.rpow_natCast]
      · have h1 : 1 ≤ i := by omega
        have h2 : i < 2 * n := by omega
        have hmid : ¬(i = 0 ∨ i = 2 * n) := by omega
        obtain ⟨W, hWmon, hWF, hWnorm⟩ := hW i h1 h2
        refine ⟨W, hWmon, ?_, hWnorm⟩
        rw [hF'mid i hmid, aeval_linearEquiv_conj, hWF, map_zero]
