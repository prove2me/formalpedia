-- Prove2me | solution 1 for TW12.exists_groupAlgebra_basis_of_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/41ec63a9-8b1d-5cc3-b0eb-c383b0386334

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.OrzechProperty
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.Module
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TW12_exists_groupAlgebra_basis_of_descent
set_option autoImplicit false

namespace Impl

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

theorem natCast_mem_nonunits_monoidAlgebra {p : ℕ} [Fact p.Prime]
    (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (Δ : Type) [CommGroup Δ] :
    ((p : ℕ) : MonoidAlgebra 𝒪 Δ) ∈ nonunits (MonoidAlgebra 𝒪 Δ) := by
  intro hu
  have h2 : IsUnit ((Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) ((p : ℕ) : MonoidAlgebra 𝒪 Δ)) :=
    hu.map _
  rw [map_natCast] at h2
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hp) h2

theorem isUnit_one_sub_of_counit_eq_zero {p : ℕ} [Fact p.Prime]
    (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {Δ : Type} [CommGroup Δ] [Fintype Δ]
    (hΔ : ∀ g : Δ, ∃ n : ℕ, g ^ (p ^ n) = 1)
    (y : MonoidAlgebra 𝒪 Δ)
    (hy : Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ) y = 0) :
    IsUnit (1 - y) := by
  classical
  set N : ℕ := Finset.univ.sup fun g : Δ => (hΔ g).choose with hN
  have hgN : ∀ g : Δ, g ^ (p ^ N) = 1 := by
    intro g
    have h1 : (hΔ g).choose ≤ N := by
      rw [hN]; exact Finset.le_sup (f := fun g : Δ => (hΔ g).choose) (Finset.mem_univ g)
    have h2 : g ^ (p ^ (hΔ g).choose) = 1 := (hΔ g).choose_spec
    have h3 : p ^ N = p ^ (hΔ g).choose * p ^ (N - (hΔ g).choose) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h3, pow_mul, h2, one_pow]
  set z : MonoidAlgebra 𝒪 Δ := y ^ (p ^ N) with hzdef
  have hsum : ∑ g ∈ y.coeff.support, y.coeff g = 0 := by
    have h1 : y = ∑ g ∈ y.coeff.support, MonoidAlgebra.single g (y.coeff g) := by
      exact (MonoidAlgebra.sum_coeff_single y).symm
    have h2 : Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ) y
        = ∑ g ∈ y.coeff.support, y.coeff g := by
      conv_lhs => rw [h1]
      rw [map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp [Bialgebra.counitAlgHom_apply]
    rw [← h2, hy]
  have hdecomp : y = ∑ g ∈ y.coeff.support,
      MonoidAlgebra.single (1 : Δ) (y.coeff g) * (MonoidAlgebra.single g (1 : 𝒪) - 1) := by
    have h1 : ∀ g : Δ, MonoidAlgebra.single (1 : Δ) (y.coeff g) * (MonoidAlgebra.single g (1 : 𝒪) - 1)
        = MonoidAlgebra.single g (y.coeff g) - MonoidAlgebra.single (1 : Δ) (y.coeff g) := by
      intro g
      rw [mul_sub, mul_one, MonoidAlgebra.single_mul_single, one_mul, mul_one]
    rw [Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_sub_distrib]
    have h2 : ∑ g ∈ y.coeff.support, MonoidAlgebra.single g (y.coeff g) = y := MonoidAlgebra.sum_coeff_single y
    have h3 : ∑ g ∈ y.coeff.support, MonoidAlgebra.single (1 : Δ) (y.coeff g)
        = MonoidAlgebra.single (1 : Δ) (∑ g ∈ y.coeff.support, y.coeff g) :=
      (map_sum (MonoidAlgebra.singleAddHom (1 : Δ)) _ _).symm
    rw [h2, h3, hsum, MonoidAlgebra.single_zero, sub_zero]
  set I : Ideal (MonoidAlgebra 𝒪 Δ) :=
    Ideal.span ({((p : ℕ) : MonoidAlgebra 𝒪 Δ)} : Set (MonoidAlgebra 𝒪 Δ)) with hI
  haveI hch : CharP ((MonoidAlgebra 𝒪 Δ) ⧸ I) p :=
    CharP.quotient (MonoidAlgebra 𝒪 Δ) p (natCast_mem_nonunits_monoidAlgebra hp Δ)
  have hmk : Ideal.Quotient.mk I z = 0 := by
    rw [hzdef, map_pow]
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    rw [sum_pow_char_pow]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [map_mul, mul_pow]
    have h0 : (Ideal.Quotient.mk I (MonoidAlgebra.single g (1 : 𝒪)) - 1) ^ p ^ N = 0 := by
      rw [sub_pow_char_pow, one_pow, ← map_pow, MonoidAlgebra.single_pow, one_pow, hgN g,
        ← MonoidAlgebra.one_def, map_one, sub_self]
    rw [map_sub, map_one, h0, mul_zero]
  obtain ⟨w, hw⟩ : ∃ w, z = ((p : ℕ) : MonoidAlgebra 𝒪 Δ) * w := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hmk)
    exact ⟨c, by rw [mul_comm]; exact hc.symm⟩
  have h1z : IsUnit ((1 : MonoidAlgebra 𝒪 Δ) - z) := by
    haveI hfin : Module.Finite 𝒪 (MonoidAlgebra 𝒪 Δ) :=
      Module.Finite.of_basis (MonoidAlgebra.basis Δ 𝒪)
    haveI hfree : Module.Free 𝒪 (MonoidAlgebra 𝒪 Δ) :=
      Module.Free.of_basis (MonoidAlgebra.basis Δ 𝒪)
    set b : Module.Basis Δ 𝒪 (MonoidAlgebra 𝒪 Δ) :=
      (MonoidAlgebra.basis Δ 𝒪) with hb
    set f : MonoidAlgebra 𝒪 Δ →ₗ[𝒪] MonoidAlgebra 𝒪 Δ :=
      LinearMap.mulLeft 𝒪 ((1 : MonoidAlgebra 𝒪 Δ) - z) with hf
    have hsplit : f = LinearMap.id - (p : 𝒪) • LinearMap.mulLeft 𝒪 w := by
      refine LinearMap.ext fun m => ?_
      simp only [hf, LinearMap.mulLeft_apply, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.smul_apply]
      rw [hw, sub_mul, one_mul, mul_assoc,
        show ((p : ℕ) : MonoidAlgebra 𝒪 Δ) = algebraMap 𝒪 (MonoidAlgebra 𝒪 Δ) ((p : ℕ) : 𝒪) from
          (map_natCast _ p).symm,
        ← Algebra.smul_def]
    have hmat : (IsLocalRing.residue 𝒪).mapMatrix (LinearMap.toMatrix b b f) = 1 := by
      have hp0 : IsLocalRing.residue 𝒪 (p : 𝒪) = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr hp
      rw [hsplit, map_sub, map_smul, LinearMap.toMatrix_id, RingHom.mapMatrix_apply]
      ext i j
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        map_sub, map_mul, hp0, zero_mul, sub_zero]
      by_cases hij : i = j
      · subst hij; simp [Matrix.one_apply_eq]
      · simp [Matrix.one_apply_ne hij]
    have hdet : IsLocalRing.residue 𝒪 (LinearMap.det f) = 1 := by
      rw [← LinearMap.det_toMatrix b f, RingHom.map_det, hmat, Matrix.det_one]
    have hdu : IsUnit (LinearMap.det f) := by
      by_contra hcon
      have h1 : LinearMap.det f ∈ IsLocalRing.maximalIdeal 𝒪 :=
        (IsLocalRing.mem_maximalIdeal _).mpr hcon
      have h2 : IsLocalRing.residue 𝒪 (LinearMap.det f) = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr h1
      rw [hdet] at h2
      exact one_ne_zero h2
    have hfu : IsUnit f := (LinearMap.isUnit_iff_isUnit_det f).mpr hdu
    obtain ⟨u, hu⟩ := hfu
    refine IsUnit.of_mul_eq_one ((↑u⁻¹ : MonoidAlgebra 𝒪 Δ →ₗ[𝒪] MonoidAlgebra 𝒪 Δ) 1) ?_
    have h3 : (↑u * ↑u⁻¹ : MonoidAlgebra 𝒪 Δ →ₗ[𝒪] MonoidAlgebra 𝒪 Δ) = 1 := u.mul_inv
    calc ((1 : MonoidAlgebra 𝒪 Δ) - z) * ((↑u⁻¹ : MonoidAlgebra 𝒪 Δ →ₗ[𝒪] MonoidAlgebra 𝒪 Δ) 1)
        = f ((↑u⁻¹ : MonoidAlgebra 𝒪 Δ →ₗ[𝒪] MonoidAlgebra 𝒪 Δ) 1) := by
          rw [hf]; simp [LinearMap.mulLeft_apply]
      _ = (↑u : MonoidAlgebra 𝒪 Δ →ₗ[𝒪] MonoidAlgebra 𝒪 Δ)
            ((↑u⁻¹ : MonoidAlgebra 𝒪 Δ →ₗ[𝒪] MonoidAlgebra 𝒪 Δ) 1) := by rw [hu]
      _ = (↑u * ↑u⁻¹ : MonoidAlgebra 𝒪 Δ →ₗ[𝒪] MonoidAlgebra 𝒪 Δ) 1 := rfl
      _ = 1 := by rw [h3]; rfl
  have hgeo : (1 - y) * ∑ i ∈ Finset.range (p ^ N), y ^ i = 1 - z := by
    have h := geom_sum_mul y (p ^ N)
    have h2 : (1 - y) * ∑ i ∈ Finset.range (p ^ N), y ^ i
        = -((∑ i ∈ Finset.range (p ^ N), y ^ i) * (y - 1)) := by ring
    rw [h2, h, hzdef]
    ring
  exact isUnit_of_mul_isUnit_left (hgeo ▸ h1z)

theorem isUnit_of_isUnit_counit {p : ℕ} [Fact p.Prime]
    (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {Δ : Type} [CommGroup Δ] [Fintype Δ]
    (hΔ : ∀ g : Δ, ∃ n : ℕ, g ^ (p ^ n) = 1)
    (a : MonoidAlgebra 𝒪 Δ)
    (ha : IsUnit (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ) a)) :
    IsUnit a := by
  obtain ⟨u, hu⟩ := ha
  have h1 : Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)
      (1 - algebraMap 𝒪 (MonoidAlgebra 𝒪 Δ) (↑u⁻¹ : 𝒪) * a) = 0 := by
    rw [map_sub, map_one, map_mul, AlgHom.commutes, ← hu]
    simp
  have h2 : IsUnit (algebraMap 𝒪 (MonoidAlgebra 𝒪 Δ) (↑u⁻¹ : 𝒪) * a) := by
    have h3 := isUnit_one_sub_of_counit_eq_zero hp hΔ _ h1
    rwa [sub_sub_cancel] at h3
  have h4 : a = algebraMap 𝒪 (MonoidAlgebra 𝒪 Δ) (↑u : 𝒪)
      * (algebraMap 𝒪 (MonoidAlgebra 𝒪 Δ) (↑u⁻¹ : 𝒪) * a) := by
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  rw [h4]
  exact (u.isUnit.map (algebraMap 𝒪 (MonoidAlgebra 𝒪 Δ))).mul h2

theorem isLocalRing_monoidAlgebra_impl
    {p : ℕ} [Fact p.Prime] (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (Δ : Type) [CommGroup Δ] [Fintype Δ]
    (hΔ : ∀ g : Δ, ∃ n : ℕ, g ^ (p ^ n) = 1) :
    IsLocalRing (MonoidAlgebra 𝒪 Δ) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases hc : IsUnit (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ) a)
  · exact Or.inl (isUnit_of_isUnit_counit hp hΔ a hc)
  · refine Or.inr (isUnit_of_isUnit_counit hp hΔ _ ?_)
    rw [map_sub, map_one]
    have h1 : Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ) a ∈ IsLocalRing.maximalIdeal 𝒪 :=
      (IsLocalRing.mem_maximalIdeal _).mpr hc
    have h2 : (1 : 𝒪) - Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ) a
        ∉ IsLocalRing.maximalIdeal 𝒪 := by
      intro h3
      have h4 : (1 : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪 := by
        have h5 := Ideal.add_mem _ h3 h1
        simp only [sub_add_cancel] at h5
        exact h5
      exact (Ideal.ne_top_iff_one _).mp
        (IsLocalRing.maximalIdeal.isMaximal 𝒪).ne_top h4
    by_contra h5
    exact h2 ((IsLocalRing.mem_maximalIdeal _).mpr h5)

end Impl

open Impl in
theorem solution {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {p : ℕ} [Fact p.Prime] (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (Δ : Type) [CommGroup Δ] [Fintype Δ]
    (hΔ : ∀ g : Δ, ∃ n : ℕ, g ^ (p ^ n) = 1)
    (M : Type) [AddCommGroup M] [Module (MonoidAlgebra 𝒪 Δ) M]
    [Module 𝒪 M] [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 Δ) M]
    (d : ℕ)
    (B : Fin (d * Fintype.card Δ) → M)
    (hBspan : ∀ x : M, ∃ a : Fin (d * Fintype.card Δ) → 𝒪, x = ∑ i, a i • B i)
    (hBrel : ∀ a : Fin (d * Fintype.card Δ) → 𝒪,
      ∑ i, a i • B i = 0 ↔ ∀ i, a i = 0)
    (M₀ : Type) [AddCommGroup M₀] [Module 𝒪 M₀]
    (lam : M →+ M₀)
    (hlam_smul : ∀ (a : 𝒪) (m : M), lam (a • m) = a • lam m)
    (hlam_surj : Function.Surjective lam)
    (hlam_ker : ∀ m : M, lam m = 0 ↔ m ∈
      (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ))) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M))
    (b₀ : Fin d → M₀)
    (hb₀span : ∀ x : M₀, ∃ a : Fin d → 𝒪, x = ∑ i, a i • b₀ i) :
    ∃ b : Fin d → M,
      (∀ x : M, ∃ c : Fin d → MonoidAlgebra 𝒪 Δ, x = ∑ i, c i • b i) ∧
      (∀ c : Fin d → MonoidAlgebra 𝒪 Δ, ∑ i, c i • b i = 0 ↔ ∀ i, c i = 0) := by
  classical
  haveI hA : IsLocalRing (MonoidAlgebra 𝒪 Δ) := isLocalRing_monoidAlgebra_impl hp Δ hΔ
  have hBtop : Submodule.span 𝒪 (Set.range B) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha⟩ := hBspan x
    rw [ha]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI hMfin : Module.Finite 𝒪 M := by
    refine ⟨⟨Finset.univ.image B, ?_⟩⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hBtop]
  haveI hMfinA : Module.Finite (MonoidAlgebra 𝒪 Δ) M :=
    Module.Finite.of_restrictScalars_finite 𝒪 _ _
  choose b hb using fun i => hlam_surj (b₀ i)
  have haug : RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ))
      ≤ IsLocalRing.maximalIdeal (MonoidAlgebra 𝒪 Δ) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hxu
    have h1 : IsUnit (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ) x) := hxu.map _
    rw [RingHom.mem_ker.mp hx] at h1
    exact not_isUnit_zero h1
  have hstep : (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M)
      ≤ Submodule.span (MonoidAlgebra 𝒪 Δ) (Set.range b)
        ⊔ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)))
          • (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M) := by
    intro m _
    obtain ⟨a, ha⟩ := hb₀span (lam m)
    have h1 : lam (m - ∑ i, a i • b i) = 0 := by
      rw [map_sub, map_sum]
      have h2 : ∀ i ∈ Finset.univ, lam (a i • b i) = a i • b₀ i := fun i _ => by
        rw [hlam_smul, hb i]
      rw [Finset.sum_congr rfl h2, ← ha, sub_self]
    have h3 := (hlam_ker _).mp h1
    have h4 : (∑ i, a i • b i) ∈ Submodule.span (MonoidAlgebra 𝒪 Δ) (Set.range b) := by
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← algebraMap_smul (MonoidAlgebra 𝒪 Δ) (a i) (b i)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h5 : m = (∑ i, a i • b i) + (m - ∑ i, a i • b i) := by abel
    rw [h5]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h4) (Submodule.mem_sup_right h3)
  have hnak := Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson
    (I := RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ))) (J := ⊥)
    (N := Submodule.span (MonoidAlgebra 𝒪 Δ) (Set.range b)) (N' := ⊤)
    Module.Finite.fg_top
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact haug)
    hstep
  have hspan_top : Submodule.span (MonoidAlgebra 𝒪 Δ) (Set.range b) = ⊤ := by
    rw [sup_top_eq, Submodule.bot_smul, sup_bot_eq] at hnak
    exact hnak.symm
  have hspan_cl : ∀ x : M, ∃ c : Fin d → MonoidAlgebra 𝒪 Δ, x = ∑ i, c i • b i := by
    have hcl : ∀ x ∈ Submodule.span (MonoidAlgebra 𝒪 Δ) (Set.range b),
        ∃ c : Fin d → MonoidAlgebra 𝒪 Δ, x = ∑ i, c i • b i := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        refine ⟨Pi.single j 1, ?_⟩
        rw [Finset.sum_eq_single j]
        · rw [Pi.single_eq_same, one_smul]
        · intro i _ hij
          rw [Pi.single_eq_of_ne hij, zero_smul]
        · intro h
          exact absurd (Finset.mem_univ j) h
      | zero => exact ⟨0, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨cy, hcy⟩ := hy
        obtain ⟨cz, hcz⟩ := hz
        refine ⟨cy + cz, ?_⟩
        rw [hcy, hcz, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm
      | smul a y _ hy =>
        obtain ⟨cy, hcy⟩ := hy
        refine ⟨a • cy, ?_⟩
        rw [hcy, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, mul_smul]
    intro x
    exact hcl x (by rw [hspan_top]; exact Submodule.mem_top)
  let φ : (Fin d → MonoidAlgebra 𝒪 Δ) →ₗ[𝒪] M :=
    { toFun := fun c => ∑ i, c i • b i
      map_add' := fun c₁ c₂ => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_assoc a (c i) (b i) }
  have hφ_apply : ∀ c, φ c = ∑ i, c i • b i := fun c => rfl
  have hφsurj : Function.Surjective φ := fun x => by
    obtain ⟨c, hc⟩ := hspan_cl x
    exact ⟨c, hc.symm⟩
  have hli : LinearIndependent 𝒪 B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    exact (hBrel c).mp hc
  have hsp : ⊤ ≤ Submodule.span 𝒪 (Set.range B) := hBtop.ge
  let bM : Module.Basis (Fin (d * Fintype.card Δ)) 𝒪 M := Module.Basis.mk hli hsp
  let bA : Module.Basis Δ 𝒪 (MonoidAlgebra 𝒪 Δ) :=
    (MonoidAlgebra.basis Δ 𝒪)
  let bDom0 : Module.Basis ((_ : Fin d) × Δ) 𝒪 (Fin d → MonoidAlgebra 𝒪 Δ) :=
    Pi.basis fun _ => bA
  let eIdx : ((_ : Fin d) × Δ) ≃ Fin (d * Fintype.card Δ) :=
    (Equiv.sigmaEquivProd (Fin d) Δ).trans
      ((Equiv.prodCongr (Equiv.refl (Fin d)) (Fintype.equivFin Δ)).trans finProdFinEquiv)
  let bDom : Module.Basis (Fin (d * Fintype.card Δ)) 𝒪 (Fin d → MonoidAlgebra 𝒪 Δ) :=
    bDom0.reindex eIdx
  let e₁ := bDom.equivFun
  let e₂ := bM.equivFun
  let endo : M →ₗ[𝒪] M := φ ∘ₗ e₁.symm.toLinearMap ∘ₗ e₂.toLinearMap
  have hendo_surj : Function.Surjective endo := by
    have h1 : Function.Surjective (⇑φ ∘ ⇑e₁.symm ∘ ⇑e₂) :=
      hφsurj.comp ((EquivLike.surjective e₁.symm).comp (EquivLike.surjective e₂))
    exact h1
  have hendo_inj : Function.Injective endo :=
    OrzechProperty.injective_of_surjective_endomorphism endo hendo_surj
  have hφinj : Function.Injective φ := by
    have h1 : ∀ c, φ c = endo (e₂.symm (e₁ c)) := by
      intro c
      show φ c = φ (e₁.symm (e₂ (e₂.symm (e₁ c))))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    intro c₁ c₂ hc
    have h2 : endo (e₂.symm (e₁ c₁)) = endo (e₂.symm (e₁ c₂)) := by
      rw [← h1, ← h1]; exact hc
    exact (EquivLike.injective e₁) ((EquivLike.injective e₂.symm) (hendo_inj h2))
  refine ⟨b, hspan_cl, fun c => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · have h0 : φ c = φ 0 := by
      rw [hφ_apply, hc, hφ_apply]
      simp
    have h1 := hφinj h0
    intro i
    exact congrFun h1 i
  · exact Finset.sum_eq_zero fun i _ => by rw [hc i, zero_smul]

end S_TW12_exists_groupAlgebra_basis_of_descent
end P2MW
export P2MW.S_TW12_exists_groupAlgebra_basis_of_descent (solution)
