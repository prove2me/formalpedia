-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_of_weaklyQuasiFiniteAt_87a0107f95bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:20.150071+00:00
-- url     : https://prove2.me/submissions/e49f518e-a928-4109-aa6b-36c2ff2b2e00

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped nonZeroDivisors
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (d : ℕ) [Algebra (MvPolynomial (Fin d) ℤ) A]
    (hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℤ) A))
    [Algebra.FiniteType (MvPolynomial (Fin d) ℤ) A]
    (𝔪 : Ideal A) [𝔪.IsPrime] [Algebra.WeaklyQuasiFiniteAt (MvPolynomial (Fin d) ℤ) 𝔪] :
    ∃ r ∉ 𝔪, ∃ N : Submodule A (integralClosure A K), N.FG ∧
      ∀ x : integralClosure A K, ∃ n : ℕ, r ^ n • x ∈ N := by
  classical
  set C := MvPolynomial (Fin d) ℤ
  have hZ := Algebra.ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt (R := C) 𝔪
  obtain ⟨r, hr𝔪, hrint, hm⟩ := Algebra.zariskisMainProperty_iff.mp hZ
  choose m hm using hm
  let _ : Algebra C K := ((algebraMap A K).comp (algebraMap C A)).toAlgebra
  have : IsScalarTower C A K := IsScalarTower.of_algebraMap_eq' rfl
  have hinjCK : Function.Injective (algebraMap C K) := (IsFractionRing.injective A K).comp hinj
  have : FaithfulSMul C K := (faithfulSMul_iff_algebraMap_injective C K).mpr hinjCK
  let _ : Algebra (FractionRing C) K := FractionRing.liftAlgebra C K
  have hr0 : algebraMap A K r ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective A K)]
    exact fun h => hr𝔪 (h ▸ 𝔪.zero_mem)
  have hintK : ∀ a : A, IsIntegral C a → IsIntegral (FractionRing C) (algebraMap A K a) :=
    fun a ha => (ha.map (IsScalarTower.toAlgHom C A K)).tower_top
  have : FiniteDimensional (FractionRing C) K := by
    obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := C) (A := A)
    let T : Set K := insert (algebraMap A K r) ((fun x => algebraMap A K (r ^ m x * x)) '' t)
    have hTint : ∀ z ∈ T, IsIntegral (FractionRing C) z := by
      rintro z (rfl | ⟨x, -, rfl⟩)
      · exact hintK r hrint
      · exact hintK _ (hm x)
    have : Finite T := ((t.finite_toSet.image _).insert _).to_subtype
    have hfd := IntermediateField.finiteDimensional_adjoin hTint
    have htop : IntermediateField.adjoin (FractionRing C) T = ⊤ := by
      rw [eq_top_iff]
      rintro z -
      have hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing C) T := by
        intro a
        have ha : a ∈ Algebra.adjoin C (t : Set A) := ht ▸ Algebra.mem_top
        induction ha using Algebra.adjoin_induction with
        | mem x hx =>
          have hr' : algebraMap A K r ∈ IntermediateField.adjoin (FractionRing C) T :=
            IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
          have hx' : algebraMap A K (r ^ m x * x) ∈ IntermediateField.adjoin (FractionRing C) T :=
            IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)
          have : algebraMap A K x = algebraMap A K (r ^ m x * x) / algebraMap A K r ^ m x := by
            rw [map_mul, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hr0)]
          rw [this]
          exact div_mem hx' (pow_mem hr' _)
        | algebraMap c =>
          rw [← IsScalarTower.algebraMap_apply C A K, IsScalarTower.algebraMap_apply C (FractionRing C) K]
          exact IntermediateField.algebraMap_mem _ _
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) z
      exact div_mem (hA a) (hA b)
    rw [htop] at hfd
    exact (IntermediateField.topEquiv (F := FractionRing C) (E := K)).toLinearEquiv.finiteDimensional
  have : CharZero (FractionRing C) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective C (FractionRing C))
  have : Algebra.IsSeparable (FractionRing C) K := Algebra.IsSeparable.of_integral _ _
  have : Module.Finite C (integralClosure C K) :=
    IsIntegralClosure.finite C (FractionRing C) K (integralClosure C K)
  obtain ⟨g, hg⟩ := (Module.Finite.fg_top : (⊤ : Submodule C (integralClosure C K)).FG)
  let ι : integralClosure C K → integralClosure A K := fun y => ⟨y.1, y.2.tower_top⟩
  let N : Submodule A (integralClosure A K) := Submodule.span A (ι '' g)
  have hN : ∀ y : integralClosure C K, ι y ∈ N := by
    intro y
    have hy : y ∈ Submodule.span C (g : Set (integralClosure C K)) := hg ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => exact N.zero_mem
    | add y z _ _ hy hz =>
      have : ι (y + z) = ι y + ι z := rfl
      rw [this]; exact N.add_mem hy hz
    | smul c y _ hy =>
      have : ι (c • y) = algebraMap C A c • ι y := by
        apply Subtype.ext
        change c • (y : K) = algebraMap C A c • (y : K)
        rw [Algebra.smul_def, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
      rw [this]; exact N.smul_mem _ hy
  refine ⟨r, hr𝔪, N, Submodule.fg_span (g.finite_toSet.image ι), fun x => ?_⟩
  obtain ⟨P, hPm, hPx⟩ := x.2
  set D := P.natDegree
  set M := (Finset.range (D + 1)).sup fun i => m (P.coeff i)
  let A₀ := integralClosure C A
  have hcoeff : ∀ i, IsIntegral C ((P.scaleRoots (r ^ M)).coeff i) := by
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i D with hi | hi | hi
    · have hmi : m (P.coeff i) ≤ M :=
        Finset.le_sup (f := fun i => m (P.coeff i)) (Finset.mem_range.mpr (by omega))
      obtain ⟨k, hk⟩ : ∃ k, D - i = k + 1 := ⟨D - i - 1, by omega⟩
      have : P.coeff i * (r ^ M) ^ (D - i) =
          (r ^ m (P.coeff i) * P.coeff i) * (r ^ (M - m (P.coeff i)) * (r ^ M) ^ k) := by
        rw [hk, pow_succ]
        rw [show (r ^ M) = r ^ m (P.coeff i) * r ^ (M - m (P.coeff i)) by
          rw [← pow_add, Nat.add_sub_cancel' hmi]]
        ring
      rw [this]
      exact (hm _).mul ((hrint.pow _).mul ((hrint.pow _).pow _))
    · rw [hi, Nat.sub_self, pow_zero, mul_one, ← Polynomial.leadingCoeff, hPm.leadingCoeff]
      exact isIntegral_one
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact isIntegral_zero
  have hlifts : P.scaleRoots (r ^ M) ∈ Polynomial.lifts (algebraMap A₀ A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hcoeff i⟩, rfl⟩
  have hmonic : (P.scaleRoots (r ^ M)).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_scaleRoots,
      Polynomial.coeff_scaleRoots_natDegree, hPm.leadingCoeff]
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hmonic
  have hint : IsIntegral C (algebraMap A K (r ^ M) * (x : K)) := by
    have h0 : Polynomial.aeval (algebraMap A K (r ^ M) * (x : K)) (P.scaleRoots (r ^ M)) = 0 :=
      Polynomial.scaleRoots_aeval_eq_zero (by rw [Polynomial.aeval_def]; exact hPx)
    have h1 : IsIntegral A₀ (algebraMap A K (r ^ M) * (x : K)) := by
      refine ⟨Q, hQm, ?_⟩
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap A, hQ]
      exact h0
    exact isIntegral_trans (R := C) (A := A₀) _ h1
  refine ⟨M, ?_⟩
  have : r ^ M • x = ι ⟨_, hint⟩ := by
    apply Subtype.ext
    change r ^ M • (x : K) = _
    rw [Algebra.smul_def]
  rw [this]
  exact hN _
end GroundTheory.Heights₂.Heights.Model
