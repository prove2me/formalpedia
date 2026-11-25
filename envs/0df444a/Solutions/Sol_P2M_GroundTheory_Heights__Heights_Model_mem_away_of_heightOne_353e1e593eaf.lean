-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mem_away_of_heightOne_353e1e593eaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:43.25739+00:00
-- url     : https://prove2.me/submissions/474e7df5-b654-49ce-9aca-67ba3f51be83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PAwayHeightOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (hHOI : HeightOneIntersection.Statement)
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (Ω : Type) [Field Ω] [Algebra A Ω] (hinj : Function.Injective (algebraMap A Ω))
    (h : A) (hh : h ≠ 0) (a : Ω)
    (hs : ∃ s : A, s ≠ 0 ∧ ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n * s) * a = algebraMap A Ω g)
    (hP : ∀ P : Ideal A, P.IsPrime → P.height = 1 → h ∉ P →
      ∃ t : A, t ∉ P ∧ ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n * t) * a = algebraMap A Ω g) :
    ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n) * a = algebraMap A Ω g := by
  let K := FractionRing A
  let φ : K →+* Ω := IsFractionRing.lift hinj
  have hφ : ∀ y : A, φ (algebraMap A K y) = algebraMap A Ω y := fun y =>
    IsFractionRing.lift_algebraMap hinj y
  have hφinj : Function.Injective φ := φ.injective
  obtain ⟨s, hs0, n, g, hg⟩ := hs
  have hns : h ^ n * s ≠ 0 := mul_ne_zero (pow_ne_zero _ hh) hs0
  have hnsΩ : algebraMap A Ω (h ^ n * s) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap A Ω)]
    exact fun e => hns (hinj e)
  let k : K := algebraMap A K g / algebraMap A K (h ^ n * s)
  have hk : φ k = a := by
    simp only [k, map_div₀, hφ]
    rw [← hg, mul_div_cancel_left₀ _ hnsΩ]

  have back : ∀ y z : A, algebraMap A Ω y * a = algebraMap A Ω z →
      algebraMap A K y * k = algebraMap A K z := by
    intro y z e
    apply hφinj
    rw [map_mul, hk, hφ, hφ, e]
  have hS : Submonoid.powers h ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hh
  let A' : Subalgebra A K := Localization.subalgebra.ofField K (Submonoid.powers h) hS
  have : IsLocalization (Submonoid.powers h) A' :=
    Localization.subalgebra.isLocalization_ofField K (Submonoid.powers h) hS
  have : IsNoetherianRing A' :=
    IsLocalization.isNoetherianRing (Submonoid.powers h) A' inferInstance
  have : IsIntegrallyClosed A' :=
    isIntegrallyClosed_of_isLocalization A' (Submonoid.powers h) hS
  have key := hHOI A' K
  have hkmem : k ∈ Subalgebra.toSubmodule (⊥ : Subalgebra A' K) := by
    rw [key, Submodule.mem_iInf]
    intro P
    rw [Submodule.mem_iInf]
    intro hP1
    let Q : Ideal A := P.asIdeal.comap (algebraMap A A')
    have : Q.IsPrime := Ideal.comap_isPrime _ _
    have hQ1 : Q.height = 1 := by
      rw [← hP1]
      exact IsLocalization.height_under (Submonoid.powers h) P.asIdeal
    have hhQ : h ∉ Q := by
      intro hq
      have hu : IsUnit (algebraMap A A' h) :=
        IsLocalization.map_units A' (⟨h, Submonoid.mem_powers h⟩ : Submonoid.powers h)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)
    obtain ⟨t, htQ, m, z, hz⟩ := hP Q inferInstance hQ1 hhQ
    refine ⟨algebraMap A A' (h ^ m * t), ?_, ?_⟩
    · intro hmem
      have hmem' : h ^ m * t ∈ Q := hmem
      rcases (inferInstance : Q.IsPrime).mem_or_mem hmem' with h1 | h1
      · exact hhQ ((inferInstance : Q.IsPrime).mem_of_pow_mem _ h1)
      · exact htQ h1
    · rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot]
      refine ⟨algebraMap A A' z, ?_⟩
      rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
      exact (back _ _ hz).symm
  rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot] at hkmem
  obtain ⟨y, hy⟩ := hkmem
  obtain ⟨b, u, hu, hyb⟩ : ∃ (b u : A) (_ : u ∈ Submonoid.powers h),
      (y : K) = algebraMap A K b * (algebraMap A K u)⁻¹ := y.2
  obtain ⟨m, rfl⟩ := hu
  have hu0 : algebraMap A K (h ^ m) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap A K)]
    exact fun e => pow_ne_zero m hh (IsFractionRing.injective A K e)
  have hyk : (y : K) = k := hy
  refine ⟨m, b, ?_⟩
  have e1 : algebraMap A K (h ^ m) * k = algebraMap A K b := by
    rw [← hyk, hyb, mul_comm, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  have e2 := congrArg φ e1
  rwa [map_mul, hk, hφ, hφ] at e2
end GroundTheory.Heights₂.Heights.Model
