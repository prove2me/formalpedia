-- Prove2me | solution 1 for PhilipponMultiplicity.prime_nsmul_range_closure_has_nonempty_interior
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T22:04:38.929977+00:00
-- url     : https://prove2.me/submissions/3a4d6cec-3041-4cb3-be97-89d94eafb83d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_local_analytic_addition_model
import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

section

set_option autoImplicit false

open Filter Topology

namespace PhilipponMultiplicity.LocalAddition

variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

/-- The two local unit identities determine the derivative of a local addition law. -/
theorem derivative_of_units (μ : E × E → E) (d : E × E →L[K] E)
    (hd : HasStrictFDerivAt μ d 0)
    (hleft : ∀ᶠ u in 𝓝 (0 : E), μ (u, 0) = u)
    (hright : ∀ᶠ u in 𝓝 (0 : E), μ (0, u) = u) :
    d = ContinuousLinearMap.fst K E E + ContinuousLinearMap.snd K E E := by
  have hl := hd.comp (0 : E) (f := fun u : E => (u, (0 : E)))
    ((hasStrictFDerivAt_id (𝕜 := K) (0 : E)).prodMk
      (hasStrictFDerivAt_const (𝕜 := K) (0 : E) (0 : E)))
  have hr := hd.comp (0 : E) (f := fun u : E => ((0 : E), u))
    ((hasStrictFDerivAt_const (𝕜 := K) (0 : E) (0 : E)).prodMk
      (hasStrictFDerivAt_id (𝕜 := K) (0 : E)))
  have hl' := (hl.hasFDerivAt.congr_of_eventuallyEq (Filter.EventuallyEq.symm hleft)).unique
    (hasFDerivAt_id (𝕜 := K) (0 : E))
  have hr' := (hr.hasFDerivAt.congr_of_eventuallyEq (Filter.EventuallyEq.symm hright)).unique
    (hasFDerivAt_id (𝕜 := K) (0 : E))
  apply ContinuousLinearMap.ext
  intro z
  have hzl := DFunLike.congr_fun hl' z.1
  have hzr := DFunLike.congr_fun hr' z.2
  have hz : z = (z.1, 0) + (0, z.2) := by simp
  rw [hz, map_add]
  simpa using congrArg₂ (· + ·) hzl hzr

/-- Iteration of the local addition law, defined globally for convenience. -/
def multiple (μ : E × E → E) : ℕ → E → E
  | 0, _ => 0
  | n + 1, u => μ (multiple μ n u, u)

theorem multiple_zero (μ : E × E → E) (hzero : μ 0 = 0) (n : ℕ) :
    multiple μ n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change μ (multiple μ n 0, 0) = 0
    rw [ih]
    exact hzero

theorem multiple_derivative (μ : E × E → E) (hzero : μ 0 = 0)
    (hd : HasStrictFDerivAt μ
      (ContinuousLinearMap.fst K E E + ContinuousLinearMap.snd K E E) 0) (n : ℕ) :
    HasStrictFDerivAt (multiple μ n) (n • ContinuousLinearMap.id K E) 0 := by
  induction n with
  | zero => simpa [multiple] using hasStrictFDerivAt_const (𝕜 := K) (0 : E) (0 : E)
  | succ n ih =>
    have hd' : HasStrictFDerivAt μ
        (ContinuousLinearMap.fst K E E + ContinuousLinearMap.snd K E E)
        (multiple μ n 0, 0) := by
      rw [multiple_zero μ hzero n]
      exact hd
    have hc := hd'.comp (0 : E) (f := fun u : E => (multiple μ n u, u))
      (ih.prodMk (hasStrictFDerivAt_id (𝕜 := K) (0 : E)))
    convert hc using 1
    · ext u
      rfl
    · ext u
      simp

theorem multiple_compatible {G : Type*} [AddCommGroup G]
    (μ : E × E → E) (hzero : μ 0 = 0)
    (hd : HasStrictFDerivAt μ
      (ContinuousLinearMap.fst K E E + ContinuousLinearMap.snd K E E) 0)
    (φ : E → G) (hφ : φ 0 = 0)
    (hcompat : ∀ᶠ z in 𝓝 (0 : E × E), φ (μ z) = φ z.1 + φ z.2) (n : ℕ) :
    ∀ᶠ u in 𝓝 (0 : E), φ (multiple μ n u) = n • φ u := by
  induction n with
  | zero => simp [multiple, hφ]
  | succ n ih =>
    have hc : Tendsto (fun u => (multiple μ n u, u)) (𝓝 0) (𝓝 (0 : E × E)) := by
      have hm := (multiple_derivative μ hzero hd n).continuousAt
      have hz : (multiple μ n 0, (0 : E)) = (0 : E × E) := by
        rw [multiple_zero μ hzero n]
        rfl
      have ht := (hm.prodMk continuousAt_id).tendsto
      change Tendsto (fun u => (multiple μ n u, u)) (𝓝 0)
        (𝓝 (multiple μ n 0, (0 : E))) at ht
      rwa [hz] at ht
    filter_upwards [hc.eventually hcompat, ih] with u hu hi
    simpa [multiple, hi, add_nsmul] using hu

theorem multiple_image_mem_nhds [CompleteSpace E]
    (μ : E × E → E) (hzero : μ 0 = 0)
    (hd : HasStrictFDerivAt μ
      (ContinuousLinearMap.fst K E E + ContinuousLinearMap.snd K E E) 0)
    (n : ℕ) (hn : (n : K) ≠ 0) {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    multiple μ n '' U ∈ 𝓝 (0 : E) := by
  have hs : (n • ContinuousLinearMap.id K E).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro v
    refine ⟨(n : K)⁻¹ • v, ?_⟩
    simp [← Nat.cast_smul_eq_nsmul K, smul_smul, hn]
  have heq := (multiple_derivative μ hzero hd n).map_nhds_eq_of_surj hs
  rw [multiple_zero μ hzero n] at heq
  rw [← heq]
  exact Filter.image_mem_map hU

/-- A local analytic addition model with Zariski-thick neighborhoods forces every
nonzero scalar multiple to have a range whose closure has nonempty interior. -/
theorem range_closure_interior [CompleteSpace E]
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    (μ : E × E → E) (hμ : AnalyticAt K μ 0)
    (hzero : μ 0 = 0)
    (hleft : ∀ᶠ u in 𝓝 (0 : E), μ (u, 0) = u)
    (hright : ∀ᶠ u in 𝓝 (0 : E), μ (0, u) = u)
    (φ : E → G) (hφ : φ 0 = 0)
    (hcompat : ∀ᶠ z in 𝓝 (0 : E × E), φ (μ z) = φ z.1 + φ z.2)
    (hthick : ∀ U : Set E, U ∈ 𝓝 (0 : E) →
      (interior (closure (φ '' U))).Nonempty)
    (n : ℕ) (hn : (n : K) ≠ 0) :
    (interior (closure (Set.range (fun x : G => n • x)))).Nonempty := by
  have hd := hμ.hasStrictFDerivAt
  rw [derivative_of_units μ _ hd hleft hright] at hd
  let U := {u : E | φ (multiple μ n u) = n • φ u}
  have hU : U ∈ 𝓝 (0 : E) := multiple_compatible μ hzero hd φ hφ hcompat n
  have hV := multiple_image_mem_nhds μ hzero hd n hn hU
  have hsubset : φ '' (multiple μ n '' U) ⊆ Set.range (fun x : G => n • x) := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨φ u, hu.symm⟩
  exact (hthick _ hV).mono (interior_mono (closure_mono hsubset))

end PhilipponMultiplicity.LocalAddition
end

section

set_option autoImplicit false
open Filter Topology

namespace PhilipponMultiplicity

private theorem localAddition_complete {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

private theorem localAddition_charZero {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CharZero K := by
  rcases hK with ⟨e, _⟩ | ⟨p, hp, h⟩
  · exact e.toRingHom.charZero
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, _⟩ := h
    exact e.toRingHom.charZero

theorem positive_nsmul_interior_of_local_addition
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (hmodel : ∃ (d : ℕ) (φ : (Fin d → K) → G.Point)
      (μ : ((Fin d → K) × (Fin d → K)) → (Fin d → K)),
      φ 0 = 0 ∧ AnalyticAt K μ 0 ∧ μ 0 = 0 ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), μ (u, 0) = u) ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), μ (0, u) = u) ∧
      (∀ᶠ z in 𝓝 (0 : (Fin d → K) × (Fin d → K)),
        φ (μ z) = φ z.1 + φ z.2) ∧
      (∀ U : Set (Fin d → K), U ∈ 𝓝 0 →
        (@interior _ G.zariskiTopology
          (@closure _ G.zariskiTopology (φ '' U))).Nonempty))
    (n : ℕ) (hn : n ≠ 0) :
    (@interior _ G.zariskiTopology
      (@closure _ G.zariskiTopology (Set.range (fun x : G.Point => n • x)))).Nonempty := by
  letI : CompleteSpace K := localAddition_complete hK
  letI : CharZero K := localAddition_charZero hK
  letI : TopologicalSpace G.Point := G.zariskiTopology
  obtain ⟨d, φ, μ, hφ, hμ, hzero, hleft, hright, hcompat, hthick⟩ := hmodel
  exact LocalAddition.range_closure_interior μ hμ hzero hleft hright φ hφ hcompat hthick
    n (Nat.cast_ne_zero.mpr hn)

end PhilipponMultiplicity
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (p : ℕ) (hp : p.Prime) :
    (@interior _ G.zariskiTopology
      (@closure _ G.zariskiTopology (Set.range (fun x : G.Point => p • x)))).Nonempty := by
  exact positive_nsmul_interior_of_local_addition K hK G
    (exists_local_analytic_addition_model K hK G) p hp.ne_zero
