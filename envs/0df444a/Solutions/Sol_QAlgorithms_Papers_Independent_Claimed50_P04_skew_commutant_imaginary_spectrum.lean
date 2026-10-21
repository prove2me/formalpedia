-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P04.skew_commutant_imaginary_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:25:04.195959+00:00
-- url     : https://prove2.me/submissions/4f0b88e6-cbf9-426a-8eee-90046313520a

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P04
open QAlgorithms.Papers.Independent.Claimed50.P04
noncomputable section

open Set

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Frontier30.P26
  (Invariant LieAdmissible ClosedCone CompactlyEmbedded CompactCartan Hermitian bracketSpan
    TubeType)

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedSpace

section Modules

variable {L V : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem g58c_antisymm' {E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (halt : ∀ v, b v v = 0) (v w : E) : b v w = - b w v := by
  have := halt (v + w)
  simp [halt v, halt w] at this
  exact eq_neg_of_add_eq_zero_left this

/-- Lemma 2.19, PDF p. 10: the -# condition is its defining form equation;
the spectral condition concerns the complexification, not the real spectrum. -/
theorem solution (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V)
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : SymplecticModule rho omega)
    (hc : StrictConvexType rho omega) (T : Module.End ℝ V) (ht : ModuleEnd rho T)
    (hskew : ∀ v w, omega (T v) w = -omega v (T w)) :
    ∀ z ∈ ComplexEigenvalues T, z.re = 0 := by
  intro z hz
  obtain ⟨⟨halt, _⟩, hpres⟩ := hs
  obtain ⟨x, hx⟩ := hc
  obtain ⟨u, v, huv, hu, hv⟩ := hz
  have anti := g58c_antisymm' omega halt
  -- g(a,b) = omega (rho x a) b is symmetric
  have hpx : ∀ a b, omega (rho x a) b = - omega a (rho x b) := fun a b =>
    eq_neg_of_add_eq_zero_left (hpres x a b)
  have gsymm : ∀ a b, omega (rho x a) b = omega (rho x b) a := by
    intro a b; rw [hpx, anti a]; ring
  -- T is g-skew : g(T a, a) = 0
  have gskew : ∀ a, omega (rho x (T a)) a = 0 := by
    intro a
    have e1 : omega (rho x (T a)) a = omega (T (rho x a)) a := by rw [ht]
    have e2 := hskew (rho x a) a
    have e3 : omega (rho x a) (T a) = omega (rho x (T a)) a := gsymm _ _
    have e4 : omega (rho x a) (T a) = - omega a (rho x (T a)) := hpx _ _
    have e5 : omega a (rho x (T a)) = - omega (rho x (T a)) a := anti _ _
    linarith
  have g1 := gskew u
  have g2 := gskew v
  rw [hu] at g1; rw [hv] at g2
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul] at g1 g2
  have gs := gsymm u v
  have pos : 0 < omega (rho x u) u + omega (rho x v) v := by
    rcases huv with h | h
    · have := hx u h
      have : 0 ≤ omega (rho x v) v := by
        by_cases hv0 : v = 0
        · simp [hv0]
        · exact (hx v hv0).le
      linarith
    · have := hx v h
      have : 0 ≤ omega (rho x u) u := by
        by_cases hu0 : u = 0
        · simp [hu0]
        · exact (hx u hu0).le
      linarith
  have : z.re * (omega (rho x u) u + omega (rho x v) v) = 0 := by
    linear_combination g1 + g2 - z.im * gs
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · linarith

end Modules

end

