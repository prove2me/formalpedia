-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPA.op_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:04:21.806614+00:00
-- url     : https://prove2.me/submissions/5d748a94-5ddd-4e48-ab28-e8fb7403c42c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPtsA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.NPA
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
namespace ReciprocityTheory.ChartRestriction.G.T0.NPA
theorem _root_.solution (ϖ : 𝓞 K) (hϖ : ϖ ∈ la.asIdeal) (hϖ2 : ϖ ∉ la.asIdeal ^ 2) :
    Irreducible (algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)) := by
  classical
  have hdvd : la.asIdeal ∣ Ideal.span {ϖ} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hϖ)
  obtain ⟨J, hJ⟩ := hdvd
  have hJla : ¬ J ≤ la.asIdeal := by
    intro hle
    apply hϖ2
    have hsub : Ideal.span {ϖ} ≤ la.asIdeal ^ 2 := by
      rw [hJ, sq]
      exact Ideal.mul_mono_right hle
    exact hsub (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsJ, hsla⟩ := Set.not_subset.mp hJla
  have key : ∀ a ∈ la.asIdeal, ∃ b, s * a = ϖ * b := by
    intro a ha
    have hmem : s * a ∈ Ideal.span {ϖ} := by
      rw [hJ, mul_comm s a]
      exact Ideal.mul_mem_mul ha hsJ
    exact Ideal.mem_span_singleton.mp hmem
  have hsnot : MvPolynomial.C s ∉ laT D N la := by
    unfold laT
    rw [MvPolynomial.mem_map_C_iff]
    intro h
    apply hsla
    simpa using h 0
  have hsu : IsUnit (algebraMap (OT K D N) (Op D N la) (MvPolynomial.C s)) :=
    IsLocalization.map_units (Op D N la) (⟨MvPolynomial.C s, hsnot⟩ : (laT D N la).primeCompl)
  have hsub : ∀ a ∈ la.asIdeal, algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a) ∈
      Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)} := by
    intro a ha
    obtain ⟨b, hb⟩ := key a ha
    obtain ⟨u, hu⟩ := hsu
    have e : algebraMap (OT K D N) (Op D N la) (MvPolynomial.C s) *
        algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a) =
        algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ) *
          algebraMap (OT K D N) (Op D N la) (MvPolynomial.C b) := by
      simp only [← map_mul, hb]
    rw [← hu] at e
    refine Ideal.mem_span_singleton.mpr ⟨algebraMap (OT K D N) (Op D N la) (MvPolynomial.C b) * ↑u⁻¹, ?_⟩
    calc algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a)
        = ↑u⁻¹ * (↑u * algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a)) := by simp
      _ = ↑u⁻¹ * (algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ) *
          algebraMap (OT K D N) (Op D N la) (MvPolynomial.C b)) := by rw [e]
      _ = _ := by ring
  have hm : IsLocalRing.maximalIdeal (Op D N la) =
      Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      have hle : laT D N la ≤ Ideal.comap (algebraMap (OT K D N) (Op D N la))
          (Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)}) := by
        show Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) la.asIdeal ≤ _
        refine Ideal.map_le_iff_le_comap.mpr ?_
        intro a ha
        exact hsub a ha
      exact hle
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hϖ)
  set x := algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ) with hxdef
  have hx0 : x ≠ 0 := by
    have hϖ0 : ϖ ≠ 0 := fun h => hϖ2 (h ▸ Ideal.zero_mem _)
    rw [hxdef]
    refine (map_ne_zero_iff _ (IsLocalization.injective (Op D N la)
      (Ideal.primeCompl_le_nonZeroDivisors (laT D N la)))).mpr ?_
    simpa using hϖ0
  have hxm : x ∈ IsLocalRing.maximalIdeal (Op D N la) := by
    rw [hm]
    exact Ideal.mem_span_singleton_self x
  have hxnu : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).mp hxm
  refine ⟨hxnu, ?_⟩
  intro a b hab
  by_contra hcon
  push_neg at hcon
  have ha : a ∈ IsLocalRing.maximalIdeal (Op D N la) := (IsLocalRing.mem_maximalIdeal a).mpr hcon.1
  have hb : b ∈ IsLocalRing.maximalIdeal (Op D N la) := (IsLocalRing.mem_maximalIdeal b).mpr hcon.2
  rw [hm, Ideal.mem_span_singleton] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  apply hxnu
  have h2 : x * (a' * (x * b')) = x * 1 := by
    rw [mul_one, ← mul_assoc]
    exact hab.symm
  have h3 : a' * (x * b') = 1 := mul_left_cancel₀ hx0 h2
  have h4 : x * (b' * a') = 1 := by
    rw [← h3]
    ring
  exact ⟨⟨x, b' * a', h4, by rw [mul_comm]; exact h4⟩, rfl⟩
end ReciprocityTheory.ChartRestriction.G.T0.NPA
