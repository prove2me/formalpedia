-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.exists_delta_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:27:32.579717+00:00
-- url     : https://prove2.me/submissions/da47a1de-22b3-4948-9f1c-45543fc8faad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Formalism.L2.Pj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution {P : Ideal (𝓞 E)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∃ δ : 𝓞 E, δ ∈ differentIdeal ℤ (𝓞 E) ∧ δ ≠ 0 ∧
      (normalizedFactors (Ideal.span {δ})).count P = (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P := by
  set Dif := differentIdeal ℤ (𝓞 E) with hDif
  have hD0 : Dif ≠ ⊥ := differentIdeal_ne_bot

  have hlt : Dif * P < Dif := by
    refine lt_of_le_of_ne Ideal.mul_le_left fun heq => ?_
    have h1 : Dif * P = Dif * ⊤ := by rw [heq, Ideal.mul_top]
    have := mul_left_cancel₀ (by rwa [Ne, Ideal.zero_eq_bot]) h1
    exact hP.ne_top this
  obtain ⟨δ, hδD, hδP⟩ := SetLike.exists_of_lt hlt
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hδP (Submodule.zero_mem _)
  refine ⟨δ, hδD, hδ0, ?_⟩

  obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hδD)
  have hKP : ¬ K ≤ P := by
    intro hle
    apply hδP
    have : Ideal.span {δ} ≤ Dif * P := by rw [hK]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self δ)
  have hK0 : K ≠ 0 := by
    rintro rfl
    rw [mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hK
    exact hδ0 hK
  have hcK : (normalizedFactors K).count P = 0 := by
    refine Multiset.count_eq_zero.2 fun hP' => hKP ?_
    exact Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP')
  rw [hK, UniqueFactorizationMonoid.normalizedFactors_mul (by rwa [Ne, Ideal.zero_eq_bot]) hK0,
    Multiset.count_add, hcK, add_zero]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
