-- Prove2me | solution 1 for PI.LocLatEq.W.locLatEq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:03:44.018284+00:00
-- url     : https://prove2.me/submissions/7c24f20e-5b9c-47d0-bd33-8794fc88df5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
import Theorems.Thm_PI_LocLatEq_W_latL_le
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocLatEq PI.LocLatEq.W
namespace PI.LocLatEq.W
theorem _root_.solution (hU : UnitP) (hA : AvoidP) (hC : CoreP) : PI.LocLatEq.Stmt := by
  intro F E _ _ _ _ _ h2 sig p A n Λ₁ Λ₂ hf1 hf2
  constructor
  · intro heq P hP x
    have key : ∀ (Λ Λ' : Submodule (𝓞 E) (Fin n → E)), Λ'.FG → latL A Λ = latL A Λ' →
        (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ) → (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ') := by
      rintro Λ Λ' hf' he ⟨s, hs, hsx⟩
      have hy : bc A (s • x) ∈ latL A Λ' := he ▸ Submodule.subset_span ⟨_, hsx, rfl⟩
      obtain ⟨d, hd, hdy⟩ := hC F E h2 sig p A n Λ' hf' (s • x) hy
      refine ⟨algebraMap (𝓞 F) (𝓞 E) d * s, ?_, by rwa [mul_smul]⟩
      intro hm
      rcases P.isPrime.mem_or_mem hm with h | h
      · apply hd
        rw [← hP]
        exact h
      · exact hs h
    exact ⟨key Λ₁ Λ₂ hf2 heq, key Λ₂ Λ₁ hf1 heq.symm⟩
  · intro h
    have side : ∀ (Λ Λ' : Submodule (𝓞 E) (Fin n → E)),
        (∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
          ∀ x : Fin n → E, (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ) →
            (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ')) → latL A Λ ≤ latL A Λ' := by
      intro Λ Λ' hh
      apply latL_le A hU
      intro x hx
      apply hA F E p (Λ'.comap (LinearMap.toSpanSingleton (𝓞 E) _ x))
      intro P hP hle
      have h1 : (1 : 𝓞 E) ∉ P.asIdeal := fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      obtain ⟨s, hs, hsx⟩ := hh P hP x ⟨1, h1, by simpa using hx⟩
      exact hs (hle (by simpa [LinearMap.toSpanSingleton_apply] using hsx))
    exact le_antisymm (side Λ₁ Λ₂ (fun P hP x => (h P hP x).1))
      (side Λ₂ Λ₁ (fun P hP x => (h P hP x).2))
end PI.LocLatEq.W
