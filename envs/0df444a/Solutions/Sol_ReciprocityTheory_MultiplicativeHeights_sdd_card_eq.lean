-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:24:13.428132+00:00
-- url     : https://prove2.me/submissions/720e7138-7a51-4797-985a-6e431fdc5220

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type} [Field K] [NumberField K] {r e : ℕ}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {k k₀ k₁ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K)
    (a : Fin (k₀ + k₁) → Fin r → K) (hb : IsKBasisIn B b) (haB : ∀ i, a i ∈ B)
    (hali : LinearIndependent K a) (has : ∀ x ∈ B, x ∈ Submodule.span K (Set.range a)) :
    k = k₀ + k₁ := by
  have hsp : Submodule.span K (Set.range b) = Submodule.span K (Set.range a) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact has _ (hb.1 i)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hb.2.2 _ (haB i)
  have h1 := finrank_span_eq_card hb.2.1
  have h2 := finrank_span_eq_card hali
  rw [hsp, h2] at h1
  simpa using h1.symm
end ReciprocityTheory.MultiplicativeHeights
