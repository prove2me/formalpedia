-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.exists_mk_locRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:00.251815+00:00
-- url     : https://prove2.me/submissions/5bf520c6-871a-4b0e-b37a-c7abe8fbe20a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (t : locRing K p) : ∃ a b : MvPolynomial (Fin n) ℂ, eval p b ≠ 0 ∧
      t * algebraMap _ (locRing K p) b = algebraMap _ (locRing K p) a := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (ptIdeal p).primeCompl y
  have hb' : b ∉ ptIdeal p := hb
  refine ⟨a, b, ?_, ?_⟩
  · intro h
    apply hb'
    simp only [ptIdeal, RingHom.mem_ker]
    exact h
  · first
    | rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
        IsLocalization.mk'_spec]
    | (show Ideal.Quotient.mk _ (IsLocalization.mk' _ a ⟨b, hb⟩) *
          Ideal.Quotient.mk _ (algebraMap _ _ b) = Ideal.Quotient.mk _ (algebraMap _ _ a)
       rw [← map_mul, IsLocalization.mk'_spec])
end ReciprocityTheory.AnForm.R
