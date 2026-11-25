-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kirrWord_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:56.584032+00:00
-- url     : https://prove2.me/submissions/de28b9d6-68d3-4d97-be10-4c8f4663073e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : ∀ a, A a a u = (ν a : ℂ) • u) :
    ∀ l a, A a a (kirrWord A u l) = (kirrWt ν l a : ℂ) • kirrWord A u l
  | [], a => by simpa [kirrWord, kirrWt] using hu a
  | p :: l, a => by
    obtain ⟨b, c⟩ := p
    have ih := solution hA hu l a
    have key := LinearMap.congr_fun (hA a a b c) (kirrWord A u l)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at key
    simp only [kirrWord, kirrWt]
    rw [sub_eq_iff_eq_add, ih, map_smul] at key
    rw [key]
    by_cases h1 : a = b <;> by_cases h2 : c = a
    · subst h1; subst h2; simp [root]
    · subst h1; (simp [root, h2, Ne.symm h2, add_smul]; abel)
    · subst h2; (simp [root, h1, add_smul]; abel)
    · simp [root, h1, h2, Ne.symm h2]
end ReciprocityTheory.ChartRestriction.DS
