-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_locPart_normal_f08e45df3bf5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:46.966089+00:00
-- url     : https://prove2.me/submissions/2ce630a4-9906-4824-b7af-57e8c05600b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_mul_0a86f7155eda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultiHomog_one_zero_4334cb17c577


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
variable {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
theorem _root_.solution (h𝓜 : KH.IsMGraded S ι 𝓜) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T M} (hx : x ∈ KH.locPart ι 𝓜 T c) :
    ∃ (m : M) (t : T) (a : K → ℕ), IsMultiHomog (t : MRingOver S ι) a ∧
      m ∈ 𝓜 (c + fun k => (a k : ℤ)) ∧ x = LocalizedModule.mk m t := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, 1, 0, isMultiHomog_one_zero, zero_mem _, (LocalizedModule.zero_mk 1).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    obtain ⟨m', t', a', ht', hm', rfl⟩ := hy
    have e : ∀ a a' : K → ℕ, (c + fun k => ((a + a') k : ℤ)) =
        (c + fun k => (a k : ℤ)) + fun k => (a' k : ℤ) := by
      intro a a'
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    refine ⟨t' • m + t • m', t * t', a + a', isMultiHomog_mul ht ht', add_mem ?_ ?_,
      LocalizedModule.mk_add_mk⟩
    · rw [Submonoid.smul_def, e]
      exact h𝓜.2 _ _ _ _ ht' hm
    · rw [Submonoid.smul_def, add_comm a a', e]
      exact h𝓜.2 _ _ _ _ ht hm'
  | smul s x _ hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    exact ⟨s • m, t, a, ht, Submodule.smul_mem _ s hm, LocalizedModule.smul'_mk s m t⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
