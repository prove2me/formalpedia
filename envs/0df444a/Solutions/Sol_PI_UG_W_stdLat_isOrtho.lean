-- Prove2me | solution 1 for PI.UG.W.stdLat_isOrtho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:49.631834+00:00
-- url     : https://prove2.me/submissions/dedaf764-e661-4246-91ed-83bdf9753311

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_StdLatEqSpan
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_UnimodLocalOfLocDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UG PI.UG.W
namespace PI.UG.W
theorem _root_.solution (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (hStd E n) (stdLat E n) n := by
  refine ⟨fun i => Pi.single i 1, ?_, ?_, ?_, ?_⟩
  · convert (Pi.basisFun E (Fin n)).linearIndependent using 1 <;> first | rfl | (funext i; simp)
  · convert (Pi.basisFun E (Fin n)).span_eq using 3 <;> first | rfl | (funext i; simp)
  · apply le_antisymm
    · intro x hx
      rw [stdLat, Submodule.mem_pi] at hx
      have hx' : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := fun i =>
        Submodule.mem_one.mp (hx i (Set.mem_univ i))
      choose r hr using hx'
      have hxe : x = ∑ i, r i • (Pi.single i (1 : E) : Fin n → E) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
      rw [hxe]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, stdLat, Submodule.mem_pi]
      intro j _
      rw [Submodule.mem_one]
      by_cases hij : j = i
      · subst hij
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, hij]⟩
  · intro i j
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_apply, hij, Ne.symm hij]
end PI.UG.W
