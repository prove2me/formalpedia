-- Prove2me | solution 1 for PI.SelfDualLoc.W.ND.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:28:55.59586+00:00
-- url     : https://prove2.me/submissions/ac2cd0be-ac7a-4bac-b242-58502a7a624e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg
import Theorems.Thm_PI_SelfDualLoc_W_ND_mem_intOE_iff
import Theorems.Thm_PI_SelfDualLoc_W_ND_coe_mem_intOE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W PI.SelfDualLoc.W.ND
open PI.SelfDualLoc
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace PI.SelfDualLoc.W.ND
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ z ∈ L, ∀ j, (d : E) * z j ∈ intOE E := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 E)⁰
    (S.biUnion fun s => Finset.univ.image fun j => s j)
  refine ⟨(b : 𝓞 E), nonZeroDivisors.ne_zero b.2, ?_⟩
  have hgen : ∀ s ∈ S, ∀ j, ((b : 𝓞 E) : E) * s j ∈ intOE E := by
    intro s hs j
    obtain ⟨a, ha⟩ := hb (s j)
      (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)
    refine (mem_intOE_iff _).2 ⟨a, ?_⟩
    rw [show ((b : 𝓞 E) : E) * s j = b • s j from by rw [Submonoid.smul_def, Algebra.smul_def]]
    exact ha
  intro z hz
  rw [← hS] at hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero =>
    intro j
    simp only [Pi.zero_apply, mul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro j
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx j) (hy j)
  | smul a x _ hx =>
    intro j
    have e : ((b : 𝓞 E) : E) * (a • x) j = (a : E) * (((b : 𝓞 E) : E) * x j) := by
      change ((b : 𝓞 E) : E) * ((a : E) * x j) = _
      ring
    rw [e]
    exact mul_mem (coe_mem_intOE a) (hx j)
end PI.SelfDualLoc.W.ND
