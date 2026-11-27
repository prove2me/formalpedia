-- Prove2me | solution 1 for PI.DIP.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:15:40.241339+00:00
-- url     : https://prove2.me/submissions/ec4fe368-f75a-4fe0-82c2-4e74ff009a2d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_DetMemOneOfEntries

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
open PI PI.DIP
variable {E : Type} [Field E] [NumberField E] {N : ℕ}
namespace PI.DIP
theorem _root_.solution (L₀ : Submodule (𝓞 E) (Fin N → E)) (hfg : L₀.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ x ∈ L₀, ∀ i, algebraMap (𝓞 E) E d * x i ∈ (1 : Submodule (𝓞 E) E) := by
  obtain ⟨G, hG⟩ := hfg
  have hs : ∀ z : E, ∃ b : 𝓞 E, b ≠ 0 ∧ algebraMap (𝓞 E) E b * z ∈ (1 : Submodule (𝓞 E) E) := by
    intro z
    obtain ⟨q, hq⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) z
    refine ⟨q.2, nonZeroDivisors.ne_zero q.2.2, Submodule.mem_one.mpr ⟨q.1, ?_⟩⟩
    rw [← hq, mul_comm]
  choose b hb0 hb using hs
  refine ⟨∏ g ∈ G, ∏ i, b (g i), ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun g _ => Finset.prod_ne_zero_iff.mpr fun i _ => hb0 _
  · intro x hx
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      intro i
      have hdvd : b (y i) ∣ ∏ g ∈ G, ∏ i, b (g i) :=
        (Finset.dvd_prod_of_mem (fun i => b (y i)) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun g => ∏ i, b (g i)) hy)
      obtain ⟨e, he⟩ := hdvd
      rw [he, map_mul, mul_comm (algebraMap _ _ (b (y i))), mul_assoc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hb _)
    | zero => intro i; simp
    | add y z _ _ hy hz =>
      intro i
      simp only [Pi.add_apply, mul_add]
      exact add_mem (hy i) (hz i)
    | smul a y _ hy =>
      intro i
      rw [Pi.smul_apply, mul_smul_comm]
      exact Submodule.smul_mem _ _ (hy i)
end PI.DIP
