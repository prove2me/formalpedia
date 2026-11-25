-- Prove2me | solution 1 for PI.LocalEndW.isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:58:19.027162+00:00
-- url     : https://prove2.me/submissions/136779e0-eebc-4289-a194-88cf522f9fc5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_HenselRoot
import Theorems.Thm_PI_LocalEndW_norm_le_one_of_mem
import Theorems.Thm_PI_LocalEndW_mem_pow_smul_top_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Filter Topology
open PI PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocalEndW
theorem _root_.solution (ϖ : v.adicCompletionIntegers F) (hϖ : ϖ ≠ 0)
    (h1 : ‖(ϖ : v.adicCompletion F)‖ < 1) :
    IsAdicComplete (Ideal.span {ϖ}) (v.adicCompletionIntegers F) := by
  have hr0 : 0 < ‖(ϖ : v.adicCompletion F)‖ := norm_pos_iff.mpr (fun h => hϖ (Subtype.ext h))
  have key : ∀ (n : ℕ) (x y : v.adicCompletionIntegers F),
      x ≡ y [SMOD ((Ideal.span {ϖ}) ^ n • ⊤ : Submodule (v.adicCompletionIntegers F) (v.adicCompletionIntegers F))] ↔
        ‖(x : v.adicCompletion F) - y‖ ≤ ‖(ϖ : v.adicCompletion F)‖ ^ n := by
    intro n x y
    rw [SModEq.sub_mem, mem_pow_smul_top_iff v ϖ hϖ]
    simp
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h : ∀ n : ℕ, ‖(x : v.adicCompletion F)‖ ≤ ‖(ϖ : v.adicCompletion F)‖ ^ n := fun n => by
      simpa using (key n x 0).mp (hx n)
    have hx0 : ‖(x : v.adicCompletion F)‖ ≤ 0 :=
      ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le h1) h
    exact Subtype.ext (norm_le_zero_iff.mp hx0)
  · intro f hf
    have hc : ∀ n : ℕ, dist (f n : v.adicCompletion F) (f (n + 1)) ≤ 1 * ‖(ϖ : v.adicCompletion F)‖ ^ n := fun n => by
      rw [dist_eq_norm, one_mul]
      exact (key n _ _).mp (hf n.le_succ)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ 1 h1 hc)
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm (fun n => norm_le_one_of_mem v (f n))
    refine ⟨⟨L, Valued.toNormedField.norm_le_one_iff.mp hL1⟩, fun n => ?_⟩
    rw [key]
    have ht : Tendsto (fun m => ‖(f n : v.adicCompletion F) - f m‖) atTop (𝓝 ‖(f n : v.adicCompletion F) - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    exact le_of_tendsto ht (eventually_atTop.mpr ⟨n, fun m hm => (key n _ _).mp (hf hm)⟩)
end PI.LocalEndW
