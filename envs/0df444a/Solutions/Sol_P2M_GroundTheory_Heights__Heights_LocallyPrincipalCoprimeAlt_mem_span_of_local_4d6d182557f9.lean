-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_mem_span_of_local_4d6d182557f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:34.554849+00:00
-- url     : https://prove2.me/submissions/01bc70cc-2895-4fea-8164-ed9e7696ba16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLocallyPrincipalCoprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
variable {L : Type} [Field L]
namespace GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
theorem _root_.solution {B : Subring L} {M : AddSubgroup L} {ι : Type} {a : ι → L}
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    {z : L} (hz : z ∈ M) : z ∈ Submodule.span B (Set.range a) := by
  set S := Submodule.span B (Set.range a)
  by_contra hzS
  have hJ : S.colon {z} ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ S.colon {z} := h ▸ Submodule.mem_top
    rw [Submodule.mem_colon_singleton, one_smul] at h1
    exact hzS h1
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hJ
  obtain ⟨i, hi⟩ := hloc m hm
  obtain ⟨b, c, hbm, hbc⟩ := hi z hz
  apply hbm
  apply hJm
  have e : b • z = c • a i := by rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, hbc]
  rw [Submodule.mem_colon_singleton, e]
  exact S.smul_mem c (Submodule.subset_span ⟨i, rfl⟩)
end GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
