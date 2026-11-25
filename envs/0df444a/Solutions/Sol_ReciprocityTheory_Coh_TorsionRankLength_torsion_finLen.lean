-- Prove2me | solution 1 for ReciprocityTheory.Coh.TorsionRankLength.torsion_finLen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:47:27.816461+00:00
-- url     : https://prove2.me/submissions/e3bc9aab-3a3f-48e9-b435-45ad4becd553

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLenA
import Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_len_quot_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.TorsionRankLength
universe u
open Module Submodule Function
open scoped Pointwise TensorProduct
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H]
namespace ReciprocityTheory.Coh.TorsionRankLength
theorem _root_.solution : IsFiniteLength R (torsion R H) := by
  obtain ⟨ι, _, p, hp, e, ⟨f⟩⟩ :=
    Module.equiv_directSum_of_isTorsion (R := R) (M := torsion R H) (torsion_isTorsion)
  rw [← Module.length_ne_top_iff, f.length_eq,
    (DirectSum.linearEquivFunOnFintype R ι (fun i => R ⧸ R ∙ p i ^ e i)).length_eq,
    Module.length_pi_of_fintype]
  have : ∀ i, Module.length R (R ⧸ R ∙ p i ^ e i) = e i := fun i => len_quot_pow (hp i) (e i)
  simp only [this]
  exact (ENat.sum_lt_top.mpr fun i _ => ENat.natCast_lt_top _).ne
end ReciprocityTheory.Coh.TorsionRankLength
