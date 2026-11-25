-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.frob_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:52:22.792298+00:00
-- url     : https://prove2.me/submissions/f21f9dd1-b071-48a7-a125-872861a3ecea

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution (hv : v.Integers O) : Function.Surjective (frobenius (ModP O p) p) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C x) hp.out.pos
  have hvy : v y ≤ 1 := by
    have h1 : v y ^ p ≤ 1 := by
      rw [← map_pow, hy]
      exact hv.map_le_one x
    exact (pow_le_one_iff_of_nonneg (by positivity) hp.out.ne_zero).1 h1
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvy
  refine ⟨Ideal.Quotient.mk _ z, ?_⟩
  rw [frobenius_def, ← map_pow]
  congr 1
  exact hv.hom_inj (by rw [map_pow, hy])
end ReciprocityTheory.PGsh.Ainf
