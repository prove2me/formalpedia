-- Prove2me | solution 1 for SensitivityWeightedCliqueCertificate.check_sound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:32:31.422128+00:00
-- url     : https://prove2.me/submissions/f3893e60-348e-4307-ad82-08052f87618c

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CliqueCertificate
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_WeightedCliqueCertificate
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Bitwise
import Theorems.Thm_SensitivityWeightedCliqueCertificate_coloring_bound

namespace SensitivityCliqueCertificate
end SensitivityCliqueCertificate
namespace SensitivityWeightedCliqueCertificate
end SensitivityWeightedCliqueCertificate

section


/-! The same explicit branch/coloring proof objects with nonnegative vertex weights. -/
namespace SensitivityWeightedCliqueCertificate

open scoped BigOperators
open SensitivityCliqueCertificate
set_option autoImplicit false









theorem coloringCheck_sound {adj weight : ℕ → ℕ} {mask bound : ℕ}
    {classes : List (List ℕ)} (hcheck : coloringCheck adj weight mask bound classes = true)
    (vertices : Finset ℕ) (hmask : InMask mask vertices) (hclique : Clique adj vertices) :
    (∑ v ∈ vertices, weight v) ≤ bound := by
  obtain ⟨hsize, hrest⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨hcover, hclasses⟩ := Bool.and_eq_true_iff.mp hrest
  have hsize' : (classes.map (classFee weight)).sum ≤ bound := of_decide_eq_true hsize
  have hcover' : mask &&& maskOf classes.flatten = mask := of_decide_eq_true hcover
  apply (coloring_bound adj weight classes (List.all_eq_true.mp hclasses) vertices hclique ?_).trans hsize'
  intro v hv
  apply (testBit_maskOf classes.flatten v).mp
  have hbit := congrArg (fun n => n.testBit v) hcover'
  simpa only [Nat.testBit_and, hmask v hv, Bool.true_and] using hbit







end SensitivityWeightedCliqueCertificate

end

/-! The same explicit branch/coloring proof objects with nonnegative vertex weights. -/
open SensitivityWeightedCliqueCertificate
open scoped BigOperators
open SensitivityCliqueCertificate
set_option autoImplicit false

theorem solution (adj weight : ℕ → ℕ) (certificate : Certificate)
    (mask bound : ℕ) (hcheck : check adj weight mask bound certificate = true)
    (vertices : Finset ℕ) (hmask : InMask mask vertices) (hclique : Clique adj vertices) :
    (∑ v ∈ vertices, weight v) ≤ bound := by
  induction certificate generalizing mask bound vertices with
  | color classes => exact coloringCheck_sound hcheck vertices hmask hclique
  | split v inside outside ihin ihout =>
    obtain ⟨hsize, hrest⟩ := Bool.and_eq_true_iff.mp hcheck
    obtain ⟨hin, hout⟩ := Bool.and_eq_true_iff.mp hrest
    have hweight : weight v ≤ bound := of_decide_eq_true hsize
    by_cases hv : v ∈ vertices
    · have herase : (∑ w ∈ vertices.erase v, weight w) ≤ bound - weight v := by
        apply ihin (mask &&& adj v) (bound - weight v) hin
        · intro w hw
          obtain ⟨hnev, hw⟩ := Finset.mem_erase.mp hw
          simp only [Nat.testBit_and, hmask w hw, Bool.true_and]
          exact hclique v hv w hw hnev.symm
        · intro a ha b hb hne
          exact hclique a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2 hne
      have hsum := Finset.sum_erase_add vertices weight hv
      have hsub := Nat.sub_add_cancel hweight
      omega
    · apply ihout (mask ^^^ 2 ^ v) bound hout vertices ?_ hclique
      intro w hw
      have hne : v ≠ w := by intro heq; exact hv (heq ▸ hw)
      simp only [Nat.testBit_xor, Nat.testBit_two_pow_of_ne hne, hmask w hw, Bool.bne_false]
