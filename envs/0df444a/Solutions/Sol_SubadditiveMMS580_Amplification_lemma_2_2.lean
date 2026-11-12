-- Prove2me | solution 1 for SubadditiveMMS580.Amplification.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:57:46.08721+00:00
-- url     : https://prove2.me/submissions/f5b4b36d-0850-4b3a-974b-594f45b4cbed

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.L22

theorem mms_erase_le {m : ℕ} (w : Finset (Fin m) → ℝ) (hmono : IsMonotone w) (k : ℕ)
    (hk : 1 ≤ k) (g : Fin m) :
    LittleCharity.MMS.mms w (k + 1) Finset.univ ≤
      LittleCharity.MMS.mms w k (Finset.univ.erase g) := by
  classical
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : Nonempty (Fin (k + 1)) := ⟨0⟩
  unfold LittleCharity.MMS.mms
  apply ciSup_le
  intro f
  set c : Fin (k + 1) := f g with hc
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin (k + 1) → Fin k, ∀ j, φ (c.succAbove j) = j :=
    (Fin.succAbove_right_injective (p := c)).hasLeftInverse
  refine le_trans ?_ (le_ciSup (f := fun f' : Fin m → Fin k =>
    ⨅ j : Fin k, w ((Finset.univ.erase g).filter (fun x => f' x = j)))
    (Set.finite_range _).bddAbove (fun x => φ (f x)))
  apply le_ciInf
  intro j'
  refine le_trans (ciInf_le (Set.finite_range _).bddBelow (c.succAbove j')) ?_
  apply hmono
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq] at hx ⊢
  refine ⟨⟨?_, trivial⟩, by rw [hx, hφ]⟩
  rintro rfl
  exact Fin.succAbove_ne c j' hx.symm

end SubadditiveMMS580.Amplification.Dev.L22

namespace SubadditiveMMS580.Amplification
open SubadditiveMMS580.Amplification.Dev.L22 in
theorem chk_lemma_2_2 (n : ℕ) (hn : 2 ≤ n) {m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (i : Fin n) (g : Fin m) :
    (∀ j : Fin n, j ≠ i →
      LittleCharity.MMS.mms (v j) n Finset.univ ≤
        LittleCharity.MMS.mms (v j) (n - 1) (Finset.univ.erase g)) ∧
    ∀ α : ℝ, α * LittleCharity.MMS.mms (v i) n Finset.univ ≤ v i {g} →
      α * LittleCharity.MMS.mms (v i) n Finset.univ ≤ v i ({g} : Finset (Fin m)) := by
  refine ⟨fun j _ => ?_, fun α h => h⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using mms_erase_le (v j) (hmono j) k (by omega) g

end SubadditiveMMS580.Amplification
end

theorem solution : type_of% @SubadditiveMMS580.Amplification.chk_lemma_2_2 := @SubadditiveMMS580.Amplification.chk_lemma_2_2
