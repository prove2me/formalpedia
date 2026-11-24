-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.symm_swap_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:07.01291+00:00
-- url     : https://prove2.me/submissions/2320a205-4401-47e4-bbef-6a5efc8a774f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (f : ℕ → V) (a b : ℕ)
    (ha : a < n) (hb : b < n) :
    I (fun j => f j) = I (fun j => f (if (j : ℕ) = a then b else if (j : ℕ) = b then a else j)) := by
  have h := hI (Equiv.swap (⟨a, ha⟩ : Fin n) ⟨b, hb⟩) (fun j => f j)
  refine h.symm.trans (congrArg I (funext fun j => ?_))
  show f ((Equiv.swap (⟨a, ha⟩ : Fin n) ⟨b, hb⟩ j : Fin n) : ℕ) =
    f (if (j : ℕ) = a then b else if (j : ℕ) = b then a else j)
  refine congrArg f ?_
  by_cases h1 : (j : ℕ) = a
  · rw [if_pos h1]
    have hj : j = ⟨a, ha⟩ := Fin.ext h1
    simp [hj]
  · by_cases h2 : (j : ℕ) = b
    · rw [if_neg h1, if_pos h2]
      have hj : j = ⟨b, hb⟩ := Fin.ext h2
      simp [hj]
    · have h1' : j ≠ ⟨a, ha⟩ := fun h => h1 (congrArg Fin.val h)
      have h2' : j ≠ ⟨b, hb⟩ := fun h => h2 (congrArg Fin.val h)
      rw [if_neg h1, if_neg h2, Equiv.swap_apply_of_ne_of_ne h1' h2']
end ReciprocityTheory.ChartRestriction.G.AI
