-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.csq_dd_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:34.468139+00:00
-- url     : https://prove2.me/submissions/34b20c1e-411c-4480-a31b-f4ac51a0cab2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (i a j b : Fin n) :
    E a i * cp i a * (E j b * cm j b) + E j b * cm j b * (E a i * cp i a) =
      (if i = j then E a b * (cp i a * cm j b) else 0) - (if b = a then E j i * (cp i a * cm j b) else 0) +
        (if b = a then (if j = i then E i a * E a i else 0) else 0) := by
  have c1 : E j b * cp i a = cp i a * E j b := (hEC j b i a).1
  have c2 : E a i * cm j b = cm j b * E a i := (hEC a i j b).2
  have hcar : cm j b * cp i a = (if j = i ∧ b = a then 1 else 0) - cp i a * cm j b :=
    eq_sub_of_add_eq (hC j b i a).2.2
  have hgl : E a i * E j b =
      E j b * E a i + ((if i = j then E a b else 0) - (if b = a then E j i else 0)) := by
    rw [← hE a i j b]; abel
  have step : E a i * cp i a * (E j b * cm j b) + E j b * cm j b * (E a i * cp i a) =
      E a i * E j b * (cp i a * cm j b) + E j b * E a i * (cm j b * cp i a) := by
    calc _ = E a i * (E j b * cp i a) * cm j b + E j b * (E a i * cm j b) * cp i a := by
            rw [c1, c2]; noncomm_ring
      _ = _ := by noncomm_ring
  rw [step, hgl, hcar]
  rcases eq_or_ne i j with h1 | h1 <;> rcases eq_or_ne b a with h2 | h2
  · subst h1; subst h2
    simp only [eq_self_iff_true, and_self, if_true]
    noncomm_ring
  · subst h1
    simp only [eq_self_iff_true, if_true, h2, if_false, and_false]
    noncomm_ring
  · subst h2
    simp only [eq_self_iff_true, if_true, h1, Ne.symm h1, if_false, false_and]
    noncomm_ring
  · simp only [h1, h2, Ne.symm h1, if_false, and_false, false_and]
    noncomm_ring
end ReciprocityTheory.ChartRestriction.DS
