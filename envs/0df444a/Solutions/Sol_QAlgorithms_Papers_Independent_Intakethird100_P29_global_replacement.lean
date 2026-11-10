-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P29.global_replacement
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:02:25.867217+00:00
-- url     : https://prove2.me/submissions/f10861b1-c5b2-4ba3-ba39-cea7b75a9745

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P29

noncomputable section

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Intakethird100.P29
  QAlgorithms.Papers.Independent.Advance50.P47
  QAlgorithms.Papers.Independent.Information100.P56 in
theorem solution {s t : BellScenario} (p : Behavior s) (q : Behavior t)
    (hp : IsCorrelation p) (hq : IsCorrelation q) :
    ∃ g : GlobalWiring s t, g.apply p = q := by
  let x0 : s.X := ⟨0, s.xPositive⟩
  let y0 : s.Y := ⟨0, s.yPositive⟩
  let g : GlobalWiring s t :=
    { input := fun _ _ xy => (if xy.1 = x0 then (1 : ℝ) else 0) * (if xy.2 = y0 then (1 : ℝ) else 0)
      output := fun _ _ _ _ chi psi ab => q chi psi ab.1 ab.2
      inputLaw := by
        intro chi psi
        refine ⟨fun xy => ?_, ?_⟩
        · positivity
        · rw [Fintype.sum_prod_type]
          simp
      outputLaw := by
        intro a b x y chi psi
        refine ⟨fun ab => hq.1 _ _ _ _, ?_⟩
        rw [Fintype.sum_prod_type]
        exact hq.2 chi psi }
  refine ⟨g, ?_⟩
  funext chi psi α β
  show ∑ a, ∑ b, ∑ x, ∑ y, q chi psi α β * p x y a b *
    ((if x = x0 then (1 : ℝ) else 0) * (if y = y0 then (1 : ℝ) else 0)) = q chi psi α β
  have h1 : ∀ a b, ∑ x, ∑ y, q chi psi α β * p x y a b *
      ((if x = x0 then (1 : ℝ) else 0) * (if y = y0 then (1 : ℝ) else 0))
      = q chi psi α β * p x0 y0 a b := by
    intro a b
    rw [Fintype.sum_eq_single x0 (fun x hx => by simp [hx])]
    rw [Fintype.sum_eq_single y0 (fun y hy => by simp [hy])]
    simp
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))]
  simp_rw [← Finset.mul_sum]
  rw [hp.2 x0 y0, mul_one]
