-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimA.sympl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:42.615244+00:00
-- url     : https://prove2.me/submissions/8ac17855-3bd9-4b04-bbd2-e65139a906e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimA_perp_surj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimA
open Module
namespace ReciprocityTheory.ChartRestriction.G.I2.DimA
theorem _root_.solution : ∀ (n : ℕ) (H : Type) [AddCommGroup H] [Module.Free ℤ H] [Module.Finite ℤ H],
    finrank ℤ H = n → ∀ B : H →ₗ[ℤ] H →ₗ[ℤ] ℤ, (∀ h, B h h = 0) →
    (∀ φ : H →ₗ[ℤ] ℤ, ∃ x, B x = φ) →
    ∃ k, n = 2 * k ∧ ∃ e f : Fin k → H, (∀ i j, B (e i) (e j) = 0) ∧
      (∀ i j, B (e i) (f j) = if i = j then 1 else 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ _ hn B halt hB
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨0, rfl, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  let b := Module.finBasisOfFinrankEq ℤ H hn
  obtain ⟨x, hx⟩ := hB (b.coord ⟨0, hpos⟩)
  have hxf : B x (b ⟨0, hpos⟩) = 1 := by rw [hx]; simp
  set e := x
  set f := b ⟨0, hpos⟩
  let Q := perp B e f
  haveI : Module.Free ℤ Q := Module.Free.of_basis (Q.basisOfPid b).2
  haveI : Module.Finite ℤ Q := Module.Finite.of_basis (Q.basisOfPid b).2
  have hr : finrank ℤ Q + 2 = n := by
    have h : finrank ℤ H = finrank ℤ (Q × ℤ × ℤ) := (splitEquiv B halt e f hxf).finrank_eq
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, hn] at h
    omega
  have halt' : ∀ h : Q, B.domRestrict₁₂ Q Q h h = 0 := fun h => halt h
  obtain ⟨k', hk', e', f', hee, hef⟩ :=
    ih (n - 2) (by omega) Q (by omega) (B.domRestrict₁₂ Q Q) halt'
      (perp_surj B halt e f hxf hB)
  refine ⟨k' + 1, by omega, Fin.cons e (fun i => (e' i : H)), Fin.cons f (fun i => (f' i : H)),
    ?_, ?_⟩
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using halt e
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [alt_swap B halt, ((mem_perp B).1 (e' j).2).1, neg_zero]
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact ((mem_perp B).1 (e' i).2).1
      | succ j =>
        simp only [Fin.cons_succ]
        exact hee i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hxf
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [alt_swap B halt, ((mem_perp B).1 (f' j).2).1, neg_zero]
        simp [(Fin.succ_ne_zero j).symm]
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [((mem_perp B).1 (e' i).2).2]
        simp [Fin.succ_ne_zero i]
      | succ j =>
        simp only [Fin.cons_succ, Fin.succ_inj]
        exact hef i j
end ReciprocityTheory.ChartRestriction.G.I2.DimA
