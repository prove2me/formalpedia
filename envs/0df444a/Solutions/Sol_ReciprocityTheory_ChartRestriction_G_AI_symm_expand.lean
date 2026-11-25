-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.symm_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:51.829407+00:00
-- url     : https://prove2.me/submissions/7b8019b8-8198-433f-87a1-708332a54142

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CompRightEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_symm_piecewise_eq_mix

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
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (c : ℝ) :
    I (fun _ => y + c • x) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * c ^ j * I (mix j x y) := by
  classical
  have h1 : (fun _ : Fin n => y + c • x) = (fun _ => c • x) + (fun _ => y) := by
    funext i
    simp [add_comm]
  rw [h1, MultilinearMap.map_add_univ]
  have h2 : ∀ s : Finset (Fin n),
      I (s.piecewise (fun _ => c • x) fun _ => y) = c ^ s.card * I (mix s.card x y) := by
    intro s
    have h3 : (s.piecewise (fun _ => c • x) fun _ => y) =
        s.piecewise (fun i => c • (s.piecewise (fun _ => x) (fun _ => y)) i)
          (s.piecewise (fun _ => x) fun _ => y) := by
      funext i
      by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
    rw [h3, MultilinearMap.map_piecewise_smul, symm_piecewise_eq_mix I hI, Finset.prod_const, smul_eq_mul]
  simp only [h2]
  have h4 := Finset.sum_powerset_apply_card (f := fun k => c ^ k * I (mix k x y))
    (x := (Finset.univ : Finset (Fin n)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h4
  rw [h4]
  simp only [nsmul_eq_mul, mul_assoc]
end ReciprocityTheory.ChartRestriction.G.AI
