-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.multi_pres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:30:25.214564+00:00
-- url     : https://prove2.me/submissions/3b4deae8-a63b-47be-b395-cffcbd397c45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SupportFreeOfBlockSubstInvariant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_mem_support_compB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_one_block
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K : Type} [Field K] [CharZero K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (z : KTf K D N)
    (hz : ∀ (b : Fin (D + 1)) (u : Kˣ), sigF (K := K) (D := D) (N := N) b u z = z)
    (p q : KTp K D N) (hq : q ≠ 0)
    (hpq : algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q)
    (hp0 : ∀ s ∈ p.support, degB 0 s = 0) (hq0 : ∀ s ∈ q.support, degB 0 s = 0) :
    ∃ a b : KTp K D N, b ≠ 0 ∧
      algebraMap (KTp K D N) (KTf K D N) a = z * algebraMap (KTp K D N) (KTf K D N) b ∧
      ∃ m : Fin (D + 1) → ℕ, m 0 = 0 ∧ ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m a ∧
        ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m b := by
  classical
  have key : ∀ S : Finset (Fin (D + 1)), ∃ a b : KTp K D N, b ≠ 0 ∧
      algebraMap (KTp K D N) (KTf K D N) a = z * algebraMap (KTp K D N) (KTf K D N) b ∧
      (∀ s ∈ a.support, degB 0 s = 0) ∧ (∀ s ∈ b.support, degB 0 s = 0) ∧
      ∃ m : Fin (D + 1) → ℕ, ∀ i ∈ S,
        (∀ s ∈ a.support, degB i s = m i) ∧ (∀ s ∈ b.support, degB i s = m i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨p, q, hq, hpq, hp0, hq0, 0, by simp⟩
    | insert i S hi ih =>
      obtain ⟨a, b, hb, hab, ha0, hb0, m, hm⟩ := ih
      obtain ⟨k, hk0, hk⟩ := one_block i z (hz i) a b hb hab
      refine ⟨compB i k a, compB i k b, hk0, hk, fun s hs => ha0 s (mem_support_compB hs).1,
        fun s hs => hb0 s (mem_support_compB hs).1, Function.update m i k, ?_⟩
      intro i' hi'
      rcases Finset.mem_insert.mp hi' with rfl | hi'
      · simp only [Function.update_self]
        exact ⟨fun s hs => (mem_support_compB hs).2, fun s hs => (mem_support_compB hs).2⟩
      · have hne : i' ≠ i := fun h => hi (h ▸ hi')
        rw [Function.update_of_ne hne]
        exact ⟨fun s hs => (hm i' hi').1 s (mem_support_compB hs).1,
          fun s hs => (hm i' hi').2 s (mem_support_compB hs).1⟩
  obtain ⟨a, b, hb, hab, ha0, hb0, m, hm⟩ := key Finset.univ
  refine ⟨a, b, hb, hab, fun i => if i = 0 then 0 else m i, by simp, ?_, ?_⟩
  · intro s hs i
    by_cases hi : i = 0
    · subst hi
      simpa [degB] using ha0 s hs
    · simpa [hi, degB] using (hm i (Finset.mem_univ i)).1 s hs
  · intro s hs i
    by_cases hi : i = 0
    · subst hi
      simpa [degB] using hb0 s hs
    · simpa [hi, degB] using (hm i (Finset.mem_univ i)).2 s hs
end ReciprocityTheory.ChartRestriction.G.T0
