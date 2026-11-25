-- Prove2me | solution 1 for UpperTheory.Reformulated.B.IwahoriEntryBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:00:17.276419+00:00
-- url     : https://prove2.me/submissions/2be502c4-66d3-4fdf-85ed-72354154e9f3

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IwahoriEntryBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
namespace UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers
private lemma entry_bound {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {h : GL (Fin n) L} (hh : h ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL L n) (i j : Fin n) :
    (Valued.v ((h : Matrix (Fin n) (Fin n) L) i j) ≤ 1) ∧
    ((j : ℕ) < (i : ℕ) → Valued.v ((h : Matrix (Fin n) (Fin n) L) i j) < 1) := by
  classical
  have hk := (Subgroup.mem_iInf.mp hh) ⟨(j : ℕ) + 1, by omega⟩
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hk
  have hx : (Pi.single j (1 : L) : Fin n → L) ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n ((j : ℕ) + 1) := by
    intro t
    by_cases ht : t = j
    · subst ht
      simp
    · have : Pi.single (M := fun _ => L) j (1 : L) t = 0 := Pi.single_eq_of_ne ht _
      split_ifs <;> simp [this]
  have hy := Set.smul_mem_smul_set (a := (Matrix.GeneralLinearGroup.toLin.toMonoidHom h)) hx
  have hk' : Matrix.GeneralLinearGroup.toLin.toMonoidHom h • UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n ((j : ℕ) + 1)
      = UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n ((j : ℕ) + 1) := hk
  rw [hk'] at hy
  have key : (Matrix.GeneralLinearGroup.toLin.toMonoidHom h) • (Pi.single j (1 : L) : Fin n → L)
      = (h : Matrix (Fin n) (Fin n) L) *ᵥ Pi.single j 1 := by
    rfl
  rw [key] at hy
  have e : ((h : Matrix (Fin n) (Fin n) L) *ᵥ Pi.single j 1) i = (h : Matrix (Fin n) (Fin n) L) i j := by
    simp [Matrix.mulVec_single_one]
  have hi := hy i
  rw [e] at hi
  constructor
  · split_ifs at hi with hc
    · exact hi
    · exact hi.le
  · intro hlt
    rw [if_neg (by omega)] at hi
    exact hi
end UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers
end

set_option autoImplicit false
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
open UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers
namespace UpperTheory.Reformulated.B.IwahoriEntryBound
theorem _root_.solution :
    ∀ {L : Type} [inst : Field L] [inst_1 : Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {g : GL (Fin n) L},
      g ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL L n →
        ∀ (i : Fin n),
          (Valued.v : L → WithZero (Multiplicative ℤ)) ((↑g : Matrix (Fin n) (Fin n) L) i i) =
            (1 : WithZero (Multiplicative ℤ)) := by
  intro L _ _ n g hg i
  classical
  have hg' : g⁻¹ ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL L n := inv_mem hg
  have hprod : ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hii := congrFun (congrFun hprod i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hii
  set a := ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * (g : Matrix (Fin n) (Fin n) L) i i with ha
  have hrest : Valued.v (∑ j ∈ Finset.univ.erase i,
      ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j * (g : Matrix (Fin n) (Fin n) L) j i) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    rw [Valuation.map_mul]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    ·
      have h1 := (entry_bound hg' i j).2 hlt
      have h2 := (entry_bound hg j i).1
      calc _ ≤ Valued.v (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) * 1 := by gcongr
        _ = _ := mul_one _
        _ < 1 := h1
    · have h1 := (entry_bound hg' i j).1
      have h2 := (entry_bound hg j i).2 hlt
      calc _ ≤ 1 * Valued.v ((g : Matrix (Fin n) (Fin n) L) j i) := by gcongr
        _ = _ := one_mul _
        _ < 1 := h2
  have hva : 1 ≤ Valued.v a := by
    by_contra hc
    push Not at hc
    have := Valuation.map_add_lt _ hc hrest
    rw [hii, Valuation.map_one] at this
    exact lt_irrefl _ this
  have hgi := (entry_bound hg i i).1
  have hinv := (entry_bound hg' i i).1
  apply le_antisymm hgi
  calc (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v a := hva
    _ = _ := Valuation.map_mul _ _ _
    _ ≤ 1 * Valued.v ((g : Matrix (Fin n) (Fin n) L) i i) := by gcongr
    _ = _ := one_mul _
end UpperTheory.Reformulated.B.IwahoriEntryBound
