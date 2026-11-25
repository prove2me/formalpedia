-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_heis_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:34.369885+00:00
-- url     : https://prove2.me/submissions/d3613ff1-f182-409b-b291-7f2f4ca5b945

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos


section
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
private theorem e0_apply_eq_ite (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) :
    e0 k r' p = if p.val = 0 then 1 else 0 := by
  simp only [e0, bvec, Pi.single_apply, eI, a0, Fin.ext_iff]
private theorem sum_eq_sum_mp_of_zero_at_edges (k r' : ℕ) (g : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hz : ∀ q : Fin (2 * (1 + r') + k + 1), (q.val = 0 ∨ q.val = 2 * (1 + r') + k) → g q = 0) :
    ∑ q, g q = ∑ j, g (mp k r' j) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (mp k r'))) ?_]
  · rw [Finset.sum_image]
    intro a _ b _ hab
    apply Fin.ext
    have := congrArg Fin.val hab
    simp only [mp] at this
    omega
  · intro q _ hq
    apply hz
    have hql := q.isLt
    by_contra hne
    apply hq
    rw [Finset.mem_image]
    refine ⟨⟨q.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp only [mp]
    omega
private theorem liftVec_apply_eq_zero_of_edge (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * (1 + r') + k + 1))
    (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) : liftVec k 1 r' v q = 0 := by
  simp only [liftVec]
  split_ifs with h
  · exfalso; omega
  · rfl
private theorem liftVec_apply_mp (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (mp k r' j) = v j := by
  have hj := j.isLt
  simp only [liftVec, mp]
  split_ifs with h
  · first
      | rfl
      | exact congrArg v (Fin.ext (Nat.add_sub_cancel j.val 1))
      | (simp; intro; omega)
  · exfalso; omega
private theorem Hpk_one_add_apply_mp_mp (k r' : ℕ) (i j : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') (mp k r' i) (mp k r' j) = Hpk k r' i j := by
  have hi := i.isLt
  have hj := j.isLt
  have e1 : (mp k r' i).val = i.val + 1 := rfl
  have e2 : (mp k r' j).val = j.val + 1 := rfl
  simp only [and_true, true_and, Hpk, Fin.ext_iff, e1, e2]
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all
private theorem Hpk_mulVec_liftVec_eq_liftVec_mulVec (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ liftVec k 1 r' v = liftVec k 1 r' (Hpk k r' *ᵥ v) := by
  funext p
  have hpl := p.isLt
  show ∑ q, Hpk k (1 + r') p q * liftVec k 1 r' v q = liftVec k 1 r' (Hpk k r' *ᵥ v) p
  rw [sum_eq_sum_mp_of_zero_at_edges k r' (fun q => Hpk k (1 + r') p q * liftVec k 1 r' v q)
    (fun q hq => by
      show Hpk k (1 + r') p q * liftVec k 1 r' v q = 0
      rw [liftVec_apply_eq_zero_of_edge k r' v q hq, mul_zero])]
  simp only [liftVec_apply_mp]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · have hpe : p = mp k r' ⟨p.val - 1, by omega⟩ := Fin.ext (by simp only [mp]; omega)
    rw [hpe, liftVec_apply_mp]
    show _ = ∑ j, Hpk k r' _ j * v j
    simp only [Hpk_one_add_apply_mp_mp]
  · have h0 : liftVec k 1 r' (Hpk k r' *ᵥ v) p = 0 := by
      simp only [liftVec]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0]
    apply Finset.sum_eq_zero
    intro j _
    have hj := j.isLt
    have : Hpk k (1 + r') p (mp k r' j) = 0 := by
      simp only [Hpk, mp, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, zero_mul]
private theorem dotProduct_star_liftVec_liftVec (k r' : ℕ) (y w : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' y) ⬝ᵥ liftVec k 1 r' w = star y ⬝ᵥ w := by
  show ∑ q, star (liftVec k 1 r' y q) * liftVec k 1 r' w q = ∑ j, star (y j) * w j
  rw [sum_eq_sum_mp_of_zero_at_edges k r' (fun q => star (liftVec k 1 r' y q) * liftVec k 1 r' w q)
    (fun q hq => by
      show star (liftVec k 1 r' y q) * liftVec k 1 r' w q = 0
      rw [liftVec_apply_eq_zero_of_edge k r' w q hq, mul_zero])]
  simp only [liftVec_apply_mp]
private theorem herm_liftVec_liftVec (k r' : ℕ) (v y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' v) (liftVec k 1 r' y) = herm (Hpk k r') v y := by
  rw [herm, herm, Hpk_mulVec_liftVec_eq_liftVec_mulVec, dotProduct_star_liftVec_liftVec]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r' : ℕ} (hHA : HeisAct) (x : HPar k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    heis0 k r' x *ᵥ liftVec k 1 r' v = liftVec k 1 r' v - herm (Hpk k r') v x.1 • e0 k r' := by
  have h3 : herm (Hpk k (1 + r')) (liftVec k 1 r' v) (e0 k r') = 0 := by
    rw [herm, Hpk_mulVec_liftVec_eq_liftVec_mulVec]
    show ∑ p, star (e0 k r' p) * liftVec k 1 r' (Hpk k r' *ᵥ v) p = 0
    apply Finset.sum_eq_zero
    intro p _
    rw [e0_apply_eq_ite]
    split_ifs with hp
    · rw [liftVec_apply_eq_zero_of_edge k r' _ p (Or.inl hp), mul_zero]
    · rw [star_zero, zero_mul]
  rw [heis0, hHA k r', herm_liftVec_liftVec, h3]
  simp
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
