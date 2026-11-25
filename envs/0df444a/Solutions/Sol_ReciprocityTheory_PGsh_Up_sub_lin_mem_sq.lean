-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.sub_lin_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:17:24.22815+00:00
-- url     : https://prove2.me/submissions/f2538f59-aff6-4d5b-a3cd-11d43ea37b21

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_monX_zero_at
import Theorems.Thm_ReciprocityTheory_PGsh_Up_monX_single
import Theorems.Thm_ReciprocityTheory_PGsh_Up_monX_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_monX_mem_sq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hv : v.Integers R) (D : Lifts H U X) (hdet : (valM D).det ≠ 0)
    (hbasis : H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val))
    {f : Nb p g → C} (hf : f ∈ augIdeal H.AA.carrier) :
    ∃ c : Ix g → R, (∀ k, algebraMap R C (c k) = linX D f k) ∧
      f - ∑ k, c k • xL D k ∈ sqIdeal (augIdeal H.AA.carrier) := by
  classical
  have hfA : f ∈ Submodule.span R (Set.range fun α => monX D α) := by
    have h := (Submodule.mem_inf.mp hf).1
    rw [hbasis] at h
    exact h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hfA
  have hf0 : f 0 = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hf).2
  have hval : f = (valM D) *ᵥ (fun α => algebraMap R C (c α)) := by
    rw [← hc]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Matrix.mulVec, dotProduct, valM,
      Matrix.of_apply]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  have hcoef : coefX D f = fun α => algebraMap R C (c α) := by
    rw [coefX, hval, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  refine ⟨fun k => c (Pi.single k 1), fun k => ?_, ?_⟩
  · rw [linX, hcoef]
  · set P : Nb p g → Prop := fun α => α ≠ 0 ∧ ∀ k, α ≠ Pi.single k 1 with hP
    have hw0 : algebraMap R C (c 0) = 0 := by
      have h := congrFun hval 0
      rw [hf0] at h
      simp only [Matrix.mulVec, dotProduct, valM, Matrix.of_apply] at h
      rw [Finset.sum_eq_single 0 (fun α _ hα => by rw [monX_zero_at D hα, zero_mul])
        (fun h => absurd (Finset.mem_univ 0) h), monX_zero] at h
      simpa using h.symm
    have hB : ∑ α, (if P α then 0 else c α • monX D α) = ∑ k, c (Pi.single k 1) • xL D k := by
      have hsub : ∑ α, (if P α then 0 else c α • monX D α) =
          ∑ α ∈ Finset.univ.image (fun k : Ix g => (Pi.single k (1 : ZMod p) : Nb p g)),
            (if P α then 0 else c α • monX D α) := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun α _ hα => ?_
        by_cases hPα : P α
        · simp [hPα]
        · rw [if_neg hPα]
          have h0 : α = 0 := by
            by_contra h0
            apply hPα
            refine ⟨h0, fun k hk => hα ?_⟩
            exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk.symm⟩
          subst h0
          rw [monX_zero]
          funext y
          simp [Algebra.smul_def, hw0]
      rw [hsub, Finset.sum_image (fun k _ k' _ h => by
        by_contra hne
        have h2 := congrFun h k
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h2
        exact one_ne_zero h2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hnP : ¬ P (Pi.single k 1) := fun h => h.2 k rfl
      rw [if_neg hnP, monX_single]
    have hA : ∀ α, (if P α then c α • monX D α else 0) ∈ sqIdeal (augIdeal H.AA.carrier) := by
      intro α
      split_ifs with h
      · exact Submodule.smul_mem _ _ (monX_mem_sq D h.1 h.2)
      · exact Submodule.zero_mem _
    have hsum : f = ∑ α, (if P α then c α • monX D α else 0) +
        ∑ α, (if P α then 0 else c α • monX D α) := by
      rw [← Finset.sum_add_distrib, ← hc]
      refine Finset.sum_congr rfl fun α _ => ?_
      split_ifs <;> simp
    rw [← hB, hsum, add_sub_cancel_right]
    exact Submodule.sum_mem _ fun α _ => hA α
end ReciprocityTheory.PGsh.Up
