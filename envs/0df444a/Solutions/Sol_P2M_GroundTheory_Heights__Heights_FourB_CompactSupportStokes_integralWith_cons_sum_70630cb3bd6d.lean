-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integralWith_cons_sum_70630cb3bd6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:32.518091+00:00
-- url     : https://prove2.me/submissions/4cca0b4e-4627-48c4-9aa6-3194761fa118

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_locDens_cons_congr_1469dadc76d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_term_ecea057f1f1f
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_cons_add
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_locDens_cons_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_smooth_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff Manifold
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
theorem _root_.solution [T2Space X] (A : FinHolAtlas (e + 1) X) (χ : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) {ι : Type*} (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ m, A.Smooth (f m)) {L : Set X} (hL : IsCompact L)
    (hfL : ∀ m, tsupport (f m) ⊆ L) :
    integralWith A χ (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ s, f m x) Φ) (fun _ => 1) =
      ∑ m ∈ s, integralWith A χ (Fin.cons (LocPot.ofFun (f m)) Φ) (fun _ => 1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    unfold integralWith
    refine Finset.sum_eq_zero fun k _ => ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have h0 : (A.chart k).symm y ∉ tsupport (fun x => ∑ m ∈ (∅ : Finset ι), f m x) := by
      simp
    rw [st_locDens_cons_eq_zero A k _ Φ hy h0, mul_zero]
  | insert a s ha ih =>
    have hS : A.Smooth (fun x => ∑ m ∈ s, f m x) := st_smooth_sum A s hf
    have hSL : tsupport (fun x => ∑ m ∈ s, f m x) ⊆ L := by
      refine closure_minimal ?_ hL.isClosed
      intro x hx
      obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      exact hfL m (subset_tsupport _ hm)
    have hd : ∀ k, ∀ y ∈ (A.chart k).target,
        locDens A (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ insert a s, f m x) Φ) k y =
          locDens A (Fin.cons (LocPot.ofFun (f a)) Φ) k y +
            locDens A (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ s, f m x) Φ) k y := by
      intro k y hy
      rw [← locDens_cons_add A _ _ Φ (isPotential_ofFun A _ (hf a)) (isPotential_ofFun A _ hS) k hy]
      refine locDens_cons_congr A Φ ?_ k y
      funext x z
      simp [Finset.sum_insert ha, LocPot.ofFun]
      rfl
    rw [Finset.sum_insert ha, ← ih]
    unfold integralWith
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_add (integrableOn_term A χ Φ hΦ k k _ (hf a) hL (hfL a) (Or.inl rfl))
      (integrableOn_term A χ Φ hΦ k k _ hS hL hSL (Or.inl rfl))]
    refine setIntegral_congr_fun (A.chart k).open_target.measurableSet fun y hy => ?_
    simp only
    rw [hd k y hy]
    ring
end GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
