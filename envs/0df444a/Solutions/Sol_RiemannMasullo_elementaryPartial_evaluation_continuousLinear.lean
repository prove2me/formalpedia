-- Prove2me | solution 1 for RiemannMasullo.elementaryPartial_evaluation_continuousLinear
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:31:19.544844+00:00
-- url     : https://prove2.me/submissions/b427765c-33ed-4196-94b3-0b3acce7b0df

-- New supporting theorem for the polynomial seminorms in Appendix D.
import Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ContDiff ENNReal

theorem solution (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ∃ L : ElementarySchwartz m n r F →L[ℂ] ℂ, ∀ f, L f = elementaryPartial f β γ x a b := by
  classical
  let E := ElementarySchwartz m n r F
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let dirs : List X :=
    (List.ofFn (fun k : Fin m ↦ List.replicate (β k) (EuclideanSpace.single k 1, 0))).flatten ++
    (List.ofFn (fun k : Fin n ↦ List.replicate (γ k) (0, EuclideanSpace.single k 1))).flatten
  have hdiff (f : E) := (((f.property.1 a b).of_le
    (show (dirs.length : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
      exact_mod_cast (le_top : (dirs.length : ℕ∞) ≤ ⊤))).contDiffAt (x:=x))
  let L : E →ₗ[ℂ] ℂ :=
    { toFun := fun f => elementaryPartial f β γ x a b
      map_add' := fun f g => by
        change iteratedFDeriv ℝ dirs.length
          ((fun v => f (elementaryCover v a b)) + (fun v => g (elementaryCover v a b))) x dirs.get = _
        rw [iteratedFDeriv_add_apply (hdiff f) (hdiff g), ContinuousMultilinearMap.add_apply]
        rfl
      map_smul' := fun c f => by
        change iteratedFDeriv ℝ dirs.length (c • (fun v => f (elementaryCover v a b))) x dirs.get = _
        rw [iteratedFDeriv_const_smul_apply (a:=c) (hdiff f),ContinuousMultilinearMap.smul_apply]
        rfl }
  let i : ElementarySchwartzIndex m n r := (0,β,γ,0)
  have hdom (f : E) : ‖L f‖ ≤ elementarySchwartzSeminorm i f := by
    have h : (‖L f‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound f.val i := by
      unfold elementarySchwartzBound
      apply le_iSup_of_le x
      apply le_iSup_of_le a
      apply le_iSup_of_le b
      simp [i,L]
    exact ENNReal.toReal_mono (f.property.2 i).ne h
  have hc : Continuous L := by
    apply Seminorm.cont_withSeminorms_normedSpace _ elementarySchwartz_withSeminorms L
    refine ⟨{i},1,?_⟩
    intro f
    simp [Seminorm.comp_apply]
    exact (hdom f).trans (Finset.le_sup (f:=elementarySchwartzSeminorm) (Finset.mem_singleton_self i) f)
  exact ⟨⟨L,hc⟩,fun _ => rfl⟩
