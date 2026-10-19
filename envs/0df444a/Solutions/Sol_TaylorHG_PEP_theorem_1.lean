-- Prove2me | solution 1 for TaylorHG.PEP.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T09:54:24.279539+00:00
-- url     : https://prove2.me/submissions/26d4e093-fcc3-4bc9-91c5-9e527e9c0ea8

-- Direction: Alexander Richard Towell (queelius); formalization: OpenAI Codex.
-- Mathematical construction: Taylor, Hendrickx and Glineur, arXiv:1502.05666v6, Theorem 1.
-- Platform formulation: mikedeng1; review: Shuze Chen; subgradient definition: Shor.
import Mathlib
import Definitions.Def_TaylorHG_PEP_Interp
set_option autoImplicit false
open TaylorHG.PEP
namespace ConvexInterpolation
lemma class_zero {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) : FClass 0 ⊤ f := by
  refine ⟨hf,?_,?_⟩
  · intro x y g h _ _
    simp only [ENNReal.inv_top,ENNReal.toReal_zero,zero_mul]
    exact norm_nonneg _
  · simpa only [NNReal.coe_zero,zero_div,zero_mul,sub_zero] using hf
end ConvexInterpolation

theorem solution {d : ℕ} {ι : Type*} [Fintype ι]
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) :
    Interpolable 0 ⊤ x g fv ↔
      ∀ i j, fv j + inner ℝ (g j) (x i - x j) ≤ fv i := by
  classical
  constructor
  · rintro ⟨f,hf,hi⟩ i j
    have h := (hi j).2 (x i)
    rw [(hi i).1,(hi j).1] at h
    linarith
  · intro h
    cases isEmpty_or_nonempty ι with
    | inl he =>
      let := he
      exact ⟨fun _ => 0,ConvexInterpolation.class_zero _ (convexOn_const _ convex_univ),fun i => isEmptyElim i⟩
    | inr he =>
      let := he
      let A := fun (j : ι) (z : EuclideanSpace ℝ (Fin d)) => fv j+inner ℝ (g j) (z-x j)
      let f := fun z => ⨆ j, A j z
      have hbound (z) : BddAbove (Set.range (fun j => A j z)) := (Set.finite_range _).bddAbove
      have hle (j z) : A j z ≤ f z := le_ciSup (hbound z) j
      have hf : ConvexOn ℝ Set.univ f := by
        refine ⟨convex_univ,?_⟩
        intro u _ v _ a b ha hb hab
        apply ciSup_le
        intro j
        have hu := mul_le_mul_of_nonneg_left (hle j u) ha
        have hv := mul_le_mul_of_nonneg_left (hle j v) hb
        have heq : A j (a • u+b • v)=a*A j u+b*A j v := by
          dsimp [A]
          simp only [inner_sub_right,inner_add_right,inner_smul_right]
          have heq : b=1-a := by linarith
          rw [heq]
          ring
        rw [heq]
        exact add_le_add hu hv
      have hval (i) : f (x i)=fv i := by
        apply le_antisymm
        · exact ciSup_le (fun j => h i j)
        · have hi := hle i (x i)
          simpa only [A,sub_self,inner_zero_right,add_zero] using hi
      refine ⟨f,ConvexInterpolation.class_zero f hf,?_⟩
      intro i
      refine ⟨hval i,?_⟩
      intro z
      have hi := hle i z
      rw [hval i]
      dsimp [A] at hi
      linarith
