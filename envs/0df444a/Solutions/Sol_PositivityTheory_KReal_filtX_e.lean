-- Prove2me | solution 1 for PositivityTheory.KReal.filtX_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:38.767853+00:00
-- url     : https://prove2.me/submissions/0f0ec33f-e81f-46ca-931c-7324556c110b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasB
import Theorems.Thm_PositivityTheory_KReal_wordX_cons
import Theorems.Thm_PositivityTheory_KReal_filtX_mono
import Theorems.Thm_PositivityTheory_KReal_filtX_X

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
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {K I : Type} {M : Type} [AddCommGroup M] [Module ℂ M] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.KReal
theorem _root_.solution [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j) (ρ : K → Module.End ℂ V)
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v)) (n : ℕ) (k : K) :
    ∀ x ∈ filtX X ι n, e k x ∈ filtX X ι n := by
  have key : ∀ (l : List I) (v : V), e k (wordX X l (ι v)) ∈ filtX X ι l.length := by
    intro l v
    induction l with
    | nil =>
      have : e k (wordX X [] (ι v)) = wordX X [] (ι (ρ k v)) := by simp [wordX, hι]
      rw [this]
      exact Submodule.subset_span ⟨[], _, le_rfl, rfl⟩
    | cons a l ih =>
      have h := LinearMap.congr_fun (h1 k a) (wordX X l (ι v))
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at h
      rw [wordX_cons, sub_eq_iff_eq_add.1 h, List.length_cons]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
        (filtX_X X ι _ a _ ih)
      exact filtX_X X ι _ j _ (Submodule.subset_span ⟨l, v, le_rfl, rfl⟩)
  have : filtX X ι n ≤ (filtX X ι n).comap (e k) := by
    conv_lhs => rw [filtX]
    rw [Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    exact filtX_mono X ι hl (key l v)
  exact fun x hx => this hx
end PositivityTheory.KReal
