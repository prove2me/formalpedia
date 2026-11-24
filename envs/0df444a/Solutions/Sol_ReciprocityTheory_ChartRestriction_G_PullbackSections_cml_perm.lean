-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:20.933994+00:00
-- url     : https://prove2.me/submissions/80a9eb3b-9780-4d72-93cc-adf94c78e9af

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {l l' : List V} (p : l.Perm l') :
    ∀ (n : ℕ) (M : ContinuousMultilinearMap ℂ (fun _ : Fin n => V) ℂ),
      (∀ (v : Fin n → V) (σ : Equiv.Perm (Fin n)), M (v ∘ σ) = M v) →
      ∀ (h : l.length = n) (h' : l'.length = n),
        M (fun i => l.get (i.cast h.symm)) = M (fun i => l'.get (i.cast h'.symm)) := by
  intro n M hM
  let F : List V → ℂ := fun k => if hk : k.length = n then M (fun i => k.get (i.cast hk.symm)) else 0
  have key : ∀ l₀ : List V, F (l₀ ++ l) = F (l₀ ++ l') := by
    induction p with
    | nil => intro l₀; rfl
    | @cons x l₁ l₂ _ ih =>
      intro l₀
      have e₁ : l₀ ++ x :: l₁ = (l₀ ++ [x]) ++ l₁ := by simp
      have e₂ : l₀ ++ x :: l₂ = (l₀ ++ [x]) ++ l₂ := by simp
      rw [e₁, e₂]
      exact ih _
    | swap x y k =>
      intro l₀
      simp only [F]
      by_cases hk : (l₀ ++ y :: x :: k).length = n
      · have hk' : (l₀ ++ x :: y :: k).length = n := by simpa using hk
        rw [dif_pos hk, dif_pos hk']
        have hlt : l₀.length + 1 < n := by simp at hk; omega
        rw [← hM _ (Equiv.swap (⟨l₀.length, by omega⟩ : Fin n) ⟨l₀.length + 1, hlt⟩)]
        congr 1
        funext i
        obtain ⟨i, hi⟩ := i
        simp only [Function.comp_apply, Equiv.swap_apply_def, Fin.mk.injEq]
        split_ifs with h1 h2
        · subst h1
          simp [List.getElem_append]
        · subst h2
          simp [List.getElem_append]
        · rcases lt_or_ge i l₀.length with h3 | h3
          · simp [List.getElem_append, h3]
          · obtain ⟨j, rfl⟩ : ∃ j, i = l₀.length + (j + 2) := ⟨i - (l₀.length + 2), by omega⟩
            simp [List.getElem_append]
      · have hk' : ¬ (l₀ ++ x :: y :: k).length = n := by simpa using hk
        rw [dif_neg hk, dif_neg hk']
    | trans _ _ ih₁ ih₂ => intro l₀; exact (ih₁ l₀).trans (ih₂ l₀)
  intro h h'
  have e := key []
  simp only [F, List.nil_append, dif_pos h, dif_pos h'] at e
  exact e
end ReciprocityTheory.ChartRestriction.G.PullbackSections
