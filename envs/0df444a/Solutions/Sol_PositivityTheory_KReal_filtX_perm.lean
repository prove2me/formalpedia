-- Prove2me | solution 1 for PositivityTheory.KReal.filtX_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:28:12.177735+00:00
-- url     : https://prove2.me/submissions/2da0b928-e5b8-4e8b-9b45-ccf6ad2a7e40

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasB
import Theorems.Thm_PositivityTheory_KReal_wordX_cons
import Theorems.Thm_PositivityTheory_KReal_filtX_X
import Theorems.Thm_PositivityTheory_KReal_filtX_e

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
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h2 : ∀ i j, X i * X j - X j * X i ∈ Submodule.span ℂ (Set.range e)) (ρ : K → Module.End ℂ V)
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v)) {l l' : List I} (h : l.Perm l') (n : ℕ)
    (hn : l.length ≤ n + 1) (v : V) : wordX X l (ι v) - wordX X l' (ι v) ∈ filtX X ι n := by
  induction h generalizing n with
  | nil => simp
  | @cons a l l' hp ih =>
    rw [wordX_cons, wordX_cons, ← map_sub]
    cases n with
    | zero =>
      have h0 : l = [] := List.length_eq_zero_iff.1 (by simpa using hn)
      subst h0
      have h0' : l' = [] := hp.nil_eq.symm
      subst h0'
      simp
    | succ n => exact filtX_X X ι n a _ (ih n (by simpa using hn))
  | swap a b l =>
    have hl : l.length ≤ n := by simp only [List.length_cons] at hn; omega
    have hm : wordX X l (ι v) ∈ filtX X ι n := Submodule.subset_span ⟨l, v, hl, rfl⟩
    have hall : ∀ E ∈ Submodule.span ℂ (Set.range e), E (wordX X l (ι v)) ∈ filtX X ι n := by
      intro E hE
      induction hE using Submodule.span_induction with
      | mem E hE =>
        obtain ⟨k, rfl⟩ := hE
        exact filtX_e e X c h1 ρ ι hι n k _ hm
      | zero => simp
      | add E F _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
      | smul a E _ h1 => exact Submodule.smul_mem _ a h1
    simp only [wordX_cons]
    exact hall _ (h2 b a)
  | trans p1 p2 ih1 ih2 =>
    have := Submodule.add_mem _ (ih1 n hn) (ih2 n (p1.length_eq ▸ hn))
    rwa [sub_add_sub_cancel] at this
end PositivityTheory.KReal
