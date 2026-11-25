-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension.exists_append_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:01:17.920021+00:00
-- url     : https://prove2.me/submissions/2d2becf4-8f65-48d6-ac51-b93f107aa8b6

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_HadZStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension
open Matrix
private theorem exists_linearIndependent_append_of_codim {r : ℕ} (w : Fin r → (Fin r → ℚ))
    (hw : LinearIndependent ℚ w) :
    ∀ d a (u0 : Fin a → (Fin r → ℚ)), LinearIndependent ℚ u0 → r - a = d → a ≤ r →
      ∃ m, ∃ f : Fin m → Fin r, a + m = r ∧ LinearIndependent ℚ (Fin.append u0 (w ∘ f)) := by
  intro d
  induction d with
  | zero =>
    intro a u0 hu0 hd har
    refine ⟨0, Fin.elim0, by omega, ?_⟩
    rw [Fin.append_right_nil u0 _ rfl]
    exact hu0.comp _ (Fin.cast_injective _)
  | succ d ih =>
    intro a u0 hu0 hd har
    obtain ⟨j, hj⟩ : ∃ j, w j ∉ Submodule.span ℚ (Set.range u0) := by
      by_contra hcon
      push_neg at hcon
      haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
      have htop : Submodule.span ℚ (Set.range w) = ⊤ :=
        hw.span_eq_top_of_card_eq_finrank (by simp)
      have hle : Submodule.span ℚ (Set.range w) ≤ Submodule.span ℚ (Set.range u0) :=
        Submodule.span_le.mpr (Set.range_subset_iff.mpr hcon)
      rw [htop, top_le_iff] at hle
      have h1 : Module.finrank ℚ (Submodule.span ℚ (Set.range u0)) ≤ Fintype.card (Fin a) :=
        finrank_range_le_card (R := ℚ) u0
      rw [hle, finrank_top] at h1
      simp at h1
      omega
    have hu1 : LinearIndependent ℚ (Fin.snoc u0 (w j) : Fin (a + 1) → (Fin r → ℚ)) :=
      linearIndependent_fin_snoc.mpr ⟨hu0, hj⟩
    obtain ⟨m, f, hm, hli⟩ := ih (a + 1) (Fin.snoc u0 (w j)) hu1 (by omega) (by omega)
    refine ⟨m + 1, Fin.cons j f, by omega, ?_⟩
    rw [Fin.comp_cons, Fin.append_right_cons]
    exact hli.comp _ (Fin.cast_injective _)
end ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension
open Matrix
namespace ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension
theorem _root_.solution {a r : ℕ} (u0 : Fin a → (Fin r → ℚ)) (hu0 : LinearIndependent ℚ u0)
    (w : Fin r → (Fin r → ℚ)) (hw : LinearIndependent ℚ w) :
    ∃ m, ∃ f : Fin m → Fin r, a + m = r ∧ LinearIndependent ℚ (Fin.append u0 (w ∘ f)) := by
  have har : a ≤ r := by
    have h := hu0.fintype_card_le_finrank
    simpa using h
  exact exists_linearIndependent_append_of_codim w hw _ a u0 hu0 rfl har
end ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension
