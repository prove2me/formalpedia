-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_kIrrHW_int__ae85b70f4a59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:15.967243+00:00
-- url     : https://prove2.me/submissions/1f6e600c-7136-4c78-a71a-ac85def3eafb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_CompactRelationsApplyComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_compactRelations_apply_comm

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) {Λ : Fin n → ℝ} {V : Submodule ℂ M}
    (hV : IsKIrrHW ε F Λ V) : ∀ a b, a < b → ε a = ε b → ∃ m : ℕ, Λ a - Λ b = m := by
  intro a b hab hε
  obtain ⟨hfin, hst, -, w, hwV, hw0, hwt, hwh⟩ := hV
  have hne : a ≠ b := ne_of_lt hab
  have hba : b ≠ a := fun h => hne h.symm
  obtain ⟨v, hv0, hvs⟩ : ∃ v : ℕ → M, v 0 = w ∧ ∀ k, v (k + 1) = F b a (v k) :=
    ⟨fun k => (F b a ^ k) w, by simp, fun k => by simp only [pow_succ', Module.End.mul_apply]⟩
  have hmem : ∀ k, v k ∈ V := by
    intro k
    induction k with
    | zero => rw [hv0]; exact hwV
    | succ k ih => rw [hvs]; exact hst b a hε.symm _ ih

  have hA : ∀ k : ℕ, F a a (v k) = (((Λ a - (k : ℝ)) : ℝ) : ℂ) • v k := by
    intro k
    induction k with
    | zero => rw [hv0, hwt a]; simp
    | succ k ih =>
      have c := compactRelations_apply_comm hF (a := a) (b := a) (c := b) (d := a) rfl hε.symm (v k)
      simp only [hne, if_false, if_true, add_zero] at c
      rw [hvs, c, ih, map_smul]
      push_cast
      module

  have hB : ∀ k : ℕ, F b b (v k) = (((Λ b + (k : ℝ)) : ℝ) : ℂ) • v k := by
    intro k
    induction k with
    | zero => rw [hv0, hwt b]; simp
    | succ k ih =>
      have c := compactRelations_apply_comm hF (a := b) (b := b) (c := b) (d := a) rfl hε.symm (v k)
      simp only [hne, if_false, if_true, sub_zero] at c
      rw [hvs, c, ih, map_smul]
      push_cast
      module

  have hE : ∀ k : ℕ, F a b (v (k + 1)) = ((((k : ℝ) + 1) * (Λ a - Λ b - (k : ℝ)) : ℝ) : ℂ) • v k := by
    intro k
    induction k with
    | zero =>
      have c := compactRelations_apply_comm hF (a := a) (b := b) (c := b) (d := a) hε hε.symm w
      simp only [if_true] at c
      rw [hvs 0, hv0, c, hwh a b hab hε, map_zero, hwt a, hwt b]
      push_cast
      module
    | succ k ih =>
      have c := compactRelations_apply_comm hF (a := a) (b := b) (c := b) (d := a) hε hε.symm (v (k + 1))
      simp only [if_true] at c
      rw [hvs (k + 1), c, ih, map_smul, ← hvs k, hA (k + 1), hB (k + 1)]
      push_cast
      module

  obtain ⟨m, hm0, hm1⟩ : ∃ m, v m ≠ 0 ∧ v (m + 1) = 0 := by
    by_contra hcon
    have hall : ∀ k, v k ≠ 0 := by
      intro k
      induction k with
      | zero => rw [hv0]; exact hw0
      | succ k ih => exact fun h => hcon ⟨k, ih, h⟩
    have hinj : Function.Injective (fun k : ℕ => (((Λ a - (k : ℝ)) : ℝ) : ℂ)) := by
      intro k j h
      have h1 : Λ a - (k : ℝ) = Λ a - (j : ℝ) := Complex.ofReal_injective h
      have h2 : (k : ℝ) = (j : ℝ) := by linarith
      exact_mod_cast h2
    have hli : LinearIndependent ℂ v :=
      Module.End.eigenvectors_linearIndependent' (F a a) _ hinj v
        (fun k => Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (hA k), hall k⟩)
    have hli' : LinearIndependent ℂ (fun k => (⟨v k, hmem k⟩ : V)) :=
      LinearIndependent.of_comp V.subtype hli
    have : Module.Finite ℂ V := hfin
    exact Module.Finite.not_linearIndependent_of_infinite _ hli'
  have h := hE m
  rw [hm1, map_zero] at h
  have hc : (((((m : ℝ) + 1) * (Λ a - Λ b - (m : ℝ))) : ℝ) : ℂ) = 0 :=
    (smul_eq_zero.mp h.symm).resolve_right hm0
  have hr : ((m : ℝ) + 1) * (Λ a - Λ b - (m : ℝ)) = 0 := Complex.ofReal_eq_zero.mp hc
  have hpos : (m : ℝ) + 1 ≠ 0 := by positivity
  have hz := (mul_eq_zero.mp hr).resolve_left hpos
  exact ⟨m, by linarith⟩
end ReciprocityTheory.ChartRestriction.DS.HW
