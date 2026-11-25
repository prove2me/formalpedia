-- Prove2me | solution 1 for ReciprocityTheory.AnForm.exists_perm_coord_complement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:44.437902+00:00
-- url     : https://prove2.me/submissions/ce2aaf36-ec61-482b-a908-5b3e9cfc5a51

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Function
namespace ReciprocityTheory.AnForm
theorem _root_.solution {e c : ℕ} (A : (Fin (e + c) → ℂ) →ₗ[ℂ] (Fin c → ℂ))
    (hA : Surjective A) :
    ∃ σ : Equiv.Perm (Fin (e + c)),
      ∀ v, (∀ i : Fin e, v (σ (Fin.castAdd c i)) = 0) → A v = 0 → v = 0 := by
  classical
  set col : Fin (e + c) → (Fin c → ℂ) := fun j => A (Pi.single j 1)
  have hexp : ∀ v : Fin (e + c) → ℂ, A v = ∑ j, v j • col j := by
    intro v
    have : v = ∑ j, v j • (Pi.single j 1 : Fin (e + c) → ℂ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp [col, map_sum, map_smul]
  have hspan : Submodule.span ℂ (Set.range col) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨v, rfl⟩ := hA y
    rw [hexp]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℂ col
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hsp' : Submodule.span ℂ (Set.range (col ∘ a)) = ⊤ := hsp.trans hspan
  let b : Module.Basis κ ℂ (Fin c → ℂ) := Module.Basis.mk hli (by rw [hsp'])
  have hκ : Fintype.card κ = c := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  let q : Fin (e + c) → Prop := fun j => j ∈ Set.range a
  let eT : Fin c ≃ {j // q j} :=
    (Fintype.equivFinOfCardEq hκ).symm.trans (Equiv.ofInjective a ha)
  have hcard : Fintype.card {j // ¬ q j} = e := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, ← Fintype.card_congr eT, Fintype.card_fin]
    omega
  let eC : Fin e ≃ {j // ¬ q j} := (Fintype.equivFinOfCardEq hcard).symm
  let σ : Equiv.Perm (Fin (e + c)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr eC eT).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl q)))
  refine ⟨σ, fun v hv hAv => ?_⟩
  have hσ : ∀ i, σ (Fin.castAdd c i) = (eC i).1 := by
    intro i; simp [σ]
  have hoff : ∀ j, ¬ q j → v j = 0 := by
    intro j hj
    have := hv (eC.symm ⟨j, hj⟩)
    rwa [hσ, Equiv.apply_symm_apply] at this
  have hsum : ∑ k, v (a k) • (col ∘ a) k = 0 := by
    rw [← hAv, hexp]
    show ∑ k, v (a k) • col (a k) = _
    rw [← Finset.sum_image (s := Finset.univ) (g := a) (f := fun j => v j • col j)
      (fun x _ y _ h => ha h)]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have : ¬ q j := by
      rintro ⟨k, rfl⟩; exact hj (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    simp [hoff j this]
  have hzero := (Fintype.linearIndependent_iff.mp hli) (fun k => v (a k)) hsum
  funext j
  by_cases hj : q j
  · obtain ⟨k, rfl⟩ := hj; simpa using hzero k
  · simpa using hoff j hj
end ReciprocityTheory.AnForm
