-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_parametrisation_e159ba74b0c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:41.639654+00:00
-- url     : https://prove2.me/submissions/a83d1d97-b7f3-48c0-adef-7d14dd7f42a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimeQuasiFiniteSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_differentiableOn_polyEval_2217afe5cc1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_card_roots_toFinset_6020b0b710aa

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
theorem _root_.solution (hSR : ComplexSets.SimpleRootBranch.Statement)
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (c : Fin n → ℂ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Δ : MvPolynomial (Fin d) ℂ)
    (S : Fin n → Polynomial (MvPolynomial (Fin d) ℂ))
    (hP : ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
      (m.map (eval y)).natDegree = m.natDegree ∧ (m.map (eval y)).Separable ∧
      (∀ x ∈ ComplexSets.fibre Q A y, (m.map (eval y)).IsRoot (∑ j, c j * x j) ∧
        ∀ j, eval y Δ * x j = ((S j).map (eval y)).eval (∑ k, c k * x k)) ∧
      ∀ τ : ℂ, (m.map (eval y)).IsRoot τ → ∃ x ∈ ComplexSets.fibre Q A y, ∑ j, c j * x j = τ)
    (y : Fin d → ℂ) (hy : eval y Δ ≠ 0) :
    ∃ (U : Set (Fin d → ℂ)) (N : ℕ) (s : Fin N → (Fin d → ℂ) → Fin n → ℂ),
      IsOpen U ∧ y ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
      ∀ y' ∈ U, (∀ j, s j y' ∈ ComplexSets.fibre Q A y') ∧
        Function.Injective (fun j => s j y') ∧
        ComplexSets.fibre Q A y' ⊆ Set.range (fun j => s j y') := by
  have hcnt : ∀ w : Fin d → ℂ, eval w Δ ≠ 0 → (m.map (eval w)).roots.toFinset.card = m.natDegree := by
    intro w hw
    obtain ⟨hd, hs, -, -⟩ := hP w hw
    rw [card_roots_toFinset hs, hd]
  obtain ⟨-, hsep, -, -⟩ := hP y hy
  obtain ⟨R, hR⟩ : ∃ R : Finset ℂ, R = (m.map (eval y)).roots.toFinset := ⟨_, rfl⟩
  let τ : Fin R.card → ℂ := fun j => (R.equivFin.symm j : ℂ)
  have hRroot : ∀ z ∈ R, (m.map (eval y)).IsRoot z := by
    intro z hz
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots'] at hz
    exact hz.2
  have hτroot : ∀ j, (m.map (eval y)).IsRoot (τ j) := fun j => hRroot _ (R.equivFin.symm j).2
  have hτinj : Function.Injective τ := fun i j h => R.equivFin.symm.injective (Subtype.ext h)
  have hder : ∀ j, (m.map (eval y)).derivative.eval (τ j) ≠ 0 := by
    intro j
    have h := hsep.aeval_derivative_ne_zero (x := τ j) (by
      rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]; exact hτroot j)
    rwa [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] at h
  choose U B ψ hU hyU hBo hτB hψd hψy hψ using fun j => hSR d m y (τ j) (hτroot j) (hder j)
  let W : Fin R.card → Fin R.card → Set (Fin d → ℂ) :=
    fun j k => U j ∩ U k ∩ {w | j ≠ k → ψ j w ≠ ψ k w}
  have hWo : ∀ j k, IsOpen (W j k) := by
    intro j k
    by_cases hjk : j = k
    · have : W j k = U j ∩ U k := by
        ext w
        simp [W, hjk]
      rw [this]
      exact (hU j).inter (hU k)
    · have : W j k = (U j ∩ U k) ∩ (fun w => ψ j w - ψ k w) ⁻¹' {0}ᶜ := by
        ext w
        simp [W, hjk, sub_eq_zero]
      rw [this]
      exact ContinuousOn.isOpen_inter_preimage
        (((hψd j).mono Set.inter_subset_left).sub ((hψd k).mono Set.inter_subset_right)).continuousOn
        ((hU j).inter (hU k)) isOpen_compl_singleton
  let V : Set (Fin d → ℂ) := {w | eval w Δ ≠ 0} ∩ ⋂ j, ⋂ k, W j k
  have hVo : IsOpen V := (isOpen_ne_fun (MvPolynomial.continuous_eval Δ) continuous_const).inter
    (isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => hWo j k)
  have hyV : y ∈ V := by
    refine ⟨hy, Set.mem_iInter.2 fun j => Set.mem_iInter.2 fun k => ⟨⟨hyU j, hyU k⟩, fun hjk => ?_⟩⟩
    rw [hψy j, hψy k]
    exact fun h => hjk (hτinj h)
  have hVU : ∀ w ∈ V, ∀ j, w ∈ U j := fun w hw j => (Set.mem_iInter.1 (Set.mem_iInter.1 hw.2 j) j).1.1
  have hVd : ∀ w ∈ V, ∀ j k, j ≠ k → ψ j w ≠ ψ k w :=
    fun w hw j k => (Set.mem_iInter.1 (Set.mem_iInter.1 hw.2 j) k).2
  let s : Fin R.card → (Fin d → ℂ) → Fin n → ℂ :=
    fun j w i => ((S i).map (eval w)).eval (ψ j w) * (eval w Δ)⁻¹
  refine ⟨V, R.card, s, hVo, hyV, fun j => ?_, fun y' hy' => ?_⟩
  · rw [differentiableOn_pi]
    intro i
    have hΔd : DifferentiableOn ℂ (fun w : Fin d → ℂ => eval w Δ) V :=
      (AnalyticOnNhd.eval_mvPolynomial Δ).differentiableOn.mono (Set.subset_univ _)
    exact (differentiableOn_polyEval (S i) ((hψd j).mono fun w hw => hVU w hw j)).mul
      (hΔd.inv fun w (hw : w ∈ V) => hw.1)
  obtain ⟨-, hsep', hfib', hroot'⟩ := hP y' hy'.1
  have hψroot : ∀ j, (m.map (eval y')).IsRoot (ψ j y') := fun j =>
    ((hψ j y' (hVU y' hy' j)).2 _ (hψ j y' (hVU y' hy' j)).1).2 rfl
  have hrec : ∀ x ∈ ComplexSets.fibre Q A y', ∀ j, ∑ k, c k * x k = ψ j y' → s j y' = x := by
    intro x hx j hj
    funext i
    simp only [s]
    rw [← hj, ← (hfib' x hx).2 i, mul_comm, inv_mul_cancel_left₀ hy'.1]
  have hmem : ∀ j, ∃ x ∈ ComplexSets.fibre Q A y', ∑ k, c k * x k = ψ j y' ∧ s j y' = x := by
    intro j
    obtain ⟨x, hx, hxl⟩ := hroot' _ (hψroot j)
    exact ⟨x, hx, hxl, hrec x hx j hxl⟩
  refine ⟨fun j => ?_, fun j k hjk => ?_, fun x hx => ?_⟩
  · obtain ⟨x, hx, -, hsx⟩ := hmem j
    rw [hsx]
    exact hx
  · obtain ⟨x, hx, hxl, hsx⟩ := hmem j
    obtain ⟨x', hx', hxl', hsx'⟩ := hmem k
    by_contra hne
    apply hVd y' hy' j k hne
    have hxx : x = x' := by
      rw [← hsx, ← hsx']
      exact hjk
    rw [← hxl, ← hxl', hxx]
  · have hinjψ : Function.Injective (fun j => ψ j y') := fun j k h =>
      by_contra fun hne => hVd y' hy' j k hne h
    have hsub : Finset.univ.image (fun j => ψ j y') ⊆ (m.map (eval y')).roots.toFinset := by
      intro z hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨hsep'.ne_zero, hψroot j⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_image_of_injective _ hinjψ, Finset.card_univ, Fintype.card_fin, hcnt y' hy'.1,
        hR, hcnt y hy])
    have hl : ∑ k, c k * x k ∈ (m.map (eval y')).roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨hsep'.ne_zero, (hfib' x hx).1⟩
    rw [← heq] at hl
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hl
    exact ⟨j, hrec x hx j hj.symm⟩
end GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
