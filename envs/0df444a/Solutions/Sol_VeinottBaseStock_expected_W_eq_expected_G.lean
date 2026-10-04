-- Prove2me | solution 1 for VeinottBaseStock.expected_W_eq_expected_G
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:22:13.929986+00:00
-- url     : https://prove2.me/submissions/ca8627b4-ebca-40cd-8da9-86c771193701

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open VeinottBaseStock in
lemma fa014e59_W_measurable {n m : ℕ} (M : Model n m) (hM : M.Standing) (k : ℕ) :
    Measurable (Function.uncurry (M.W k)) := by
  have hg := hM.g_measurable k
  have hs := hM.s_measurable k
  unfold Function.uncurry Model.W
  have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => M.c k ⬝ᵥ p.1) := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))
  have h3 : Measurable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => M.c (k+1) ⬝ᵥ M.s k p.1 p.2) := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul ((measurable_pi_apply i).comp hs))
  exact (h1.add hg).sub (measurable_const.mul h3)

open VeinottBaseStock MeasureTheory ProbabilityTheory in
theorem solution {n m : ℕ} (M : Model n m) (x₁ : Fin n → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → Fin m → ℝ) (hM : M.Standing) (hD : M.IsDemandProcess P D)
    (Ŷ : Pol n m) (hŶ : M.Feasible x₁ Ŷ) (k : ℕ)
    (hint : Integrable (fun ω => M.W k (M.orderSeq Ŷ (fun j => D j ω) k) (D k ω)) P) :
    ∫ ω, M.W k (M.orderSeq Ŷ (fun j => D j ω) k) (D k ω) ∂P =
      ∫ ω, M.G k (M.orderSeq Ŷ (fun j => D j ω) k) ∂P := by
  set S : Finset ℕ := Finset.range k with hS
  set T : Finset ℕ := {k} with hT
  have hST : Disjoint S T := by simp [S, T]
  have hind := hD.indep.indepFun_finset S T hST hD.measurable
  let φ : ((i : S) → Fin m → ℝ) → (Fin n → ℝ) :=
    fun f => Ŷ k (fun j : Fin k => f ⟨j, by simp [S]⟩)
  let ψ : ((i : T) → Fin m → ℝ) → (Fin m → ℝ) := fun f => f ⟨k, by simp [T]⟩
  have hφ : Measurable φ := (hŶ.measurable k).comp (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
  have hψ : Measurable ψ := measurable_pi_apply _
  have hYZ := hind.comp hφ hψ
  set Y : Ω → Fin n → ℝ := fun ω => M.orderSeq Ŷ (fun j => D j ω) k with hYdef
  have hYeq : (φ ∘ fun a (i : S) => D i a) = Y := by
    funext ω; rfl
  have hZeq : (ψ ∘ fun a (i : T) => D i a) = D k := by
    funext ω; rfl
  rw [hYeq, hZeq] at hYZ
  have hYm : Measurable Y := by
    rw [← hYeq]; exact hφ.comp (measurable_pi_lambda _ (fun i => hD.measurable i))
  have hZm : Measurable (D k) := hD.measurable k
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hZm.aemeasurable).1 hYZ
  rw [hD.law k] at hmap
  have : IsProbabilityMeasure (M.Φ k) := hM.isProbabilityMeasure k
  have hWm := fa014e59_W_measurable M hM k
  have hpm : Measurable (fun ω => (Y ω, D k ω)) := hYm.prodMk hZm
  have hL : ∫ ω, M.W k (Y ω) (D k ω) ∂P =
      ∫ p, Function.uncurry (M.W k) p ∂((P.map Y).prod (M.Φ k)) := by
    rw [← hmap, integral_map hpm.aemeasurable hWm.aestronglyMeasurable]
    rfl
  have hint' : Integrable (Function.uncurry (M.W k)) ((P.map Y).prod (M.Φ k)) := by
    rw [← hmap, integrable_map_measure hWm.aestronglyMeasurable hpm.aemeasurable]
    exact hint
  rw [hL, integral_prod _ hint']
  have hG : (fun y => ∫ t, Function.uncurry (M.W k) (y, t) ∂(M.Φ k)) = M.G k := by
    funext y
    unfold Model.G
    rw [Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 (hM.Φ_compl_Dset k))]
    rfl
  have hGi := hint'.integral_prod_left
  rw [hG] at hGi ⊢
  rw [integral_map hYm.aemeasurable hGi.aestronglyMeasurable]
