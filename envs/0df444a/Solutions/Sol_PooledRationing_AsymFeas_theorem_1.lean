-- Prove2me | solution 1 for PooledRationing.AsymFeas.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T08:49:27.440976+00:00
-- url     : https://prove2.me/submissions/b69f0776-c798-432c-98d5-dc5e488b95c9

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting
import Theorems.Thm_PooledRationing_AsymFeas_minimax_display
import Theorems.Thm_PooledRationing_AsymFeas_claim_22

set_option autoImplicit false
open PooledRationing.AsymFeas MeasureTheory

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Jiang, Wang and Zhang, SSRN 3385089, Theorem 1.
theorem solution {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (hc : 0 ≤ c) (hβ : ∀ j, β j ∈ Set.Ioo 0 1)
    (hF2 : MemLp id 2 F) (hDnn : ∀ᵐ D ∂F, (0 : Fin n → ℝ) ≤ D)
    (hA1_mono : ∀ j d, Monotone (fun s => R j s d))
    (hA1_usc : ∀ j d, UpperSemicontinuous (fun s => R j s d))
    (hA1_compact : ∀ D, IsCompact (P c D))
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (h : (Fin n → ℝ) → ℝ) (hh : Integrable h F)
    (hRenv : ∀ D, ∀ x ∈ P c D, ∀ j, R j (x.1 j) (D j) ≤ h D)
    (hsel : ∀ w : Fin n → ℝ, 0 ≤ w → ∃ φ : DetPolicy P c,
      ∀ D, IsMaxOn (weightedService R w D) (P c D) (φ.toFun D)) :
    IsAsymFeasible F R β P c ↔ ∀ w : Fin n → ℝ, 0 ≤ w →
      ∑ j, w j*β j ≤ ∫ D, maxWeightedValue P c R w D ∂F := by
  classical
  constructor
  · intro hfeas w hw
    have hrc (φ : DetPolicy P c) (j : Fin n) :
        Integrable (fun D => R j ((φ.toFun D).1 j) (D j)) F := by
      have hm : Measurable (fun D => R j ((φ.toFun D).1 j) (D j)) :=
        (hRmeas j).comp (((measurable_pi_apply j).comp φ.measurable'.fst).prodMk (measurable_pi_apply j))
      exact hh.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun D => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hRnonneg _ _ _)]
        exact hRenv D (φ.toFun D) (φ.mem' D) j))
    have hweighted (φ : DetPolicy P c) : Integrable (fun D => weightedService R w D (φ.toFun D)) F :=
      integrable_finsetSum _ (fun j _ => (hrc φ j).const_mul (w j))
    have hint (φ : DetPolicy P c) : (∫ D, weightedService R w D (φ.toFun D) ∂F) =
        ∑ j, w j*detService F R φ j := by
      unfold weightedService
      rw [integral_finsetSum _ (fun j _ => (hrc φ j).const_mul (w j))]
      simp only [integral_const_mul,detService]
    obtain ⟨φmax,hφmax⟩ := hsel w hw
    have hmax (D) : maxWeightedValue P c R w D = weightedService R w D (φmax.toFun D) := by
      unfold maxWeightedValue
      apply IsGreatest.csSup_eq
      refine ⟨⟨φmax.toFun D,φmax.mem' D,rfl⟩,?_⟩
      rintro _ ⟨x,hx,rfl⟩
      exact hφmax D hx
    have hdet (φ : DetPolicy P c) : (∑ j, w j*detService F R φ j) ≤
        ∫ D, maxWeightedValue P c R w D ∂F := by
      simp_rw [hmax]
      rw [←hint φ]
      exact integral_mono (hweighted φ) (hweighted φmax) (fun D => hφmax D (φ.mem' D))
    have hmix (lam : RandPolicy P c) : (∑ j, w j*service F R lam j) ≤
        ∫ D, maxWeightedValue P c R w D ∂F := by
      calc
        _ = ∑ i, lam.wt i * (∑ j, w j*detService F R (lam.pol i) j) := by
          simp only [service,Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ ≤ ∑ i, lam.wt i * (∫ D, maxWeightedValue P c R w D ∂F) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hdet (lam.pol i)) (lam.wt_nonneg i))
        _ = _ := by rw [←Finset.sum_mul,lam.wt_sum,one_mul]
    have hW : 0 ≤ ∑ j, w j := Finset.sum_nonneg (fun j _ => hw j)
    apply le_of_forall_pos_le_add
    intro δ hδ
    let ε := δ/((∑ j, w j)+1)
    have hε : 0 < ε := div_pos hδ (by linarith)
    obtain ⟨lam,hlam⟩ := hfeas ε hε
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun j _ => mul_le_mul_of_nonneg_left (hlam j) (hw j))
    have hprod : ε*(∑ j, w j) ≤ δ := by
      have hEq : ε*((∑ j, w j)+1)=δ := div_mul_cancel₀ δ (by linarith)
      nlinarith only [hEq,hε.le]
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul] at hs
    have hm := hmix lam
    linarith only [hs,hm,hprod]
  · intro h18 ε hε
    obtain ⟨lam,hlam⟩ := minimax_display F P c R β hc hβ hF2 hDnn hA1_mono hA1_usc
      hA1_compact hRnonneg hRmeas h hh hRenv hsel h18 ε hε
    exact ⟨lam,claim_22 F P c R β ε hε lam hlam⟩

#print axioms solution
