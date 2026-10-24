-- Prove2me | solution 1 for PooledRationing.MaxWeighted.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:19:38.535688+00:00
-- url     : https://prove2.me/submissions/26251e27-2f90-4e45-b9f8-5da45f606db2

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting

open MeasureTheory

namespace MWWeakDualityAux

open PooledRationing.AsymFeas

theorem integrable_cost {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ) (K : ℝ) (hf : ∀ᵐ D ∂F, ∀ x ∈ P c D, |f x.2| ≤ K)
    (ψ : DetPolicy P c) : Integrable (fun D => f (ψ.toFun D).2) F := by
  have hfc : Continuous f := LinearMap.continuous_of_finiteDimensional f
  have hm : Measurable (fun D => f (ψ.toFun D).2) :=
    hfc.measurable.comp (measurable_snd.comp ψ.measurable')
  refine Integrable.of_bound (C := K) hm.aestronglyMeasurable ?_
  filter_upwards [hf] with D hD
  simpa [Real.norm_eq_abs] using hD _ (ψ.mem' D)

theorem integrable_serv {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}
    (R : Fin n → ℝ → ℝ → ℝ) (hDnn : ∀ᵐ D ∂F, 0 ≤ D)
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (C : ℝ) (hA3R : ∀ j s d, s ≤ d → R j s d ≤ C)
    (hPs : ∀ D, 0 ≤ D → ∀ x ∈ P c D, ∀ j, x.1 j ≤ D j)
    (ψ : DetPolicy P c) (j : Fin n) :
    Integrable (fun D => R j ((ψ.toFun D).1 j) (D j)) F := by
  have hm : Measurable (fun D => R j ((ψ.toFun D).1 j) (D j)) := by
    have h1 : Measurable (fun D : Fin n → ℝ => ((ψ.toFun D).1 j, D j)) :=
      ((measurable_pi_apply j).comp (measurable_fst.comp ψ.measurable')).prodMk
        (measurable_pi_apply j)
    exact (hRmeas j).comp h1
  refine Integrable.of_bound (C := C) hm.aestronglyMeasurable ?_
  filter_upwards [hDnn] with D hD
  rw [Real.norm_eq_abs, abs_of_nonneg (hRnonneg _ _ _)]
  exact hA3R _ _ _ (hPs D hD _ (ψ.mem' D) j)

end MWWeakDualityAux

open MWWeakDualityAux PooledRationing.AsymFeas

theorem solution
    {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (PooledRationing.AsymFeas.Sol n m)) (c : Fin m → ℝ)
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ) (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (hc : 0 ≤ c) (hβ : ∀ j, β j ∈ Set.Ioo 0 1)
    (hF2 : MemLp id 2 F) (hDnn : ∀ᵐ D ∂F, 0 ≤ D)
    (hRmono : ∀ j d, Monotone (fun s => R j s d))
    (hRusc : ∀ j d, UpperSemicontinuous (fun s => R j s d))
    (hPcpt : ∀ D, IsCompact (P c D))
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (B : ℝ) (hA3supp : ∀ᵐ D ∂F, ∀ j, |D j| ≤ B)
    (C : ℝ) (hA3R : ∀ j s d, s ≤ d → R j s d ≤ C)
    (hPs : ∀ D, 0 ≤ D → ∀ x ∈ P c D, ∀ j, x.1 j ≤ D j)
    (K : ℝ) (hf : ∀ᵐ D ∂F, ∀ x ∈ P c D, |f x.2| ≤ K)
    (hfeas : PooledRationing.AsymFeas.IsFeasible F R β P c)
    (w : Fin n → ℝ) (hw : 0 ≤ w) (φw : PooledRationing.AsymFeas.DetPolicy P c)
    (hφw : ∀ D, IsMinOn (PooledRationing.AsymFeas.mwsObjective f R w D) (P c D) (φw.toFun D)) :
    ∑ j, w j * β j + PooledRationing.AsymFeas.detCost F f φw - ∑ j, w j * PooledRationing.AsymFeas.detService F R φw j
      ≤ PooledRationing.AsymFeas.obj11 F f R β P c := by
  classical
  -- the Lagrangian value of a deterministic policy
  have hlag : ∀ ψ : DetPolicy P c,
      detCost F f ψ - ∑ j, w j * detService F R ψ j =
        ∫ D, mwsObjective f R w D (ψ.toFun D) ∂F := by
    intro ψ
    simp only [detCost, detService, mwsObjective]
    rw [integral_sub (integrable_cost F f K hf ψ)
      (integrable_finsetSum _ fun j _ =>
        (integrable_serv F R hDnn hRnonneg hRmeas C hA3R hPs ψ j).const_mul (w j))]
    rw [integral_finsetSum _ fun j _ =>
        (integrable_serv F R hDnn hRnonneg hRmeas C hA3R hPs ψ j).const_mul (w j)]
    simp_rw [integral_const_mul]
  have hint : ∀ ψ : DetPolicy P c, Integrable (fun D => mwsObjective f R w D (ψ.toFun D)) F := by
    intro ψ
    simp only [mwsObjective]
    exact (integrable_cost F f K hf ψ).sub (integrable_finsetSum _ fun j _ =>
        (integrable_serv F R hDnn hRnonneg hRmeas C hA3R hPs ψ j).const_mul (w j))
  have hcmp : ∀ ψ : DetPolicy P c,
      detCost F f φw - ∑ j, w j * detService F R φw j ≤
        detCost F f ψ - ∑ j, w j * detService F R ψ j := by
    intro ψ
    rw [hlag, hlag]
    exact integral_mono (hint φw) (hint ψ) fun D => hφw D (ψ.mem' D)
  set A := detCost F f φw - ∑ j, w j * detService F R φw j with hA
  obtain ⟨lam0, hlam0⟩ := hfeas
  have hbound : ∀ lam : RandPolicy P c, (∀ j, β j ≤ service F R lam j) →
      ∑ j, w j * β j + A ≤ cost F f lam := by
    intro lam hlam
    have h1 : ∀ i, lam.wt i * (A + ∑ j, w j * detService F R (lam.pol i) j) ≤
        lam.wt i * detCost F f (lam.pol i) := by
      intro i
      apply mul_le_mul_of_nonneg_left _ (lam.wt_nonneg i)
      have := hcmp (lam.pol i)
      linarith
    have h2 : ∑ i, lam.wt i * (A + ∑ j, w j * detService F R (lam.pol i) j) =
        A + ∑ j, w j * service F R lam j := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, lam.wt_sum, one_mul,
        service, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    have h3 : ∑ j, w j * β j ≤ ∑ j, w j * service F R lam j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hlam j) (hw j)
    have h4 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
    rw [h2] at h4
    simp only [cost]
    linarith
  have : ∑ j, w j * β j + A ≤ obj11 F f R β P c := by
    refine le_csInf ⟨cost F f lam0, lam0, hlam0, rfl⟩ ?_
    rintro v ⟨lam, hlam, rfl⟩
    exact hbound lam hlam
  linarith
