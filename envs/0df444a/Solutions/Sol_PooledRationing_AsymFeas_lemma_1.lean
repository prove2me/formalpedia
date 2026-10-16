-- Prove2me | solution 1 for PooledRationing.AsymFeas.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T07:59:06.774662+00:00
-- url     : https://prove2.me/submissions/a54dd5b0-0b8f-4d82-96eb-fb8eda940347

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting

set_option autoImplicit false
open PooledRationing.AsymFeas MeasureTheory

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Jiang, Wang and Zhang, SSRN 3385089, Lemma 1.
theorem solution {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ)
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (_β : Fin n → ℝ)
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (h : (Fin n → ℝ) → ℝ) (hh : Integrable h F)
    (hRenv : ∀ D, ∀ x ∈ P c D, ∀ j, R j (x.1 j) (D j) ≤ h D)
    (hfenv : ∀ D, ∀ x ∈ P c D, |f x.2| ≤ h D)
    (w : Fin n → ℝ) (_hw : 0 ≤ w)
    (φw : DetPolicy P c)
    (hφw : ∀ D, IsMinOn (mwsObjective f R w D) (P c D) (φw.toFun D)) :
    (⨅ φ : DetPolicy P c, Fdual F f R w φ) = Fdual F f R w φw ∧
      Fdual F f R w φw = ∫ D, g P c f R w D ∂F := by
  classical
  have hfc (φ : DetPolicy P c) : Integrable (fun D => f (φ.toFun D).2) F := by
    have hm : Measurable (fun D => f (φ.toFun D).2) :=
      f.continuous_of_finiteDimensional.measurable.comp φ.measurable'.snd
    exact hh.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun D => by
      simpa only [Real.norm_eq_abs] using hfenv D (φ.toFun D) (φ.mem' D)))
  have hrc (φ : DetPolicy P c) (j : Fin n) :
      Integrable (fun D => R j ((φ.toFun D).1 j) (D j)) F := by
    have hm : Measurable (fun D => R j ((φ.toFun D).1 j) (D j)) :=
      (hRmeas j).comp (((measurable_pi_apply j).comp φ.measurable'.fst).prodMk (measurable_pi_apply j))
    exact hh.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun D => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hRnonneg _ _ _)]
      exact hRenv D (φ.toFun D) (φ.mem' D) j))
  have hsc (φ : DetPolicy P c) : Integrable (fun D => ∑ j, w j * R j ((φ.toFun D).1 j) (D j)) F :=
    integrable_finsetSum _ (fun j _ => (hrc φ j).const_mul (w j))
  have hoc (φ : DetPolicy P c) : Integrable (fun D => mwsObjective f R w D (φ.toFun D)) F :=
    (hfc φ).sub (hsc φ)
  have heq (φ : DetPolicy P c) : Fdual F f R w φ = ∫ D, mwsObjective f R w D (φ.toFun D) ∂F := by
    unfold Fdual detCost detService mwsObjective
    rw [integral_sub (hfc φ) (hsc φ), integral_finsetSum _ (fun j _ => (hrc φ j).const_mul (w j))]
    simp only [integral_const_mul]
  have hmin (φ : DetPolicy P c) : Fdual F f R w φw ≤ Fdual F f R w φ := by
    rw [heq,heq]
    exact integral_mono (hoc φw) (hoc φ) (fun D => hφw D (φ.mem' D))
  constructor
  · change sInf (Set.range (fun φ : DetPolicy P c => Fdual F f R w φ)) = _
    apply IsLeast.csInf_eq
    refine ⟨Set.mem_range_self φw, ?_⟩
    rintro _ ⟨φ,rfl⟩
    exact hmin φ
  · rw [heq]
    apply integral_congr_ae
    filter_upwards [] with D
    symm
    unfold g
    apply IsLeast.csInf_eq
    refine ⟨⟨φw.toFun D,φw.mem' D,rfl⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact hφw D hx
