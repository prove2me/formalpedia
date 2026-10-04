-- Prove2me | solution 1 for ServiceParts.Allocation.netInv_normal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:43:11.203549+00:00
-- url     : https://prove2.me/submissions/9bb70da6-05e5-4e84-9141-6a5c4decec64

import Mathlib
import Definitions.Def_ServiceParts_Allocation_PoolingSystem

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory in
/-- Law of a finite sum of independent real Gaussians. -/
lemma p29070623_sum_law {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (mu v : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hlaw : ∀ i, P.map (X i) = gaussianReal (mu i) (Real.toNNReal (v i))) (T : Finset ι) :
    P.map (fun ω => ∑ i ∈ T, X i ω) =
      gaussianReal (∑ i ∈ T, mu i) (Real.toNNReal (∑ i ∈ T, v i)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp [Measure.map_const, gaussianReal_zero_var]
  | insert k T hk ih =>
    have hfun : (fun ω => ∑ i ∈ insert k T, X i ω) = X k + (fun ω => ∑ i ∈ T, X i ω) := by
      funext ω; simp [Finset.sum_insert hk]
    have hind2 : IndepFun (X k) (fun ω => ∑ i ∈ T, X i ω) P := by
      have h := (hind.indepFun_finsetSum_of_notMem hX hk).symm
      have he : (∑ j ∈ T, X j) = (fun ω => ∑ i ∈ T, X i ω) := by
        funext ω; simp [Finset.sum_apply]
      rwa [he] at h
    rw [hfun, gaussianReal_add_gaussianReal_of_indepFun hind2 (hlaw k) ih,
      Finset.sum_insert hk, Finset.sum_insert hk,
      Real.toNNReal_add (hv k) (Finset.sum_nonneg (fun i _ => hv i))]

open MeasureTheory ProbabilityTheory ServiceParts.Allocation in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (S : PoolingSystem Ω P m) (s : ℝ) (j : Fin m) :
    P.map (S.netInv s j) =
      gaussianReal ((s - (S.D + S.A + 1) * ∑ i, S.μ i) * (S.σ j / ∑ i, S.σ i))
        (Real.toNNReal ((S.A + 1) * S.σ j ^ 2 +
          (S.σ j / ∑ i, S.σ i) ^ 2 * S.D * ∑ i, S.σ i ^ 2)) := by
  classical
  set X : ℕ × Fin m → Ω → ℝ := fun p => S.demand p.1 p.2 with hXdef
  have hXm : ∀ p, Measurable (X p) := fun p => S.demand_measurable p.1 p.2
  have hind : iIndepFun X P := S.demand_indep
  have hlaw : ∀ p, P.map (X p) =
      gaussianReal (S.μ p.2) (Real.toNNReal (S.σ p.2 ^ 2)) := fun p => S.demand_law p.1 p.2
  set T0 : Finset (ℕ × Fin m) := Finset.Icc 1 S.D ×ˢ Finset.univ with hT0
  set T1 : Finset (ℕ × Fin m) := Finset.Icc (S.D + 1) (S.D + S.A + 1) ×ˢ {j} with hT1
  set U : Ω → ℝ := fun ω => ∑ p ∈ T0, X p ω with hU
  set V : Ω → ℝ := fun ω => ∑ p ∈ T1, X p ω with hV
  have hY0 : ∀ ω, S.Y0 ω = U ω := by
    intro ω
    simp only [PoolingSystem.Y0, hU, hT0, Finset.sum_product, hXdef]
  have hYw : ∀ ω, S.Yw j ω = V ω := by
    intro ω
    simp only [PoolingSystem.Yw, hV, hT1, Finset.sum_product, Finset.sum_singleton, hXdef]
  have hUlaw := p29070623_sum_law X hXm hind (fun p => S.μ p.2) (fun p => S.σ p.2 ^ 2)
    (fun p => sq_nonneg _) hlaw T0
  have hVlaw := p29070623_sum_law X hXm hind (fun p => S.μ p.2) (fun p => S.σ p.2 ^ 2)
    (fun p => sq_nonneg _) hlaw T1
  have hdisj : Disjoint T0 T1 := by
    rw [Finset.disjoint_left]
    intro p hp0 hp1
    simp only [hT0, hT1, Finset.mem_product, Finset.mem_Icc] at hp0 hp1
    omega
  have hUV : IndepFun U V P := by
    have h := hind.indepFun_finset T0 T1 hdisj hXm
    have hg0 : Measurable (fun x : (T0 → ℝ) => ∑ i, x i) := by fun_prop
    have hg1 : Measurable (fun x : (T1 → ℝ) => ∑ i, x i) := by fun_prop
    have h2 := h.comp hg0 hg1
    have e0 : U = (fun x : (T0 → ℝ) => ∑ i, x i) ∘ (fun a (i : T0) => X i a) := by
      funext ω
      simp only [hU, Function.comp_apply]
      exact (Finset.sum_coe_sort T0 (fun p => X p ω)).symm
    have e1 : V = (fun x : (T1 → ℝ) => ∑ i, x i) ∘ (fun a (i : T1) => X i a) := by
      funext ω
      simp only [hV, Function.comp_apply]
      exact (Finset.sum_coe_sort T1 (fun p => X p ω)).symm
    rw [e0, e1]; exact h2
  set c : ℝ := S.σ j / ∑ i, S.σ i with hc
  set K : ℝ := (S.A + 1) * S.μ j + (s - (S.A + 1) * ∑ i, S.μ i) * c with hK
  have hnet : S.netInv s j = (fun ω => K + (-c) * U ω) + (fun ω => -V ω) := by
    funext ω
    simp only [PoolingSystem.netInv, PoolingSystem.alloc, Pi.add_apply, hY0, hYw, hK, hc]
    ring
  have hUm : Measurable U := by
    simp only [hU]; exact Finset.measurable_sum _ (fun p _ => hXm p)
  have hVm : Measurable V := by
    simp only [hV]; exact Finset.measurable_sum _ (fun p _ => hXm p)
  have hind3 : IndepFun (fun ω => K + (-c) * U ω) (fun ω => -V ω) P := by
    have hf : Measurable (fun x : ℝ => K + (-c) * x) := by fun_prop
    have hg : Measurable (fun x : ℝ => -x) := by fun_prop
    exact hUV.comp hf hg
  have hlawA : P.map (fun ω => K + (-c) * U ω) =
      gaussianReal (K + (-c) * ∑ p ∈ T0, S.μ p.2)
        (.mk ((-c) ^ 2) (sq_nonneg _) * Real.toNNReal (∑ p ∈ T0, S.σ p.2 ^ 2)) := by
    have hcomp : (fun ω => K + (-c) * U ω) = (fun x : ℝ => K + x) ∘ (fun x : ℝ => (-c) * x) ∘ U := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) hUm, hUlaw, gaussianReal_map_const_mul,
      gaussianReal_map_const_add, add_comm]
  have hlawB : P.map (fun ω => -V ω) =
      gaussianReal (-(∑ p ∈ T1, S.μ p.2)) (Real.toNNReal (∑ p ∈ T1, S.σ p.2 ^ 2)) := by
    have hcomp : (fun ω => -V ω) = (fun x : ℝ => -x) ∘ V := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) hVm, hVlaw, gaussianReal_map_neg]
  rw [hnet, gaussianReal_add_gaussianReal_of_indepFun hind3 hlawA hlawB]
  have hcard0 : (Finset.Icc 1 S.D).card = S.D := by simp
  have hcard1 : (Finset.Icc (S.D + 1) (S.D + S.A + 1)).card = S.A + 1 := by
    simp only [Nat.card_Icc]; omega
  have hm0 : ∑ p ∈ T0, S.μ p.2 = (S.D : ℝ) * ∑ i, S.μ i := by
    simp only [hT0, Finset.sum_product, Finset.sum_const, hcard0, nsmul_eq_mul]
  have hm1 : ∑ p ∈ T1, S.μ p.2 = ((S.A : ℝ) + 1) * S.μ j := by
    simp only [hT1, Finset.sum_product, Finset.sum_singleton, Finset.sum_const, hcard1,
      nsmul_eq_mul]
    push_cast; ring
  have hv0 : ∑ p ∈ T0, S.σ p.2 ^ 2 = (S.D : ℝ) * ∑ i, S.σ i ^ 2 := by
    simp only [hT0, Finset.sum_product, Finset.sum_const, hcard0, nsmul_eq_mul]
  have hv1 : ∑ p ∈ T1, S.σ p.2 ^ 2 = ((S.A : ℝ) + 1) * S.σ j ^ 2 := by
    simp only [hT1, Finset.sum_product, Finset.sum_singleton, Finset.sum_const, hcard1,
      nsmul_eq_mul]
    push_cast; ring
  rw [hm0, hm1, hv0, hv1]
  have hD0 : 0 ≤ (S.D : ℝ) * ∑ i, S.σ i ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hA0 : 0 ≤ ((S.A : ℝ) + 1) * S.σ j ^ 2 := by positivity
  congr 1
  · simp only [hK]; ring
  · rw [← NNReal.coe_inj, NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ hD0,
      Real.coe_toNNReal _ hA0, Real.coe_toNNReal _ (by positivity)]
    change (-c) ^ 2 * ((S.D : ℝ) * ∑ i, S.σ i ^ 2) + ((S.A : ℝ) + 1) * S.σ j ^ 2 = _
    ring
