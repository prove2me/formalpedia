-- Prove2me | solution 1 for ProgHedging.Nonconvex.limit_mem_M_N
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:51:18.344924+00:00
-- url     : https://prove2.me/submissions/2bf42d17-8446-4aa5-a863-15c7bac07dab

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone
open Filter Topology

namespace Aux_PH_lim
open ProgHedging.Convex
open Classical

lemma Japply {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (X : Policy S n) (s : S)
    (j : Fin n) : pr.J X s j =
      (∑ s' ∈ Finset.univ.filter (fun s' => (pr.bundle (pr.period j)).r s' s), pr.p s' * X s' j) /
      (∑ s' ∈ Finset.univ.filter (fun s' => (pr.bundle (pr.period j)).r s' s), pr.p s') := rfl

lemma filt_eq {S : Type*} [Fintype S] (σ : Setoid S) (s s' : S) (h : σ.r s s') :
    Finset.univ.filter (fun s'' => σ.r s'' s) = Finset.univ.filter (fun s'' => σ.r s'' s') := by
  ext s''
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h1; exact σ.iseqv.trans h1 h
  · intro h1; exact σ.iseqv.trans h1 (σ.iseqv.symm h)

lemma J_class {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (X : Policy S n) (j : Fin n)
    (s s' : S) (h : (pr.bundle (pr.period j)).r s s') : pr.J X s j = pr.J X s' j := by
  rw [Japply, Japply, filt_eq _ s s' h]

lemma den_pos {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (s : S) (j : Fin n) :
    0 < ∑ s' ∈ Finset.univ.filter (fun s' => (pr.bundle (pr.period j)).r s' s), pr.p s' := by
  apply Finset.sum_pos (fun s' _ => pr.p_pos s')
  exact ⟨s, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact
    (pr.bundle (pr.period j)).iseqv.refl s⟩

lemma JJ {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (X : Policy S n) :
    pr.J (pr.J X) = pr.J X := by
  funext s
  ext j
  rw [Japply]
  have hc : ∀ s' ∈ Finset.univ.filter (fun s' => (pr.bundle (pr.period j)).r s' s),
      pr.p s' * pr.J X s' j = pr.p s' * pr.J X s j := by
    intro s' hs'
    rw [J_class pr X j s' s (Finset.mem_filter.mp hs').2]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_mul, mul_div_right_comm,
    div_self (den_pos pr s j).ne', one_mul]

noncomputable def Jl {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) : Policy S n →ₗ[ℝ] Policy S n where
  toFun := pr.J
  map_add' X Y := by
    funext s
    ext j
    simp only [Pi.add_apply, PiLp.add_apply, Japply, mul_add, Finset.sum_add_distrib, add_div]
  map_smul' c X := by
    funext s
    ext j
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, Japply, RingHom.id_apply]
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun s' _ => by ring)

end Aux_PH_lim

open ProgHedging.Nonconvex in
theorem solution {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (X W : ℕ → ProgHedging.Convex.Policy S n) (hseq : pr.IsLocalPHSeq r δ X W)
    (Xs Ws : ProgHedging.Convex.Policy S n) (hX : Tendsto X atTop (𝓝 Xs)) (hW : Tendsto W atTop (𝓝 Ws)) :
    Ws ∈ pr.M ∧ Tendsto (fun ν => pr.K (X ν)) atTop (𝓝 0) ∧ Xs ∈ pr.N := by
  obtain ⟨-, hW0, hstep⟩ := hseq
  have hJc : Continuous pr.J := (Aux_PH_lim.Jl pr).continuous_of_finiteDimensional
  have hJadd : ∀ A B, pr.J (A + B) = pr.J A + pr.J B := (Aux_PH_lim.Jl pr).map_add
  have hJsmul : ∀ (c : ℝ) A, pr.J (c • A) = c • pr.J A := (Aux_PH_lim.Jl pr).map_smul
  have hJK : ∀ A, pr.J (pr.K A) = 0 := by
    intro A
    unfold ProgHedging.Convex.Problem.K
    have h1 : pr.J (A - pr.J A) + pr.J (pr.J A) = pr.J A := by
      rw [← hJadd, sub_add_cancel]
    rw [Aux_PH_lim.JJ] at h1
    exact add_eq_right.mp h1
  have hJW : ∀ ν, pr.J (W ν) = 0 := by
    intro ν
    induction ν with
    | zero => exact hW0
    | succ k ih =>
      rw [(hstep k).2, hJadd, hJsmul, hJK, smul_zero, add_zero, ih]
  have hKc : Continuous pr.K := by
    unfold ProgHedging.Convex.Problem.K
    exact continuous_id.sub hJc
  have hM : Ws ∈ pr.M := by
    have h1 : Tendsto (fun ν => pr.J (W ν)) atTop (𝓝 (pr.J Ws)) := (hJc.tendsto Ws).comp hW
    simp only [hJW] at h1
    show pr.J Ws = 0
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hK1 : ∀ ν, pr.K (X (ν + 1)) = r⁻¹ • (W (ν + 1) - W ν) := by
    intro ν
    rw [(hstep ν).2, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hKlim : Tendsto (fun ν => pr.K (X ν)) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simp only [hK1]
    have : Tendsto (fun ν => r⁻¹ • (W (ν + 1) - W ν)) atTop (𝓝 (r⁻¹ • (Ws - Ws))) :=
      ((hW.comp (tendsto_add_atTop_nat 1)).sub hW).const_smul r⁻¹
    rwa [sub_self, smul_zero] at this
  refine ⟨hM, hKlim, ?_⟩
  have hKs : pr.K Xs = 0 := by
    have h1 : Tendsto (fun ν => pr.K (X ν)) atTop (𝓝 (pr.K Xs)) := (hKc.tendsto Xs).comp hX
    exact tendsto_nhds_unique h1 hKlim
  have hXs : Xs = pr.J Xs := by
    unfold ProgHedging.Convex.Problem.K at hKs
    exact sub_eq_zero.mp hKs
  intro j s s' hss'
  rw [hXs]
  exact Aux_PH_lim.J_class pr Xs j s s' hss'
