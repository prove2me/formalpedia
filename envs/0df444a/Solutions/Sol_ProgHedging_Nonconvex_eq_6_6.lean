-- Prove2me | solution 1 for ProgHedging.Nonconvex.eq_6_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:54:10.36381+00:00
-- url     : https://prove2.me/submissions/35837e17-2862-4506-89ad-2585ef379b91

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone
open Filter Topology
open scoped RealInnerProductSpace

namespace Aux_PH64
open ProgHedging.Convex

lemma ip_self {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (X : Policy S n) :
    pr.ip X X = ∑ s, pr.p s * ‖X s‖ ^ 2 := by
  unfold Problem.ip
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [real_inner_self_eq_norm_sq]

lemma ip_nonneg {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (X : Policy S n) :
    0 ≤ pr.ip X X := by
  rw [ip_self]
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (pr.p_pos s).le (sq_nonneg _))

lemma pnorm_sq {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (X : Policy S n) :
    pr.pnorm X ^ 2 = ∑ s, pr.p s * ‖X s‖ ^ 2 := by
  unfold Problem.pnorm
  rw [Real.sq_sqrt (ip_nonneg pr X), ip_self]

end Aux_PH64

namespace Aux_PH66
open ProgHedging.Nonconvex in
theorem local_opt {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (X W : ℕ → ProgHedging.Convex.Policy S n) (hseq : pr.IsLocalPHSeq r δ X W) :
    (∀ Y Z : ProgHedging.Convex.Policy S n, pr.pnorm (Y - Z) ≤ pr.deltaPrime δ → ∀ s, ‖Y s - Z s‖ ≤ δ) ∧
    ∀ ν, X (ν + 1) ∈ pr.adm ∧ ∀ Y ∈ pr.adm, pr.pnorm (Y - X (ν + 1)) ≤ pr.deltaPrime δ →
      pr.Fnu r (pr.J (X ν)) (W ν) (X (ν + 1)) ≤ pr.Fnu r (pr.J (X ν)) (W ν) Y := by
  have part1 : ∀ Y Z : ProgHedging.Convex.Policy S n, pr.pnorm (Y - Z) ≤ pr.deltaPrime δ →
      ∀ s, ‖Y s - Z s‖ ≤ δ := by
    intro Y Z h s
    haveI : Nonempty S := ⟨s⟩
    have hbdd : BddBelow (Set.range fun s => Real.sqrt (pr.p s)) :=
      ⟨0, by rintro _ ⟨t, rfl⟩; exact Real.sqrt_nonneg _⟩
    have hinf_le : (⨅ s, Real.sqrt (pr.p s)) ≤ Real.sqrt (pr.p s) := ciInf_le hbdd s
    have hinf_nn : 0 ≤ ⨅ s, Real.sqrt (pr.p s) := le_ciInf (fun t => Real.sqrt_nonneg _)
    have hpn : 0 ≤ pr.pnorm (Y - Z) := Real.sqrt_nonneg _
    have hsq : pr.pnorm (Y - Z) ^ 2 ≤ (pr.deltaPrime δ) ^ 2 := pow_le_pow_left₀ hpn h 2
    rw [Aux_PH64.pnorm_sq] at hsq
    have hsingle : pr.p s * ‖(Y - Z) s‖ ^ 2 ≤ ∑ t, pr.p t * ‖(Y - Z) t‖ ^ 2 :=
      Finset.single_le_sum (f := fun t => pr.p t * ‖(Y - Z) t‖ ^ 2)
        (fun t _ => mul_nonneg (pr.p_pos t).le (sq_nonneg _)) (Finset.mem_univ s)
    have hdp : (pr.deltaPrime δ) ^ 2 ≤ δ ^ 2 * pr.p s := by
      unfold Problem.deltaPrime
      have h1 : (⨅ s, Real.sqrt (pr.p s)) ^ 2 ≤ Real.sqrt (pr.p s) ^ 2 :=
        pow_le_pow_left₀ hinf_nn hinf_le 2
      rw [Real.sq_sqrt (pr.p_pos s).le] at h1
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg δ)
    rw [Pi.sub_apply] at hsingle
    have hps := pr.p_pos s
    have : ‖Y s - Z s‖ ^ 2 ≤ δ ^ 2 := by
      by_contra hc
      push_neg at hc
      nlinarith
    nlinarith [norm_nonneg (Y s - Z s)]
  refine ⟨part1, fun ν => ?_⟩
  obtain ⟨-, -, hstep⟩ := hseq
  obtain ⟨hloc, -⟩ := hstep ν
  have hFnu : ∀ V Wv Xv : ProgHedging.Convex.Policy S n, pr.Fnu r V Wv Xv =
      ∑ s, pr.p s * pr.subObj s (V s) (Wv s) r (Xv s) := by
    intro V Wv Xv
    unfold Problem.Fnu
    rw [Aux_PH64.pnorm_sq]
    unfold ProgHedging.Convex.Problem.F ProgHedging.Convex.Problem.ip
      ProgHedging.Convex.Problem.subObj
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Pi.sub_apply]
    ring
  refine ⟨fun s => (hloc s).1, fun Y hY hball => ?_⟩
  rw [hFnu, hFnu]
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (pr.p_pos s).le
  exact (hloc s).2 (Y s) (hY s) (part1 Y (X (ν + 1)) hball s)

end Aux_PH66

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
    Xs ∈ pr.adm ∧ ∀ Y ∈ pr.adm, pr.pnorm (Y - Xs) < pr.deltaPrime δ →
      pr.F Xs + pr.ip Xs Ws ≤ pr.F Y + pr.ip Y Ws + r / 2 * pr.pnorm (Y - Xs) ^ 2 := by
  have hloc := (Aux_PH66.local_opt pr hr hδ X W hseq).2
  have hX1 : Tendsto (fun ν => X (ν + 1)) atTop (𝓝 Xs) := hX.comp (tendsto_add_atTop_nat 1)
  -- admissibility
  have hadm : Xs ∈ pr.adm := by
    intro s
    have hs : Tendsto (fun ν => X (ν + 1) s) atTop (𝓝 (Xs s)) :=
      ((continuous_apply s).tendsto Xs).comp hX1
    exact (pr.C_closed s).mem_of_tendsto hs (Eventually.of_forall (fun ν => (hloc ν).1 s))
  -- continuity facts
  have hJc : Continuous pr.J := (Aux_PH_lim.Jl pr).continuous_of_finiteDimensional
  have hF : Continuous pr.F := by
    unfold ProgHedging.Convex.Problem.F
    exact continuous_finset_sum _ (fun s _ =>
      continuous_const.mul ((pr.f_locallyLipschitz s).continuous.comp (continuous_apply s)))
  have hip : Continuous (fun q : ProgHedging.Convex.Policy S n × ProgHedging.Convex.Policy S n =>
      pr.ip q.1 q.2) := by
    unfold ProgHedging.Convex.Problem.ip
    exact continuous_finset_sum _ (fun s _ => continuous_const.mul
      (((continuous_apply s).comp continuous_fst).inner ((continuous_apply s).comp continuous_snd)))
  have hpn : Continuous pr.pnorm := by
    unfold ProgHedging.Convex.Problem.pnorm
    exact Real.continuous_sqrt.comp (hip.comp (continuous_id.prodMk continuous_id))
  have hpn0 : pr.pnorm 0 = 0 := by
    unfold ProgHedging.Convex.Problem.pnorm ProgHedging.Convex.Problem.ip
    simp
  -- J Xs = Xs
  obtain ⟨-, -, hstep⟩ := hseq
  have hK1 : ∀ ν, pr.K (X (ν + 1)) = r⁻¹ • (W (ν + 1) - W ν) := by
    intro ν
    rw [(hstep ν).2, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hKc : Continuous pr.K := by
    unfold ProgHedging.Convex.Problem.K
    exact continuous_id.sub hJc
  have hKs : pr.K Xs = 0 := by
    have h1 : Tendsto (fun ν => pr.K (X (ν + 1))) atTop (𝓝 (pr.K Xs)) := (hKc.tendsto Xs).comp hX1
    have h2 : Tendsto (fun ν => pr.K (X (ν + 1))) atTop (𝓝 0) := by
      simp only [hK1]
      have : Tendsto (fun ν => r⁻¹ • (W (ν + 1) - W ν)) atTop (𝓝 (r⁻¹ • (Ws - Ws))) :=
        ((hW.comp (tendsto_add_atTop_nat 1)).sub hW).const_smul r⁻¹
      rwa [sub_self, smul_zero] at this
    exact tendsto_nhds_unique h1 h2
  have hJXs : pr.J Xs = Xs := by
    unfold ProgHedging.Convex.Problem.K at hKs
    exact (sub_eq_zero.mp hKs).symm
  have hJX : Tendsto (fun ν => pr.J (X ν)) atTop (𝓝 Xs) := by
    have := (hJc.tendsto Xs).comp hX
    rwa [hJXs] at this
  refine ⟨hadm, fun Y hY hYlt => ?_⟩
  -- limits of both sides
  have hL : Tendsto (fun ν => pr.Fnu r (pr.J (X ν)) (W ν) (X (ν + 1))) atTop
      (𝓝 (pr.F Xs + pr.ip Xs Ws + r / 2 * pr.pnorm (Xs - Xs) ^ 2)) := by
    unfold Problem.Fnu
    refine ((((hF.tendsto Xs).comp hX1).add ((hip.tendsto (Xs, Ws)).comp (hX1.prodMk_nhds hW))).add
      (tendsto_const_nhds.mul ((((hpn.tendsto (Xs - Xs)).comp (hX1.sub hJX))).pow 2)))
  have hR : Tendsto (fun ν => pr.Fnu r (pr.J (X ν)) (W ν) Y) atTop
      (𝓝 (pr.F Y + pr.ip Y Ws + r / 2 * pr.pnorm (Y - Xs) ^ 2)) := by
    unfold Problem.Fnu
    refine (tendsto_const_nhds.add ((hip.tendsto (Y, Ws)).comp
      (tendsto_const_nhds.prodMk_nhds hW))).add
      (tendsto_const_nhds.mul ((((hpn.tendsto (Y - Xs)).comp (tendsto_const_nhds.sub hJX))).pow 2))
  have hev : ∀ᶠ ν in atTop, pr.pnorm (Y - X (ν + 1)) ≤ pr.deltaPrime δ := by
    have h1 : Tendsto (fun ν => pr.pnorm (Y - X (ν + 1))) atTop (𝓝 (pr.pnorm (Y - Xs))) :=
      (hpn.tendsto (Y - Xs)).comp (tendsto_const_nhds.sub hX1)
    exact (h1.eventually (gt_mem_nhds hYlt)).mono (fun ν h => h.le)
  have := le_of_tendsto_of_tendsto hL hR (hev.mono (fun ν h => (hloc ν).2 Y hY h))
  rw [sub_self, hpn0] at this
  simpa using this
