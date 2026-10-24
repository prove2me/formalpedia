-- Prove2me | solution 1 for SensitivityPoA.Continuity.lemma_4_c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T09:29:53.813173+00:00
-- url     : https://prove2.me/submissions/8372eb2e-a226-4488-981b-a3bf9a2a4a16

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Continuity_Setting

namespace SensitivityPoA.Continuity.PoA2Aux

open KellyStochasticNetworks SensitivityPoA.Continuity Filter Topology

lemma sum_flow_eq {N : Network} {Γ : Game N} {f : Fin N.R → ℝ} (hf : IsFlow Γ f) :
    ∑ r, f r = totalDemand Γ.d := by
  rw [← Finset.sum_fiberwise Finset.univ N.s f]
  unfold totalDemand
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact hf.2 k

lemma flow_nonneg {N : Network} {Γ : Game N} {f : Fin N.R → ℝ} (hf : IsFlow Γ f) (r : Fin N.R) :
    0 ≤ f r := hf.1 r

lemma flow_le {N : Network} {Γ : Game N} {f : Fin N.R → ℝ} (hf : IsFlow Γ f) (r : Fin N.R) :
    f r ≤ totalDemand Γ.d := by
  rw [← sum_flow_eq hf]
  exact Finset.single_le_sum (fun i _ => flow_nonneg hf i) (Finset.mem_univ r)

lemma linkFlow_nonneg {N : Network} (hN : N.Standing) {f : Fin N.R → ℝ} (hf : ∀ r, 0 ≤ f r)
    (j : Fin N.J) : 0 ≤ linkFlow N.A f j := by
  unfold linkFlow
  refine Finset.sum_nonneg (fun r _ => mul_nonneg ?_ (hf r))
  rcases hN.1 j r with h | h <;> rw [h] <;> norm_num

lemma linkFlow_le {N : Network} (hN : N.Standing) {Γ : Game N} {f : Fin N.R → ℝ}
    (hf : IsFlow Γ f) (j : Fin N.J) : linkFlow N.A f j ≤ totalDemand Γ.d := by
  rw [← sum_flow_eq hf]
  unfold linkFlow
  refine Finset.sum_le_sum (fun r _ => ?_)
  have := flow_nonneg hf r
  rcases hN.1 j r with h | h <;> rw [h] <;> linarith

lemma linkFlow_ge_path {N : Network} (hN : N.Standing) {f : Fin N.R → ℝ} (hf : ∀ r, 0 ≤ f r)
    (j : Fin N.J) (r : Fin N.R) (hjr : N.A j r = 1) : f r ≤ linkFlow N.A f j := by
  unfold linkFlow
  have : N.A j r * f r = f r := by rw [hjr, one_mul]
  rw [← this]
  refine Finset.single_le_sum (f := fun r => N.A j r * f r) (fun i _ => mul_nonneg ?_ (hf i))
    (Finset.mem_univ r)
  rcases hN.1 j i with h | h <;> rw [h] <;> norm_num

lemma tendsto_linkFlow {N : Network} {fs : ℕ → Fin N.R → ℝ} {f : Fin N.R → ℝ}
    (h : Tendsto fs atTop (𝓝 f)) (j : Fin N.J) :
    Tendsto (fun n => linkFlow N.A (fs n) j) atTop (𝓝 (linkFlow N.A f j)) := by
  unfold linkFlow
  refine tendsto_finset_sum _ (fun r _ => ?_)
  exact (tendsto_pi_nhds.1 h r).const_mul _

/-- Distance bounds. -/
lemma demand_le_dist {N : Network} (Γ Γ' : Game N) :
    ‖Γ.d - Γ'.d‖ ≤ gameDist Γ Γ' := le_max_left _ _

lemma endpoint_le_dist {N : Network} (Γ Γ' : Game N) (j : Fin N.J) :
    |Γ.τ j (totalDemand Γ.d) - Γ'.τ j (totalDemand Γ'.d)| ≤ gameDist Γ Γ' := by
  refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_right _ _))
  have := norm_le_pi_norm (fun j => Γ.τ j (totalDemand Γ.d) -
        Γ'.τ j (totalDemand Γ'.d)) j
  simpa [Real.norm_eq_abs] using this

lemma unif_le_dist {N : Network} (Γ Γ' : Game N) (hΓ : Γ.IsGeneralized)
    (hΓ' : Γ'.IsGeneralized) (j : Fin N.J) (y : ℝ) (hy0 : 0 ≤ y)
    (hy : y ≤ min (totalDemand Γ.d) (totalDemand Γ'.d)) :
    |Γ.τ j y - Γ'.τ j y| ≤ gameDist Γ Γ' := by
  refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_right _ _))
  set m := min (totalDemand Γ.d) (totalDemand Γ'.d)
  apply le_csSup
  · refine ⟨∑ i, (Γ.τ i m + Γ'.τ i m), ?_⟩
    rintro _ ⟨⟨i, z⟩, ⟨-, hz⟩, rfl⟩
    simp only at hz ⊢
    have hm : 0 ≤ m := le_trans hz.1 hz.2
    have a1 := (hΓ.1 i).2.2 z hz.1
    have a2 := (hΓ'.1 i).2.2 z hz.1
    have b1 := (hΓ.1 i).2.1 (Set.mem_Ici.2 hz.1) (Set.mem_Ici.2 hm) hz.2
    have b2 := (hΓ'.1 i).2.1 (Set.mem_Ici.2 hz.1) (Set.mem_Ici.2 hm) hz.2
    have : |Γ.τ i z - Γ'.τ i z| ≤ Γ.τ i m + Γ'.τ i m := by
      rw [abs_le]; constructor <;> linarith
    refine le_trans this ?_
    refine Finset.single_le_sum (f := fun i => Γ.τ i m + Γ'.τ i m) (fun i _ => ?_)
      (Finset.mem_univ i)
    exact add_nonneg ((hΓ.1 i).2.2 m hm) ((hΓ'.1 i).2.2 m hm)
  · exact ⟨⟨j, y⟩, ⟨Set.mem_univ _, ⟨hy0, hy⟩⟩, rfl⟩

section Seq

variable {N : Network} {Γ : Game N} {Γs : ℕ → Game N}

lemma tendsto_d (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0)) :
    Tendsto (fun n => (Γs n).d) atTop (𝓝 Γ.d) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => demand_le_dist _ _) hlim

lemma tendsto_T (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0)) :
    Tendsto (fun n => totalDemand (Γs n).d) atTop (𝓝 (totalDemand Γ.d)) := by
  unfold totalDemand
  exact tendsto_finset_sum _ (fun k _ => tendsto_pi_nhds.1 (tendsto_d hlim) k)

lemma tendsto_dk (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0)) (k : Fin N.Sd) :
    Tendsto (fun n => (Γs n).d k) atTop (𝓝 (Γ.d k)) :=
  tendsto_pi_nhds.1 (tendsto_d hlim) k

lemma tendsto_comp_sub (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Tendsto (fun n => gameDist (Γs (φ n)) Γ) atTop (𝓝 0) :=
  hlim.comp hφ.tendsto_atTop

/-- Arc cost convergence. -/
lemma tendsto_arc (hΓ : Γ ∈ gameSpace N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0)) (j : Fin N.J)
    (x : ℕ → ℝ) (hx0 : ∀ n, 0 ≤ x n) (hxT : ∀ n, x n ≤ totalDemand (Γs n).d) (X : ℝ)
    (hX : Tendsto x atTop (𝓝 X)) :
    Tendsto (fun n => (Γs n).τ j (x n)) atTop (𝓝 (Γ.τ j X)) := by
  have hX0 : 0 ≤ X := ge_of_tendsto' hX hx0
  have hTn := tendsto_T hlim
  set T := totalDemand Γ.d
  have hXT : X ≤ T := le_of_tendsto_of_tendsto' hX hTn hxT
  have hT0 : 0 ≤ T := le_trans hX0 hXT
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc := (hΓ.1.1 j).1 X (Set.mem_Ici.2 hX0)
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hδc⟩ := hc (ε / 2) (by linarith)
  have e1 := (Metric.tendsto_atTop.1 hlim) (ε / 2) (by linarith)
  have e2 := (Metric.tendsto_atTop.1 hX) δ hδ
  obtain ⟨n1, h1⟩ := e1
  obtain ⟨n2, h2⟩ := e2
  refine ⟨max n1 n2, fun n hn => ?_⟩
  have hD := h1 n (le_trans (le_max_left _ _) hn)
  have hx := h2 n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq] at hD hx ⊢
  have hD0 : 0 ≤ gameDist (Γs n) Γ := le_trans (norm_nonneg _) (demand_le_dist _ _)
  rw [sub_zero, abs_of_nonneg hD0] at hD
  have hgn := (hΓs n).1
  by_cases hcase : x n ≤ T
  · have u := unif_le_dist (Γs n) Γ hgn hΓ.1 j (x n) (hx0 n) (le_min (hxT n) hcase)
    have v := hδc (Set.mem_Ici.2 (hx0 n)) (by rw [Real.dist_eq]; exact hx)
    rw [Real.dist_eq] at v
    calc |(Γs n).τ j (x n) - Γ.τ j X|
        ≤ |(Γs n).τ j (x n) - Γ.τ j (x n)| + |Γ.τ j (x n) - Γ.τ j X| := abs_sub_le _ _ _
      _ < ε := by linarith
  · push_neg at hcase
    have hTTn : T ≤ totalDemand (Γs n).d := le_trans hcase.le (hxT n)
    have u := unif_le_dist (Γs n) Γ hgn hΓ.1 j T hT0 (le_min hTTn le_rfl)
    have w := endpoint_le_dist (Γs n) Γ j
    have m1 := (hgn.1 j).2.1 (Set.mem_Ici.2 hT0) (Set.mem_Ici.2 (hx0 n)) hcase.le
    have m2 := (hgn.1 j).2.1 (Set.mem_Ici.2 (hx0 n)) (Set.mem_Ici.2 (le_trans hT0 hTTn)) (hxT n)
    have hTX : |T - X| < δ := by
      rw [abs_of_nonneg (by linarith)]
      rw [abs_lt] at hx; linarith
    have v := hδc (Set.mem_Ici.2 hT0) (by rw [Real.dist_eq]; exact hTX)
    rw [Real.dist_eq] at v
    rw [abs_le] at u w
    rw [abs_lt] at v ⊢
    constructor <;> linarith

end Seq

end SensitivityPoA.Continuity.PoA2Aux


namespace SensitivityPoA.Continuity.PoA2Aux

open KellyStochasticNetworks SensitivityPoA.Continuity Filter Topology

/-- Number of paths of an OD pair. -/
noncomputable def pc (N : Network) (k : Fin N.Sd) : ℝ :=
  ((Finset.univ.filter (fun r => N.s r = k)).card : ℝ)

lemma pc_pos {N : Network} (hN : N.Standing) (k : Fin N.Sd) : 0 < pc N k := by
  unfold pc
  have := hN.2.2.2.2 k
  exact_mod_cast (by omega : 0 < (Finset.univ.filter (fun r => N.s r = k)).card)

lemma sum_filter_congr {N : Network} (k : Fin N.Sd) (g : Fin N.R → ℝ) (h : Fin N.Sd → Fin N.R → ℝ)
    (hgh : ∀ r, g r = h (N.s r) r) :
    (∑ r ∈ Finset.univ.filter (fun r => N.s r = k), g r) =
      ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), h k r := by
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [Finset.mem_filter] at hr
  rw [hgh r, hr.2]

lemma unif_mem {N : Network} (hN : N.Standing) (e : Fin N.Sd → ℝ) (he : ∀ k, 0 ≤ e k) :
    (fun r => e (N.s r) / pc N (N.s r)) ∈ wardropFeasible N.s e := by
  refine ⟨fun r => div_nonneg (he _) (pc_pos hN _).le, fun k => ?_⟩
  rw [sum_filter_congr k _ (fun k _ => e k / pc N k) (fun r => rfl)]
  rw [Finset.sum_const, nsmul_eq_mul]
  have := pc_pos hN k
  unfold pc at this ⊢
  field_simp

lemma flow_exists {N : Network} (hN : N.Standing) (Γ : Game N) (hΓ : Γ.IsGeneralized) :
    ∃ f, IsFlow Γ f := ⟨_, unif_mem hN Γ.d hΓ.2⟩

lemma cost_nonneg {N : Network} (hN : N.Standing) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    {f : Fin N.R → ℝ} (hf : ∀ r, 0 ≤ f r) : 0 ≤ cost Γ f := by
  unfold cost
  refine Finset.sum_nonneg (fun j _ => mul_nonneg (linkFlow_nonneg hN hf j) ?_)
  exact (hΓ.1 j).2.2 _ (linkFlow_nonneg hN hf j)

section Seq

variable {N : Network} {Γ : Game N} {Γs : ℕ → Game N}

lemma tendsto_pathCost (hN : N.Standing) (hΓ : Γ ∈ gameSpace N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0))
    (fs : ℕ → Fin N.R → ℝ) (hfs : ∀ n, IsFlow (Γs n) (fs n)) (f : Fin N.R → ℝ)
    (hf : Tendsto fs atTop (𝓝 f)) (r : Fin N.R) :
    Tendsto (fun n => pathCost (Γs n) (fs n) r) atTop (𝓝 (pathCost Γ f r)) := by
  unfold pathCost
  refine tendsto_finset_sum _ (fun j _ => ?_)
  refine Tendsto.mul_const _ ?_
  exact tendsto_arc hΓ hΓs hlim j _ (fun n => linkFlow_nonneg hN (hfs n).1 j)
    (fun n => linkFlow_le hN (hfs n) j) _ (tendsto_linkFlow hf j)

lemma tendsto_cost (hN : N.Standing) (hΓ : Γ ∈ gameSpace N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0))
    (fs : ℕ → Fin N.R → ℝ) (hfs : ∀ n, IsFlow (Γs n) (fs n)) (f : Fin N.R → ℝ)
    (hf : Tendsto fs atTop (𝓝 f)) :
    Tendsto (fun n => cost (Γs n) (fs n)) atTop (𝓝 (cost Γ f)) := by
  unfold cost
  refine tendsto_finset_sum _ (fun j _ => ?_)
  refine Tendsto.mul (tendsto_linkFlow hf j) ?_
  exact tendsto_arc hΓ hΓs hlim j _ (fun n => linkFlow_nonneg hN (hfs n).1 j)
    (fun n => linkFlow_le hN (hfs n) j) _ (tendsto_linkFlow hf j)

lemma isFlow_of_tendsto (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0))
    (fs : ℕ → Fin N.R → ℝ) (hfs : ∀ n, IsFlow (Γs n) (fs n)) (f : Fin N.R → ℝ)
    (hf : Tendsto fs atTop (𝓝 f)) : IsFlow Γ f := by
  refine ⟨fun r => ge_of_tendsto' (tendsto_pi_nhds.1 hf r) (fun n => (hfs n).1 r), fun k => ?_⟩
  have h1 : Tendsto (fun n => ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), fs n r) atTop
      (𝓝 (∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r)) :=
    tendsto_finset_sum _ (fun r _ => tendsto_pi_nhds.1 hf r)
  have h2 : (fun n => ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), fs n r) =
      fun n => (Γs n).d k := funext (fun n => (hfs n).2 k)
  rw [h2] at h1
  exact tendsto_nhds_unique h1 (tendsto_dk hlim k)

lemma exists_subseq (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0))
    (fs : ℕ → Fin N.R → ℝ) (hfs : ∀ n, IsFlow (Γs n) (fs n)) :
    ∃ f : Fin N.R → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fs ∘ φ) atTop (𝓝 f) := by
  obtain ⟨B, hB⟩ := (tendsto_T hlim).bddAbove_range
  have hK : IsCompact (Set.Icc (0 : Fin N.R → ℝ) (fun _ => B)) := isCompact_Icc
  have hmem : ∀ n, fs n ∈ Set.Icc (0 : Fin N.R → ℝ) (fun _ => B) := by
    intro n
    refine ⟨fun r => (hfs n).1 r, fun r => le_trans (flow_le (hfs n) r) ?_⟩
    exact hB ⟨n, rfl⟩
  obtain ⟨f, -, φ, hφ, h⟩ := hK.tendsto_subseq hmem
  exact ⟨f, φ, hφ, h⟩

/-- Lemma 5a: approximation of a flow of the limit game. -/
lemma approx (hN : N.Standing) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0))
    (f : Fin N.R → ℝ) (hf : IsFlow Γ f) :
    ∃ fs : ℕ → Fin N.R → ℝ,
      (∀ n, IsFlow (Γs n) (fs n)) ∧ Tendsto fs atTop (𝓝 f) := by
  classical
  let g : ℕ → Fin N.R → ℝ := fun n r =>
    if Γ.d (N.s r) = 0 then (Γs n).d (N.s r) / pc N (N.s r)
    else f r * ((Γs n).d (N.s r) / Γ.d (N.s r))
  have hdpos : ∀ k, Γ.d k ≠ 0 → 0 < Γ.d k := by
    intro k hk
    have h0 : 0 ≤ Γ.d k := by
      rw [← hf.2 k]; exact Finset.sum_nonneg (fun r _ => hf.1 r)
    exact lt_of_le_of_ne h0 (Ne.symm hk)
  have hzero : ∀ r, Γ.d (N.s r) = 0 → f r = 0 := by
    intro r hr
    have h := hf.2 (N.s r)
    rw [hr] at h
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hf.1 i)).1 h r
      (by simp)
    exact this
  refine ⟨g, fun n => ⟨fun r => ?_, fun k => ?_⟩, ?_⟩
  · simp only [g]
    have hd := (hΓs n).1.2 (N.s r)
    split_ifs with h
    · exact div_nonneg hd (pc_pos hN _).le
    · exact mul_nonneg (hf.1 r) (div_nonneg hd (hdpos _ h).le)
  · rw [sum_filter_congr k (g n) (fun k r => if Γ.d k = 0 then (Γs n).d k / pc N k
      else f r * ((Γs n).d k / Γ.d k)) (fun r => rfl)]
    by_cases h : Γ.d k = 0
    · simp only [h, if_true]
      rw [Finset.sum_const, nsmul_eq_mul]
      have := pc_pos hN k
      unfold pc at this ⊢
      field_simp
    · simp only [h, if_false]
      rw [← Finset.sum_mul, hf.2 k]
      field_simp
  · rw [tendsto_pi_nhds]
    intro r
    simp only [g]
    by_cases h : Γ.d (N.s r) = 0
    · simp only [h, if_true]
      rw [hzero r h]
      have := ((tendsto_dk hlim (N.s r)).div_const (pc N (N.s r)))
      rwa [h, zero_div] at this
    · simp only [h, if_false]
      have := ((tendsto_dk hlim (N.s r)).div_const (Γ.d (N.s r))).const_mul (f r)
      rwa [div_self h, mul_one] at this

lemma SOCost_le (hN : N.Standing) (Γ' : Game N) (hΓ' : Γ'.IsGeneralized) (f : Fin N.R → ℝ)
    (hf : IsFlow Γ' f) : SOCost Γ' ≤ cost Γ' f := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨g, hg, rfl⟩; exact cost_nonneg hN Γ' hΓ' hg.1⟩
  · exact ⟨f, hf, rfl⟩

lemma exists_near_SO (hN : N.Standing) (Γ' : Game N) (hΓ' : Γ'.IsGeneralized) (ε : ℝ)
    (hε : 0 < ε) : ∃ f, IsFlow Γ' f ∧ cost Γ' f < SOCost Γ' + ε := by
  obtain ⟨f0, hf0⟩ := flow_exists hN Γ' hΓ'
  obtain ⟨_, ⟨f, hf, rfl⟩, h⟩ := Real.lt_sInf_add_pos (s := cost Γ' '' {f | IsFlow Γ' f})
    ⟨_, ⟨f0, hf0, rfl⟩⟩ hε
  exact ⟨f, hf, h⟩

lemma le_SOCost (hN : N.Standing) (Γ' : Game N) (hΓ' : Γ'.IsGeneralized) (c : ℝ)
    (hc : ∀ f, IsFlow Γ' f → c ≤ cost Γ' f) : c ≤ SOCost Γ' := by
  obtain ⟨f0, hf0⟩ := flow_exists hN Γ' hΓ'
  refine le_csInf ⟨cost Γ' f0, f0, hf0, rfl⟩ ?_
  rintro _ ⟨f, hf, rfl⟩
  exact hc f hf

/-- Lemma 5b (cost part). -/
lemma tendsto_SOCost (hN : N.Standing) (hΓ : Γ ∈ gameSpace N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0)) :
    Tendsto (fun n => SOCost (Γs n)) atTop (𝓝 (SOCost Γ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- upper bound
  have hup : ∀ᶠ n in atTop, SOCost (Γs n) < SOCost Γ + ε := by
    obtain ⟨f, hf, hfc⟩ := exists_near_SO hN Γ hΓ.1 (ε / 2) (by linarith)
    obtain ⟨fs, hfs, hfsl⟩ := approx hN hΓs hlim f hf
    have hc := tendsto_cost hN hΓ hΓs hlim fs hfs f hfsl
    have := (Metric.tendsto_atTop.1 hc) (ε / 2) (by linarith)
    obtain ⟨n0, h0⟩ := this
    refine eventually_atTop.2 ⟨n0, fun n hn => ?_⟩
    have h1 := h0 n hn
    rw [Real.dist_eq, abs_lt] at h1
    have h2 := SOCost_le hN (Γs n) (hΓs n).1 (fs n) (hfs n)
    linarith
  -- lower bound
  have hlow : ∀ᶠ n in atTop, SOCost Γ - ε < SOCost (Γs n) := by
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨ψ, hψ, hψP⟩ := extraction_of_frequently_atTop hcon
    have hlim' := tendsto_comp_sub hlim ψ hψ
    have hΓs' : ∀ n, Γs (ψ n) ∈ gameSpace N := fun n => hΓs _
    choose g hg hgc using fun n => exists_near_SO hN (Γs (ψ n)) (hΓs (ψ n)).1
      (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    obtain ⟨f, φ, hφ, hfl⟩ := exists_subseq hlim' g hg
    have hlim'' := tendsto_comp_sub hlim' φ hφ
    have hfΓ : IsFlow Γ f := isFlow_of_tendsto hlim'' (g ∘ φ) (fun n => hg _) f hfl
    have hc := tendsto_cost hN hΓ (fun n => hΓs _) hlim'' (g ∘ φ) (fun n => hg _) f hfl
    have hle := SOCost_le hN Γ hΓ.1 f hfΓ
    have hsmall : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have := (Metric.tendsto_atTop.1 hc) (ε / 2) (by linarith)
    obtain ⟨n0, h0⟩ := this
    obtain ⟨n1, h1⟩ := (Metric.tendsto_atTop.1 hsmall) (ε / 2) (by linarith)
    have a := h0 (max n0 n1) (le_max_left _ _)
    have b := h1 (max n0 n1) (le_max_right _ _)
    have c := hgc (φ (max n0 n1))
    have d := hψP (φ (max n0 n1))
    simp only [Function.comp] at a
    rw [Real.dist_eq, abs_lt] at a b
    push_neg at d
    linarith
  obtain ⟨n0, h0⟩ := eventually_atTop.1 (hup.and hlow)
  refine ⟨n0, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have := h0 n hn
  constructor <;> linarith

end Seq

end SensitivityPoA.Continuity.PoA2Aux


namespace SensitivityPoA.Continuity.PoA2Aux

open KellyStochasticNetworks SensitivityPoA.Continuity Filter Topology

lemma sum_tau_linkFlow {N : Network} (Γ : Game N) (f g : Fin N.R → ℝ) :
    (∑ j, Γ.τ j (linkFlow N.A f j) * linkFlow N.A g j) = ∑ r, g r * pathCost Γ f r := by
  show (∑ j, Γ.τ j (linkFlow N.A f j) * ∑ r, N.A j r * g r) =
    ∑ r, g r * ∑ j, Γ.τ j (linkFlow N.A f j) * N.A j r
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

lemma cost_eq {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) :
    cost Γ f = ∑ j, Γ.τ j (linkFlow N.A f j) * linkFlow N.A f j := by
  unfold cost
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- A Wardrop equilibrium solves the variational inequality. -/
lemma we_vi {N : Network} (hN : N.Standing) (Γ : Game N) (f g : Fin N.R → ℝ)
    (hf : IsWE Γ f) (hg : IsFlow Γ g) :
    (∑ j, Γ.τ j (linkFlow N.A f j) * linkFlow N.A f j) ≤
      ∑ j, Γ.τ j (linkFlow N.A f j) * linkFlow N.A g j := by
  rw [sum_tau_linkFlow, sum_tau_linkFlow]
  rw [← Finset.sum_fiberwise Finset.univ N.s (fun r => f r * pathCost Γ f r),
    ← Finset.sum_fiberwise Finset.univ N.s (fun r => g r * pathCost Γ f r)]
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hne : (Finset.univ.filter (fun r => N.s r = k)).Nonempty := by
    rw [← Finset.card_pos]; have := hN.2.2.2.2 k; omega
  obtain ⟨r0, hr0, hmin⟩ := Finset.exists_min_image _ (pathCost Γ f) hne
  rw [Finset.mem_filter] at hr0
  calc (∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r * pathCost Γ f r)
      ≤ ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r * pathCost Γ f r0 := by
        refine Finset.sum_le_sum (fun r hr => ?_)
        rw [Finset.mem_filter] at hr
        rcases (hf.1.1 r).lt_or_eq with h | h
        · exact mul_le_mul_of_nonneg_left (hf.2 r r0 (by rw [hr0.2, hr.2]) h) (hf.1.1 r)
        · rw [← h]; simp
    _ = ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), g r * pathCost Γ f r0 := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hf.1.2 k, hg.2 k]
    _ ≤ ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), g r * pathCost Γ f r := by
        refine Finset.sum_le_sum (fun r hr => ?_)
        exact mul_le_mul_of_nonneg_left (hmin r hr) (hg.1 r)

/-- All Wardrop equilibria have the same cost. -/
lemma we_cost_unique {N : Network} (hN : N.Standing) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (f g : Fin N.R → ℝ) (hf : IsWE Γ f) (hg : IsWE Γ g) : cost Γ f = cost Γ g := by
  have v1 := we_vi hN Γ f g hf hg.1
  have v2 := we_vi hN Γ g f hg hf.1
  set F := linkFlow N.A f
  set G := linkFlow N.A g
  have hF0 := linkFlow_nonneg hN hf.1.1
  have hG0 := linkFlow_nonneg hN hg.1.1
  have hterm : ∀ j, 0 ≤ (Γ.τ j (F j) - Γ.τ j (G j)) * (F j - G j) := by
    intro j
    rcases le_total (F j) (G j) with h | h
    · have := (hΓ.1 j).2.1 (Set.mem_Ici.2 (hF0 j)) (Set.mem_Ici.2 (hG0 j)) h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have := (hΓ.1 j).2.1 (Set.mem_Ici.2 (hG0 j)) (Set.mem_Ici.2 (hF0 j)) h
      exact mul_nonneg (by linarith) (by linarith)
  have hsum : (∑ j, (Γ.τ j (F j) - Γ.τ j (G j)) * (F j - G j)) = 0 := by
    apply le_antisymm _ (Finset.sum_nonneg (fun j _ => hterm j))
    have : (∑ j, (Γ.τ j (F j) - Γ.τ j (G j)) * (F j - G j)) =
        ((∑ j, Γ.τ j (F j) * F j) - ∑ j, Γ.τ j (F j) * G j) +
        ((∑ j, Γ.τ j (G j) * G j) - ∑ j, Γ.τ j (G j) * F j) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this]; linarith
  have heq : ∀ j, Γ.τ j (F j) = Γ.τ j (G j) := by
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).1 hsum j (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · rw [show F j = G j by linarith]
  rw [cost_eq, cost_eq]
  apply le_antisymm
  · refine le_trans v1 (le_of_eq (Finset.sum_congr rfl (fun j _ => by rw [heq j])))
  · refine le_trans v2 (le_of_eq (Finset.sum_congr rfl (fun j _ => by rw [heq j])))

section Seq

variable {N : Network} {Γ : Game N} {Γs : ℕ → Game N}

lemma isWE_of_tendsto (hN : N.Standing) (hΓ : Γ ∈ gameSpace N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0))
    (fs : ℕ → Fin N.R → ℝ) (hfs : ∀ n, IsWE (Γs n) (fs n)) (f : Fin N.R → ℝ)
    (hf : Tendsto fs atTop (𝓝 f)) : IsWE Γ f := by
  have hfl : ∀ n, IsFlow (Γs n) (fs n) := fun n => (hfs n).1
  refine ⟨isFlow_of_tendsto hlim fs hfl f hf, fun r r' hs hpos => ?_⟩
  have hev : ∀ᶠ n in atTop, 0 < fs n r :=
    (tendsto_pi_nhds.1 hf r).eventually (lt_mem_nhds hpos)
  have h1 := tendsto_pathCost hN hΓ hΓs hlim fs hfl f hf r
  have h2 := tendsto_pathCost hN hΓ hΓs hlim fs hfl f hf r'
  exact le_of_tendsto_of_tendsto h1 h2 (hev.mono (fun n hn => (hfs n).2 r r' hs hn))

end Seq

/-- The extended latency. -/
noncomputable def tauHat {N : Network} (Γ : Game N) (j : Fin N.J) (x : ℝ) : ℝ :=
  Γ.τ j (max x 0)

lemma tauHat_cont {N : Network} (Γ : Game N) (hΓ : Γ.IsGeneralized) (j : Fin N.J) :
    Continuous (tauHat Γ j) :=
  (hΓ.1 j).1.comp_continuous (continuous_id.max continuous_const)
    (fun x => Set.mem_Ici.2 (le_max_right _ _))

noncomputable def Phi {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : ℝ :=
  ∑ j, ∫ u in (0:ℝ)..(linkFlow N.A f j), tauHat Γ j u

lemma prim_cont (g : ℝ → ℝ) (hg : Continuous g) : Continuous (fun u => ∫ x in (0:ℝ)..u, g x) :=
  continuous_iff_continuousAt.2 (fun u => (hg.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt)

lemma Phi_cont {N : Network} (Γ : Game N) (hΓ : Γ.IsGeneralized) : Continuous (Phi Γ) := by
  unfold Phi
  refine continuous_finset_sum _ (fun j _ => ?_)
  refine (prim_cont _ (tauHat_cont Γ hΓ j)).comp ?_
  unfold linkFlow
  exact continuous_finset_sum _ (fun r _ => continuous_const.mul (continuous_apply r))

lemma flowSet_compact {N : Network} (Γ : Game N) : IsCompact {f : Fin N.R → ℝ | IsFlow Γ f} := by
  have hset : {f : Fin N.R → ℝ | IsFlow Γ f} = (⋂ r, {f : Fin N.R → ℝ | 0 ≤ f r}) ∩
      ⋂ k, {f : Fin N.R → ℝ | (∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r) = Γ.d k} := by
    ext f; simp [IsFlow, wardropFeasible, Set.mem_iInter]
  have hcl : IsClosed {f : Fin N.R → ℝ | IsFlow Γ f} := by
    rw [hset]
    exact (isClosed_iInter fun r => isClosed_le continuous_const (continuous_apply r)).inter
      (isClosed_iInter fun k => isClosed_eq
        (continuous_finset_sum _ fun r _ => continuous_apply r) continuous_const)
  refine (isCompact_Icc (a := (0 : Fin N.R → ℝ)) (b := fun _ => totalDemand Γ.d)).of_isClosed_subset
    hcl ?_
  intro f hf
  exact ⟨fun r => hf.1 r, fun r => flow_le hf r⟩

/-- Existence of a Wardrop equilibrium (Beckmann's potential). -/
lemma we_exists {N : Network} (hN : N.Standing) (Γ : Game N) (hΓ : Γ.IsGeneralized) :
    ∃ f, IsWE Γ f := by
  classical
  obtain ⟨f, hf, hmin⟩ := (flowSet_compact Γ).exists_isMinOn (flow_exists hN Γ hΓ)
    (Phi_cont Γ hΓ).continuousOn
  refine ⟨f, hf, fun r r' hs hpos => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hrr : r ≠ r' := by rintro rfl; exact lt_irrefl _ hcon
  let v : Fin N.R → ℝ := fun x => (if x = r' then 1 else 0) - (if x = r then 1 else 0)
  let a : Fin N.J → ℝ := fun j => N.A j r' - N.A j r
  have hlink : ∀ t j, linkFlow N.A (fun x => f x + t * v x) j = linkFlow N.A f j + t * a j := by
    intro t j
    unfold linkFlow
    simp only [v, a, mul_add, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hfeas : ∀ t, 0 ≤ t → t ≤ f r → IsFlow Γ (fun x => f x + t * v x) := by
    intro t ht0 htr
    refine ⟨fun x => ?_, fun k => ?_⟩
    · simp only [v]
      by_cases hx : x = r
      · subst hx
        simp only [if_neg hrr, if_true]
        linarith
      · simp only [if_neg hx]
        have := hf.1 x
        split_ifs <;> nlinarith
    · rw [Finset.sum_add_distrib, hf.2 k, ← Finset.mul_sum]
      simp only [v, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [hs]; simp
  let φ : ℝ → ℝ := fun t => ∑ j, ∫ u in (0:ℝ)..(linkFlow N.A f j + t * a j), tauHat Γ j u
  have hφ : ∀ t, Phi Γ (fun x => f x + t * v x) = φ t := by
    intro t; unfold Phi; simp only [φ, hlink]
  have hD : HasDerivAt φ (∑ j, tauHat Γ j (linkFlow N.A f j) * a j) 0 := by
    refine HasDerivAt.fun_sum (fun j _ => ?_)
    have h1 := ((tauHat_cont Γ hΓ j).integral_hasStrictDerivAt 0
      (linkFlow N.A f j + 0 * a j)).hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => linkFlow N.A f j + t * a j) (1 * a j) 0 :=
      ((hasDerivAt_id (0:ℝ)).mul_const (a j)).const_add _
    have := h1.comp (0:ℝ) h2
    simp only [zero_mul, add_zero, one_mul] at this
    exact this
  have hDval : (∑ j, tauHat Γ j (linkFlow N.A f j) * a j) = pathCost Γ f r' - pathCost Γ f r := by
    unfold pathCost
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [tauHat, a, max_eq_left (linkFlow_nonneg hN hf.1 j)]
    ring
  have hneg : (∑ j, tauHat Γ j (linkFlow N.A f j) * a j) < 0 := by
    rw [hDval]; unfold pathCost; linarith
  rw [hasDerivAt_iff_tendsto_slope] at hD
  have hD' := hD.mono_left (nhdsWithin_mono _ (fun x (hx : x ∈ Set.Ioi (0:ℝ)) =>
    (ne_of_gt (Set.mem_Ioi.1 hx) : x ≠ 0)))
  have e1 : ∀ᶠ t in 𝓝[>] (0:ℝ), slope φ 0 t < 0 := hD'.eventually (gt_mem_nhds hneg)
  have e2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo 0 (f r) := Ioo_mem_nhdsGT hpos
  obtain ⟨t, ht1, ht2⟩ := (e1.and e2).exists
  rw [slope_def_field, sub_zero] at ht1
  have hlt : φ t < φ 0 := by
    have := ht2.1
    by_contra hc; push_neg at hc
    have : 0 ≤ (φ t - φ 0) / t := div_nonneg (by linarith) this.le
    linarith
  have hmt := hmin (hfeas t ht2.1.le ht2.2.le)
  simp only [Set.mem_setOf_eq] at hmt
  rw [hφ] at hmt
  have h0 : Phi Γ f = φ 0 := by
    rw [← hφ]; congr 1; funext x; simp
  linarith

lemma WECost_eq {N : Network} (hN : N.Standing) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (f : Fin N.R → ℝ) (hf : IsWE Γ f) : WECost Γ = cost Γ f := by
  unfold WECost
  have : cost Γ '' {f | IsWE Γ f} = {cost Γ f} := by
    ext c
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact we_cost_unique hN Γ hΓ g f hg hf
    · rintro rfl; exact ⟨f, hf, rfl⟩
  rw [this, csSup_singleton]

section Seq

variable {N : Network} {Γ : Game N} {Γs : ℕ → Game N}

/-- Lemma 5c (cost part). -/
lemma tendsto_WECost (hN : N.Standing) (hΓ : Γ ∈ gameSpace N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0)) :
    Tendsto (fun n => WECost (Γs n)) atTop (𝓝 (WECost Γ)) := by
  choose w hw using fun n => we_exists hN (Γs n) (hΓs n).1
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hlim1 : Tendsto (fun n => gameDist (Γs (ns n)) Γ) atTop (𝓝 0) := hlim.comp hns
  obtain ⟨f, φ, hφ, hfl⟩ := exists_subseq hlim1 (fun n => w (ns n)) (fun n => (hw _).1)
  have hlim2 : Tendsto (fun n => gameDist (Γs (ns (φ n))) Γ) atTop (𝓝 0) :=
    hlim1.comp hφ.tendsto_atTop
  have hfwe : IsWE Γ f :=
    isWE_of_tendsto hN hΓ (fun n => hΓs _) hlim2 _ (fun n => hw _) f hfl
  have hc := tendsto_cost hN hΓ (fun n => hΓs _) hlim2 _ (fun n => (hw _).1) f hfl
  refine ⟨φ, ?_⟩
  rw [WECost_eq hN Γ hΓ.1 f hfwe]
  refine hc.congr (fun n => ?_)
  exact (WECost_eq hN _ (hΓs _).1 _ (hw _)).symm

end Seq

end SensitivityPoA.Continuity.PoA2Aux


namespace SensitivityPoA.Continuity.PoA2Aux

open KellyStochasticNetworks SensitivityPoA.Continuity Filter Topology

lemma R_pos {N : Network} (hN : N.Standing) : 0 < N.R := by
  have k : Fin N.Sd := ⟨0, hN.2.2.1⟩
  have := hN.2.2.2.2 k
  have h2 := Finset.card_le_univ (Finset.univ.filter (fun r => N.s r = k))
  simp only [Fintype.card_fin] at h2
  omega

lemma cost_lower {N : Network} (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N) :
    ∃ c, 0 < c ∧ ∀ f, IsFlow Γ f → c ≤ cost Γ f := by
  set T := totalDemand Γ.d
  have hT : 0 < T := hΓ.2.1
  have hR : (0 : ℝ) < N.R := by exact_mod_cast R_pos hN
  have hR1 : (1 : ℝ) ≤ N.R := by exact_mod_cast R_pos hN
  set t := T / (N.R : ℝ)
  have ht0 : 0 < t := div_pos hT hR
  have htT : t ≤ T := div_le_self hT.le hR1
  have hJ : (Finset.univ : Finset (Fin N.J)).Nonempty := by
    obtain ⟨j, _⟩ := hN.2.1 ⟨0, R_pos hN⟩
    exact ⟨j, Finset.mem_univ _⟩
  obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image _ (fun j => Γ.τ j t) hJ
  have hm : 0 < Γ.τ j0 t := hΓ.2.2 j0 t ht0 htT
  refine ⟨t * Γ.τ j0 t, mul_pos ht0 hm, fun f hf => ?_⟩
  have hne : (Finset.univ : Finset (Fin N.R)).Nonempty := ⟨⟨0, R_pos hN⟩, Finset.mem_univ _⟩
  obtain ⟨r, -, hr⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => t) (g := f) (by
      rw [sum_flow_eq hf, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [t]; field_simp; exact le_rfl)
  obtain ⟨j, hj⟩ := hN.2.1 r
  have hF := linkFlow_ge_path hN hf.1 j r hj
  have hF0 := linkFlow_nonneg hN hf.1
  have hmono := (hΓ.1.1 j).2.1 (Set.mem_Ici.2 ht0.le) (Set.mem_Ici.2 (hF0 j)) (le_trans hr hF)
  calc t * Γ.τ j0 t ≤ t * Γ.τ j t := mul_le_mul_of_nonneg_left (hj0 j (Finset.mem_univ _)) ht0.le
    _ ≤ linkFlow N.A f j * Γ.τ j (linkFlow N.A f j) :=
        mul_le_mul (le_trans hr hF) hmono (le_of_lt (lt_of_lt_of_le hm (hj0 j (Finset.mem_univ _))))
          (hF0 j)
    _ ≤ cost Γ f := by
        unfold cost
        exact Finset.single_le_sum (f := fun j => linkFlow N.A f j * Γ.τ j (linkFlow N.A f j))
          (fun i _ => mul_nonneg (hF0 i) ((hΓ.1.1 i).2.2 _ (hF0 i))) (Finset.mem_univ j)

lemma SOCost_pos {N : Network} (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N) :
    0 < SOCost Γ := by
  obtain ⟨c, hc, h⟩ := cost_lower hN Γ hΓ
  exact lt_of_lt_of_le hc (le_SOCost hN Γ hΓ.1 c h)

end SensitivityPoA.Continuity.PoA2Aux



namespace SensitivityPoA.Continuity.PoA2Aux

open KellyStochasticNetworks SensitivityPoA.Continuity Filter Topology

lemma SO_cost_eq {N : Network} (hN : N.Standing) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (f : Fin N.R → ℝ) (hf : IsSO Γ f) : SOCost Γ = cost Γ f :=
  le_antisymm (SOCost_le hN Γ hΓ f hf.1) (le_SOCost hN Γ hΓ _ hf.2)

section Seq

variable {N : Network} {Γ : Game N} {Γs : ℕ → Game N}

lemma isSO_of_tendsto (hN : N.Standing) (hΓ : Γ ∈ gameSpace N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Tendsto (fun n => gameDist (Γs n) Γ) atTop (𝓝 0))
    (fs : ℕ → Fin N.R → ℝ) (hfs : ∀ n, IsSO (Γs n) (fs n)) (f : Fin N.R → ℝ)
    (hf : Tendsto fs atTop (𝓝 f)) : IsSO Γ f := by
  have hfl : ∀ n, IsFlow (Γs n) (fs n) := fun n => (hfs n).1
  have hF := isFlow_of_tendsto hlim fs hfl f hf
  have hc := tendsto_cost hN hΓ hΓs hlim fs hfl f hf
  have hs := tendsto_SOCost hN hΓ hΓs hlim
  have : cost Γ f = SOCost Γ := by
    refine tendsto_nhds_unique hc (hs.congr (fun n => ?_))
    exact SO_cost_eq hN _ (hΓs n).1 _ (hfs n)
  refine ⟨hF, fun g hg => ?_⟩
  rw [this]; exact SOCost_le hN Γ hΓ.1 g hg

end Seq

end SensitivityPoA.Continuity.PoA2Aux

namespace SensitivityPoA.Continuity.PoA2Aux
open KellyStochasticNetworks SensitivityPoA.Continuity Filter Topology

theorem m_lemma_5_b (N : Network) (hN : N.Standing)
    (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (Γs : ℕ → Game N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Filter.Tendsto (fun n => gameDist (Γs n) Γ) Filter.atTop (nhds 0))
    (fs : ℕ → Fin N.R → ℝ) (hfs : ∀ n, IsSO (Γs n) (fs n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (fstar : Fin N.R → ℝ) (hfstar : ∀ r, 0 ≤ fstar r)
    (hsub : Filter.Tendsto (fun i => fs (φ i)) Filter.atTop (nhds fstar)) :
    IsSO Γ fstar ∧
    ((∃! g : Fin N.R → ℝ, IsSO Γ g) →
      ∃ g : Fin N.R → ℝ, IsSO Γ g ∧ Filter.Tendsto fs Filter.atTop (nhds g)) ∧
    Filter.Tendsto (fun n => SOCost (Γs n)) Filter.atTop (nhds (SOCost Γ)) := by
  refine ⟨isSO_of_tendsto hN hΓ (fun n => hΓs _) (hlim.comp hφ.tendsto_atTop) _
    (fun n => hfs _) fstar hsub, fun ⟨g, hg, huniq⟩ => ⟨g, hg, ?_⟩,
    tendsto_SOCost hN hΓ hΓs hlim⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hlim1 : Tendsto (fun n => gameDist (Γs (ns n)) Γ) atTop (𝓝 0) := hlim.comp hns
  obtain ⟨f, ψ, hψ, hfl⟩ := exists_subseq hlim1 (fun n => fs (ns n)) (fun n => (hfs _).1)
  have hlim2 : Tendsto (fun n => gameDist (Γs (ns (ψ n))) Γ) atTop (𝓝 0) :=
    hlim1.comp hψ.tendsto_atTop
  have hso := isSO_of_tendsto hN hΓ (fun n => hΓs _) hlim2 _ (fun n => hfs _) f hfl
  rw [huniq f hso] at hfl
  exact ⟨ψ, hfl⟩

theorem m_lemma_5_c (N : Network) (hN : N.Standing)
    (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (Γs : ℕ → Game N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Filter.Tendsto (fun n => gameDist (Γs n) Γ) Filter.atTop (nhds 0))
    (fs : ℕ → Fin N.R → ℝ) (hfs : ∀ n, IsWE (Γs n) (fs n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (fwe : Fin N.R → ℝ) (hfwe : ∀ r, 0 ≤ fwe r)
    (hsub : Filter.Tendsto (fun i => fs (φ i)) Filter.atTop (nhds fwe)) :
    IsWE Γ fwe ∧
    ((∃! g : Fin N.R → ℝ, IsWE Γ g) →
      ∃ g : Fin N.R → ℝ, IsWE Γ g ∧ Filter.Tendsto fs Filter.atTop (nhds g)) ∧
    Filter.Tendsto (fun n => WECost (Γs n)) Filter.atTop (nhds (WECost Γ)) := by
  refine ⟨isWE_of_tendsto hN hΓ (fun n => hΓs _) (hlim.comp hφ.tendsto_atTop) _
    (fun n => hfs _) fwe hsub, fun ⟨g, hg, huniq⟩ => ⟨g, hg, ?_⟩,
    tendsto_WECost hN hΓ hΓs hlim⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hlim1 : Tendsto (fun n => gameDist (Γs (ns n)) Γ) atTop (𝓝 0) := hlim.comp hns
  obtain ⟨f, ψ, hψ, hfl⟩ := exists_subseq hlim1 (fun n => fs (ns n)) (fun n => (hfs _).1)
  have hlim2 : Tendsto (fun n => gameDist (Γs (ns (ψ n))) Γ) atTop (𝓝 0) :=
    hlim1.comp hψ.tendsto_atTop
  have hwe := isWE_of_tendsto hN hΓ (fun n => hΓs _) hlim2 _ (fun n => hfs _) f hfl
  rw [huniq f hwe] at hfl
  exact ⟨ψ, hfl⟩

lemma minArc_le {N : Network} (Γ : Game N) (x : ℝ) (j : Fin N.J) : minArc Γ x ≤ Γ.τ j x :=
  csInf_le (Set.finite_range _).bddBelow ⟨j, rfl⟩

lemma le_maxArc {N : Network} (Γ : Game N) (x : ℝ) (j : Fin N.J) : Γ.τ j x ≤ maxArc Γ x :=
  le_csSup (Set.finite_range _).bddAbove ⟨j, rfl⟩

lemma minArc_pos {N : Network} (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (x : ℝ) (hx : 0 < x) (hxT : x ≤ totalDemand Γ.d) : 0 < minArc Γ x := by
  have : Nonempty (Fin N.J) := by
    obtain ⟨j, _⟩ := hN.2.1 ⟨0, R_pos hN⟩
    exact ⟨j⟩
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun j : Fin N.J => Γ.τ j x)
  have h : minArc Γ x = Γ.τ j x := hj.symm
  rw [h]; exact hΓ.2.2 j x hx hxT

lemma cost_ge_min {N : Network} (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (f : Fin N.R → ℝ) (hf : IsFlow Γ f) :
    totalDemand Γ.d / (N.R : ℝ) * minArc Γ (totalDemand Γ.d / (N.R : ℝ)) ≤ cost Γ f := by
  set T := totalDemand Γ.d
  have hT : 0 < T := hΓ.2.1
  have hR : (0 : ℝ) < N.R := by exact_mod_cast R_pos hN
  set t := T / (N.R : ℝ)
  have ht0 : 0 < t := div_pos hT hR
  have hne : (Finset.univ : Finset (Fin N.R)).Nonempty := ⟨⟨0, R_pos hN⟩, Finset.mem_univ _⟩
  obtain ⟨r, -, hr⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => t) (g := f) (by
      rw [sum_flow_eq hf, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [t]; field_simp; exact le_rfl)
  obtain ⟨j, hj⟩ := hN.2.1 r
  have hF := linkFlow_ge_path hN hf.1 j r hj
  have hF0 := linkFlow_nonneg hN hf.1
  have hmono := (hΓ.1.1 j).2.1 (Set.mem_Ici.2 ht0.le) (Set.mem_Ici.2 (hF0 j)) (le_trans hr hF)
  have hτt := (hΓ.1.1 j).2.2 t ht0.le
  calc t * minArc Γ t ≤ t * Γ.τ j t := mul_le_mul_of_nonneg_left (minArc_le Γ t j) ht0.le
    _ ≤ linkFlow N.A f j * Γ.τ j (linkFlow N.A f j) :=
        mul_le_mul (le_trans hr hF) hmono hτt (hF0 j)
    _ ≤ cost Γ f := by
        unfold cost
        exact Finset.single_le_sum (f := fun j => linkFlow N.A f j * Γ.τ j (linkFlow N.A f j))
          (fun i _ => mul_nonneg (hF0 i) ((hΓ.1.1 i).2.2 _ (hF0 i))) (Finset.mem_univ j)

lemma cost_le_max {N : Network} (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (f : Fin N.R → ℝ) (hf : IsFlow Γ f) :
    cost Γ f ≤ (N.J : ℝ) * totalDemand Γ.d * maxArc Γ (totalDemand Γ.d) := by
  set T := totalDemand Γ.d
  have hT : 0 < T := hΓ.2.1
  have hF0 := linkFlow_nonneg hN hf.1
  unfold cost
  calc (∑ j, linkFlow N.A f j * Γ.τ j (linkFlow N.A f j))
      ≤ ∑ _j : Fin N.J, T * maxArc Γ T := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hle := linkFlow_le hN hf j
        have hmono := (hΓ.1.1 j).2.1 (Set.mem_Ici.2 (hF0 j)) (Set.mem_Ici.2 hT.le) hle
        have h0 := (hΓ.1.1 j).2.2 _ (hF0 j)
        calc linkFlow N.A f j * Γ.τ j (linkFlow N.A f j) ≤ T * Γ.τ j T :=
              mul_le_mul hle hmono h0 hT.le
          _ ≤ T * maxArc Γ T := mul_le_mul_of_nonneg_left (le_maxArc Γ T j) hT.le
    _ = (N.J : ℝ) * T * maxArc Γ T := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem m_lemma_3 (N : Network) (hN : N.Standing)
    (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (f fwe fso : Fin N.R → ℝ)
    (hf : IsFlow Γ f) (hwe : IsWE Γ fwe) (hso : IsSO Γ fso) :
    (∀ j, 0 ≤ KellyStochasticNetworks.linkFlow N.A f j ∧ KellyStochasticNetworks.linkFlow N.A f j ≤ totalDemand Γ.d) ∧
    0 < totalDemand Γ.d / (N.R : ℝ) *
      minArc Γ (totalDemand Γ.d / (N.R : ℝ)) ∧
    totalDemand Γ.d / (N.R : ℝ) *
      minArc Γ (totalDemand Γ.d / (N.R : ℝ)) ≤ cost Γ fso ∧
    cost Γ fso ≤ cost Γ fwe ∧
    cost Γ fwe ≤ (N.J : ℝ) * totalDemand Γ.d *
      maxArc Γ (totalDemand Γ.d) ∧
    1 ≤ PoA Γ ∧
    PoA Γ ≤ (N.J : ℝ) * (N.R : ℝ) *
      maxArc Γ (totalDemand Γ.d) /
      minArc Γ (totalDemand Γ.d / (N.R : ℝ)) := by
  set T := totalDemand Γ.d
  have hT : 0 < T := hΓ.2.1
  have hR : (0 : ℝ) < N.R := by exact_mod_cast R_pos hN
  have hR1 : (1 : ℝ) ≤ N.R := by exact_mod_cast R_pos hN
  have ht0 : 0 < T / (N.R : ℝ) := div_pos hT hR
  have hm := minArc_pos hN Γ hΓ (T / N.R) ht0 (div_le_self hT.le hR1)
  have hlow := cost_ge_min hN Γ hΓ fso hso.1
  have hpos : 0 < T / (N.R : ℝ) * minArc Γ (T / (N.R : ℝ)) := mul_pos ht0 hm
  have hsowe := hso.2 fwe hwe.1
  have hup := cost_le_max hN Γ hΓ fwe hwe.1
  have hPoA : PoA Γ = cost Γ fwe / cost Γ fso := by
    unfold PoA; rw [WECost_eq hN Γ hΓ.1 fwe hwe, SO_cost_eq hN Γ hΓ.1 fso hso]
  have hcso : 0 < cost Γ fso := lt_of_lt_of_le hpos hlow
  refine ⟨fun j => ⟨linkFlow_nonneg hN hf.1 j, linkFlow_le hN hf j⟩, hpos, hlow, hsowe, hup,
    ?_, ?_⟩
  · rw [hPoA, one_le_div hcso]; exact hsowe
  · rw [hPoA]
    have hM0 : 0 ≤ (N.J : ℝ) * T * maxArc Γ T := le_trans (le_trans hcso.le hsowe) hup
    calc cost Γ fwe / cost Γ fso ≤ ((N.J : ℝ) * T * maxArc Γ T) /
          (T / (N.R : ℝ) * minArc Γ (T / (N.R : ℝ))) :=
          div_le_div₀ hM0 hup hpos hlow
      _ = (N.J : ℝ) * (N.R : ℝ) * maxArc Γ T / minArc Γ (T / (N.R : ℝ)) := by
          field_simp

end SensitivityPoA.Continuity.PoA2Aux


namespace SensitivityPoA.Continuity.PoA2Aux

open KellyStochasticNetworks SensitivityPoA.Continuity Filter Topology

lemma T_nonneg {N : Network} (Γ : Game N) (hΓ : Γ.IsGeneralized) : 0 ≤ totalDemand Γ.d :=
  Finset.sum_nonneg (fun k _ => hΓ.2 k)

lemma gameDist_nonneg {N : Network} (Γ Γ' : Game N) : 0 ≤ gameDist Γ Γ' :=
  le_trans (norm_nonneg _) (demand_le_dist _ _)

lemma sup_le_of {N : Network} (Γ Γ' : Game N) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ j y, 0 ≤ y → y ≤ min (totalDemand Γ.d) (totalDemand Γ'.d) →
      |Γ.τ j y - Γ'.τ j y| ≤ c) :
    sSup ((fun p : Fin N.J × ℝ => |Γ.τ p.1 p.2 - Γ'.τ p.1 p.2|) ''
        (Set.univ ×ˢ Set.Icc 0 (min (totalDemand Γ.d) (totalDemand Γ'.d)))) ≤ c := by
  refine Real.sSup_le ?_ hc
  rintro _ ⟨⟨j, y⟩, ⟨-, hy⟩, rfl⟩
  exact h j y hy.1 hy.2

lemma gameDist_le_of {N : Network} (Γ Γ' : Game N) (c : ℝ) (hc : 0 ≤ c)
    (h1 : ‖Γ.d - Γ'.d‖ ≤ c)
    (h2 : ∀ j y, 0 ≤ y → y ≤ min (totalDemand Γ.d) (totalDemand Γ'.d) →
      |Γ.τ j y - Γ'.τ j y| ≤ c)
    (h3 : ∀ j, |Γ.τ j (totalDemand Γ.d) - Γ'.τ j (totalDemand Γ'.d)| ≤ c) :
    gameDist Γ Γ' ≤ c := by
  unfold gameDist
  refine max_le h1 (max_le (sup_le_of Γ Γ' c hc h2) ?_)
  refine (pi_norm_le_iff_of_nonneg hc).2 (fun j => ?_)
  rw [Real.norm_eq_abs]; exact h3 j

lemma gameDist_symm_le {N : Network} (Γ Γ' : Game N) (hΓ : Γ.IsGeneralized)
    (hΓ' : Γ'.IsGeneralized) : gameDist Γ Γ' ≤ gameDist Γ' Γ := by
  refine gameDist_le_of Γ Γ' _ (gameDist_nonneg _ _) ?_ ?_ ?_
  · rw [norm_sub_rev]; exact demand_le_dist _ _
  · intro j y hy0 hy
    rw [abs_sub_comm]; exact unif_le_dist Γ' Γ hΓ' hΓ j y hy0 (by rw [min_comm]; exact hy)
  · intro j; rw [abs_sub_comm]; exact endpoint_le_dist Γ' Γ j

theorem m_lemma_4_ab (N : Network) (hN : N.Standing)
    (Γ₁ Γ₂ Γ₃ : Game N)
    (h₁ : Γ₁.IsGeneralized) (h₂ : Γ₂.IsGeneralized)
    (h₃ : Γ₃.IsGeneralized) :
    gameDist Γ₁ Γ₂ = gameDist Γ₂ Γ₁ ∧
    0 ≤ gameDist Γ₁ Γ₂ ∧
    (gameDist Γ₁ Γ₂ = 0 ↔ Γ₁.Equiv Γ₂) := by
  refine ⟨le_antisymm (gameDist_symm_le _ _ h₁ h₂) (gameDist_symm_le _ _ h₂ h₁),
    gameDist_nonneg _ _, ⟨fun h0 => ?_, fun ⟨hd, hτ⟩ => ?_⟩⟩
  · have hd : Γ₁.d = Γ₂.d := by
      have := demand_le_dist Γ₁ Γ₂
      rw [h0] at this
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    refine ⟨hd, fun j x hx => ?_⟩
    have := unif_le_dist Γ₁ Γ₂ h₁ h₂ j x hx.1 (by rw [← hd, min_self]; exact hx.2)
    rw [h0] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  · apply le_antisymm _ (gameDist_nonneg _ _)
    have hT : totalDemand Γ₁.d = totalDemand Γ₂.d := by rw [hd]
    refine gameDist_le_of Γ₁ Γ₂ 0 le_rfl ?_ ?_ ?_
    · rw [hd, sub_self, norm_zero]
    · intro j y hy0 hy
      rw [← hT, min_self] at hy
      rw [hτ j y ⟨hy0, hy⟩, sub_self, abs_zero]
    · intro j
      rw [← hT, hτ j _ ⟨T_nonneg Γ₁ h₁, le_rfl⟩, sub_self, abs_zero]

theorem m_lemma_4_c (N : Network) (hN : N.Standing)
    (Γ₁ Γ₂ Γ₃ : Game N)
    (h₁ : Γ₁.IsGeneralized) (h₂ : Γ₂.IsGeneralized)
    (h₃ : Γ₃.IsGeneralized) :
    gameDist Γ₁ Γ₂ ≤ gameDist Γ₁ Γ₃ + gameDist Γ₃ Γ₂ := by
  set D13 := gameDist Γ₁ Γ₃
  set D32 := gameDist Γ₃ Γ₂
  have hD13 := gameDist_nonneg Γ₁ Γ₃
  have hD32 := gameDist_nonneg Γ₃ Γ₂
  set T1 := totalDemand Γ₁.d
  set T2 := totalDemand Γ₂.d
  set T3 := totalDemand Γ₃.d
  have hT3 : 0 ≤ T3 := T_nonneg Γ₃ h₃
  refine gameDist_le_of Γ₁ Γ₂ _ (add_nonneg hD13 hD32) ?_ ?_ ?_
  · calc ‖Γ₁.d - Γ₂.d‖ = ‖(Γ₁.d - Γ₃.d) + (Γ₃.d - Γ₂.d)‖ := by congr 1; abel
      _ ≤ ‖Γ₁.d - Γ₃.d‖ + ‖Γ₃.d - Γ₂.d‖ := norm_add_le _ _
      _ ≤ D13 + D32 := add_le_add (demand_le_dist _ _) (demand_le_dist _ _)
  · intro j y hy0 hy
    have hy1 : y ≤ T1 := le_trans hy (min_le_left _ _)
    have hy2 : y ≤ T2 := le_trans hy (min_le_right _ _)
    by_cases hc : y ≤ T3
    · have a := unif_le_dist Γ₁ Γ₃ h₁ h₃ j y hy0 (le_min hy1 hc)
      have b := unif_le_dist Γ₃ Γ₂ h₃ h₂ j y hy0 (le_min hc hy2)
      calc |Γ₁.τ j y - Γ₂.τ j y| ≤ |Γ₁.τ j y - Γ₃.τ j y| + |Γ₃.τ j y - Γ₂.τ j y| :=
            abs_sub_le _ _ _
        _ ≤ D13 + D32 := add_le_add a b
    · push_neg at hc
      have a := unif_le_dist Γ₁ Γ₃ h₁ h₃ j T3 hT3 (le_min (le_trans hc.le hy1) le_rfl)
      have b := unif_le_dist Γ₃ Γ₂ h₃ h₂ j T3 hT3 (le_min le_rfl (le_trans hc.le hy2))
      have a' := endpoint_le_dist Γ₁ Γ₃ j
      have b' := endpoint_le_dist Γ₃ Γ₂ j
      have m1 := (h₁.1 j).2.1 (Set.mem_Ici.2 hT3) (Set.mem_Ici.2 hy0) hc.le
      have m2 := (h₁.1 j).2.1 (Set.mem_Ici.2 hy0) (Set.mem_Ici.2 (le_trans hy0 hy1)) hy1
      have m3 := (h₂.1 j).2.1 (Set.mem_Ici.2 hT3) (Set.mem_Ici.2 hy0) hc.le
      have m4 := (h₂.1 j).2.1 (Set.mem_Ici.2 hy0) (Set.mem_Ici.2 (le_trans hy0 hy2)) hy2
      rw [abs_le] at a b a' b' ⊢
      constructor <;> linarith
  · intro j
    calc |Γ₁.τ j T1 - Γ₂.τ j T2| ≤ |Γ₁.τ j T1 - Γ₃.τ j T3| + |Γ₃.τ j T3 - Γ₂.τ j T2| :=
          abs_sub_le _ _ _
      _ ≤ D13 + D32 := add_le_add (endpoint_le_dist _ _ j) (endpoint_le_dist _ _ j)

end SensitivityPoA.Continuity.PoA2Aux

open SensitivityPoA.Continuity SensitivityPoA.Continuity.PoA2Aux in
theorem solution (N : Network) (hN : N.Standing)
    (Γ₁ Γ₂ Γ₃ : Game N)
    (h₁ : Γ₁.IsGeneralized) (h₂ : Γ₂.IsGeneralized)
    (h₃ : Γ₃.IsGeneralized) :
    gameDist Γ₁ Γ₂ ≤ gameDist Γ₁ Γ₃ + gameDist Γ₃ Γ₂ := m_lemma_4_c N hN Γ₁ Γ₂ Γ₃ h₁ h₂ h₃
