-- Prove2me | solution 1 for TeschlODE.HigherDim.unstableSet_subset_omegaPlusSet
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:57:55.691512+00:00
-- url     : https://prove2.me/submissions/663e3b17-43c8-41ce-9ee6-f77e1c87a649

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_omegaPlusSet
import Definitions.Def_TeschlODE_HigherDim_stableSet
import Definitions.Def_TeschlODE_HigherDim_IsTrappingRegion

open Filter Topology Metric Set TeschlODE.HigherDim

lemma flow_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n)))
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M)
    (s : ℝ) (hs : s ∈ I x) (t : ℝ) (ht : t + s ∈ I x) :
    t ∈ I (Φ s x) ∧ Φ t (Φ s x) = Φ (t + s) x := by
  obtain ⟨⟨hJo, hJc, hJM, hJd⟩, -, -, -⟩ := hΦ x hx
  have hyM : Φ s x ∈ M := hJM s hs
  have hcurve : IsIntegralCurve f M {τ | τ + s ∈ I x} (fun τ => Φ (τ + s) x) := by
    refine ⟨hJo.preimage (continuous_id.add continuous_const), ⟨fun a ha b hb τ hτ => ?_⟩,
      fun τ hτ => hJM _ hτ, fun τ hτ => (hJd _ hτ).comp_add_const τ s⟩
    exact hJc.out ha hb ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  obtain ⟨-, -, -, hmax⟩ := hΦ (Φ s x) hyM
  obtain ⟨hsub, heq⟩ := hmax _ _ hcurve (by simpa using hs) (by simp)
  exact ⟨hsub ht, (heq t ht).symm⟩

lemma omega_sub_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsTrappingRegion M I Φ E) :
    omegaPlusSet M I Φ E ⊆ E := by
  obtain ⟨-, -, hEc, hEM, hEtrap⟩ := hE
  -- Lipschitz constant on `closure E`
  have hloc : LocallyLipschitzOn (closure E) f := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ := (hf.contDiffAt (hM.mem_nhds (hEM hx))).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact hEc
  -- trajectories on `[0,1]` starting in `closure E`
  have htraj : ∀ z ∈ closure E, ContinuousOn (fun τ => Φ τ z) (Icc 0 1) ∧
      (∀ τ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (fun τ => Φ τ z) (f (Φ τ z)) (Ici τ) τ) ∧
      (∀ τ ∈ Ico (0 : ℝ) 1, Φ τ z ∈ closure E) := by
    intro z hz
    obtain ⟨⟨-, hJc, -, hJd⟩, h0, hΦ0, -⟩ := hΦ z (hEM hz)
    have h1 : (1 : ℝ) ∈ I z := (hEtrap z hz 1 one_pos).1
    have hIcc : Icc (0 : ℝ) 1 ⊆ I z := hJc.out h0 h1
    refine ⟨fun τ hτ => (hJd τ (hIcc hτ)).continuousAt.continuousWithinAt,
      fun τ hτ => (hJd τ (hIcc (Ico_subset_Icc_self hτ))).hasDerivWithinAt, fun τ hτ => ?_⟩
    rcases eq_or_lt_of_le hτ.1 with h | h
    · rw [← h, hΦ0]; exact hz
    · exact subset_closure (hEtrap z hz τ h).2
  intro y hy
  obtain ⟨-, t, x, hx, ht, hlim⟩ := hy
  have hev : ∀ᶠ k in atTop, 1 < t k := ht.eventually (eventually_gt_atTop 1)
  set z : ℕ → EuclideanSpace ℝ (Fin n) := fun k => Φ (t k - 1) (x k) with hz
  have hzE : ∀ᶠ k in atTop, z k ∈ closure E ∧ Φ 1 (z k) = Φ (t k) (x k) := by
    filter_upwards [hev] with k hk
    have hxk : x k ∈ closure E := subset_closure (hx k).1
    have hpos : 0 < t k - 1 := by linarith
    refine ⟨subset_closure (hEtrap _ hxk _ hpos).2, ?_⟩
    have := (flow_core f M I Φ hΦ (x k) (hEM hxk) (t k - 1) (hEtrap _ hxk _ hpos).1 1
      (by simpa using (hx k).2)).2
    rw [hz]; simpa using this
  obtain ⟨w, hw, φ, hφ, hzφ⟩ := hEc.tendsto_subseq' (hzE.mono fun k hk => hk.1).frequently
  have hzEφ : ∀ᶠ k in atTop, z (φ k) ∈ closure E ∧ Φ 1 (z (φ k)) = Φ (t (φ k)) (x (φ k)) :=
    hφ.tendsto_atTop.eventually hzE
  -- Gronwall
  have hgr : Tendsto (fun k => Φ 1 (z (φ k))) atTop (𝓝 (Φ 1 w)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hd : Tendsto (fun k => dist (z (φ k)) w * Real.exp (K * (1 - 0))) atTop (𝓝 0) := by
      have := ((tendsto_iff_dist_tendsto_zero.mp hzφ).mul_const (Real.exp (K * (1 - 0))))
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hd
    filter_upwards [hzEφ] with k hk
    obtain ⟨c1, d1, m1⟩ := htraj _ hk.1
    obtain ⟨c2, d2, m2⟩ := htraj _ hw
    have := dist_le_of_trajectories_ODE_of_mem (v := fun _ => f) (s := fun _ => closure E)
      (fun _ _ => hK) c1 d1 m1 c2 d2 m2
      (le_of_eq (by
        rw [(hΦ _ (hEM hk.1)).2.2.1, (hΦ _ (hEM hw)).2.2.1])) 1 ⟨zero_le_one, le_rfl⟩
    simpa using this
  have hlim' : Tendsto (fun k => Φ 1 (z (φ k))) atTop (𝓝 y) := by
    refine (hlim.comp hφ.tendsto_atTop).congr' ?_
    filter_upwards [hzEφ] with k hk
    exact hk.2.symm
  rw [tendsto_nhds_unique hlim' hgr]
  exact (hEtrap w hw 1 one_pos).2

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsTrappingRegion M I Φ E) :
    ∀ x ∈ omegaPlusSet M I Φ E, stableSet M I Φ (-1) {x} ⊆ omegaPlusSet M I Φ E := by
  intro x hx y hy
  have hxE : x ∈ E := omega_sub_core f M hM hf I Φ hΦ E hE hx
  obtain ⟨hyM, hyI, hylim⟩ := hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hE.1 x hxE
  have hev : ∀ᶠ s in atTop, Φ (-1 * s) y ∈ E := by
    filter_upwards [hylim.eventually (gt_mem_nhds hε)] with s hs
    apply hball
    rw [Metric.mem_ball]
    simpa [Metric.infDist_singleton] using hs
  obtain ⟨S, hS⟩ := eventually_atTop.mp hev
  set s : ℕ → ℝ := fun k => (k : ℝ) + max S 0 with hsdef
  have hsS : ∀ k, S ≤ s k := fun k => by
    simp only [hsdef]; have := le_max_left S 0; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hs0 : ∀ k, 0 ≤ s k := fun k => by
    simp only [hsdef]; have := le_max_right S 0; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hflow : ∀ k, s k ∈ I (Φ (-s k) y) ∧ Φ (s k) (Φ (-s k) y) = Φ (s k + -s k) y := fun k =>
    flow_core f M I Φ hΦ y hyM (-s k) (hyI _ (by linarith [hs0 k])) (s k)
      (by simpa using (hΦ y hyM).2.1)
  refine ⟨hyM, s, fun k => Φ (-s k) y, fun k => ⟨?_, (hflow k).1⟩, ?_, ?_⟩
  · simpa using hS (s k) (hsS k)
  · exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · refine tendsto_const_nhds.congr fun k => ?_
    rw [(hflow k).2, add_neg_cancel, (hΦ y hyM).2.2.1]

#print axioms solution
