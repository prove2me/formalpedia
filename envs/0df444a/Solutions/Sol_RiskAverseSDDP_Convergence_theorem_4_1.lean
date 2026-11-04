-- Prove2me | solution 1 for RiskAverseSDDP.Convergence.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:09:19.630186+00:00
-- url     : https://prove2.me/submissions/830fef21-d407-44d8-8266-78a2b5b8f31b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Definitions.Def_RiskAverseSDDP_Convergence_Sampling
import Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_28
import Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_29
import Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_31
import Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_32
import Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_33
open Filter Topology MeasureTheory ProbabilityTheory
open RiskAverseSDDP.Convergence

namespace RASDDPThm41

lemma Q_last {T n M q p : ℕ} (D : Model T n M q p) (x : Hist n T) : D.Q T x = 0 := by
  simp [Model.Q, Model.Qaux]

/-- Convergence along `S` and along `S'`, with `S ∪ S' ⊇ {k ≥ 1}`, gives convergence. -/
lemma tendsto_of_two {α : Type*} [TopologicalSpace α] {u : ℕ → α} {a : α} (A B : Set ℕ)
    (hAB : ∀ k, 1 ≤ k → k ∈ A ∨ k ∈ B)
    (hA : Tendsto u (atTop ⊓ 𝓟 A) (𝓝 a)) (hB : Tendsto u (atTop ⊓ 𝓟 B) (𝓝 a)) :
    Tendsto u atTop (𝓝 a) := by
  have h := hA.sup hB
  rw [← inf_sup_left, sup_principal] at h
  refine h.mono_left (le_inf le_rfl (le_principal_iff.2 ?_))
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact hAB k hk

/-- From `0 ≤ c - a k ≤ g k → 0` in `EReal`, deduce `a k → c`. -/
lemma tendsto_of_sub_squeeze {a g : ℕ → EReal} {c : EReal}
    (h0 : ∀ k, 0 ≤ c - a k) (hle : ∀ k, c - a k ≤ g k) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 c) := by
  have hd : Tendsto (fun k => c - a k) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg h0 hle
  have hfin : ∀ᶠ k in atTop, c - a k ≠ ⊥ ∧ c - a k ≠ ⊤ := by
    have h1 : ∀ᶠ k in atTop, c - a k < 1 := hd.eventually (gt_mem_nhds (by norm_num))
    have h2 : ∀ᶠ k in atTop, (-1 : EReal) < c - a k := hd.eventually (lt_mem_nhds (by norm_num))
    filter_upwards [h1, h2] with k hk1 hk2
    exact ⟨ne_bot_of_gt hk2, ne_top_of_lt hk1⟩
  obtain ⟨k0, hk0⟩ := (hfin.and (eventually_ge_atTop 0)).exists
  have hc : c ≠ ⊥ ∧ c ≠ ⊤ := by
    obtain ⟨⟨hb, ht⟩, _⟩ := hk0
    refine ⟨fun h => hb (by simp [h]), fun h => ht ?_⟩
    rw [h]
    by_cases ha : a k0 = ⊤
    · exact absurd (by rw [h, ha]; rfl : c - a k0 = ⊥) hb
    · exact EReal.top_sub ha
  lift c to ℝ using ⟨hc.2, hc.1⟩
  have hev : ∀ᶠ k in atTop, a k = (c : EReal) + -((c : EReal) - a k) := by
    filter_upwards [hfin] with k ⟨hb, ht⟩
    have ha1 : a k ≠ ⊤ := fun h => hb (by rw [h]; rfl)
    have ha2 : a k ≠ ⊥ := fun h => ht (by rw [h]; exact EReal.sub_bot (EReal.coe_ne_bot c))
    lift a k to ℝ using ⟨ha1, ha2⟩ with b
    rw [← EReal.coe_sub, ← EReal.coe_neg, ← EReal.coe_add]
    congr 1; ring
  have hlim : Tendsto (fun k => (c : EReal) + -((c : EReal) - a k)) atTop (𝓝 ((c : EReal) + -0)) := by
    have hn : Tendsto (fun k => -((c : EReal) - a k)) atTop (𝓝 (-0)) :=
      (continuous_neg.tendsto (0 : EReal)).comp hd
    have hca := EReal.continuousAt_add_coe_coe c 0
    simp only [neg_zero] at hn ⊢
    exact (hca.tendsto.comp (tendsto_const_nhds.prodMk_nhds (by simpa using hn)) :)
  simp only [neg_zero, add_zero] at hlim
  exact hlim.congr' (hev.mono fun k hk => hk.symm)

end RASDDPThm41

open RASDDPThm41 in
theorem solution {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ) (hT : 1 ≤ T)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℕ → Fin M) (hH3 : D.H3 P ξ)
    (r : Ω → RunData n M) (hr : ∀ ω, D.IsRun R (fun k t => ξ k ω t) (r ω)) :
    ∀ᵐ ω ∂P,
      (∀ s, s < T → ∀ ν : Fin s → Fin M,
        Tendsto (fun k => D.Q (s + 1) ((r ω).hist k s ν) - (r ω).Qm k (s + 1) ((r ω).hist k s ν))
          atTop (𝓝 0)) ∧
      Tendsto (fun k => D.stageVal 0 0 ((r ω).Qm k 1) (Hist.empty n)) atTop (𝓝 D.Q1) ∧
      ∀ xs : EuclideanSpace ℝ (Fin n),
        MapClusterPt xs atTop (fun k => (r ω).x k 0 Fin.elim0) → D.IsFirstStageOptimal xs := by
  -- (4.29) holds almost surely, simultaneously for the finitely many nodes
  have h429 : ∀ᵐ ω ∂P, ∀ s, s + 2 ≤ T → ∀ ν : Fin s → Fin M,
      Tendsto (fun k => D.Q (s + 1) ((r ω).hist k s ν) - (r ω).Qm k (s + 1) ((r ω).hist k s ν))
        (atTop ⊓ 𝓟 (iterSet (fun k t => ξ k ω t) s ν)) (𝓝 0) →
      Tendsto (fun k => D.Q (s + 1) ((r ω).hist k s ν) - (r ω).Qm k (s + 1) ((r ω).hist k s ν))
        (atTop ⊓ 𝓟 {k | 1 ≤ k ∧ sampNode (fun k t => ξ k ω t) k s ≠ ν}) (𝓝 0) := by
    rw [ae_all_iff]
    intro s
    by_cases hs : s + 2 ≤ T
    · have h := eq_4_29 D ε hS hH2 R P ξ hH3 r hr s hs
      rw [← ae_all_iff] at h
      filter_upwards [h] with ω hω _ ν using hω ν
    · exact Eventually.of_forall fun ω h => absurd h hs
  filter_upwards [h429] with ω hω
  set ys : ℕ → ℕ → Fin M := fun k t => ξ k ω t
  have hrω := hr ω
  -- (i) by backward induction on the stage
  have hi : ∀ d s, s + 1 + d = T → ∀ ν : Fin s → Fin M,
      Tendsto (fun k => D.Q (s + 1) ((r ω).hist k s ν) - (r ω).Qm k (s + 1) ((r ω).hist k s ν))
        atTop (𝓝 0) := by
    intro d
    induction d with
    | zero =>
      intro s hs ν
      have hs' : T = s + 1 := by omega
      subst hs'
      have hQT := hrω.2.1
      simp only [Q_last, hQT, sub_zero]
      exact tendsto_const_nhds
    | succ d ih =>
      intro s hs ν
      have hs2 : s + 2 ≤ T := by omega
      have h427 : ∀ j : Fin M, Tendsto (fun k =>
          D.Q (s + 2) ((r ω).hist k (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j)) -
            (r ω).Qm k (s + 2) ((r ω).hist k (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j)))
          atTop (𝓝 0) := fun j => ih (s + 1) (by omega) _
      have hA := eq_4_28 D ε hS hH2 R ys (r ω) hrω s hs2 ν h427
      have hB := hω s hs2 ν hA
      refine tendsto_of_two _ _ (fun k hk => ?_) hA hB
      by_cases hk' : sampNode ys k s = ν
      · exact Or.inl ⟨hk, hk'⟩
      · exact Or.inr ⟨hk, hk'⟩
  have hI : ∀ s, s < T → ∀ ν : Fin s → Fin M,
      Tendsto (fun k => D.Q (s + 1) ((r ω).hist k s ν) - (r ω).Qm k (s + 1) ((r ω).hist k s ν))
        atTop (𝓝 0) := fun s hs ν => hi (T - (s + 1)) s (by omega) ν
  -- (ii): (4.31), (4.32) and the accumulation-point argument
  have h2 := hI 0 hT Fin.elim0
  have h432 := eq_4_32 D ε hT hS hH2 R ys (r ω) hrω h2
  have h431 := eq_4_31 D ε hT hS hH2 R ys (r ω) hrω
  have hval : Tendsto (fun k => D.stageVal 0 0 ((r ω).Qm k 1) (Hist.empty n)) atTop (𝓝 D.Q1) :=
    tendsto_of_sub_squeeze (fun k => (h431 k).1) (fun k => (h431 k).2) h432
  exact ⟨hI, hval, eq_4_33 D ε hT hS hH2 R ys (r ω) hrω hval h432⟩
