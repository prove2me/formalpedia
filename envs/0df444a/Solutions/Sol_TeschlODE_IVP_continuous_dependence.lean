-- Prove2me | solution 1 for TeschlODE.IVP.continuous_dependence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:09:55.873728+00:00
-- url     : https://prove2.me/submissions/dfddcf9b-2629-48b5-ad82-5da7d42a15f7

import Mathlib
import Definitions.Def_TeschlODE_IVP_IsSolutionOn
import Definitions.Def_TeschlODE_IVP_LocallyLipschitzSecond

set_option autoImplicit false

namespace BC546CF1

open Set Filter Topology

/-- Forward Gronwall estimate on an order-connected set. -/
theorem fwd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → E → E) (S : ℝ → Set E) (J : Set ℝ) (hJ : J.OrdConnected)
    (a : ℝ) (ha : a ∈ J) (x y : ℝ → E)
    (hx : ∀ s ∈ J, HasDerivWithinAt x (F s (x s)) J s)
    (hy : ∀ s ∈ J, HasDerivWithinAt y (G s (y s)) J s)
    (hxS : ∀ s ∈ J, x s ∈ S s) (hyS : ∀ s ∈ J, y s ∈ S s)
    (L M : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ s u v, u ∈ S s → v ∈ S s → ‖F s u - F s v‖ ≤ L * ‖u - v‖)
    (hM : ∀ s ∈ J, ‖F s (y s) - G s (y s)‖ ≤ M) :
    ∀ t ∈ J, a ≤ t → ‖x t - y t‖ ≤ gronwallBound ‖x a - y a‖ L M (t - a) := by
  intro t ht hat
  have hsub : Icc a t ⊆ J := hJ.out ha ht
  set K : NNReal := ⟨L, hL0⟩ with hK
  have hKL : (K : ℝ) = L := rfl
  have hv : ∀ s ∈ Ico a t, LipschitzOnWith K (F s) (S s) := by
    intro s _
    refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    rw [dist_eq_norm, dist_eq_norm, hKL]
    exact hL s u v hu hv
  have hder : ∀ (z : ℝ → E) (z' : ℝ → E), (∀ s ∈ J, HasDerivWithinAt z (z' s) J s) →
      ∀ s ∈ Ico a t, HasDerivWithinAt z (z' s) (Ici s) s := by
    intro z z' hz s hs
    have hsJ : s ∈ J := hsub (Ico_subset_Icc_self hs)
    have h1 : HasDerivWithinAt z (z' s) (Icc s t) s :=
      (hz s hsJ).mono (fun r hr => hsub ⟨hs.1.trans hr.1, hr.2⟩)
    exact h1.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hs.2)
  have hcont : ∀ (z : ℝ → E) (z' : ℝ → E), (∀ s ∈ J, HasDerivWithinAt z (z' s) J s) →
      ContinuousOn z (Icc a t) := by
    intro z z' hz r hr
    exact ((hz r (hsub hr)).continuousWithinAt).mono hsub
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := F) (s := S) (K := K)
    (f := x) (g := y) (f' := fun s => F s (x s)) (g' := fun s => G s (y s))
    (εf := 0) (εg := M) (δ := ‖x a - y a‖) hv (hcont x _ hx)
    (hder x _ hx) (fun s _ => by simp)
    (fun s hs => hxS s (hsub (Ico_subset_Icc_self hs))) (hcont y _ hy) (hder y _ hy)
    (fun s hs => by
      rw [dist_comm, dist_eq_norm]
      exact hM s (hsub (Ico_subset_Icc_self hs)))
    (fun s hs => hyS s (hsub (Ico_subset_Icc_self hs))) (by rw [dist_eq_norm])
    t ⟨hat, le_rfl⟩
  rw [dist_eq_norm, zero_add, hKL] at key
  exact key

theorem gb_eq (δ L M t : ℝ) :
    gronwallBound δ L M t = δ * Real.exp (L * t) +
      (if L = 0 then M * t else M / L * (Real.exp (L * t) - 1)) := by
  unfold gronwallBound
  split_ifs with h
  · subst h; simp
  · rfl

end BC546CF1

open BC546CF1 in
open TeschlODE.IVP in
theorem solution {n : ℕ} (U : Set (ℝ × EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (f g : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) (hLip : LocallyLipschitzSecond U f)
    (I : Set ℝ) (hI : I.OrdConnected) (t₀ : ℝ) (ht₀ : t₀ ∈ I)
    (x y : ℝ → EuclideanSpace ℝ (Fin n)) (x₀ y₀ : EuclideanSpace ℝ (Fin n))
    (hx : IsSolutionOn U f I x) (hx₀ : x t₀ = x₀)
    (hy : IsSolutionOn U g I y) (hy₀ : y t₀ = y₀)
    (V : Set (ℝ × EuclideanSpace ℝ (Fin n))) (hVU : V ⊆ U)
    (hxV : ∀ t ∈ I, (t, x t) ∈ V) (hyV : ∀ t ∈ I, (t, y t) ∈ V)
    (L M : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, ∀ u v : EuclideanSpace ℝ (Fin n), (t, u) ∈ V → (t, v) ∈ V →
      ‖f (t, u) - f (t, v)‖ ≤ L * ‖u - v‖)
    (hM : ∀ p ∈ V, ‖f p - g p‖ ≤ M) :
    ∀ t ∈ I, ‖x t - y t‖ ≤ ‖x₀ - y₀‖ * Real.exp (L * |t - t₀|) +
      (if L = 0 then M * |t - t₀| else M / L * (Real.exp (L * |t - t₀|) - 1)) := by
  intro t ht
  rw [← gb_eq, ← hx₀, ← hy₀]
  rcases le_total t₀ t with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact fwd (fun s u => f (s, u)) (fun s u => g (s, u)) (fun s => {u | (s, u) ∈ V}) I hI
      t₀ ht₀ x y (fun s hs => (hx s hs).2) (fun s hs => (hy s hs).2)
      (fun s hs => hxV s hs) (fun s hs => hyV s hs) L M hL0
      (fun s u v hu hv => hL s u v hu hv) (fun s hs => hM _ (hyV s hs)) t ht h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    have hJ : (Neg.neg ⁻¹' I : Set ℝ).OrdConnected := by
      refine ⟨fun a ha b hb c hc => ?_⟩
      exact hI.out hb ha ⟨neg_le_neg hc.2, neg_le_neg hc.1⟩
    have hdx : ∀ (z : ℝ → EuclideanSpace ℝ (Fin n)) (k : ℝ × EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n)), IsSolutionOn U k I z →
        ∀ s ∈ (Neg.neg ⁻¹' I : Set ℝ), HasDerivWithinAt (fun r => z (-r))
          ((fun s u => -k (-s, u)) s ((fun r => z (-r)) s)) (Neg.neg ⁻¹' I) s := by
      intro z k hz s hs
      have h1 := (hz (-s) hs).2
      have h2 : HasDerivWithinAt (Neg.neg : ℝ → ℝ) (-1) (Neg.neg ⁻¹' I) s :=
        (hasDerivAt_neg s).hasDerivWithinAt
      have h3 := h1.scomp s h2 (fun r hr => hr)
      simpa [Function.comp_def, neg_one_smul] using h3
    have := fwd (fun s u => -f (-s, u)) (fun s u => -g (-s, u)) (fun s => {u | (-s, u) ∈ V})
      (Neg.neg ⁻¹' I) hJ (-t₀) (by simpa using ht₀) (fun r => x (-r)) (fun r => y (-r))
      (hdx x f hx) (hdx y g hy)
      (fun s hs => hxV (-s) hs) (fun s hs => hyV (-s) hs) L M hL0
      (fun s u v hu hv => by
        rw [neg_sub_neg, norm_sub_rev]; exact hL (-s) u v hu hv)
      (fun s hs => by
        rw [neg_sub_neg, norm_sub_rev]; exact hM _ (hyV (-s) hs))
      (-t) (by simpa using ht) (neg_le_neg h)
    rw [show t₀ - t = -t - -t₀ by ring]
    simpa only [neg_neg] using this
