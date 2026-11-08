-- Prove2me | solution 1 for OrabonaOL.OGD.ogd_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T19:32:27.46919+00:00
-- url     : https://prove2.me/submissions/40eb2227-a0f5-4770-8341-de239a245ef5

import Mathlib
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj
import Definitions.Def_OrabonaOL_OGD_IsProjectedOGDRun

set_option autoImplicit false

namespace OrabonaOL.OGD.Aux
open OrabonaOL.OGD Filter Topology

variable {d : ℕ}

lemma tangent_convex {P : Set (EuclideanSpace ℝ (Fin d))} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : ConvexOn ℝ P h) {y u : EuclideanSpace ℝ (Fin d)} (hy : y ∈ P) (hu : u ∈ P)
    {L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ} (hd : HasFDerivAt h L y) :
    h y + L (u - y) ≤ h u := by
  have hl : HasLineDerivAt ℝ h (L (u - y)) y (u - y) := hd.hasLineDerivAt (u - y)
  have ht := hl.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ • (h (y + t • (u - y)) - h y) ≤ h u - h y := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1 := hc.2 hy hu (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (show 1 - t + t = 1 by ring)
    have heq : (1 - t) • y + t • u = y + t • (u - y) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at h1
    rw [smul_eq_mul, inv_mul_le_iff₀ ht0]
    nlinarith
  have := le_of_tendsto ht hev
  linarith

lemma inner_gradient_eq (f : EuclideanSpace ℝ (Fin d) → ℝ) (x v : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (gradient f x) v = fderiv ℝ f x v := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

lemma proj_sq_le {V : Set (EuclideanSpace ℝ (Fin d))} (hV : Convex ℝ V)
    {z p u : EuclideanSpace ℝ (Fin d)} (hp : IsEuclideanProj V z p) (hu : u ∈ V) :
    ‖p - u‖ ^ 2 ≤ ‖z - u‖ ^ 2 := by
  obtain ⟨hpV, hmin⟩ := hp
  have : Nonempty V := ⟨⟨p, hpV⟩⟩
  have hinf : ‖z - p‖ = ⨅ w : V, ‖z - w‖ := by
    apply le_antisymm
    · exact le_ciInf fun w => hmin w w.2
    · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨p, hpV⟩ : V)
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hV hpV).1 hinf u hu
  have e1 : z - u = (z - p) - (u - p) := by abel
  have e2 : ‖(z - p) - (u - p)‖ ^ 2 = ‖z - p‖ ^ 2 - 2 * inner ℝ (z - p) (u - p) + ‖u - p‖ ^ 2 :=
    norm_sub_sq_real _ _
  rw [e1, e2, norm_sub_rev p u]
  nlinarith [sq_nonneg ‖z - p‖]

lemma step_bound {V : Set (EuclideanSpace ℝ (Fin d))} (hV : Convex ℝ V)
    {x x' g u : EuclideanSpace ℝ (Fin d)} {η : ℝ} (hη : 0 < η)
    (hp : IsEuclideanProj V (x - η • g) x') (hu : u ∈ V) :
    inner ℝ (x - u) g ≤ (‖x - u‖ ^ 2 - ‖x' - u‖ ^ 2) / (2 * η) + η / 2 * ‖g‖ ^ 2 := by
  have h1 := proj_sq_le hV hp hu
  have e1 : x - η • g - u = (x - u) - η • g := by abel
  have e2 : ‖(x - u) - η • g‖ ^ 2 = ‖x - u‖ ^ 2 - 2 * inner ℝ (x - u) (η • g) + ‖η • g‖ ^ 2 :=
    norm_sub_sq_real _ _
  rw [e1, e2, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h1
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  have e3 : η / 2 * ‖g‖ ^ 2 * (2 * η) = η ^ 2 * ‖g‖ ^ 2 := by ring
  rw [e3]
  nlinarith

lemma tele_mono (a e : ℕ → ℝ) (B : ℝ) (N : ℕ)
    (he : ∀ t ∈ Finset.Icc 1 N, 0 < e t)
    (hmono : ∀ t : ℕ, 1 ≤ t → t + 1 ≤ N → e (t + 1) ≤ e t)
    (hB : ∀ t ∈ Finset.Icc 1 N, a t ≤ B) :
    ∀ n : ℕ, 1 ≤ n → n ≤ N →
      ∑ t ∈ Finset.Icc 1 n, (a t - a (t + 1)) / e t ≤ B / e n - 1 / e n * a (n + 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro hN
    rw [Finset.Icc_self, Finset.sum_singleton]
    have h1 := div_le_div_of_nonneg_right (hB 1 (Finset.mem_Icc.2 ⟨le_rfl, hN⟩))
      (he 1 (Finset.mem_Icc.2 ⟨le_rfl, hN⟩)).le
    have e1 : (a 1 - a (1 + 1)) / e 1 = a 1 / e 1 - 1 / e 1 * a (1 + 1) := by ring
    rw [e1]
    linarith
  | succ n hn ih =>
    intro hN
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ih' := ih (by omega)
    have hpos : 0 < e n := he n (Finset.mem_Icc.2 ⟨hn, by omega⟩)
    have hpos' : 0 < e (n + 1) := he (n + 1) (Finset.mem_Icc.2 ⟨by omega, hN⟩)
    have h1 : 1 / e n ≤ 1 / e (n + 1) := one_div_le_one_div_of_le hpos' (hmono n hn hN)
    have h2 : 0 ≤ B - a (n + 1) := sub_nonneg.2 (hB (n + 1) (Finset.mem_Icc.2 ⟨by omega, hN⟩))
    have key : B / e (n + 1) - 1 / e (n + 1) * a (n + 1 + 1)
        - (B / e n - 1 / e n * a (n + 1) + (a (n + 1) - a (n + 1 + 1)) / e (n + 1))
        = (B - a (n + 1)) * (1 / e (n + 1) - 1 / e n) := by ring
    nlinarith [mul_nonneg h2 (sub_nonneg.2 h1)]

lemma tele (a : ℕ → ℝ) : ∀ n : ℕ, 1 ≤ n →
    ∑ t ∈ Finset.Icc 1 n, (a t - a (t + 1)) = a 1 - a (n + 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem main {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (hVne : V.Nonempty) (hVclosed : IsClosed V) (hVconv : Convex ℝ V)
    (T : ℕ) (hT : 1 ≤ T)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hℓconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ V (ℓ t))
    (hℓdiff : ∀ t ∈ Finset.Icc 1 T, ∃ U : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen U ∧ V ⊆ U ∧ DifferentiableOn ℝ (ℓ t) U)
    (η : ℕ → ℝ) (hηpos : ∀ t ∈ Finset.Icc 1 T, 0 < η t)
    (hηmono : ∀ t : ℕ, 1 ≤ t → t + 1 ≤ T → η (t + 1) ≤ η t)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (hrun : IsProjectedOGDRun V η ℓ T x)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) :
    (∀ D : ℝ, (∀ y ∈ V, ∀ z ∈ V, ‖y - z‖ ≤ D) →
      ∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u) ≤
        D ^ 2 / (2 * η T) + ∑ t ∈ Finset.Icc 1 T, η t / 2 * ‖gradient (ℓ t) (x t)‖ ^ 2
          - 1 / (2 * η T) * ‖x (T + 1) - u‖ ^ 2) ∧
    (∀ c : ℝ, (∀ t ∈ Finset.Icc 1 T, η t = c) →
      ∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u) ≤
        ‖u - x 1‖ ^ 2 / (2 * c) + c / 2 * ∑ t ∈ Finset.Icc 1 T, ‖gradient (ℓ t) (x t)‖ ^ 2
          - 1 / (2 * c) * ‖x (T + 1) - u‖ ^ 2) := by
  -- iterates stay in V
  have hmem : ∀ t, 1 ≤ t → t ≤ T + 1 → x t ∈ V := by
    intro t h1 h2
    rcases Nat.lt_or_ge 1 t with h | h
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact (hrun.2 s (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).1
    · have : t = 1 := by omega
      subst this; exact hrun.1
  -- per-round bound
  have hstep : ∀ t ∈ Finset.Icc 1 T, ℓ t (x t) - ℓ t u ≤
      (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / (2 * η t)
        + η t / 2 * ‖gradient (ℓ t) (x t)‖ ^ 2 := by
    intro t ht
    have ht' := Finset.mem_Icc.1 ht
    have hxt : x t ∈ V := hmem t ht'.1 (by omega)
    obtain ⟨U, hUo, hVU, hdU⟩ := hℓdiff t ht
    have hdiff : DifferentiableAt ℝ (ℓ t) (x t) :=
      (hdU (x t) (hVU hxt)).differentiableAt (hUo.mem_nhds (hVU hxt))
    have htan := tangent_convex (hℓconv t ht) hxt hu hdiff.hasFDerivAt
    rw [← inner_gradient_eq, inner_sub_right] at htan
    have hs := step_bound hVconv (hηpos t ht) (hrun.2 t ht) hu
    rw [inner_sub_left] at hs
    have c1 := real_inner_comm (gradient (ℓ t) (x t)) (x t)
    have c2 := real_inner_comm (gradient (ℓ t) (x t)) u
    linarith
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib] at hsum
  refine ⟨fun D hD => ?_, fun c hc => ?_⟩
  · have hB : ∀ t ∈ Finset.Icc 1 T, ‖x t - u‖ ^ 2 ≤ D ^ 2 := by
      intro t ht
      have ht' := Finset.mem_Icc.1 ht
      exact pow_le_pow_left₀ (norm_nonneg _) (hD _ (hmem t ht'.1 (by omega)) u hu) 2
    have htm := tele_mono (fun t => ‖x t - u‖ ^ 2) (fun t => 2 * η t) (D ^ 2) T
      (fun t ht => by have := hηpos t ht; positivity)
      (fun t h1 h2 => by have := hηmono t h1 h2; linarith) hB T hT le_rfl
    linarith
  · have hsum' : ∑ t ∈ Finset.Icc 1 T, ((‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / (2 * η t)
        + η t / 2 * ‖gradient (ℓ t) (x t)‖ ^ 2) =
        ∑ t ∈ Finset.Icc 1 T, ((‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / (2 * c)
        + c / 2 * ‖gradient (ℓ t) (x t)‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hc t ht]
    have hsum2 := Finset.sum_le_sum hstep
    rw [hsum', Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      tele (fun t => ‖x t - u‖ ^ 2) T hT, norm_sub_rev (x 1) u] at hsum2
    have e : (‖u - x 1‖ ^ 2 - ‖x (T + 1) - u‖ ^ 2) / (2 * c) =
        ‖u - x 1‖ ^ 2 / (2 * c) - 1 / (2 * c) * ‖x (T + 1) - u‖ ^ 2 := by ring
    linarith

end OrabonaOL.OGD.Aux

open OrabonaOL.OGD in
theorem solution {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (hVne : V.Nonempty) (hVclosed : IsClosed V) (hVconv : Convex ℝ V)
    (T : ℕ) (hT : 1 ≤ T)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hℓconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ V (ℓ t))
    (hℓdiff : ∀ t ∈ Finset.Icc 1 T, ∃ U : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen U ∧ V ⊆ U ∧ DifferentiableOn ℝ (ℓ t) U)
    (η : ℕ → ℝ) (hηpos : ∀ t ∈ Finset.Icc 1 T, 0 < η t)
    (hηmono : ∀ t : ℕ, 1 ≤ t → t + 1 ≤ T → η (t + 1) ≤ η t)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (hrun : IsProjectedOGDRun V η ℓ T x)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) :
    (∀ D : ℝ, (∀ y ∈ V, ∀ z ∈ V, ‖y - z‖ ≤ D) →
      ∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u) ≤
        D ^ 2 / (2 * η T) + ∑ t ∈ Finset.Icc 1 T, η t / 2 * ‖gradient (ℓ t) (x t)‖ ^ 2
          - 1 / (2 * η T) * ‖x (T + 1) - u‖ ^ 2) ∧
    (∀ c : ℝ, (∀ t ∈ Finset.Icc 1 T, η t = c) →
      ∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u) ≤
        ‖u - x 1‖ ^ 2 / (2 * c) + c / 2 * ∑ t ∈ Finset.Icc 1 T, ‖gradient (ℓ t) (x t)‖ ^ 2
          - 1 / (2 * c) * ‖x (T + 1) - u‖ ^ 2) := by
  exact OrabonaOL.OGD.Aux.main V hVne hVclosed hVconv T hT ℓ hℓconv hℓdiff η hηpos hηmono
    x hrun u hu
