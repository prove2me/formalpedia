-- Prove2me | solution 1 for QAlgorithms.Childs.adiabatic_theorem
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:19:19.748893+00:00
-- url     : https://prove2.me/submissions/69fbb2eb-d287-4e96-9b80-ba2834989b4e

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false

open Set Filter Topology Metric QAlgorithms
open scoped NNReal

namespace AdiabaticThmAux

/-- Global existence and uniqueness for linear ODEs `x' = B(t) x` on a Banach space. -/
theorem linearODE_existsUnique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (x₀ : E) :
    ∃! x : ℝ → E, x 0 = x₀ ∧ ∀ t, HasDerivAt x (B t (x t)) t := by
  have bound : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ‖B t‖ ≤ C := by
    intro a b
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hB.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun t ht => (hC t ht).trans (le_max_left _ _)⟩
  have U : ∀ (a b t₀ : ℝ) (f g : ℝ → E), t₀ ∈ Ioo a b →
      (∀ t ∈ Ioo a b, HasDerivAt f (B t (f t)) t) →
      (∀ t ∈ Ioo a b, HasDerivAt g (B t (g t)) t) → f t₀ = g t₀ → EqOn f g (Ioo a b) := by
    intro a b t₀ f g ht hf hg heq
    obtain ⟨C, hC0, hC⟩ := bound a b
    refine ODE_solution_unique_of_mem_Ioo (v := fun t x => B t x) (s := fun _ => univ)
      (K := ⟨C, hC0⟩) (fun t ht' => ?_) ht (fun t ht' => ⟨hf t ht', trivial⟩)
      (fun t ht' => ⟨hg t ht', trivial⟩) heq
    refine ((B t).lipschitz.weaken ?_).lipschitzOnWith
    change ‖B t‖ ≤ C
    exact hC t (Ioo_subset_Icc_self ht')
  have L : ∀ T : ℝ, ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ ∀ s ∈ Icc (-T) T, ∀ x : E, ∃ y : ℝ → E, y s = x ∧
      ∀ t ∈ Ioo (s - h) (s + h), HasDerivAt y (B t (y t)) t := by
    intro T
    obtain ⟨C, hC0, hC⟩ := bound (-T - 1) (T + 1)
    refine ⟨1 / (2 * C + 2), by positivity, ?_, ?_⟩
    · rw [div_le_one (by positivity)]; linarith
    intro s hs x
    set h := 1 / (2 * C + 2) with hh
    have hpos : 0 < h := by positivity
    have hh1 : h ≤ 1 := by rw [hh, div_le_one (by positivity)]; linarith
    have hs0 : s ∈ Icc (s - h) (s + h) := ⟨by linarith, by linarith⟩
    have hsub : Icc (s - h) (s + h) ⊆ Icc (-T - 1) (T + 1) := by
      intro t ht; exact ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
    have hPL : IsPicardLindelof (fun t y => B t y) (⟨s, hs0⟩ : Icc (s - h) (s + h)) x
        ⟨‖x‖ + 1, by positivity⟩ 0 ⟨C * (2 * ‖x‖ + 1), by positivity⟩ ⟨C, hC0⟩ := by
      refine ⟨fun t ht => ?_, fun y _ => ?_, fun t ht y hy => ?_, ?_⟩
      · refine ((B t).lipschitz.weaken ?_).lipschitzOnWith
        change ‖B t‖ ≤ C
        exact hC t (hsub ht)
      · exact ((hB.clm_apply continuous_const).continuousOn)
      · change ‖B t y‖ ≤ C * (2 * ‖x‖ + 1)
        have hy' : ‖y‖ ≤ 2 * ‖x‖ + 1 := by
          have h3 : dist y x ≤ ‖x‖ + 1 := mem_closedBall.mp hy
          have h2 := norm_le_insert' y x
          rw [← dist_eq_norm] at h2
          linarith
        calc ‖B t y‖ ≤ ‖B t‖ * ‖y‖ := (B t).le_opNorm y
          _ ≤ C * (2 * ‖x‖ + 1) :=
            mul_le_mul (hC t (hsub ht)) hy' (norm_nonneg _) hC0
      · simp only [NNReal.coe_mk]
        have hm : max (s + h - s) (s - (s - h)) = h := by
          rw [show s + h - s = h by ring, show s - (s - h) = h by ring, max_self]
        rw [hm, hh]
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        have e0 : ((0 : ℝ≥0) : ℝ) = 0 := rfl
        rw [e0]
        change C * (2 * ‖x‖ + 1) ≤ (‖x‖ + 1 - 0) * (2 * C + 2)
        nlinarith [norm_nonneg x]
    obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨α, hα0, fun t ht => ?_⟩
    exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have G : ∀ (a b c d : ℝ) (y z : ℝ → E), a < b → c < b → b ≤ d →
      (∀ t ∈ Ioo a b, HasDerivAt y (B t (y t)) t) →
      (∀ t ∈ Ioo c d, HasDerivAt z (B t (z t)) t) → EqOn y z (Ioo (max a c) b) →
      ∃ w : ℝ → E, (∀ t ∈ Ioo a d, HasDerivAt w (B t (w t)) t) ∧ EqOn w y (Ioo a b) ∧
        EqOn w z (Ioo (max a c) d) := by
    intro a b c d y z hab hcb hbd hy hz hyz
    refine ⟨fun t => if t < b then y t else z t, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · by_cases htb : t < b
      · have hev : (fun t => if t < b then y t else z t) =ᶠ[𝓝 t] y := by
          filter_upwards [Iio_mem_nhds htb] with u hu
          simp [show u < b from hu]
        have := (hy t ⟨ht.1, htb⟩).congr_of_eventuallyEq hev
        simpa [htb] using this
      · have hct : c < t := lt_of_lt_of_le hcb (not_lt.mp htb)
        have hev : (fun t => if t < b then y t else z t) =ᶠ[𝓝 t] z := by
          filter_upwards [Ioi_mem_nhds (show max a c < t from max_lt ht.1 hct)] with u hu
          by_cases hub : u < b
          · simp only [hub, if_true]; exact hyz ⟨hu, hub⟩
          · simp [hub]
        have := (hz t ⟨hct, ht.2⟩).congr_of_eventuallyEq hev
        simpa [htb] using this
    · simp [ht.2]
    · by_cases htb : t < b
      · simp only [htb, if_true]; exact hyz ⟨ht.1, htb⟩
      · simp [htb]
  have Ex : ∀ T : ℝ, ∃ y : ℝ → E, y 0 = x₀ ∧ ∀ t ∈ Ioo (-T) T, HasDerivAt y (B t (y t)) t := by
    intro T
    obtain ⟨h, hpos, hh1, hloc⟩ := L (|T| + 1)
    have P : ∀ N : ℕ, (N : ℝ) * (h / 2) ≤ |T| + 1 → ∃ y : ℝ → E, y 0 = x₀ ∧
        ∀ t ∈ Ioo (-((N + 1) * (h / 2))) ((N + 1) * (h / 2)), HasDerivAt y (B t (y t)) t := by
      intro N
      induction N with
      | zero =>
        intro _
        obtain ⟨y, hy0, hy⟩ := hloc 0 ⟨by linarith [abs_nonneg T], by linarith [abs_nonneg T]⟩ x₀
        refine ⟨y, hy0, fun t ht => hy t ⟨?_, ?_⟩⟩
        · simp at ht; linarith [ht.1]
        · simp at ht; linarith [ht.2]
      | succ N ih =>
        intro hN
        push_cast at hN
        obtain ⟨y, hy0, hy⟩ := ih (by nlinarith)
        set r : ℝ := (N + 1) * (h / 2) with hr
        have hr0 : h / 2 ≤ r := by rw [hr]; nlinarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
        set s : ℝ := r - h / 2 with hs
        have hs0 : 0 ≤ s := by linarith
        have hsT : s ≤ |T| + 1 := by rw [hs, hr]; nlinarith
        obtain ⟨z, hz0, hz⟩ := hloc s ⟨by linarith [abs_nonneg T], hsT⟩ (y s)
        have hyz : EqOn y z (Ioo (max (-r) (s - h)) r) :=
          U _ _ s y z ⟨max_lt (by linarith) (by linarith), by linarith⟩
            (fun t ht => hy t ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩)
            (fun t ht => hz t ⟨(le_max_right _ _).trans_lt ht.1, by linarith [ht.2]⟩) hz0.symm
        obtain ⟨w, hw, hwy, -⟩ := G (-r) r (s - h) (s + h) y z (by linarith) (by linarith)
          (by linarith) hy hz hyz
        have hsT' : -s ∈ Icc (-(|T| + 1)) (|T| + 1) := ⟨by linarith, by linarith⟩
        obtain ⟨z', hz'0, hz'⟩ := hloc (-s) hsT' (w (-s))
        have hz'w : EqOn z' w (Ioo (max (-s - h) (-r)) (-s + h)) :=
          U _ _ (-s) z' w ⟨max_lt (by linarith) (by linarith), by linarith⟩
            (fun t ht => hz' t ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩)
            (fun t ht => hw t ⟨(le_max_right _ _).trans_lt ht.1, by linarith [ht.2]⟩) hz'0
        obtain ⟨w', hw', -, hw'w⟩ := G (-s - h) (-s + h) (-r) (s + h) z' w (by linarith)
          (by linarith) (by linarith) hz' hw hz'w
        refine ⟨w', ?_, fun t ht => hw' t ⟨?_, ?_⟩⟩
        · rw [hw'w ⟨max_lt (by linarith) (by linarith), by linarith⟩,
            hwy ⟨by linarith, by linarith⟩, hy0]
        · have := ht.1; push_cast at this; linarith
        · have := ht.2; push_cast at this; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * (|T| + 1) / h)
    classical
    let N₀ := Nat.find (⟨N, hN⟩ : ∃ N : ℕ, 2 * (|T| + 1) / h < N)
    have hN₀ : 2 * (|T| + 1) / h < N₀ := Nat.find_spec (⟨N, hN⟩ : ∃ N : ℕ, 2 * (|T| + 1) / h < N)
    have hN₀pos : 0 < N₀ := by
      have : (0 : ℝ) < N₀ := lt_of_le_of_lt (by positivity) hN₀
      exact_mod_cast this
    obtain ⟨M, hM⟩ : ∃ M, N₀ = M + 1 := ⟨N₀ - 1, by omega⟩
    have hMle : ¬ (2 * (|T| + 1) / h < M) := Nat.find_min _ (by omega : M < N₀)
    push_neg at hMle
    have hMb : (M : ℝ) * (h / 2) ≤ |T| + 1 := by
      rw [le_div_iff₀ hpos] at hMle; linarith
    obtain ⟨y, hy0, hy⟩ := P M hMb
    refine ⟨y, hy0, fun t ht => hy t ⟨?_, ?_⟩⟩
    · have h1 : 2 * (|T| + 1) < (M + 1 : ℝ) * h := by
        have := hN₀; rw [hM, div_lt_iff₀ hpos] at this; push_cast at this; linarith
      have := ht.1; have := le_abs_self T; nlinarith
    · have h1 : 2 * (|T| + 1) < (M + 1 : ℝ) * h := by
        have := hN₀; rw [hM, div_lt_iff₀ hpos] at this; push_cast at this; linarith
      have := ht.2; have := le_abs_self T; nlinarith
  choose Y hY0 hY using Ex
  have agree : ∀ T₁ T₂ u, |u| < T₁ → |u| < T₂ → Y T₁ u = Y T₂ u := by
    intro T₁ T₂ u h1 h2
    have hm : |u| < min T₁ T₂ := lt_min h1 h2
    refine U (-(min T₁ T₂)) (min T₁ T₂) 0 (Y T₁) (Y T₂) ⟨?_, ?_⟩
      (fun t ht => hY T₁ t ⟨?_, ?_⟩) (fun t ht => hY T₂ t ⟨?_, ?_⟩) (by rw [hY0, hY0]) ?_
    all_goals first
      | (have := abs_nonneg u; linarith [min_le_left T₁ T₂, min_le_right T₁ T₂])
      | (linarith [ht.1, ht.2, min_le_left T₁ T₂, min_le_right T₁ T₂])
      | exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  refine ⟨fun t => Y (|t| + 1) t, ⟨?_, fun t => ?_⟩, ?_⟩
  · simp only; exact hY0 _
  · have hev : (fun u => Y (|u| + 1) u) =ᶠ[𝓝 t] Y (|t| + 1) := by
      have hc : Continuous fun u : ℝ => |u| := continuous_abs
      filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds (show |t| < |t| + 1 by linarith))]
        with u hu
      exact agree _ _ u (by linarith) hu
    have hd := (hY (|t| + 1) t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)
    have := hd.congr_of_eventuallyEq hev
    simpa [agree (|t| + 1) (|t| + 1) t (by linarith) (by linarith)] using this
  · rintro Ψ ⟨hΨ0, hΨ⟩
    funext t
    have h1 := U (-(|t| + 1)) (|t| + 1) 0 Ψ (Y (|t| + 1))
      ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
      (fun u _ => hΨ u) (fun u hu => hY _ u hu) (by rw [hΨ0, hY0])
    exact h1 ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Kato's perturbation formulas at a point `s ∈ S` for a differentiable operator family `H`. -/
theorem kato_at_general (H P R : ℝ → (E →L[ℂ] E)) (D : E →L[ℂ] E) (lam : ℝ → ℝ) (γ : ℝ)
    (hγ : 0 < γ) (S : Set ℝ) (s : ℝ) (hs : s ∈ S)
    (hHd : HasDerivWithinAt H D S s)
    (hHP : ∀ t ∈ S, H t * P t = (lam t : ℂ) • P t)
    (hPH : ∀ t ∈ S, P t * H t = (lam t : ℂ) • P t)
    (hHR : ∀ t ∈ S, H t * R t - (lam t : ℂ) • R t = 1 - P t)
    (hRH : ∀ t ∈ S, R t * H t - (lam t : ℂ) • R t = 1 - P t)
    (hRP : ∀ t ∈ S, R t * P t = 0) (hPR : ∀ t ∈ S, P t * R t = 0)
    (hPn : ∀ t ∈ S, ‖P t‖ ≤ 1) (hRn : ∀ t ∈ S, ‖R t‖ ≤ γ⁻¹)
    (hPP : P s * P s = P s)
    (hlam : ContinuousWithinAt lam S s)
    (φ : (E →L[ℂ] E) →L[ℂ] ℂ) (hφP : φ (P s) = 1) :
    HasDerivWithinAt P (-(R s * D * P s + P s * D * R s)) S s ∧
    HasDerivWithinAt R (φ (P s * D * P s) • (R s * R s) - R s * D * R s
        - R s * (-(R s * D * P s + P s * D * R s))
        - (-(R s * D * P s + P s * D * R s)) * R s) S s := by
  set P0 := P s with hP0def
  set R0 := R s with hR0def
  set H0 := H s with hH0def
  set g := γ⁻¹ with hgdef
  have hg : 0 < g := inv_pos.mpr hγ
  have hgγ : γ * g = 1 := mul_inv_cancel₀ hγ.ne'
  have hP0n : ‖P0‖ ≤ 1 := hPn s hs
  have hR0n : ‖R0‖ ≤ g := hRn s hs
  set c : ℝ → ℂ := fun t => (((t - s)⁻¹ : ℝ) : ℂ) with hcdef
  have hch : ∀ t, t ≠ s → c t * ((t - s : ℝ) : ℂ) = 1 := by
    intro t hts
    simp only [hcdef]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hts), Complex.ofReal_one]
  have hsl : ∀ (F : ℝ → (E →L[ℂ] E)) t, slope F s t = c t • (F t - F s) := by
    intro F t
    rw [slope_def_module, RCLike.real_smul_eq_coe_smul (K := ℂ)]; rfl
  let ΔH : ℝ → (E →L[ℂ] E) := fun t => if t = s then D else c t • (H t - H0)
  have hH : ∀ t, H t = H0 + ((t - s : ℝ) : ℂ) • ΔH t := by
    intro t
    by_cases hts : t = s
    · simp [ΔH, hts, hH0def]
    · have hc1 : ((t - s : ℝ) : ℂ) * c t = 1 := by rw [mul_comm]; exact hch t hts
      simp only [ΔH, if_neg hts, smul_smul, hc1, one_smul, hH0def, add_sub_cancel]
  have id1 : ∀ t ∈ S, P t - P0 = ((lam t : ℂ) - lam s) • (R0 * (P t - P0) - (P t - P0) * R t)
      - ((t - s : ℝ) : ℂ) • (R0 * ΔH t * P t + P0 * ΔH t * R t) := by
    intro t ht
    have e1 : (1 - P0) * P t = ((lam t : ℂ) - lam s) • (R0 * (P t - P0))
        - ((t - s : ℝ) : ℂ) • (R0 * ΔH t * P t) := by
      calc (1 - P0) * P t = (R0 * H0 - (lam s : ℂ) • R0) * P t := by rw [hRH s hs]
        _ = R0 * (H t * P t) - ((t - s : ℝ) : ℂ) • (R0 * ΔH t * P t)
            - (lam s : ℂ) • (R0 * P t) := by
          rw [hH t]
          simp only [mul_add, add_mul, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
          module
        _ = _ := by
          rw [hHP t ht, mul_smul_comm, mul_sub, hRP s hs, sub_zero]
          module
    have e2 : P0 * (1 - P t) = ((lam t : ℂ) - lam s) • ((P t - P0) * R t)
        + ((t - s : ℝ) : ℂ) • (P0 * ΔH t * R t) := by
      calc P0 * (1 - P t) = P0 * (H t * R t - (lam t : ℂ) • R t) := by rw [hHR t ht]
        _ = (P0 * H0) * R t + ((t - s : ℝ) : ℂ) • (P0 * ΔH t * R t)
            - (lam t : ℂ) • (P0 * R t) := by
          rw [hH t]
          simp only [mul_add, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc]
        _ = _ := by
          rw [hPH s hs, smul_mul_assoc, sub_mul, hPR t ht]
          module
    calc P t - P0 = (1 - P0) * P t - P0 * (1 - P t) := by noncomm_ring
      _ = _ := by rw [e1, e2]; module
  have idY : ∀ t ∈ S, R t - R0 = ((lam t : ℂ) - lam s) • (R0 * R t)
      - ((t - s : ℝ) : ℂ) • (R0 * ΔH t * R t) - R0 * (P t - P0) - (P t - P0) * R t := by
    intro t ht
    have e34 : R0 * (1 - P t) - (1 - P0) * R t = ((t - s : ℝ) : ℂ) • (R0 * ΔH t * R t)
        - ((lam t : ℂ) - lam s) • (R0 * R t) := by
      rw [← hHR t ht, ← hRH s hs, hH t]
      simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
      module
    have h1 := hRP s hs
    have h2 := hPR t ht
    calc R t - R0 = R t - R0 + R0 * P0 - P t * R t := by rw [h1, h2]; abel
      _ = -(R0 * (1 - P t) - (1 - P0) * R t) - R0 * (P t - P0) - (P t - P0) * R t := by
        noncomm_ring
      _ = _ := by rw [e34]; module
  have eL : ∀ t ∈ S, ((lam t : ℂ) - lam s) • (P0 * P t)
      = ((t - s : ℝ) : ℂ) • (P0 * ΔH t * P t) := by
    intro t ht
    have : (lam t : ℂ) • (P0 * P t) = (lam s : ℂ) • (P0 * P t)
        + ((t - s : ℝ) : ℂ) • (P0 * ΔH t * P t) := by
      calc (lam t : ℂ) • (P0 * P t) = P0 * (H t * P t) := by rw [hHP t ht, mul_smul_comm]
        _ = (P0 * H0) * P t + ((t - s : ℝ) : ℂ) • (P0 * ΔH t * P t) := by
          rw [hH t]
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
        _ = _ := by rw [hPH s hs, smul_mul_assoc]
    rw [sub_smul, this]; abel
  set L := 𝓝[S] s with hL
  have hle : 𝓝[S \ {s}] s ≤ L := nhdsWithin_mono _ Set.diff_subset
  have hΔH_slope : Tendsto ΔH (𝓝[S \ {s}] s) (𝓝 D) := by
    refine (hasDerivWithinAt_iff_tendsto_slope.mp hHd).congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have hts : t ≠ s := ht.2
    simp only [ΔH, if_neg hts, hsl H t, hH0def]
  have hΔH : Tendsto ΔH L (𝓝 D) := by
    intro U hU
    rw [Filter.mem_map, mem_nhdsWithin]
    obtain ⟨V, hVopen, hsV, hVU⟩ := mem_nhdsWithin.mp (hΔH_slope hU)
    refine ⟨V, hVopen, hsV, fun t ht => ?_⟩
    by_cases hts : t = s
    · subst hts; simpa [ΔH] using mem_of_mem_nhds hU
    · exact hVU ⟨ht.1, ht.2, hts⟩
  have hδ : Tendsto (fun t => (lam t : ℂ) - lam s) L (𝓝 0) := by
    have h1 : Tendsto (fun t => (lam t : ℂ)) L (𝓝 (lam s : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hlam
    simpa using h1.sub_const (lam s : ℂ)
  have hδn : Tendsto (fun t => ‖(lam t : ℂ) - lam s‖) L (𝓝 0) := by
    simpa using hδ.norm
  have hh : Tendsto (fun t : ℝ => ‖((t - s : ℝ) : ℂ)‖) L (𝓝 0) := by
    have : Tendsto (fun t : ℝ => ‖((t - s : ℝ) : ℂ)‖) (𝓝 s) (𝓝 ‖((s - s : ℝ) : ℂ)‖) :=
      (by fun_prop : Continuous fun t : ℝ => ‖((t - s : ℝ) : ℂ)‖).tendsto s
    simpa using this.mono_left nhdsWithin_le_nhds
  set D1 := ‖D‖ + 1 with hD1def
  have hD1pos : 0 < D1 := by positivity
  have hev : ∀ᶠ t in L, t ∈ S ∧ ‖(lam t : ℂ) - lam s‖ ≤ γ / 4 ∧ ‖ΔH t‖ ≤ D1 := by
    refine eventually_mem_nhdsWithin.and (Eventually.and ?_ ?_)
    · exact (hδn.eventually (gt_mem_nhds (by positivity : (0:ℝ) < γ / 4))).mono fun t ht => ht.le
    · exact (hΔH.norm.eventually (gt_mem_nhds (by linarith : ‖D‖ < D1))).mono fun t ht => ht.le
  have hXb : ∀ᶠ t in L, ‖P t - P0‖ ≤ 4 * g * D1 * ‖((t - s : ℝ) : ℂ)‖ := by
    filter_upwards [hev] with t ⟨ht, hδt, hΔHt⟩
    have hRt := hRn t ht
    have hPt := hPn t ht
    have b1 : ‖R0 * (P t - P0) - (P t - P0) * R t‖ ≤ 2 * g * ‖P t - P0‖ := by
      calc _ ≤ ‖R0‖ * ‖P t - P0‖ + ‖P t - P0‖ * ‖R t‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ g * ‖P t - P0‖ + ‖P t - P0‖ * g := by gcongr
        _ = _ := by ring
    have b2 : ‖R0 * ΔH t * P t + P0 * ΔH t * R t‖ ≤ 2 * g * D1 := by
      calc _ ≤ ‖R0‖ * ‖ΔH t‖ * ‖P t‖ + ‖P0‖ * ‖ΔH t‖ * ‖R t‖ :=
            (norm_add_le _ _).trans (add_le_add norm_mul₃_le norm_mul₃_le)
        _ ≤ g * D1 * 1 + 1 * D1 * g := by gcongr
        _ = _ := by ring
    have key : ‖P t - P0‖ ≤ ‖(lam t : ℂ) - lam s‖ * (2 * g * ‖P t - P0‖)
        + ‖((t - s : ℝ) : ℂ)‖ * (2 * g * D1) := by
      calc ‖P t - P0‖ = ‖_‖ := congrArg norm (id1 t ht)
        _ ≤ _ := norm_sub_le _ _
        _ ≤ _ := by rw [norm_smul, norm_smul]; gcongr
    have h4 : ‖(lam t : ℂ) - lam s‖ * (2 * g * ‖P t - P0‖) ≤ γ / 4 * (2 * g * ‖P t - P0‖) := by
      gcongr
    have h3 : γ / 4 * (2 * g * ‖P t - P0‖) = ‖P t - P0‖ / 2 := by
      linear_combination (‖P t - P0‖ / 2) * hgγ
    nlinarith
  have hX : Tendsto (fun t => P t - P0) L (𝓝 0) := by
    refine squeeze_zero_norm' hXb ?_
    simpa using hh.const_mul (4 * g * D1)
  have hYb : ∀ᶠ t in L, ‖R t - R0‖ ≤ ‖(lam t : ℂ) - lam s‖ * (g * g)
      + ‖((t - s : ℝ) : ℂ)‖ * (g * D1 * g) + 2 * g * ‖P t - P0‖ := by
    filter_upwards [hev] with t ⟨ht, _, hΔHt⟩
    have hRt := hRn t ht
    have c1 : ‖R0 * R t‖ ≤ g * g := (norm_mul_le _ _).trans (by gcongr)
    have c2 : ‖R0 * ΔH t * R t‖ ≤ g * D1 * g := norm_mul₃_le.trans (by gcongr)
    have c3 : ‖R0 * (P t - P0)‖ ≤ g * ‖P t - P0‖ := (norm_mul_le _ _).trans (by gcongr)
    have c4 : ‖(P t - P0) * R t‖ ≤ ‖P t - P0‖ * g := (norm_mul_le _ _).trans (by gcongr)
    have d1 := mul_le_mul_of_nonneg_left c1 (norm_nonneg ((lam t : ℂ) - lam s))
    have d2 := mul_le_mul_of_nonneg_left c2 (norm_nonneg ((t - s : ℝ) : ℂ))
    have n4 : ∀ a b c d : E →L[ℂ] E, ‖a - b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
      intro a b c d
      have := norm_sub_le (a - b - c) d
      have := norm_sub_le (a - b) c
      have := norm_sub_le a b
      linarith
    rw [idY t ht]
    calc _ ≤ ‖((lam t : ℂ) - lam s) • (R0 * R t)‖ + ‖((t - s : ℝ) : ℂ) • (R0 * ΔH t * R t)‖
          + ‖R0 * (P t - P0)‖ + ‖(P t - P0) * R t‖ :=
          n4 _ _ _ _
      _ ≤ _ := by rw [norm_smul, norm_smul]; linarith
  have hY : Tendsto (fun t => R t - R0) L (𝓝 0) := by
    refine squeeze_zero_norm' hYb ?_
    simpa using ((hδn.mul_const (g * g)).add (hh.mul_const (g * D1 * g))).add
      (hX.norm.const_mul (2 * g))
  have hPt : Tendsto P L (𝓝 P0) := by simpa using hX.add_const P0
  have hRt : Tendsto R L (𝓝 R0) := by simpa using hY.add_const R0
  have hev' : ∀ᶠ t in 𝓝[S \ {s}] s, ((t ∈ S ∧ ‖(lam t : ℂ) - lam s‖ ≤ γ / 4 ∧ ‖ΔH t‖ ≤ D1) ∧
      ‖P t - P0‖ ≤ 4 * g * D1 * ‖((t - s : ℝ) : ℂ)‖) ∧ t ∈ S \ {s} :=
    ((hev.and hXb).filter_mono hle).and eventually_mem_nhdsWithin
  set P' := -(R0 * D * P0 + P0 * D * R0) with hP'def
  have hBP_lim : Tendsto (fun t => (R0 * ΔH t * P t + P0 * ΔH t * R t) + P') L (𝓝 0) := by
    have h1 : Tendsto (fun t => R0 * ΔH t * P t + P0 * ΔH t * R t) L (𝓝 (-P')) := by
      rw [hP'def, neg_neg]
      exact (((tendsto_const_nhds (x := R0)).mul hΔH).mul hPt).add
        (((tendsto_const_nhds (x := P0)).mul hΔH).mul hRt)
    simpa using h1.add_const P'
  have hG : Tendsto (fun t => c t • (P t - P0)) (𝓝[S \ {s}] s) (𝓝 P') := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (g := fun t =>
      ‖(lam t : ℂ) - lam s‖ * (2 * g * (4 * g * D1))
        + ‖(R0 * ΔH t * P t + P0 * ΔH t * R t) + P'‖) ?_ ?_
    · filter_upwards [hev'] with t ⟨⟨⟨ht, _, _⟩, hXt⟩, hts⟩
      have hts : t ≠ s := hts.2
      have hRt := hRn t ht
      have hcn : ‖c t‖ * ‖((t - s : ℝ) : ℂ)‖ = 1 := by
        rw [← norm_mul, hch t hts, norm_one]
      have hGn : ‖c t • (P t - P0)‖ ≤ 4 * g * D1 := by
        rw [norm_smul]
        calc ‖c t‖ * ‖P t - P0‖ ≤ ‖c t‖ * (4 * g * D1 * ‖((t - s : ℝ) : ℂ)‖) := by gcongr
          _ = 4 * g * D1 * (‖c t‖ * ‖((t - s : ℝ) : ℂ)‖) := by ring
          _ = _ := by rw [hcn, mul_one]
      have hGid : c t • (P t - P0) = ((lam t : ℂ) - lam s) • (R0 * (c t • (P t - P0))
          - (c t • (P t - P0)) * R t) - (R0 * ΔH t * P t + P0 * ΔH t * R t) := by
        calc c t • (P t - P0) = c t • (((lam t : ℂ) - lam s) • (R0 * (P t - P0)
              - (P t - P0) * R t)
            - ((t - s : ℝ) : ℂ) • (R0 * ΔH t * P t + P0 * ΔH t * R t)) := by rw [← id1 t ht]
          _ = ((lam t : ℂ) - lam s) • (R0 * (c t • (P t - P0)) - (c t • (P t - P0)) * R t)
              - (c t * ((t - s : ℝ) : ℂ)) • (R0 * ΔH t * P t + P0 * ΔH t * R t) := by
            simp only [mul_smul_comm, smul_mul_assoc]
            module
          _ = _ := by rw [hch t hts, one_smul]
      have hdiff : c t • (P t - P0) - P' = ((lam t : ℂ) - lam s) • (R0 * (c t • (P t - P0))
          - (c t • (P t - P0)) * R t) - ((R0 * ΔH t * P t + P0 * ΔH t * R t) + P') := by
        conv_lhs => rw [hGid]
        abel
      rw [hdiff]
      have e1 : ‖R0 * (c t • (P t - P0)) - (c t • (P t - P0)) * R t‖
          ≤ 2 * g * (4 * g * D1) := by
        calc _ ≤ ‖R0‖ * ‖c t • (P t - P0)‖ + ‖c t • (P t - P0)‖ * ‖R t‖ :=
              (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
          _ ≤ g * (4 * g * D1) + (4 * g * D1) * g := by gcongr
          _ = _ := by ring
      have e3 := mul_le_mul_of_nonneg_left e1 (norm_nonneg ((lam t : ℂ) - lam s))
      calc _ ≤ _ := norm_sub_le _ _
        _ ≤ _ := by rw [norm_smul]; linarith
    · have := (hδn.mul_const (2 * g * (4 * g * D1))).add hBP_lim.norm
      simpa using this.mono_left hle
  have hφ1 : Tendsto (fun t => φ (P0 * P t)) L (𝓝 1) := by
    have : Tendsto (fun t => φ (P0 * P t)) L (𝓝 (φ (P0 * P0))) :=
      ((φ.continuous.comp (continuous_mul_left P0)).tendsto P0).comp hPt
    rwa [hPP, hφP] at this
  have hφ2 : Tendsto (fun t => φ (P0 * ΔH t * P t)) L (𝓝 (φ (P0 * D * P0))) :=
    (φ.continuous.tendsto (P0 * D * P0)).comp
      (((tendsto_const_nhds (x := P0)).mul hΔH).mul hPt)
  have hlam' : Tendsto (fun t => c t * ((lam t : ℂ) - lam s)) (𝓝[S \ {s}] s)
      (𝓝 (φ (P0 * D * P0))) := by
    have := (hφ2.div hφ1 one_ne_zero).mono_left hle
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [hev', (hφ1.eventually_ne one_ne_zero).filter_mono hle]
      with t ⟨⟨⟨ht, _⟩, _⟩, hts⟩ hne
    have hts : t ≠ s := hts.2
    rw [Pi.div_apply, div_eq_iff hne]
    have h1 := congrArg φ (eL t ht)
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    calc φ (P0 * ΔH t * P t) = (c t * ((t - s : ℝ) : ℂ)) * φ (P0 * ΔH t * P t) := by
          rw [hch t hts, one_mul]
      _ = c t * (((t - s : ℝ) : ℂ) * φ (P0 * ΔH t * P t)) := mul_assoc _ _ _
      _ = c t * (((lam t : ℂ) - lam s) * φ (P0 * P t)) := by rw [h1]
      _ = _ := by ring
  have hRt' := hRt.mono_left hle
  have hΔH' := hΔH.mono_left hle
  refine ⟨?_, ?_⟩
  · rw [hasDerivWithinAt_iff_tendsto_slope]
    exact hG.congr' (Eventually.of_forall fun t => (hsl P t).symm)
  · rw [hasDerivWithinAt_iff_tendsto_slope]
    have hK : Tendsto (fun t => (c t * ((lam t : ℂ) - lam s)) • (R0 * R t) - R0 * ΔH t * R t
        - R0 * (c t • (P t - P0)) - (c t • (P t - P0)) * R t) (𝓝[S \ {s}] s)
        (𝓝 (φ (P0 * D * P0) • (R0 * R0) - R0 * D * R0 - R0 * P' - P' * R0)) :=
      (((hlam'.smul ((tendsto_const_nhds (x := R0)).mul hRt')).sub
        (((tendsto_const_nhds (x := R0)).mul hΔH').mul hRt')).sub
        ((tendsto_const_nhds (x := R0)).mul hG)).sub (hG.mul hRt')
    refine hK.congr' ?_
    filter_upwards [hev'] with t ⟨⟨⟨ht, _⟩, _⟩, hts⟩
    have hts : t ≠ s := hts.2
    rw [hsl R t, ← hR0def, idY t ht]
    calc _ = (c t * ((lam t : ℂ) - lam s)) • (R0 * R t)
          - (c t * ((t - s : ℝ) : ℂ)) • (R0 * ΔH t * R t) - R0 * (c t • (P t - P0))
          - (c t • (P t - P0)) * R t := by rw [hch t hts, one_smul]
      _ = _ := by simp only [mul_smul_comm, smul_mul_assoc]; module

theorem bound_R' (P R D : E →L[ℂ] E)
    (l : ℂ) (g : ℝ) (hg : 0 ≤ g) (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ g) (hl : ‖l‖ ≤ ‖D‖) :
    ‖l • (R * R) - R * D * R - R * (-(R * D * P + P * D * R))
      - (-(R * D * P + P * D * R)) * R‖ ≤ 6 * g ^ 2 * ‖D‖ := by
  set Q := -(R * D * P + P * D * R) with hQdef
  have hQ : ‖Q‖ ≤ 2 * g * ‖D‖ := by
    rw [hQdef, norm_neg]
    calc _ ≤ ‖R‖ * ‖D‖ * ‖P‖ + ‖P‖ * ‖D‖ * ‖R‖ :=
          (norm_add_le _ _).trans (add_le_add norm_mul₃_le norm_mul₃_le)
      _ ≤ g * ‖D‖ * 1 + 1 * ‖D‖ * g := by gcongr
      _ = _ := by ring
  have a1 : ‖l • (R * R)‖ ≤ 1 * (g ^ 2 * ‖D‖) := by
    rw [norm_smul]
    calc _ ≤ ‖D‖ * (g * g) :=
          mul_le_mul hl ((norm_mul_le _ _).trans (by gcongr)) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have a2 : ‖R * D * R‖ ≤ 1 * (g ^ 2 * ‖D‖) :=
    norm_mul₃_le.trans ((by gcongr : ‖R‖ * ‖D‖ * ‖R‖ ≤ g * ‖D‖ * g).trans (le_of_eq (by ring)))
  have a3 : ‖R * Q‖ ≤ 2 * (g ^ 2 * ‖D‖) :=
    (norm_mul_le _ _).trans ((by gcongr : ‖R‖ * ‖Q‖ ≤ g * (2 * g * ‖D‖)).trans
      (le_of_eq (by ring)))
  have a4 : ‖Q * R‖ ≤ 2 * (g ^ 2 * ‖D‖) :=
    (norm_mul_le _ _).trans ((by gcongr : ‖Q‖ * ‖R‖ ≤ (2 * g * ‖D‖) * g).trans
      (le_of_eq (by ring)))
  have n4 : ∀ a b c d : E →L[ℂ] E, ‖a - b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    have := norm_sub_le (a - b - c) d
    have := norm_sub_le (a - b) c
    have := norm_sub_le a b
    linarith
  have := n4 (l • (R * R)) (R * D * R) (R * Q) (Q * R)
  have e : 6 * g ^ 2 * ‖D‖ = 6 * (g ^ 2 * ‖D‖) := by ring
  rw [e]; linarith

structure Good {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (lam Δ : ℝ)
    (P R : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (u : EuclideanSpace ℂ ι) : Prop where
  hHP : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A * P = (lam : ℂ) • P
  hPH : P * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A = (lam : ℂ) • P
  hHR : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A * R - (lam : ℂ) • R = 1 - P
  hRH : R * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A - (lam : ℂ) • R = 1 - P
  hRP : R * P = 0
  hPR : P * R = 0
  hPP : P * P = P
  hPn : ‖P‖ ≤ 1
  hRn : ‖R‖ ≤ Δ⁻¹
  hinner : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y)
  hfix : ∀ x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A x = (lam : ℂ) • x → P x = x
  hun : ‖u‖ = 1
  hPu : P u = u

theorem pointwise {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (lam Δ : ℝ)
    (hΔ : 0 < Δ) (hA : HasGapAround A lam Δ) :
    ∃ (P R : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (u : EuclideanSpace ℂ ι),
      Good A lam Δ P R u := by
  obtain ⟨hH, ⟨k0, hk0, huniq⟩, hgap⟩ := hA
  set b := hH.eigenvectorBasis with hbdef
  set e := hH.eigenvalues with hedef
  set eqv := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) with heqv
  have hbr : ∀ i, ascEigenvalues A (Fin.rev (eqv.symm i)) = e i := by
    intro i
    simp only [ascEigenvalues, dif_pos hH, Fin.rev_rev]
    rfl
  set i0 := eqv (Fin.rev k0) with hi0def
  have he0 : e i0 = lam := by
    rw [← hbr i0, hi0def, Equiv.symm_apply_apply, Fin.rev_rev, hk0]
  have hne : ∀ i, i ≠ i0 → e i ≠ lam := by
    intro i hi he
    apply hi
    have := huniq _ ((hbr i).trans he)
    rw [hi0def, ← this, Fin.rev_rev, Equiv.apply_symm_apply]
  have hgi : ∀ i, i ≠ i0 → Δ ≤ |e i - lam| := by
    intro i hi
    have := hgap (Fin.rev (eqv.symm i))
    rw [hbr i] at this
    exact this (hne i hi)
  have hz : ∀ i, i ≠ i0 → (e i : ℂ) - lam ≠ 0 := by
    intro i hi h
    exact hne i hi (by exact_mod_cast sub_eq_zero.mp h)
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hb : ∀ i, Matrix.toEuclideanLin A (b i) = (e i : ℂ) • b i := by
    intro i
    rw [Matrix.toEuclideanLin_apply, hbdef, hH.mulVec_eigenvectorBasis]
    ext j
    simp [RCLike.real_smul_eq_coe_mul, hedef]
  have hAx : ∀ x i, b.repr (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A x) i = (e i : ℂ) * b.repr x i := by
    intro x i
    rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
    have hact : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A x = Matrix.toEuclideanLin A x := rfl
    rw [hact, ← hsym (b i) x, hb i, inner_smul_left]
    simp
  let N : (ι → ℂ) → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := fun c =>
    (b.repr.symm.toContinuousLinearEquiv : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) ∘L
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (Matrix.diagonal c) ∘L
      (b.repr.toContinuousLinearEquiv : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
  have hN : ∀ c x i, b.repr (N c x) i = c i * b.repr x i := by
    intro c x i
    show b.repr (b.repr.symm (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (Matrix.diagonal c) (b.repr x))) i = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    show (WithLp.toLp 2 (Matrix.mulVec (Matrix.diagonal c) (WithLp.ofLp (b.repr x)))) i = _
    simp [Matrix.mulVec_diagonal]
  have hNn : ∀ (c : ι → ℂ) (M : ℝ), 0 ≤ M → (∀ i, ‖c i‖ ≤ M) → ‖N c‖ ≤ M := by
    intro c M hM hc
    refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
    rw [← b.repr.norm_map (N c x), ← b.repr.norm_map x, EuclideanSpace.norm_eq,
      EuclideanSpace.norm_eq, ← Real.sqrt_sq hM, ← Real.sqrt_mul (sq_nonneg M)]
    apply Real.sqrt_le_sqrt
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hN, norm_mul, mul_pow]
    gcongr
    exact hc i
  have hext : ∀ F G : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι,
      (∀ x i, b.repr (F x) i = b.repr (G x) i) → F = G := fun F G h =>
    ContinuousLinearMap.ext fun x => b.repr.injective (by ext i; exact h x i)
  set p : ι → ℂ := fun i => if i = i0 then 1 else 0 with hpdef
  set r : ι → ℂ := fun i => if i = i0 then 0 else ((e i : ℂ) - lam)⁻¹ with hrdef
  have hr1 : ∀ i, i ≠ i0 → ((e i : ℂ) - lam) * r i = 1 := by
    intro i hi
    simp only [hrdef, if_neg hi]
    exact mul_inv_cancel₀ (hz i hi)
  refine ⟨N p, N r, b i0, ?_⟩
  constructor
  · apply hext; intro x i
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul,
      PiLp.smul_apply, smul_eq_mul, hN, hAx]
    by_cases hi : i = i0
    · simp [hpdef, hi, he0]
    · simp [hpdef, hi]
  · apply hext; intro x i
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul,
      PiLp.smul_apply, smul_eq_mul, hN, hAx]
    by_cases hi : i = i0
    · simp [hpdef, hi, he0]
    · simp [hpdef, hi]
  · apply hext; intro x i
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_sub, map_smul,
      PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hN, hAx]
    by_cases hi : i = i0
    · simp [hpdef, hrdef, hi]
    · have h1 := hr1 i hi
      simp only [hpdef, if_neg hi]
      linear_combination (b.repr x i) * h1
  · apply hext; intro x i
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_sub, map_smul,
      PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hN, hAx]
    by_cases hi : i = i0
    · simp [hpdef, hrdef, hi]
    · have h1 := hr1 i hi
      simp only [hpdef, if_neg hi]
      linear_combination (b.repr x i) * h1
  · apply hext; intro x i
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply, map_zero,
      PiLp.zero_apply, hN]
    by_cases hi : i = i0 <;> simp [hpdef, hrdef, hi]
  · apply hext; intro x i
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply, map_zero,
      PiLp.zero_apply, hN]
    by_cases hi : i = i0 <;> simp [hpdef, hrdef, hi]
  · apply hext; intro x i
    simp only [ContinuousLinearMap.mul_apply, hN]
    by_cases hi : i = i0 <;> simp [hpdef, hi]
  · refine hNn p 1 zero_le_one fun i => ?_
    by_cases hi : i = i0 <;> simp [hpdef, hi]
  · refine hNn r Δ⁻¹ (inv_nonneg.mpr hΔ.le) fun i => ?_
    by_cases hi : i = i0
    · simp [hrdef, hi, hΔ.le]
    · simp only [hrdef, if_neg hi, norm_inv]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact inv_anti₀ hΔ (hgi i hi)
  · intro x y
    rw [← b.repr.inner_map_map (N p x) y, ← b.repr.inner_map_map x (N p y)]
    simp only [PiLp.inner_apply, hN]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = i0 <;> simp [hpdef, hi]
  · intro x hx
    apply b.repr.injective
    ext i
    have h1 := congrArg (fun y => b.repr y i) hx
    simp only [hAx, map_smul, PiLp.smul_apply, smul_eq_mul] at h1
    rw [hN]
    by_cases hi : i = i0
    · simp [hpdef, hi]
    · have h2 : ((e i : ℂ) - lam) * b.repr x i = 0 := by rw [sub_mul, h1, sub_self]
      have h3 := (mul_eq_zero.mp h2).resolve_left (hz i hi)
      simp [hpdef, hi, h3]
  · exact b.orthonormal.1 i0
  · apply b.repr.injective
    ext i
    rw [hN, OrthonormalBasis.repr_self]
    by_cases hi : i = i0 <;> simp [hpdef, hi, EuclideanSpace.single_apply]

theorem spectral_projector_regular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H1 : ℝ → Matrix ι ι ℂ)
    (hHd : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t))
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H1 s)) (Set.Icc 0 1) s)
    (hH1c : ContinuousOn (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H1 t)) (Set.Icc 0 1))
    (lam Δ : ℝ → ℝ) (hlam : ContinuousOn lam (Set.Icc 0 1))
    (γ : ℝ) (hγ : 0 < γ)
    (hΔle : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ ≤ Δ s)
    (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) (lam s) (Δ s)) :
    ∃ P P' R R' : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι),
      ContinuousOn P' (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt P (P' s) (Set.Icc 0 1) s ∧
        HasDerivWithinAt R (R' s) (Set.Icc 0 1) s ∧
        (∀ x, P s (P s x) = P s x) ∧
        (∀ x y, inner ℂ (P s x) y = inner ℂ x (P s y)) ∧
        (∀ x, act (H s) x = (lam s : ℂ) • x → P s x = x) ∧
        (∀ x, act (H s) (P s x) = (lam s : ℂ) • P s x) ∧
        (∀ x, act (H s) (R s x) - (lam s : ℂ) • R s x = x - P s x) ∧
        (∀ x, R s (P s x) = 0) ∧ (∀ x, P s (R s x) = 0) ∧
        (∀ x, P' s x = -R s (act (H1 s) (P s x)) - P s (act (H1 s) (R s x))) ∧
        ‖P s‖ ≤ 1 ∧ ‖R s‖ ≤ 1 / Δ s ∧ ‖R' s‖ ≤ 6 * specNorm (H1 s) / Δ s ^ 2 := by
  set S := Set.Icc (0 : ℝ) 1 with hS
  set D : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := fun t =>
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H1 t) with hD
  set Hclm : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := fun t =>
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t) with hHclm
  have hΔpos : ∀ t ∈ S, 0 < Δ t := fun t ht => lt_of_lt_of_le hγ (hΔle t ht)
  have hpt : ∀ t, ∃ (P R : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
      (v : EuclideanSpace ℂ ι), t ∈ S → Good (H t) (lam t) (Δ t) P R v := by
    intro t
    by_cases ht : t ∈ S
    · obtain ⟨P, R, v, h⟩ := pointwise (H t) (lam t) (Δ t) (hΔpos t ht) (hgap t ht)
      exact ⟨P, R, v, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h ht⟩
  choose P R v hG using hpt
  have hRn_γ : ∀ t ∈ S, ‖R t‖ ≤ γ⁻¹ := fun t ht =>
    (hG t ht).hRn.trans (inv_anti₀ hγ (hΔle t ht))
  let φ : ℝ → ((EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) →L[ℂ] ℂ) := fun t =>
    (innerSL ℂ (v t)).comp (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ ι) (v t))
  have hφ : ∀ t (X : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι),
      φ t X = inner ℂ (v t) (X (v t)) := fun t X => rfl
  have hK : ∀ s ∈ S, _ := fun s hs =>
    kato_at_general Hclm P R (D s) lam γ hγ S s hs (hHd s hs)
      (fun t ht => (hG t ht).hHP) (fun t ht => (hG t ht).hPH) (fun t ht => (hG t ht).hHR)
      (fun t ht => (hG t ht).hRH) (fun t ht => (hG t ht).hRP) (fun t ht => (hG t ht).hPR)
      (fun t ht => (hG t ht).hPn) hRn_γ (hG s hs).hPP (hlam s hs) (φ s)
      (by
        rw [hφ, (hG s hs).hPu, inner_self_eq_norm_sq_to_K, (hG s hs).hun]
        simp)
  refine ⟨P, fun t => -(R t * D t * P t + P t * D t * R t), R,
    fun t => φ t (P t * D t * P t) • (R t * R t) - R t * D t * R t
      - R t * (-(R t * D t * P t + P t * D t * R t))
      - (-(R t * D t * P t + P t * D t * R t)) * R t,
    ?_, fun s hs => ?_⟩
  · intro s hs
    have cP := (hK s hs).1.continuousWithinAt
    have cR := (hK s hs).2.continuousWithinAt
    have cD := hH1c s hs
    exact (((cR.mul cD).mul cP).add ((cP.mul cD).mul cR)).neg
  have G := hG s hs
  have hΔs : 0 < Δ s := hΔpos s hs
  refine ⟨(hK s hs).1, (hK s hs).2, fun x => ?_, G.hinner, fun x hx => G.hfix x hx,
    fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, G.hPn,
    by rw [one_div]; exact G.hRn, ?_⟩
  · have := congrArg (fun F => F x) G.hPP
    simpa only [ContinuousLinearMap.mul_apply] using this
  · have := congrArg (fun F => F x) G.hHP
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply] at this
    exact this
  · have := congrArg (fun F => F x) G.hHR
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at this
    exact this
  · have := congrArg (fun F => F x) G.hRP
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply] using this
  · have := congrArg (fun F => F x) G.hPR
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply] using this
  · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.mul_apply]
    rw [neg_add, ← sub_eq_add_neg]
    rfl
  · have hDn : specNorm (H1 s) = ‖D s‖ := rfl
    have hl : ‖φ s (P s * D s * P s)‖ ≤ ‖D s‖ := by
      rw [hφ]
      calc _ ≤ ‖v s‖ * ‖(P s * D s * P s) (v s)‖ := norm_inner_le_norm _ _
        _ ≤ 1 * (‖P s * D s * P s‖ * ‖v s‖) := by
          have := (P s * D s * P s).le_opNorm (v s); rw [G.hun] at this ⊢; simpa using this
        _ ≤ 1 * ((‖P s‖ * ‖D s‖ * ‖P s‖) * 1) := by rw [G.hun]; gcongr; exact norm_mul₃_le
        _ ≤ 1 * ((1 * ‖D s‖ * 1) * 1) := by gcongr <;> exact G.hPn
        _ = ‖D s‖ := by ring
    have := bound_R' (P s) (R s) (D s) (φ s (P s * D s * P s)) (Δ s)⁻¹
      (inv_nonneg.mpr hΔs.le) G.hPn G.hRn hl
    rw [hDn]
    calc _ ≤ 6 * (Δ s)⁻¹ ^ 2 * ‖D s‖ := this
      _ = _ := by field_simp

theorem adiabatic_frame_general {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H1 H2 : ℝ → Matrix ι ι ℂ)
    (hHd : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t))
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H1 s)) (Set.Icc 0 1) s)
    (hH1d : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H1 t))
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H2 s)) (Set.Icc 0 1) s)
    (lam Δ : ℝ → ℝ) (hlam : ContinuousOn lam (Set.Icc 0 1))
    (φ0 : EuclideanSpace ℂ ι) (hφ0 : IsState φ0) (hφ0e : act (H 0) φ0 = (lam 0 : ℂ) • φ0)
    (γ : ℝ) (hγ : 0 < γ)
    (hΔle : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ ≤ Δ s)
    (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) (lam s) (Δ s)) :
    ∃ u u' v v' : ℝ → EuclideanSpace ℂ ι, u 0 = φ0 ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt u (u' s) (Set.Icc 0 1) s ∧ HasDerivWithinAt v (v' s) (Set.Icc 0 1) s ∧
        IsState (u s) ∧ act (H s) (u s) = (lam s : ℂ) • u s ∧
        act (H s) (v s) - (lam s : ℂ) • v s = u' s ∧
        ‖u' s‖ ≤ specNorm (H1 s) / Δ s ∧
        ‖v s‖ ≤ specNorm (H1 s) / Δ s ^ 2 ∧
        ‖v' s‖ ≤ 13 * specNorm (H1 s) ^ 2 / Δ s ^ 3 + specNorm (H2 s) / Δ s ^ 2 := by
  have hH1c : ContinuousOn (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H1 t)) (Set.Icc 0 1) :=
    fun s hs => (hH1d s hs).continuousWithinAt
  obtain ⟨P, P', R, R', hP'c, hS⟩ :=
    spectral_projector_regular H H1 hHd hH1c lam Δ hlam γ hγ hΔle hgap
  set Dl : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H1 t) with hDldef
  set D2l : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H2 t) with hD2ldef
  have hDl : ∀ t x, act (H1 t) x = Dl t x := fun _ _ => rfl
  have hDln : ∀ t, ‖Dl t‖ = specNorm (H1 t) := fun _ => rfl
  have hD2ln : ∀ t, ‖D2l t‖ = specNorm (H2 t) := fun _ => rfl
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have key : ∀ (L : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (x : EuclideanSpace ℂ ι)
      (a b : ℝ), ‖L‖ ≤ a → ‖x‖ ≤ b → 0 ≤ a → ‖L x‖ ≤ a * b := fun L x a b hL hx ha =>
    (L.le_opNorm x).trans (mul_le_mul hL hx (norm_nonneg _) ha)
  have hri : ∀ z w : EuclideanSpace ℂ ι, inner ℝ z w = (inner ℂ z w).re := by
    intro z w
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.inner, mul_comm]
  have hPc : ContinuousOn P (Set.Icc 0 1) := fun s hs => (hS s hs).1.continuousWithinAt
  have happ : ∀ {F : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)}
      {F0 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι} {y : ℝ → EuclideanSpace ℂ ι}
      {y0 : EuclideanSpace ℂ ι} {s : ℝ}, HasDerivWithinAt F F0 (Set.Icc 0 1) s →
      HasDerivWithinAt y y0 (Set.Icc 0 1) s →
      HasDerivWithinAt (fun t => F t (y t)) (F0 (y s) + F s y0) (Set.Icc 0 1) s := by
    intro F F0 y y0 s hF hy
    have hF' : HasDerivWithinAt (fun t => (F t).restrictScalars ℝ) (F0.restrictScalars ℝ)
        (Set.Icc 0 1) s :=
      (ContinuousLinearMap.restrictScalarsL ℂ (EuclideanSpace ℂ ι) (EuclideanSpace ℂ ι) ℝ
        ℝ).hasFDerivAt.comp_hasDerivWithinAt s hF
    exact hF'.clm_apply hy
  have hPPP : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, P s (P' s (P s x)) = 0 := by
    intro s hs x
    have hc0 : HasDerivWithinAt (fun _ : ℝ => P s x) 0 (Set.Icc 0 1) s :=
      hasDerivWithinAt_const _ _ _
    have h1 := happ (hS s hs).1 (happ (hS s hs).1 hc0)
    have h2 := happ (hS s hs).1 hc0
    have h2' : HasDerivWithinAt (fun t => P t (P t (P s x))) (P' s (P s x) + P s 0)
        (Set.Icc 0 1) s :=
      h2.congr_of_mem (fun t ht => (hS t ht).2.2.1 _) hs
    have h3 := (uniqueDiffOn_Icc zero_lt_one s hs).eq_deriv _ h1 h2'
    simp only [map_zero, add_zero, (hS s hs).2.2.1] at h3
    simpa using h3
  obtain ⟨M1, hM1_0, hM1⟩ : ∃ M1 : ℝ, 0 ≤ M1 ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖Dl s‖ ≤ M1 := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hH1c
    exact ⟨max C 0, le_max_right _ _, fun s hs => (hC s hs).trans (le_max_left _ _)⟩
  have hP'n : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖P' s x‖ ≤ 2 * M1 / γ * ‖x‖ := by
    intro s hs x
    obtain ⟨-, -, -, -, -, -, -, -, -, hP'f, hPn, hRn, -⟩ := hS s hs
    rw [hP'f, hDl, hDl]
    have hg : 0 ≤ 1 / γ := by positivity
    have hΔs : 0 < Δ s := lt_of_lt_of_le hγ (hΔle s hs)
    have hRn' : ‖R s‖ ≤ 1 / γ := hRn.trans (one_div_le_one_div_of_le hγ (hΔle s hs))
    have hDls : ‖Dl s‖ ≤ M1 := hM1 s hs
    have a1 : ‖R s (Dl s (P s x))‖ ≤ 1 / γ * (M1 * (1 * ‖x‖)) :=
      key _ _ _ _ hRn' (key _ _ _ _ hDls (key _ _ _ _ hPn le_rfl zero_le_one) hM1_0) hg
    have a2 : ‖P s (Dl s (R s x))‖ ≤ 1 * (M1 * (1 / γ * ‖x‖)) :=
      key _ _ _ _ hPn (key _ _ _ _ hDls (key _ _ _ _ hRn' le_rfl hg) hM1_0) zero_le_one
    calc ‖-R s (Dl s (P s x)) - P s (Dl s (R s x))‖
        ≤ ‖R s (Dl s (P s x))‖ + ‖P s (Dl s (R s x))‖ := by
          rw [sub_eq_add_neg, ← neg_add]; rw [norm_neg]; exact norm_add_le _ _
      _ ≤ 1 / γ * (M1 * (1 * ‖x‖)) + 1 * (M1 * (1 / γ * ‖x‖)) := add_le_add a1 a2
      _ = 2 * M1 / γ * ‖x‖ := by ring
  set c : ℝ → ℝ := fun t => (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) with hc
  have hcc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hcmem : ∀ t, c t ∈ Set.Icc (0 : ℝ) 1 := fun t => (Set.projIcc (0 : ℝ) 1 zero_le_one t).2
  have hceq : ∀ t ∈ Set.Icc (0 : ℝ) 1, c t = t := fun t ht => by
    simp [hc, Set.projIcc_of_mem _ ht]
  set A : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    fun t => (P' t).comp (P t) - (P t).comp (P' t) with hA
  have hAc : ContinuousOn A (Set.Icc 0 1) := (hP'c.clm_comp hPc).sub (hPc.clm_comp hP'c)
  set B : ℝ → (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) :=
    fun t => (A (c t)).restrictScalars ℝ with hB
  have hBc : Continuous B :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ (EuclideanSpace ℂ ι) (EuclideanSpace ℂ ι) ℝ
      ℝ).continuous.comp (hAc.comp_continuous hcc hcmem)
  obtain ⟨u, ⟨hu0, hud⟩, -⟩ := linearODE_existsUnique B hBc φ0
  have hudI : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt u (A s (u s)) (Set.Icc 0 1) s := by
    intro s hs
    have := (hud s).hasDerivWithinAt (s := Set.Icc 0 1)
    simpa [hB, hceq s hs] using this
  set w : ℝ → EuclideanSpace ℂ ι := fun t => u t - P t (u t) with hw
  have hwd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt w (-(P' s (w s))) (Set.Icc 0 1) s := by
    intro s hs
    have := (hudI s hs).sub (happ (hS s hs).1 (hudI s hs))
    refine this.congr_deriv ?_
    have hpp := (hS s hs).2.2.1
    have h3 := hPPP s hs (u s)
    simp only [hA, hw, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub,
      hpp, h3]
    abel
  have hw0 : w 0 = 0 := by
    simp only [hw, hu0, (hS 0 h0).2.2.2.2.1 φ0 hφ0e, sub_self]
  have hwz : ∀ s ∈ Set.Icc (0 : ℝ) 1, w s = 0 := by
    intro s hs
    have := norm_le_gronwallBound_of_norm_deriv_right_le (f := w) (δ := 0) (K := 2 * M1 / γ)
      (ε := 0) (a := 0) (b := 1) (fun t ht => (hwd t ht).continuousWithinAt)
      (fun t ht => (hwd t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht))
      (by rw [hw0, norm_zero])
      (fun t ht => by
        rw [norm_neg, add_zero]; exact hP'n t (Set.Ico_subset_Icc_self ht) _) s hs
    rw [gronwallBound_ε0_δ0] at this
    exact norm_le_zero_iff.mp this
  have huP : ∀ s ∈ Set.Icc (0 : ℝ) 1, P s (u s) = u s := fun s hs =>
    (sub_eq_zero.mp (hwz s hs)).symm
  have hRu : ∀ s ∈ Set.Icc (0 : ℝ) 1, R s (u s) = 0 := fun s hs => by
    rw [← huP s hs]; exact (hS s hs).2.2.2.2.2.2.2.1 _
  set u' : ℝ → EuclideanSpace ℂ ι := fun t => -R t (Dl t (u t)) with hu'
  have hAu : ∀ s ∈ Set.Icc (0 : ℝ) 1, A s (u s) = u' s := by
    intro s hs
    obtain ⟨-, -, hpp, -, -, -, -, hrp, hpr, hP'f, -⟩ := hS s hs
    simp only [hA, hu', ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      huP s hs, hP'f, hDl, hRu s hs, map_zero, map_sub, map_neg, hpr, neg_zero, sub_zero]
  have hud' : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt u (u' s) (Set.Icc 0 1) s :=
    fun s hs => (hudI s hs).congr_deriv (hAu s hs)
  have hinR : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, inner ℂ (u s) (R s y) = 0 := by
    intro s hs y
    rw [← huP s hs, (hS s hs).2.2.2.1, (hS s hs).2.2.2.2.2.2.2.2.1, inner_zero_right]
  have hun : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖u s‖ = 1 := by
    have hc := constant_of_has_deriv_right_zero (f := fun t => ‖u t‖ ^ 2) (a := 0) (b := 1)
      (fun t ht => ((hud' t ht).norm_sq).continuousWithinAt)
      (fun t ht => by
        have := ((hud' t (Set.Ico_subset_Icc_self ht)).norm_sq).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ht)
        refine this.congr_deriv ?_
        rw [hri, hu', inner_neg_right, hinR t (Set.Ico_subset_Icc_self ht)]
        simp)
    intro s hs
    have h := hc s hs
    simp only [hu0] at h
    rw [show ‖φ0‖ = 1 from hφ0, one_pow] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  set v : ℝ → EuclideanSpace ℂ ι := fun t => R t (u' t) with hv
  set v' : ℝ → EuclideanSpace ℂ ι := fun t =>
    -(R' t (R t (Dl t (u t))) + R t (R' t (Dl t (u t)) + R t (D2l t (u t) + Dl t (u' t)))) with hv'
  refine ⟨u, u', v, v', hu0, fun s hs => ?_⟩
  obtain ⟨-, hRd, hpp, hsa, -, hHP, hHR, hrp, hpr, -, hPn, hRn, hR'n⟩ := hS s hs
  have hΔs : 0 < Δ s := lt_of_lt_of_le hγ (hΔle s hs)
  have hg : 0 ≤ 1 / Δ s := by positivity
  set N1 := specNorm (H1 s) with hN1
  set N2 := specNorm (H2 s) with hN2
  have hN1_0 : 0 ≤ N1 := by rw [hN1, ← hDln s]; exact norm_nonneg _
  have hN2_0 : 0 ≤ N2 := by rw [hN2, ← hD2ln s]; exact norm_nonneg _
  have hR'0 : 0 ≤ 6 * N1 / Δ s ^ 2 := by positivity
  have hDu : ‖Dl s (u s)‖ ≤ N1 * 1 := key _ _ _ _ (hDln s).le (hun s hs).le hN1_0
  have hD2u : ‖D2l s (u s)‖ ≤ N2 * 1 := key _ _ _ _ (hD2ln s).le (hun s hs).le hN2_0
  have hu'n : ‖u' s‖ ≤ 1 / Δ s * (N1 * 1) := by
    rw [hu', norm_neg]; exact key _ _ _ _ hRn hDu hg
  refine ⟨hud' s hs, ?_, by simp [IsState, hun s hs], ?_, ?_, ?_, ?_, ?_⟩
  · have hDud : HasDerivWithinAt (fun t => Dl t (u t)) (D2l s (u s) + Dl s (u' s)) (Set.Icc 0 1) s :=
      happ (hH1d s hs) (hud' s hs)
    have := (happ hRd (happ hRd hDud)).neg
    have heq : v = fun t => -(R t (R t (Dl t (u t)))) := by
      funext t; simp [hv, hu']
    rw [heq]
    exact this
  · rw [← huP s hs]; exact hHP _
  · rw [hHR, hu']
    simp [hpr]
  · refine hu'n.trans ?_
    rw [mul_one, one_div_mul_eq_div]
  · have : ‖v s‖ ≤ 1 / Δ s * (1 / Δ s * (N1 * 1)) := key _ _ _ _ hRn hu'n hg
    refine this.trans ?_
    calc 1 / Δ s * (1 / Δ s * (N1 * 1)) = N1 / Δ s ^ 2 := by field_simp
      _ ≤ N1 / Δ s ^ 2 := le_rfl
  · have t1 : ‖R' s (R s (Dl s (u s)))‖ ≤ 6 * N1 / Δ s ^ 2 * (1 / Δ s * (N1 * 1)) :=
      key _ _ _ _ hR'n (key _ _ _ _ hRn hDu hg) hR'0
    have t2a : ‖D2l s (u s) + Dl s (u' s)‖ ≤ N2 * 1 + N1 * (1 / Δ s * (N1 * 1)) :=
      (norm_add_le _ _).trans (add_le_add hD2u (key _ _ _ _ (hDln s).le hu'n hN1_0))
    have t2 : ‖R' s (Dl s (u s)) + R s (D2l s (u s) + Dl s (u' s))‖ ≤
        6 * N1 / Δ s ^ 2 * (N1 * 1) + 1 / Δ s * (N2 * 1 + N1 * (1 / Δ s * (N1 * 1))) :=
      (norm_add_le _ _).trans (add_le_add (key _ _ _ _ hR'n hDu hR'0)
        (key _ _ _ _ hRn t2a hg))
    have t3 := key _ _ _ _ hRn t2 hg
    calc ‖v' s‖ ≤ ‖R' s (R s (Dl s (u s)))‖ +
          ‖R s (R' s (Dl s (u s)) + R s (D2l s (u s) + Dl s (u' s)))‖ := by
          rw [hv', norm_neg]; exact norm_add_le _ _
      _ ≤ 6 * N1 / Δ s ^ 2 * (1 / Δ s * (N1 * 1)) +
          1 / Δ s * (6 * N1 / Δ s ^ 2 * (N1 * 1) + 1 / Δ s * (N2 * 1 + N1 * (1 / Δ s * (N1 * 1)))) :=
          add_le_add t1 t3
      _ = 13 * N1 ^ 2 / Δ s ^ 3 + N2 / Δ s ^ 2 := by field_simp; ring

theorem norm_le_of_schrodinger_source_integral {ι : Type*} [Fintype ι] (H : ℝ → Matrix ι ι ℂ)
    (hH : ∀ s ∈ Set.Icc (0 : ℝ) 1, (H s).IsHermitian) (T : ℝ)
    (f h : ℝ → EuclideanSpace ℂ ι)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (Complex.I • (T : ℂ) • act (H s) (f s) + h s) (Set.Icc 0 1) s)
    (m : ℝ → ℝ) (hmc : ContinuousOn m (Set.Icc 0 1))
    (hm : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖h s‖ ≤ m s) :
    ‖f 1‖ ≤ ‖f 0‖ + ∫ s in (0 : ℝ)..1, m s := by
  classical
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hre : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : EuclideanSpace ℂ ι,
      inner ℝ z (Complex.I • (T : ℂ) • act (H s) z) = 0 := by
    intro s hs z
    have hsym : (Matrix.toEuclideanLin (H s)).IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (hH s hs)
    have hreal := hsym.coe_re_inner_apply_self z
    have hact : act (H s) z = Matrix.toEuclideanLin (H s) z := rfl
    have hri : inner ℝ z (Complex.I • (T : ℂ) • act (H s) z) =
        (inner ℂ z (Complex.I • (T : ℂ) • act (H s) z)).re := by
      rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Complex.inner, mul_comm]
    rw [hri, inner_smul_right, inner_smul_right, hact, ← inner_conj_symm,
      ← hreal]
    simp
  set mE : ℝ → ℝ := fun t => m (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) with hmE
  have hmEc : Continuous mE :=
    hmc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun t => (Set.projIcc (0 : ℝ) 1 zero_le_one t).2)
  have hmE_eq : ∀ s ∈ Set.Icc (0 : ℝ) 1, mE s = m s := fun s hs => by
    simp [hmE, Set.projIcc_of_mem _ hs]
  have hmE_int : (∫ s in (0 : ℝ)..1, mE s) = ∫ s in (0 : ℝ)..1, m s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    exact hmE_eq s hs
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set g : ℝ → ℝ := fun s => Real.sqrt (‖f s‖ ^ 2 + ε ^ 2) with hg
  have hgpos : ∀ s, 0 < ‖f s‖ ^ 2 + ε ^ 2 := fun s => by positivity
  have hgd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt g
      (2 * inner ℝ (f s) (Complex.I • (T : ℂ) • act (H s) (f s) + h s) /
        (2 * Real.sqrt (‖f s‖ ^ 2 + ε ^ 2))) (Set.Icc 0 1) s := fun s hs =>
    (((hf s hs).norm_sq).add_const (ε ^ 2)).sqrt (hgpos s).ne'
  have hgb : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      2 * inner ℝ (f s) (Complex.I • (T : ℂ) • act (H s) (f s) + h s) /
        (2 * Real.sqrt (‖f s‖ ^ 2 + ε ^ 2)) ≤ mE s := by
    intro s hs
    rw [hmE_eq s hs]
    have hsq : 0 < Real.sqrt (‖f s‖ ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (hgpos s)
    rw [div_le_iff₀ (by positivity), inner_add_right, hre s hs, zero_add]
    have h1 : inner ℝ (f s) (h s) ≤ ‖f s‖ * ‖h s‖ := real_inner_le_norm _ _
    have h2 : ‖f s‖ ≤ Real.sqrt (‖f s‖ ^ 2 + ε ^ 2) := by
      rw [Real.le_sqrt (norm_nonneg _) (hgpos s).le]; nlinarith
    have h3 : ‖f s‖ * ‖h s‖ ≤ Real.sqrt (‖f s‖ ^ 2 + ε ^ 2) * m s :=
      mul_le_mul h2 (hm s hs) (norm_nonneg _) hsq.le
    linarith
  have hBd : ∀ s, HasDerivAt (fun s => g 0 + ∫ t in (0 : ℝ)..s, mE t) (mE s) s := fun s => by
    simpa using ((hmEc.integral_hasStrictDerivAt 0 s).hasDerivAt).const_add (g 0)
  have hmain := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := g)
    (fun s hs => (hgd s hs).continuousWithinAt)
    (fun s hs => (hgd s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs))
    (B := fun s => g 0 + ∫ t in (0 : ℝ)..s, mE t) (B' := mE) (by simp)
    (fun s _ => (hBd s).continuousAt.continuousWithinAt)
    (fun s _ => (hBd s).hasDerivWithinAt)
    (fun s hs => hgb s (Set.Ico_subset_Icc_self hs)) h1
  rw [hmE_int] at hmain
  have hf1 : ‖f 1‖ ≤ g 1 := by
    rw [hg, Real.le_sqrt (norm_nonneg _) (hgpos 1).le]; nlinarith
  have hg0 : g 0 ≤ ‖f 0‖ + ε := by
    rw [hg, Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [norm_nonneg (f 0)]⟩
  linarith

/-! ### Eigenvalue continuity and gap properties -/

theorem ascEigenvalues_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : Monotone (ascEigenvalues A) := by
  intro j k hjk
  simp only [ascEigenvalues, dif_pos hA]
  exact hA.eigenvalues₀_antitone (Fin.rev_le_rev.mpr hjk)

theorem hasGapAround_of_hasSimpleGroundState {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : HasSimpleGroundState A) {γ : ℝ} (hγ : γ ≤ spectralGap A) :
    HasGapAround A (minEigenvalue A) γ := by
  obtain ⟨hHerm, h2, hgap0⟩ := hA
  have h0 : 0 < Fintype.card ι := by omega
  have hmin : minEigenvalue A = ascEigenvalues A ⟨0, h0⟩ := dif_pos h0
  have hsg : spectralGap A = ascEigenvalues A ⟨1, h2⟩ - ascEigenvalues A ⟨0, h0⟩ := dif_pos h2
  have hlt : ∀ k : Fin (Fintype.card ι), k ≠ ⟨0, h0⟩ →
      spectralGap A ≤ ascEigenvalues A k - minEigenvalue A := by
    intro k hk
    have hk1 : (⟨1, h2⟩ : Fin (Fintype.card ι)) ≤ k := by
      change 1 ≤ k.val
      have : k.val ≠ 0 := fun h => hk (Fin.ext h)
      omega
    have hle := ascEigenvalues_mono hHerm hk1
    rw [hmin, hsg]
    linarith
  refine ⟨hHerm, ⟨⟨0, h0⟩, hmin.symm, fun k hk => ?_⟩, fun k hk => ?_⟩
  · by_contra hne
    have := hlt k hne
    linarith
  · have hne : k ≠ ⟨0, h0⟩ := fun h => hk (h ▸ hmin.symm)
    have h1 := hlt k hne
    have h2' : 0 ≤ ascEigenvalues A k - minEigenvalue A := by linarith
    rw [abs_of_nonneg h2']
    linarith

theorem re_inner_act_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : EuclideanSpace ℂ ι) :
    (inner ℂ x (act A x)).re =
      ∑ i : ι, hA.eigenvalues i * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := by
  set b := hA.eigenvectorBasis with hbdef
  set e := hA.eigenvalues with hedef
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hb : ∀ i, Matrix.toEuclideanLin A (b i) = (e i : ℂ) • b i := by
    intro i
    rw [Matrix.toEuclideanLin_apply, hbdef, hA.mulVec_eigenvectorBasis]
    ext j
    simp [RCLike.real_smul_eq_coe_mul, hedef]
  have hAx : ∀ i, b.repr (act A x) i = (e i : ℂ) * b.repr x i := by
    intro i
    rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
    have hact : act A x = Matrix.toEuclideanLin A x := rfl
    rw [hact, ← hsym (b i) x, hb i, inner_smul_left]
    simp
  rw [← b.repr.inner_map_map x (act A x), PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hAx i]
  have hz : ∀ z : ℂ, ( (e i : ℂ) * z * starRingEnd ℂ z ).re = e i * ‖z‖ ^ 2 := by
    intro z
    rw [mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  simpa [Complex.inner, mul_comm, mul_left_comm, mul_assoc] using hz (b.repr x i)

theorem sum_norm_sq_repr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (x : EuclideanSpace ℂ ι) :
    (∑ i : ι, ‖b.repr x i‖ ^ 2) = ‖x‖ ^ 2 := by
  rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]

theorem re_inner_act_sub_le_specNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) :
    (inner ℂ x (act B x)).re - (inner ℂ x (act A x)).re ≤ specNorm (B - A) := by
  have hsub : act B x - act A x = act (B - A) x := by
    simp [act, Matrix.sub_mulVec]
  have h1 : (inner ℂ x (act B x)).re - (inner ℂ x (act A x)).re =
      (inner ℂ x (act (B - A) x)).re := by
    rw [← Complex.sub_re, ← inner_sub_right, hsub]
  rw [h1]
  have h2 : (inner ℂ x (act (B - A) x)).re ≤ ‖inner ℂ x (act (B - A) x)‖ :=
    Complex.re_le_norm _
  have h3 : ‖inner ℂ x (act (B - A) x)‖ ≤ ‖x‖ * ‖act (B - A) x‖ :=
    norm_inner_le_norm _ _
  have h4 : ‖act (B - A) x‖ ≤ specNorm (B - A) * ‖x‖ :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (B - A)).le_opNorm x
  simp only [hx, one_mul, mul_one] at h3 h4
  linarith

theorem minEigenvalue_le_re_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (h0 : 0 < Fintype.card ι)
    (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) :
    minEigenvalue A ≤ (inner ℂ x (act A x)).re := by
  set eqv := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  have hmin : minEigenvalue A = ascEigenvalues A ⟨0, h0⟩ := dif_pos h0
  have he : ∀ i : ι, minEigenvalue A ≤ hA.eigenvalues i := by
    intro i
    have hbr : ascEigenvalues A (Fin.rev (eqv.symm i)) = hA.eigenvalues i := by
      simp only [ascEigenvalues, dif_pos hA, Fin.rev_rev]
      rfl
    rw [hmin, ← hbr]
    exact ascEigenvalues_mono hA (Nat.zero_le _)
  calc minEigenvalue A = minEigenvalue A * ‖x‖ ^ 2 := by rw [hx, one_pow, mul_one]
    _ = minEigenvalue A * ∑ i : ι, ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := by
      rw [sum_norm_sq_repr]
    _ = ∑ i : ι, minEigenvalue A * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ i : ι, hA.eigenvalues i * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (he i) (sq_nonneg _)
    _ = (inner ℂ x (act A x)).re := (re_inner_act_eq_sum hA x).symm

theorem minEigenvalue_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h0 : 0 < Fintype.card ι) :
    minEigenvalue B - minEigenvalue A ≤ specNorm (B - A) := by
  set eqv := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  set i0 := eqv (Fin.rev ⟨0, h0⟩) with hi0
  set u0 := hA.eigenvectorBasis i0
  have hu0 : ‖u0‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i0
  have he0 : hA.eigenvalues i0 = minEigenvalue A := by
    have hbr : ascEigenvalues A (Fin.rev (eqv.symm i0)) = hA.eigenvalues i0 := by
      simp only [ascEigenvalues, dif_pos hA, Fin.rev_rev]
      rfl
    rw [← hbr, hi0, Equiv.symm_apply_apply, Fin.rev_rev, minEigenvalue, dif_pos h0]
  have hAu0 : (inner ℂ u0 (act A u0)).re = minEigenvalue A := by
    rw [re_inner_act_eq_sum hA u0, OrthonormalBasis.repr_self]
    have hsum : (∑ i : ι, hA.eigenvalues i * ‖EuclideanSpace.single i0 (1 : ℂ) i‖ ^ 2) =
        hA.eigenvalues i0 := by
      rw [Finset.sum_eq_single i0]
      · simp [EuclideanSpace.single_apply]
      · intro i _ hi; simp [EuclideanSpace.single_apply, hi]
      · intro h; exact absurd (Finset.mem_univ i0) h
    rw [hsum, he0]
  have hBu0 := minEigenvalue_le_re_inner hB h0 u0 hu0
  have hdiff := re_inner_act_sub_le_specNorm A B u0 hu0
  linarith

theorem ascEigenvalues_one_le_re_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℂ} (hB : B.IsHermitian) (h2 : 2 ≤ Fintype.card ι)
    (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1)
    (horth : inner ℂ (hB.eigenvectorBasis
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) (Fin.rev ⟨0, by omega⟩))) x = 0) :
    ascEigenvalues B ⟨1, h2⟩ ≤ (inner ℂ x (act B x)).re := by
  have h0 : 0 < Fintype.card ι := by omega
  set eqv := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  set j0 := eqv (Fin.rev ⟨0, h0⟩) with hj0
  have hrepr0 : hB.eigenvectorBasis.repr x j0 = 0 := by
    rw [OrthonormalBasis.repr_apply_apply]
    exact horth
  have he : ∀ i : ι,
      ascEigenvalues B ⟨1, h2⟩ * ‖hB.eigenvectorBasis.repr x i‖ ^ 2 ≤
        hB.eigenvalues i * ‖hB.eigenvectorBasis.repr x i‖ ^ 2 := by
    intro i
    by_cases hi : i = j0
    · subst hi; simp [hrepr0]
    · have hk : Fin.rev (eqv.symm i) ≠ ⟨0, h0⟩ := by
        intro h
        apply hi
        rw [hj0, ← h, Fin.rev_rev, Equiv.apply_symm_apply]
      have hk1 : (⟨1, h2⟩ : Fin (Fintype.card ι)) ≤ Fin.rev (eqv.symm i) := by
        change 1 ≤ (Fin.rev (eqv.symm i)).val
        have : (Fin.rev (eqv.symm i)).val ≠ 0 := fun h => hk (Fin.ext h)
        omega
      have hbr : ascEigenvalues B (Fin.rev (eqv.symm i)) = hB.eigenvalues i := by
        simp only [ascEigenvalues, dif_pos hB, Fin.rev_rev]
        rfl
      have hle : ascEigenvalues B ⟨1, h2⟩ ≤ hB.eigenvalues i :=
        hbr ▸ ascEigenvalues_mono hB hk1
      exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  calc ascEigenvalues B ⟨1, h2⟩ = ascEigenvalues B ⟨1, h2⟩ * ‖x‖ ^ 2 := by
        rw [hx, one_pow, mul_one]
    _ = ascEigenvalues B ⟨1, h2⟩ * ∑ i : ι, ‖hB.eigenvectorBasis.repr x i‖ ^ 2 := by
      rw [sum_norm_sq_repr]
    _ = ∑ i : ι, ascEigenvalues B ⟨1, h2⟩ * ‖hB.eigenvectorBasis.repr x i‖ ^ 2 :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ i : ι, hB.eigenvalues i * ‖hB.eigenvectorBasis.repr x i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => he i
    _ = (inner ℂ x (act B x)).re := (re_inner_act_eq_sum hB x).symm

theorem ascEigenvalues_one_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h2 : 2 ≤ Fintype.card ι) :
    ascEigenvalues B ⟨1, h2⟩ - ascEigenvalues A ⟨1, h2⟩ ≤ specNorm (B - A) := by
  have h0 : 0 < Fintype.card ι := by omega
  set eqv := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  set b := hA.eigenvectorBasis
  set i0 := eqv (Fin.rev ⟨0, h0⟩) with hi0
  set i1 := eqv (Fin.rev ⟨1, h2⟩) with hi1
  have hi01 : i0 ≠ i1 := by
    intro h
    have h' := Fin.rev_injective (eqv.injective h)
    exact absurd (congrArg Fin.val h') (by simp)
  set uB := hB.eigenvectorBasis (eqv (Fin.rev ⟨0, h0⟩))
  set α0 : ℂ := inner ℂ uB (b i0)
  set α1 : ℂ := inner ℂ uB (b i1)
  have hcoeff : ∃ c0 c1 : ℂ, ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1 ∧ c0 * α0 + c1 * α1 = 0 := by
    by_cases hα0 : α0 = 0
    · refine ⟨1, 0, by simp, by simp [hα0]⟩
    · set r : ℝ := Real.sqrt (‖α0‖ ^ 2 + ‖α1‖ ^ 2) with hr
      have hpos0 : 0 < ‖α0‖ := norm_pos_iff.mpr hα0
      have hpos2 : 0 < ‖α0‖ ^ 2 + ‖α1‖ ^ 2 := by positivity
      have hrpos : 0 < r := Real.sqrt_pos.mpr hpos2
      have hr2 : r ^ 2 = ‖α0‖ ^ 2 + ‖α1‖ ^ 2 := Real.sq_sqrt hpos2.le
      have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
      refine ⟨-(α1 / r), α0 / r, ?_, ?_⟩
      · simp only [norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg hrpos.le, div_pow]
        rw [← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hrpos.ne')]
        linarith [hr2]
      · field_simp [hrc]
        ring
  obtain ⟨c0, c1, hc_norm, hc_orth⟩ := hcoeff
  set x : EuclideanSpace ℂ ι := c0 • b i0 + c1 • b i1 with hxdef
  have hrepr : ∀ i : ι, b.repr x i =
      (if i = i0 then c0 else 0) + (if i = i1 then c1 else 0) := by
    intro i
    simp [hxdef, map_add, map_smul, OrthonormalBasis.repr_self, EuclideanSpace.single_apply]
  have hx : ‖x‖ = 1 := by
    have hsq : ‖x‖ ^ 2 = 1 := by
      rw [← sum_norm_sq_repr b x, Finset.sum_eq_add i0 i1 hi01
        (fun i _ ⟨hi0', hi1'⟩ => by simp [hrepr i, hi0', hi1'])
        (fun h => absurd (Finset.mem_univ i0) h)
        (fun h => absurd (Finset.mem_univ i1) h)]
      simp [hrepr i0, hrepr i1, hi01, hi01.symm, hc_norm]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq
  have hAx_le : (inner ℂ x (act A x)).re ≤ ascEigenvalues A ⟨1, h2⟩ := by
    have he_le : ∀ i : ι, hA.eigenvalues i * ‖b.repr x i‖ ^ 2 ≤
        ascEigenvalues A ⟨1, h2⟩ * ‖b.repr x i‖ ^ 2 := by
      intro i
      have hbr : ascEigenvalues A (Fin.rev (eqv.symm i)) = hA.eigenvalues i := by
        simp only [ascEigenvalues, dif_pos hA, Fin.rev_rev]
        rfl
      by_cases hi0' : i = i0
      · subst hi0'
        have hle : hA.eigenvalues i0 ≤ ascEigenvalues A ⟨1, h2⟩ := by
          rw [← hbr, hi0, Equiv.symm_apply_apply, Fin.rev_rev]
          exact ascEigenvalues_mono hA (by simp [Fin.le_def])
        exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      · by_cases hi1' : i = i1
        · subst hi1'
          have hle : hA.eigenvalues i1 ≤ ascEigenvalues A ⟨1, h2⟩ := by
            rw [← hbr, hi1, Equiv.symm_apply_apply, Fin.rev_rev]
          exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        · simp [hrepr i, hi0', hi1']
    calc (inner ℂ x (act A x)).re
        = ∑ i : ι, hA.eigenvalues i * ‖b.repr x i‖ ^ 2 := re_inner_act_eq_sum hA x
      _ ≤ ∑ i : ι, ascEigenvalues A ⟨1, h2⟩ * ‖b.repr x i‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => he_le i
      _ = ascEigenvalues A ⟨1, h2⟩ * ∑ i : ι, ‖b.repr x i‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      _ = ascEigenvalues A ⟨1, h2⟩ * ‖x‖ ^ 2 := by rw [sum_norm_sq_repr]
      _ = ascEigenvalues A ⟨1, h2⟩ := by rw [hx, one_pow, mul_one]
  have horth : inner ℂ uB x = 0 := by
    rw [hxdef, inner_add_right, inner_smul_right, inner_smul_right]
    exact hc_orth
  have hBx := ascEigenvalues_one_le_re_inner hB h2 x hx horth
  have hdiff := re_inner_act_sub_le_specNorm A B x hx
  linarith

theorem specNorm_sub_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) :
    specNorm (A - B) = specNorm (B - A) := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (A - B)‖ =
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (B - A)‖
  rw [show A - B = -(B - A) by abel, map_neg, norm_neg]

theorem red_act_sub {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    act A (x - y) = act A x - act A y := by
  simp [act, Matrix.mulVec_sub]

theorem red_act_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ)
    (x : EuclideanSpace ℂ ι) : act A (c • x) = c • act A x := by
  simp [act, Matrix.mulVec_smul]

theorem red_act_zero {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    act A (0 : EuclideanSpace ℂ ι) = 0 := by
  simp [act]

noncomputable def matToCLM (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  letI : NormedAddCommGroup (Matrix ι ι ℂ) := Pi.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix ι ι ℂ) := Pi.normedSpace
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)
      map_add' := map_add _
      map_smul' := fun r M => by
        simp only [RingHom.id_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
          RCLike.real_smul_eq_coe_smul (K := ℂ)] }

theorem hasDerivWithinAt_toEuclideanCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → Matrix ι ι ℂ} {f' : Matrix ι ι ℂ} {S : Set ℝ} {s : ℝ}
    (hf : HasDerivWithinAt f f' S s) :
    HasDerivWithinAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (f t))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) f') S s := by
  let _ : NormedAddCommGroup (Matrix ι ι ℂ) := Pi.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix ι ι ℂ) := Pi.normedSpace
  exact (matToCLM ι).hasFDerivAt.comp_hasDerivWithinAt s hf

theorem continuousOn_toEuclideanCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → Matrix ι ι ℂ} {S : Set ℝ} (hf : ContinuousOn f S) :
    ContinuousOn (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (f t)) S := by
  let _ : NormedAddCommGroup (Matrix ι ι ℂ) := Pi.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix ι ι ℂ) := Pi.normedSpace
  exact (matToCLM ι).continuous.comp_continuousOn hf

theorem continuousOn_minEigenvalue_and_gap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ℝ → Matrix ι ι ℂ)
    (hSimple : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasSimpleGroundState (H s))
    (hHc : ContinuousOn (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t)) (Set.Icc 0 1)) :
    ContinuousOn (fun s => minEigenvalue (H s)) (Set.Icc 0 1) ∧
    ContinuousOn (fun s => spectralGap (H s)) (Set.Icc 0 1) ∧
    ∃ γ : ℝ, 0 < γ ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, γ ≤ spectralGap (H s)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < spectralGap (H s)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) (minEigenvalue (H s)) (spectralGap (H s))) := by
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hHerm : ∀ s ∈ Set.Icc (0 : ℝ) 1, (H s).IsHermitian := fun s hs => (hSimple s hs).1
  obtain ⟨_, hcard2, _⟩ := hSimple 0 h0_mem
  have hcard0 : 0 < Fintype.card ι := by omega
  have hclm_norm : ∀ M : Matrix ι ι ℂ,
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) M‖ = specNorm M := fun _ => rfl
  set lam : ℝ → ℝ := fun s => minEigenvalue (H s) with hlamdef
  set Δ : ℝ → ℝ := fun s => spectralGap (H s) with hΔdef
  have hlam_bound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |lam t - lam s| ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t) -
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s)‖ := by
    intro s hs t ht
    have hsub :
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t) -
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s)‖ = specNorm (H t - H s) := by
      rw [← map_sub, hclm_norm]
    rw [hsub, abs_sub_le_iff]
    refine ⟨minEigenvalue_sub_le (hHerm s hs) (hHerm t ht) hcard0, ?_⟩
    rw [← specNorm_sub_comm (H s) (H t)]
    exact minEigenvalue_sub_le (hHerm t ht) (hHerm s hs) hcard0
  have hlam : ContinuousOn lam (Set.Icc 0 1) := by
    intro s hs
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (g := fun t =>
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t) -
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s)‖) ?_ ?_
    · filter_upwards [eventually_mem_nhdsWithin] with t ht
      simpa [Real.norm_eq_abs] using hlam_bound s hs t ht
    · have hlim : Tendsto
          (fun t =>
            ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t) -
              Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s)‖)
          (𝓝[Set.Icc 0 1] s)
          (𝓝 ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s) -
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s)‖) :=
        ((hHc s hs).sub continuousWithinAt_const).norm
      simpa using hlim
  have hΔ_bound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |Δ t - Δ s| ≤
        2 * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t) -
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s)‖ := by
    intro s hs t ht
    have hsub :
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t) -
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s)‖ = specNorm (H t - H s) := by
      rw [← map_sub, hclm_norm]
    have hsg : ∀ u, Δ u = ascEigenvalues (H u) ⟨1, hcard2⟩ - lam u := by
      intro u
      simp only [hΔdef, spectralGap, dif_pos hcard2, hlamdef, minEigenvalue, dif_pos hcard0]
    rw [hsg t, hsg s, show ascEigenvalues (H t) ⟨1, hcard2⟩ - lam t -
        (ascEigenvalues (H s) ⟨1, hcard2⟩ - lam s) =
        (ascEigenvalues (H t) ⟨1, hcard2⟩ - ascEigenvalues (H s) ⟨1, hcard2⟩) -
        (lam t - lam s) by ring]
    have h1 : |ascEigenvalues (H t) ⟨1, hcard2⟩ - ascEigenvalues (H s) ⟨1, hcard2⟩| ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t) -
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s)‖ := by
      rw [hsub, abs_sub_le_iff]
      refine ⟨ascEigenvalues_one_sub_le (hHerm s hs) (hHerm t ht) hcard2, ?_⟩
      rw [← specNorm_sub_comm (H s) (H t)]
      exact ascEigenvalues_one_sub_le (hHerm t ht) (hHerm s hs) hcard2
    have h2 := hlam_bound s hs t ht
    have h3 := abs_sub (ascEigenvalues (H t) ⟨1, hcard2⟩ - ascEigenvalues (H s) ⟨1, hcard2⟩)
      (lam t - lam s)
    linarith
  have hΔc : ContinuousOn Δ (Set.Icc 0 1) := by
    intro s hs
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (g := fun t =>
        2 * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t) -
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s)‖) ?_ ?_
    · filter_upwards [eventually_mem_nhdsWithin] with t ht
      simpa [Real.norm_eq_abs] using hΔ_bound s hs t ht
    · have hlim : Tendsto
          (fun t =>
            ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t) -
              Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s)‖)
          (𝓝[Set.Icc 0 1] s)
          (𝓝 ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s) -
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H s)‖) :=
        ((hHc s hs).sub continuousWithinAt_const).norm
      simpa using hlim.const_mul 2
  obtain ⟨s0, hs0, hs0_min⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hΔc
  refine ⟨hlam, hΔc, Δ s0, (hSimple s0 hs0).2.2, fun s hs => hs0_min hs,
    fun s hs => lt_of_lt_of_le (hSimple s0 hs0).2.2 (hs0_min hs),
    fun s hs => hasGapAround_of_hasSimpleGroundState (hSimple s hs) le_rfl⟩

end AdiabaticThmAux

open AdiabaticThmAux in
set_option maxHeartbeats 800000 in
theorem solution :
    ∃ c1 c2 c3 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H H1 H2 : ℝ → Matrix ι ι ℂ),
        (∀ s ∈ Set.Icc (0 : ℝ) 1, HasSimpleGroundState (H s)) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt H (H1 s) (Set.Icc 0 1) s) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt H1 (H2 s) (Set.Icc 0 1) s) →
        ContinuousOn H2 (Set.Icc 0 1) →
        ∀ ε : ℝ, 0 < ε →
        ∀ T : ℝ,
          T ≥ 2 / ε * (c1 * specNorm (H1 0) / spectralGap (H 0) ^ 2 +
            c1 * specNorm (H1 1) / spectralGap (H 1) ^ 2 +
            ∫ s in (0 : ℝ)..1,
              ((3 * c1 ^ 2 + c1 + c3) * specNorm (H1 s) ^ 2 / spectralGap (H s) ^ 3 +
                c2 * specNorm (H2 s) / spectralGap (H s) ^ 2)) →
        ∀ ψ : ℝ → EuclideanSpace ℂ ι,
          SolvesScaledSchrodinger H T ψ →
          IsGroundState (H 0) (ψ 0) →
          ∃ φ1 : EuclideanSpace ℂ ι, IsGroundState (H 1) φ1 ∧ ‖ψ 1 - φ1‖ ≤ ε := by
  refine ⟨2, 1, 1, by positivity, by positivity, by positivity, ?_⟩
  intro ι _ _ H H1 H2 hSimple hH1 hH2 hH2c ε hε T hT ψ hψ hψ0
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hHerm : ∀ s ∈ Set.Icc (0 : ℝ) 1, (H s).IsHermitian := fun s hs => (hSimple s hs).1
  have hclm_norm : ∀ M : Matrix ι ι ℂ,
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) M‖ = specNorm M := fun _ => rfl
  have hHd : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t))
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H1 s)) (Set.Icc 0 1) s :=
    fun s hs => hasDerivWithinAt_toEuclideanCLM (hH1 s hs)
  have hH1d : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H1 t))
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H2 s)) (Set.Icc 0 1) s :=
    fun s hs => hasDerivWithinAt_toEuclideanCLM (hH2 s hs)
  have hHc : ContinuousOn (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t)) (Set.Icc 0 1) :=
    fun s hs => (hHd s hs).continuousWithinAt
  have hN1c : ContinuousOn (fun s => specNorm (H1 s)) (Set.Icc 0 1) :=
    continuous_norm.comp_continuousOn (fun s hs => (hH1d s hs).continuousWithinAt)
  have hN2c : ContinuousOn (fun s => specNorm (H2 s)) (Set.Icc 0 1) :=
    continuous_norm.comp_continuousOn (continuousOn_toEuclideanCLM hH2c)
  set lam : ℝ → ℝ := fun s => minEigenvalue (H s) with hlamdef
  set Δ : ℝ → ℝ := fun s => spectralGap (H s) with hΔdef
  obtain ⟨hlam, hΔc, γ, hγ_pos, hΔle, hΔpos, hgap⟩ :=
    continuousOn_minEigenvalue_and_gap H hSimple hHc
  obtain ⟨u, u', v, v', hu0, hfr⟩ :=
    adiabatic_frame_general H H1 H2 hHd hH1d lam Δ hlam (ψ 0) hψ0.1 hψ0.2 γ hγ_pos hΔle hgap
  set F : ℝ → ℝ := fun s =>
    (3 * (2 : ℝ) ^ 2 + 2 + 1) * specNorm (H1 s) ^ 2 / Δ s ^ 3 +
      1 * specNorm (H2 s) / Δ s ^ 2 with hFdef
  have hFc : ContinuousOn F (Set.Icc 0 1) := by
    refine ContinuousOn.add ?_ ?_
    · exact ((hN1c.pow 2).const_mul _).div (hΔc.pow 3)
        (fun s hs => pow_ne_zero 3 (hΔpos s hs).ne')
    · exact (hN2c.const_mul _).div (hΔc.pow 2)
        (fun s hs => pow_ne_zero 2 (hΔpos s hs).ne')
  have hN1_nonneg : ∀ s, 0 ≤ specNorm (H1 s) := fun s => by
    rw [← hclm_norm]; exact norm_nonneg _
  have hN2_nonneg : ∀ s, 0 ≤ specNorm (H2 s) := fun s => by
    rw [← hclm_norm]; exact norm_nonneg _
  have hF_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ F s := by
    intro s hs
    have := hΔpos s hs
    have := hN1_nonneg s
    have := hN2_nonneg s
    rw [hFdef]; dsimp only
    positivity
  have hv'F : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖v' s‖ ≤ F s := by
    intro s hs
    refine (hfr s hs).2.2.2.2.2.2.2.trans ?_
    have := hΔpos s hs
    have := hN1_nonneg s
    have := hN2_nonneg s
    have h1 : 13 * specNorm (H1 s) ^ 2 / Δ s ^ 3 ≤
        (3 * (2 : ℝ) ^ 2 + 2 + 1) * specNorm (H1 s) ^ 2 / Δ s ^ 3 := by
      gcongr; norm_num
    have h2 : specNorm (H2 s) / Δ s ^ 2 = 1 * specNorm (H2 s) / Δ s ^ 2 := by ring
    rw [hFdef]; dsimp only
    linarith
  set lamE : ℝ → ℝ := fun t => lam (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) with hlamE
  have hlamEc : Continuous lamE :=
    hlam.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun t => (Set.projIcc (0 : ℝ) 1 zero_le_one t).2)
  have hlamE_eq : ∀ s ∈ Set.Icc (0 : ℝ) 1, lamE s = lam s := fun s hs => by
    simp [hlamE, Set.projIcc_of_mem _ hs]
  set Λ : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, lamE t with hΛ
  have hΛd : ∀ s, HasDerivAt Λ (lamE s) s := fun s =>
    (hlamEc.integral_hasStrictDerivAt 0 s).hasDerivAt
  set T' : ℝ := -T with hT'def
  set E : ℝ → ℂ := fun s => Complex.exp ((T' : ℂ) * (Λ s : ℂ) * Complex.I) with hE
  have hEd : ∀ s, HasDerivAt E (E s * ((T' : ℂ) * (lamE s : ℂ) * Complex.I)) s := fun s =>
    (((hΛd s).ofReal_comp.const_mul (T' : ℂ)).mul_const Complex.I).cexp
  have hE0 : E 0 = 1 := by simp [hE, hΛ]
  have hEn : ∀ s, ‖E s‖ = 1 := fun s => by
    have : (T' : ℂ) * (Λ s : ℂ) * Complex.I = ((T' * Λ s : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    simp only [hE, this, Complex.norm_exp_ofReal_mul_I]
  have hψ_plus : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt ψ (Complex.I • (T' : ℂ) • act (H s) (ψ s)) (Set.Icc 0 1) s := by
    intro s hs
    refine (hψ s hs).congr_deriv ?_
    simp only [hT'def]
    push_cast
    module
  set e : ℝ → EuclideanSpace ℂ ι := fun s => ψ s - E s • u s with he
  have hed : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt e
      (Complex.I • (T' : ℂ) • act (H s) (e s) + -(E s • u' s)) (Set.Icc 0 1) s := by
    intro s hs
    have := (hψ_plus s hs).sub (((hEd s).hasDerivWithinAt).smul (hfr s hs).1)
    refine this.congr_deriv ?_
    have hHu : act (H s) (u s) = (lam s : ℂ) • u s := (hfr s hs).2.2.2.1
    simp only [he, red_act_sub, red_act_smul, hHu, hlamE_eq s hs]
    module
  have he0 : e 0 = 0 := by simp [he, hE0, hu0]
  have he1 : ‖e 1‖ ≤ ε := by
    rcases lt_or_ge 0 (∫ s in (0 : ℝ)..1, F s) with hIpos | hInonpos
    · have hΔ0 : 0 < Δ 0 := hΔpos 0 h0_mem
      have hΔ1 : 0 < Δ 1 := hΔpos 1 h1_mem
      have hN1_0 := hN1_nonneg 0
      have hN1_1 := hN1_nonneg 1
      have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
      have hT'ne : T' ≠ 0 := by linarith
      have hTc : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'ne
      set κ : ℂ := (Complex.I * (T' : ℂ))⁻¹ with hκ
      have hκn : ‖κ‖ = 1 / T := by
        simp [hκ, hT'def, abs_of_pos hT0]
      set f : ℝ → EuclideanSpace ℂ ι := fun s => e s - κ • (E s • v s) with hf
      have hfd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f
          (Complex.I • (T' : ℂ) • act (H s) (f s) + -(κ • (E s • v' s))) (Set.Icc 0 1) s := by
        intro s hs
        have := (hed s hs).sub ((((hEd s).hasDerivWithinAt).smul (hfr s hs).2.1).const_smul κ)
        refine this.congr_deriv ?_
        have hHv : act (H s) (v s) = u' s + (lam s : ℂ) • v s := by
          rw [← (hfr s hs).2.2.2.2.1]; abel
        simp only [hf, red_act_sub, red_act_smul, hHv, hlamE_eq s hs]
        rw [hκ]
        match_scalars <;> field_simp
      have hfb := norm_le_of_schrodinger_source_integral H hHerm T' f
        (fun s => -(κ • (E s • v' s))) hfd
        (fun s => F s / T) (hFc.div_const T) (fun s hs => by
          rw [norm_neg, norm_smul, norm_smul, hEn, hκn, one_mul, one_div, inv_mul_eq_div]
          gcongr
          exact hv'F s hs)
      rw [intervalIntegral.integral_div] at hfb
      have hf0 : ‖f 0‖ = ‖v 0‖ / T := by
        simp [hf, he0, hE0, norm_smul, hκn, div_eq_inv_mul]
      have he1' : e 1 = f 1 + κ • (E 1 • v 1) := by simp [hf]
      have hv0 : ‖v 0‖ ≤ 2 * specNorm (H1 0) / Δ 0 ^ 2 :=
        (hfr 0 h0_mem).2.2.2.2.2.2.1.trans (by gcongr; linarith)
      have hv1 : ‖v 1‖ ≤ 2 * specNorm (H1 1) / Δ 1 ^ 2 :=
        (hfr 1 h1_mem).2.2.2.2.2.2.1.trans (by gcongr; linarith)
      have hb : ‖e 1‖ ≤ (2 * specNorm (H1 0) / Δ 0 ^ 2 +
          2 * specNorm (H1 1) / Δ 1 ^ 2 + ∫ s in (0 : ℝ)..1, F s) / T := by
        rw [he1']
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, hEn, hκn, one_mul]
        rw [hf0] at hfb
        calc ‖f 1‖ + 1 / T * ‖v 1‖ ≤ ‖v 0‖ / T + (∫ s in (0 : ℝ)..1, F s) / T + ‖v 1‖ / T := by
              rw [one_div_mul_eq_div]; linarith
          _ = (‖v 0‖ + ‖v 1‖ + ∫ s in (0 : ℝ)..1, F s) / T := by ring
          _ ≤ (2 * specNorm (H1 0) / Δ 0 ^ 2 + 2 * specNorm (H1 1) / Δ 1 ^ 2 +
                ∫ s in (0 : ℝ)..1, F s) / T := by
              gcongr
      refine hb.trans ?_
      rw [div_le_iff₀ hT0]
      have hcS : 2 * (2 * specNorm (H1 0) / Δ 0 ^ 2 + 2 * specNorm (H1 1) / Δ 1 ^ 2 +
          ∫ s in (0 : ℝ)..1, F s) ≤ ε * T := by
        have := mul_le_mul_of_nonneg_left hT hε.le
        rwa [← mul_assoc, mul_div_cancel₀ _ hε.ne'] at this
      have hS_pos : 0 ≤ 2 * specNorm (H1 0) / Δ 0 ^ 2 + 2 * specNorm (H1 1) / Δ 1 ^ 2 +
          ∫ s in (0 : ℝ)..1, F s := by positivity
      linarith
    · obtain ⟨MΔ, hMΔ⟩ := isCompact_Icc.exists_bound_of_continuousOn hΔc
      set M := max MΔ 0 with hMdef
      have hM0 : 0 ≤ M := le_max_right _ _
      have hΔ_le_M : ∀ s ∈ Set.Icc (0 : ℝ) 1, Δ s ≤ M := fun s hs =>
        (le_abs_self (Δ s)).trans ((hMΔ s hs).trans (le_max_left _ _))
      have hu'_bound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖-(E s • u' s)‖ ≤ ε + (M / ε) * F s := by
        intro s hs
        rw [norm_neg, norm_smul, hEn s, one_mul]
        have hu's : ‖u' s‖ ≤ specNorm (H1 s) / Δ s := (hfr s hs).2.2.2.2.2.1
        set a := specNorm (H1 s) / Δ s with hadef
        have ha : a ≤ ε + a ^ 2 / ε := by
          rw [add_div' _ _ _ hε.ne']
          rw [le_div_iff₀ hε]
          nlinarith [sq_nonneg (a - ε)]
        have ha2 : a ^ 2 ≤ M * F s := by
          have hΔs := hΔpos s hs
          have hN1s := hN1_nonneg s
          have hN2s := hN2_nonneg s
          have hΔM := hΔ_le_M s hs
          have h1 : a ^ 2 = Δ s * (specNorm (H1 s) ^ 2 / Δ s ^ 3) := by
            rw [hadef]; field_simp
          have h2 : specNorm (H1 s) ^ 2 / Δ s ^ 3 ≤ F s := by
            rw [hFdef]; dsimp only
            have : 0 ≤ 1 * specNorm (H2 s) / Δ s ^ 2 := by positivity
            have : 1 * specNorm (H1 s) ^ 2 / Δ s ^ 3 ≤
                (3 * (2 : ℝ) ^ 2 + 2 + 1) * specNorm (H1 s) ^ 2 / Δ s ^ 3 := by
              gcongr
              norm_num
            rw [one_mul] at this
            linarith
          rw [h1]
          exact mul_le_mul hΔM h2 (by positivity) hM0
        have ha3 : a ^ 2 / ε ≤ (M / ε) * F s := by
          rw [div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right ha2 hε.le
        linarith
      have heb := norm_le_of_schrodinger_source_integral H hHerm T' e
        (fun s => -(E s • u' s)) hed
        (fun s => ε + (M / ε) * F s)
        (continuousOn_const.add (hFc.const_mul (M / ε)))
        hu'_bound
      rw [he0, norm_zero, zero_add] at heb
      have hFE_int : (∫ s in (0 : ℝ)..1, (ε + (M / ε) * F s)) =
          ε + (M / ε) * ∫ s in (0 : ℝ)..1, F s := by
        have hIntF : IntervalIntegrable F MeasureTheory.volume 0 1 :=
          (hFc.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
        rw [intervalIntegral.integral_add intervalIntegrable_const (hIntF.const_mul _),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        simp
      rw [hFE_int] at heb
      have hM_nonpos : (M / ε) * ∫ s in (0 : ℝ)..1, F s ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hInonpos
      linarith
  refine ⟨E 1 • u 1, ⟨?_, ?_⟩, he1⟩
  · simp only [IsState, norm_smul, hEn 1, one_mul]
    exact (hfr 1 h1_mem).2.2.1
  · have hHu1 : act (H 1) (u 1) = (lam 1 : ℂ) • u 1 := (hfr 1 h1_mem).2.2.2.1
    rw [red_act_smul, hHu1, smul_comm]
