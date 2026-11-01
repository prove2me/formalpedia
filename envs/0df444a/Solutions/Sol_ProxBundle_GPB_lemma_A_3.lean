-- Prove2me | solution 1 for ProxBundle.GPB.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T04:04:04.560001+00:00
-- url     : https://prove2.me/submissions/b558eacf-14e7-45c4-9903-d9c033046c8f

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Theorems.Thm_ProxBundle_GPB_eq_7
import Theorems.Thm_ProxBundle_GPB_lemma_4_6
import Theorems.Thm_ProxBundle_GPB_proposition_4_3

open ProxBundle.GPB
open scoped InnerProductSpace RealInnerProductSpace

lemma gpb_a3_sq_comb {n : ℕ} (x u c : E n) (t : ℝ) :
    ‖(1 - t) • x + t • u - c‖ ^ 2 =
      (1 - t) * ‖x - c‖ ^ 2 + t * ‖u - c‖ ^ 2 - t * (1 - t) * ‖u - x‖ ^ 2 := by
  have h1 : (1 - t) • x + t • u - c = (1 - t) • (x - c) + t • (u - c) := by module
  have h2 : u - x = (u - c) - (x - c) := by abel
  rw [h1, h2]
  generalize x - c = p
  generalize u - c = q
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, real_inner_comm q]
  ring

/-- Quadratic growth of a `(μ + 1/λ)`-strongly convex proximal objective at its minimizer
(Theorem 5.25(b) of Beck, as used in (46) and (52)). -/
lemma gpb_a3_qgrowth {n : ℕ} (D : Set (E n)) (μ lam : ℝ) (G : E n → ℝ) (c x : E n)
    (hG : StrongConvexOn D μ G) (hlam : 0 < lam) (hμ : 0 ≤ μ) (hx : x ∈ D)
    (hmin : ∀ u ∈ D, G x + ‖x - c‖ ^ 2 / (2 * lam) ≤ G u + ‖u - c‖ ^ 2 / (2 * lam))
    (u : E n) (hu : u ∈ D) :
    G x + ‖x - c‖ ^ 2 / (2 * lam) + (μ + 1 / lam) / 2 * ‖u - x‖ ^ 2 ≤
      G u + ‖u - c‖ ^ 2 / (2 * lam) := by
  set K := (μ + 1 / lam) / 2 * ‖u - x‖ ^ 2 with hKdef
  have hK : 0 ≤ K := by positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (1 - t) * K ≤ (G u + ‖u - c‖ ^ 2 / (2 * lam)) - (G x + ‖x - c‖ ^ 2 / (2 * lam)) := by
    intro t ht0 ht1
    have hw := hG.2 hx hu (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
    have hwD : (1 - t) • x + t • u ∈ D := hG.1 hx hu (by linarith) ht0.le (by ring)
    have hm := hmin _ hwD
    rw [gpb_a3_sq_comb] at hm
    simp only [smul_eq_mul] at hw
    rw [norm_sub_rev x u] at hw
    have h : 0 ≤ t * ((G u + ‖u - c‖ ^ 2 / (2 * lam)) - (G x + ‖x - c‖ ^ 2 / (2 * lam))
        - (1 - t) * K) := by
      rw [hKdef]
      have e : t * ((G u + ‖u - c‖ ^ 2 / (2 * lam)) - (G x + ‖x - c‖ ^ 2 / (2 * lam))
          - (1 - t) * ((μ + 1 / lam) / 2 * ‖u - x‖ ^ 2)) =
          (t * G u + (1 - t) * G x - (1 - t) * t * (μ / 2 * ‖u - x‖ ^ 2) -
              G ((1 - t) • x + t • u)) +
          (G ((1 - t) • x + t • u) +
            ((1 - t) * ‖x - c‖ ^ 2 + t * ‖u - c‖ ^ 2 - t * (1 - t) * ‖u - x‖ ^ 2) /
              (2 * lam) - (G x + ‖x - c‖ ^ 2 / (2 * lam))) := by
        field_simp
        ring
      rw [e]
      have := hw
      linarith
    have := (mul_nonneg_iff_of_pos_left ht0).mp h
    linarith
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hKδ : 0 < K + δ := by linarith
  have ht0 : 0 < δ / (K + δ) := by positivity
  have ht1 : δ / (K + δ) ≤ 1 := by rw [div_le_one hKδ]; linarith
  have h := key _ ht0 ht1
  have h2 : δ / (K + δ) * K ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hKδ]; nlinarith
  have e : (1 - δ / (K + δ)) * K = K - δ / (K + δ) * K := by ring
  linarith


lemma gpb_a3_subgrad {n : ℕ} (D : Set (E n)) (μ lam : ℝ) (G : E n → ℝ) (c z : E n)
    (hG : StrongConvexOn D μ G) (hlam : 0 < lam) (hμ : 0 ≤ μ) (hz : z ∈ D)
    (hmin : ∀ u ∈ D, G z + ‖z - c‖ ^ 2 / (2 * lam) ≤ G u + ‖u - c‖ ^ 2 / (2 * lam))
    (u : E n) (hu : u ∈ D) : G z + ⟪u - z, c - z⟫ / lam ≤ G u := by
  have hq := gpb_a3_qgrowth D μ lam G c z hG hlam hμ hz hmin u hu
  have e : ‖u - c‖ ^ 2 = ‖u - z‖ ^ 2 - 2 * ⟪u - z, c - z⟫ + ‖c - z‖ ^ 2 := by
    have : u - c = (u - z) - (c - z) := by abel
    rw [this, norm_sub_sq_real]
  rw [e, norm_sub_rev z c] at hq
  have h1 : 0 ≤ μ / 2 * ‖u - z‖ ^ 2 := by positivity
  have h2 : (μ + 1 / lam) / 2 * ‖u - z‖ ^ 2 =
      μ / 2 * ‖u - z‖ ^ 2 + ‖u - z‖ ^ 2 / (2 * lam) := by field_simp
  have h3 : (‖u - z‖ ^ 2 - 2 * ⟪u - z, c - z⟫ + ‖c - z‖ ^ 2) / (2 * lam) =
      ‖u - z‖ ^ 2 / (2 * lam) - ⟪u - z, c - z⟫ / lam + ‖c - z‖ ^ 2 / (2 * lam) := by
    field_simp
  rw [h2] at hq
  rw [h3] at hq
  linarith

/-- Lemma A.1 (monotonicity of the resolvent), in the form used in the proof of Lemma A.3. -/
lemma gpb_a3_resolvent {n : ℕ} (D : Set (E n)) (G : E n → ℝ) (c z w : E n) (lam lam' : ℝ)
    (hlam' : 0 < lam') (hll : lam' ≤ lam) (hz : z ∈ D) (hw : w ∈ D)
    (hzsub : ∀ u ∈ D, G z + ⟪u - z, c - z⟫ / lam ≤ G u)
    (hwsub : ∀ u ∈ D, G w + ⟪u - w, c - w⟫ / lam' ≤ G u) :
    ‖z - c‖ ≤ lam / lam' * ‖w - c‖ := by
  have hlam : 0 < lam := lt_of_lt_of_le hlam' hll
  have h1 := hzsub w hw
  have h2 := hwsub z hz
  have e1 : ⟪w - z, c - z⟫ = ‖z - c‖ ^ 2 - ⟪w - c, z - c⟫ := by
    have a1 : w - z = (w - c) - (z - c) := by abel
    have a2 : c - z = -(z - c) := by abel
    rw [a1, a2, inner_neg_right, inner_sub_left, real_inner_self_eq_norm_sq]; ring
  have e2 : ⟪z - w, c - w⟫ = ‖w - c‖ ^ 2 - ⟪w - c, z - c⟫ := by
    have a1 : z - w = (z - c) - (w - c) := by abel
    have a2 : c - w = -(w - c) := by abel
    rw [a1, a2, inner_neg_right, inner_sub_left, real_inner_self_eq_norm_sq,
      real_inner_comm (w - c) (z - c)]; ring
  rw [e1] at h1
  rw [e2] at h2
  have hpq : ⟪w - c, z - c⟫ ≤ ‖w - c‖ * ‖z - c‖ := real_inner_le_norm _ _
  set Pn := ‖z - c‖ with hPn
  set Qn := ‖w - c‖ with hQn
  set I := ⟪w - c, z - c⟫ with hI
  have hP0 : 0 ≤ Pn := norm_nonneg _
  have hQ0 : 0 ≤ Qn := norm_nonneg _
  -- (Pn^2 - I)/lam + (Qn^2 - I)/lam' ≤ 0
  have hsum : (Pn ^ 2 - I) / lam + (Qn ^ 2 - I) / lam' ≤ 0 := by linarith
  have hsum2 : lam' * (Pn ^ 2 - I) + lam * (Qn ^ 2 - I) ≤ 0 := by
    have e : lam' * (Pn ^ 2 - I) + lam * (Qn ^ 2 - I) =
        (lam * lam') * ((Pn ^ 2 - I) / lam + (Qn ^ 2 - I) / lam') := by
      field_simp
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hsum
  rw [div_mul_eq_mul_div, le_div_iff₀ hlam']
  by_contra hcon
  push Not at hcon
  have hPQ : Qn < Pn := by
    by_contra h
    push Not at h
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hpq (by positivity : (0:ℝ) ≤ lam' + lam)]

/-- Existence of the proximal point for a closed `μ`-convex model with domain `D`, given that a
proximal point for another stepsize exists (used for `w_{ℓ₀}` in the proof of Lemma A.3). -/
lemma gpb_a3_prox_exists {n : ℕ} (P : Instance n) (μ lam lam' : ℝ) (Γ : E n → ℝ) (c z : E n)
    (hμ : 0 ≤ μ) (hΓ : P.ConvBar μ Γ) (hlam : 0 < lam) (hlam' : 0 < lam')
    (hc : c ∈ P.D) (hz : P.IsProxMin Γ c lam z) :
    ∃ w, P.IsProxMin Γ c lam' w := by
  classical
  have hsub := gpb_a3_subgrad P.D μ lam Γ c z hΓ.1 hlam hμ hz.1 hz.2
  set F : E n → ℝ := fun u => Γ u + ‖u - c‖ ^ 2 / (2 * lam') with hF
  set G : E n → EReal := fun u => P.ext Γ u + ((‖u - c‖ ^ 2 / (2 * lam') : ℝ) : EReal) with hG
  have hGlsc : LowerSemicontinuous G := by
    apply LowerSemicontinuous.add' hΓ.2
    · exact (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous
    · intro x
      apply EReal.continuousAt_add
      · right; exact EReal.coe_ne_bot _
      · right; exact EReal.coe_ne_top _
  have hGin : ∀ u ∈ P.D, G u = ((F u : ℝ) : EReal) := by
    intro u hu
    simp only [G, F, Instance.ext, if_pos hu, EReal.coe_add]
  have hGout : ∀ u, u ∉ P.D → G u = ⊤ := by
    intro u hu
    simp only [G, Instance.ext, if_neg hu, EReal.top_add_coe]
  set K := G ⁻¹' Set.Iic ((F c : ℝ) : EReal) with hK
  have hKD : K ⊆ P.D := by
    intro u hu
    by_contra h
    simp only [K, Set.mem_preimage, Set.mem_Iic, hGout u h, top_le_iff] at hu
    exact EReal.coe_ne_top _ hu
  have hcK : c ∈ K := by
    simp only [K, Set.mem_preimage, Set.mem_Iic, hGin c hc, le_refl]
  have hKclosed : IsClosed K := hGlsc.isClosed_preimage _
  have hKbdd : Bornology.IsBounded K := by
    set e := ‖c - z‖ with he
    set A' := F c - Γ z + e ^ 2 / lam + lam' * e ^ 2 / lam ^ 2 with hA'
    rw [Metric.isBounded_iff_subset_closedBall c]
    refine ⟨1 + |4 * lam' * A'|, fun u hu => ?_⟩
    have huD := hKD hu
    have hFu : F u ≤ F c := by
      have : G u ≤ ((F c : ℝ) : EReal) := hu
      rw [hGin u huD] at this
      exact_mod_cast this
    rw [Metric.mem_closedBall, dist_eq_norm]
    set R := ‖u - c‖ with hR
    have hR0 : 0 ≤ R := norm_nonneg _
    have hs := hsub u huD
    have hin : -(‖u - z‖ * e) ≤ ⟪u - z, c - z⟫ := by
      have := abs_real_inner_le_norm (u - z) (c - z)
      rw [abs_le] at this
      linarith [this.1]
    have htri : ‖u - z‖ ≤ R + e := by
      have : u - z = (u - c) + (c - z) := by abel
      rw [this]; exact norm_add_le _ _
    have he0 : 0 ≤ e := norm_nonneg _
    have h1 : -((R + e) * e) / lam ≤ ⟪u - z, c - z⟫ / lam := by
      apply div_le_div_of_nonneg_right _ hlam.le
      nlinarith
    have hFu' : Γ u + R ^ 2 / (2 * lam') ≤ F c := hFu
    -- R^2/(2λ') - R e/λ ≤ F c - Γ z + e^2/λ
    have h2 : R ^ 2 / (2 * lam') - R * e / lam ≤ F c - Γ z + e ^ 2 / lam := by
      have : -((R + e) * e) / lam = - (R * e / lam) - e ^ 2 / lam := by ring
      linarith
    -- AM-GM
    have h3 : R * e / lam ≤ R ^ 2 / (4 * lam') + lam' * e ^ 2 / lam ^ 2 := by
      have : R ^ 2 / (4 * lam') + lam' * e ^ 2 / lam ^ 2 - R * e / lam =
          (lam * R - 2 * lam' * e) ^ 2 / (4 * lam' * lam ^ 2) := by
        field_simp; ring
      have : 0 ≤ (lam * R - 2 * lam' * e) ^ 2 / (4 * lam' * lam ^ 2) := by positivity
      linarith
    have h4 : R ^ 2 / (4 * lam') ≤ A' := by
      have : R ^ 2 / (2 * lam') = 2 * (R ^ 2 / (4 * lam')) := by field_simp; ring
      linarith
    have h5 : R ^ 2 ≤ 4 * lam' * A' := by
      rw [div_le_iff₀ (by positivity)] at h4; linarith
    rcases le_total R 1 with hR1 | hR1
    · have := abs_nonneg (4 * lam' * A'); linarith
    · have : R ≤ R ^ 2 := by nlinarith
      have := le_abs_self (4 * lam' * A'); linarith
  have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd
  obtain ⟨w, hwK, hwmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn ⟨c, hcK⟩ hKc (hGlsc.lowerSemicontinuousOn K)
  refine ⟨w, hKD hwK, fun u hu => ?_⟩
  have hGw : G w = ((F w : ℝ) : EReal) := hGin w (hKD hwK)
  show F w ≤ F u
  by_cases huK : u ∈ K
  · have := isMinOn_iff.mp hwmin u huK
    rw [hGw, hGin u hu] at this
    exact_mod_cast this
  · simp only [K, Set.mem_preimage, Set.mem_Iic, not_le] at huK
    rw [hGin u hu] at huK
    have : G w ≤ ((F c : ℝ) : EReal) := hwK
    rw [hGw] at this
    have h1 : F w ≤ F c := by exact_mod_cast this
    have h2 : F c < F u := by exact_mod_cast huK
    linarith

/-- The estimate of Lemma A.2 combined with (75): for a stepsize `λ'` with `2λ' L̄ ≤ 1`. -/
lemma gpb_a3_prox_bound {n : ℕ} (P : Instance n) (μ Mbar Lbar lam' : ℝ) (Γ : E n → ℝ)
    (c w xs : E n) (hμ : 0 ≤ μ) (hM : 0 ≤ Mbar) (hL : 0 ≤ Lbar)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mbar Lbar) (hlam' : 0 < lam') (hsmall : 2 * lam' * Lbar ≤ 1)
    (hΓ : StrongConvexOn P.D μ Γ) (hlow : ∀ u ∈ P.D, P.ellf u c + P.h u ≤ Γ u)
    (hup : ∀ u ∈ P.D, Γ u ≤ P.φ u) (hc : c ∈ P.D) (hw : P.IsProxMin Γ c lam' w)
    (hxs : P.IsOpt xs) :
    ‖w - c‖ ≤ 2 * ‖c - xs‖ + 2 * Real.sqrt 2 * lam' * Mbar := by
  have h7 := ProxBundle.GPB.eq_7 P μ Mbar Lbar hμ hM hL hA1 hA3 w hw.1 c hc
  have hq := gpb_a3_qgrowth P.D μ lam' Γ c w hΓ hlam' hμ hw.1 hw.2 xs hxs.1
  have hlo := hlow w hw.1
  have hupx := hup xs hxs.1
  have hopt := hxs.2 w hw.1
  unfold Instance.ellf at hlo h7
  unfold Instance.φ at hupx hopt
  set a := ‖w - c‖ with ha
  set b := ‖xs - w‖ with hb
  set Dd := ‖xs - c‖ with hDd
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hD0 : 0 ≤ Dd := norm_nonneg _
  -- multiply the growth inequality by 2λ'
  have hq2 : 2 * lam' * Γ w + a ^ 2 + (lam' * μ + 1) * b ^ 2 ≤ 2 * lam' * Γ xs + Dd ^ 2 := by
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ 2 * lam')
    have e1 : 2 * lam' * (Γ w + a ^ 2 / (2 * lam') + (μ + 1 / lam') / 2 * b ^ 2) =
        2 * lam' * Γ w + a ^ 2 + (lam' * μ + 1) * b ^ 2 := by field_simp
    have e2 : 2 * lam' * (Γ xs + Dd ^ 2 / (2 * lam')) = 2 * lam' * Γ xs + Dd ^ 2 := by
      field_simp
    linarith
  have hμb : b ^ 2 ≤ (lam' * μ + 1) * b ^ 2 := by nlinarith [mul_nonneg hlam'.le hμ]
  -- Γ w ≥ Γ xs - 2 M a - L/2 a^2
  have hG : Γ xs - 2 * Mbar * a - Lbar / 2 * a ^ 2 ≤ Γ w := by linarith
  have hG2 : 2 * lam' * (Γ xs - 2 * Mbar * a - Lbar / 2 * a ^ 2) ≤ 2 * lam' * Γ w :=
    mul_le_mul_of_nonneg_left hG (by positivity)
  have hLa : lam' * Lbar * a ^ 2 ≤ a ^ 2 / 2 := by nlinarith [sq_nonneg a]
  have hb2 : b ^ 2 ≤ Dd ^ 2 + 8 * lam' ^ 2 * Mbar ^ 2 := by
    nlinarith [sq_nonneg (a - 4 * lam' * Mbar)]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hbD : b ≤ Dd + 2 * Real.sqrt 2 * lam' * Mbar := by
    have hr : 0 ≤ Dd + 2 * Real.sqrt 2 * lam' * Mbar := by positivity
    have : b ^ 2 ≤ (Dd + 2 * Real.sqrt 2 * lam' * Mbar) ^ 2 := by
      have : (Dd + 2 * Real.sqrt 2 * lam' * Mbar) ^ 2 =
          Dd ^ 2 + 4 * Real.sqrt 2 * Dd * lam' * Mbar + 8 * lam' ^ 2 * Mbar ^ 2 := by
        ring_nf; rw [hs]; ring
      rw [this]
      have : 0 ≤ 4 * Real.sqrt 2 * Dd * lam' * Mbar := by positivity
      linarith
    exact (pow_le_pow_iff_left₀ hb0 hr two_ne_zero).mp this
  have htri : a ≤ b + Dd := by
    have : w - c = (w - xs) + (xs - c) := by abel
    rw [ha, this, hb, norm_sub_rev xs w]
    exact norm_add_le _ _
  rw [norm_sub_rev c xs]
  linarith

/-- (48) along the run: a serious index preceding the first `ε̄`-solution has
`‖x_j − x₀*‖ ≤ √2 d₀` (Proposition 4.3 applied to the serious iterates (43)). -/
lemma gpb_a3_run48 {n : ℕ} (P : Instance n) (μ Mbar Lbar lam ε τ : ℝ)
    (x0 x0s : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hM : 0 ≤ Mbar) (hL : 0 ≤ Lbar)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mbar Lbar)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (h29 : Cond29 μ lam ε τ Mbar Lbar)
    (hx0 : x0 ∈ P.D) (hopt : P.IsNearestOpt x0 x0s)
    (hrun : IsRun P μ lam ε τ x0 R)
    (j : ℕ) (hserious : R.t P lam j ≤ ε / 2)
    (hbefore : j = 0 ∨ ε < P.φ (R.y j) - P.φ x0s) :
    ‖R.x j - x0s‖ ≤ Real.sqrt 2 * ‖x0 - x0s‖ := by
  classical
  -- every cycle ends (Lemma 4.6)
  have hnext : ∀ j0 : ℕ, ∃ j, j0 < j ∧ R.t P lam j ≤ ε / 2 := by
    intro j0
    by_contra hcon
    push Not at hcon
    have hcontr : ∀ m : ℕ, R.t P lam (j0 + 1 + m) - ε / 4 ≤
        τ ^ m * (R.t P lam (j0 + 1) - ε / 4) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have h46 := ProxBundle.GPB.lemma_4_6 P μ Mbar Lbar lam ε τ x0 R hμ hM hL hA1 hA3
          hlam hε hτ0 hτ1 h29 hx0 hrun (j0 + 1 + m) (by omega) (hcon _ (by omega))
        rw [show j0 + 1 + (m + 1) = j0 + 1 + m + 1 by ring, pow_succ]
        calc _ ≤ τ * (R.t P lam (j0 + 1 + m) - ε / 4) := h46
          _ ≤ τ * (τ ^ m * (R.t P lam (j0 + 1) - ε / 4)) :=
              mul_le_mul_of_nonneg_left ih hτ0.le
          _ = _ := by ring
    have ha : 0 < R.t P lam (j0 + 1) - ε / 4 := by
      have := hcon (j0 + 1) (by omega); linarith
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (show 0 < ε / 4 / (R.t P lam (j0 + 1) - ε / 4) by positivity) hτ1
    have h1 := hcontr m
    have h2 := hcon (j0 + 1 + m) (by omega)
    rw [lt_div_iff₀ ha] at hm
    linarith
  let nxt : ℕ → ℕ := fun j0 => Nat.find (hnext j0)
  have nxt_spec : ∀ j0, j0 < nxt j0 ∧ R.t P lam (nxt j0) ≤ ε / 2 :=
    fun j0 => Nat.find_spec (hnext j0)
  have nxt_min : ∀ j0 i, j0 < i → i < nxt j0 → ε / 2 < R.t P lam i := by
    intro j0 i h1 h2
    have := Nat.find_min (hnext j0) h2
    push Not at this
    exact this h1
  let s : ℕ → ℕ := fun k => nxt^[k] 0
  have hs0 : s 0 = 0 := rfl
  have hs_succ : ∀ k, s (k + 1) = nxt (s k) := fun k =>
    Function.iterate_succ_apply' nxt k 0
  have hsmono : StrictMono s := strictMono_nat_of_lt_succ (fun k => by
    rw [hs_succ]; exact (nxt_spec _).1)
  have ht0 : R.t P lam 0 = 0 := by simp [Run.t]
  have hser : ∀ k, R.t P lam (s k) ≤ ε / 2 := by
    intro k
    cases k with
    | zero => rw [hs0, ht0]; positivity
    | succ k => rw [hs_succ]; exact (nxt_spec _).2
  have hΓ : ∀ j, 1 ≤ j → P.ConvBar μ (R.Γ j) ∧ ∀ u ∈ P.D, R.Γ j u ≤ P.φ u := by
    intro j hj
    obtain ⟨h1, h2, -, -, -⟩ := hrun.2.2 j hj
    by_cases ht : R.t P lam (j - 1) ≤ ε / 2
    · obtain ⟨-, hc, hu⟩ := h1 ht
      exact ⟨hc, fun u hu' => (hu u hu').2⟩
    · obtain ⟨hc, hu, -⟩ := (h2 (lt_of_not_ge ht)).2
      exact ⟨hc, hu⟩
  have hxD : ∀ i, R.x i ∈ P.D := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hrun.1]; exact hx0
    · exact ((hrun.2.2 i hi).2.2.1).1
  have hyD : ∀ j, R.y j ∈ P.D := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hrun.2.1]; exact hx0
    · obtain ⟨i, -, hi⟩ := (hrun.2.2 j hj).2.2.2.1
      rw [hi]; exact hxD i
  have hxc : ∀ j0, R.t P lam j0 ≤ ε / 2 → ∀ m, j0 + 1 ≤ m → m ≤ nxt j0 →
      R.xc m = R.x j0 := by
    intro j0 hj0 m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      exact (((hrun.2.2 (j0 + 1) (by omega)).1) (by simpa using hj0)).1
    | succ m hm ih =>
      intro hle
      have hnull : ε / 2 < R.t P lam m := nxt_min j0 m (by omega) (by omega)
      have := ((hrun.2.2 (m + 1) (by omega)).2.1) (by simpa using hnull)
      rw [this.1]
      simpa using ih (by omega)
  have hhat : IsHat P μ lam ε x0 (fun k => R.x (s k)) (fun k => R.y (s k))
      (fun k => R.Γ (s k)) := by
    refine ⟨by simp only [hs0]; exact hrun.1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hlt := (nxt_spec (s k')).1
    have hs1 : 1 ≤ s (k' + 1) := by rw [hs_succ]; omega
    have hxc' : R.xc (s (k' + 1)) = R.x (s k') := by
      rw [hs_succ]; exact hxc (s k') (hser k') _ (by omega) le_rfl
    obtain ⟨hc, hle⟩ := hΓ _ hs1
    refine ⟨hc, hle, ?_, hyD _, ?_⟩
    · have := (hrun.2.2 _ hs1).2.2.1
      rwa [hxc'] at this
    · have ht := hser (k' + 1)
      unfold Run.t at ht
      rw [if_neg (by omega)] at ht
      unfold Run.m at ht
      rw [hxc'] at ht
      exact ht
  obtain ⟨K, hK1, hKsol, -, -, h48⟩ :=
    ProxBundle.GPB.proposition_4_3 P μ lam ε x0 x0s _ _ _ hμ hA1 hlam hε hhat hopt
  -- j is a serious iterate s k
  have hexk : ∃ k, j < s (k + 1) := ⟨j, lt_of_lt_of_le (Nat.lt_succ_self j) (hsmono.id_le (j + 1))⟩
  set k := Nat.find hexk with hkdef
  have hk1 : j < s (k + 1) := Nat.find_spec hexk
  have hk0 : s k ≤ j := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, hs0]; omega
    · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have := Nat.find_min hexk (show k' < k by omega)
      push Not at this
      rw [hk']; exact this
  have hjk : s k = j := by
    by_contra hne
    have hlt : s k < j := lt_of_le_of_ne hk0 hne
    rw [hs_succ] at hk1
    have := nxt_min (s k) j hlt hk1
    linarith
  have hkK : k < K := by
    by_contra hge
    push Not at hge
    have hsK : s K ≤ j := hjk ▸ hsmono.monotone hge
    rcases hbefore with h0 | hb
    · have : k = 0 := by
        have := hsmono.id_le k; simp only [id] at this; omega
      omega
    · have hj1 : 1 ≤ j := by
        by_contra h
        have : j = 0 := by omega
        have : s K = 0 := by omega
        have := hsmono.id_le K; simp only [id] at this; omega
      have hbest : P.φ (R.y j) ≤ P.φ (R.y (s K)) := by
        rcases Nat.eq_zero_or_pos (s K) with h | h
        · rw [h, hrun.2.1, ← hrun.1]
          exact (hrun.2.2 j hj1).2.2.2.2 0 (by omega)
        · obtain ⟨i, hi, hyi⟩ := (hrun.2.2 (s K) h).2.2.2.1
          rw [hyi]
          exact (hrun.2.2 j hj1).2.2.2.2 i (by omega)
      have : P.φ (R.y (s K)) - P.φ x0s ≤ ε := hKsol
      linarith
  have := h48 k hkK
  rw [hjk] at this
  exact this

theorem solution {n : ℕ} (P : Instance n) (μ Mbar Lbar lam ε τ : ℝ)
    (x0 x0s : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hM : 0 ≤ Mbar) (hL : 0 ≤ Lbar)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mbar Lbar)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (h29 : Cond29 μ lam ε τ Mbar Lbar)
    (hx0 : x0 ∈ P.D) (hopt : P.IsNearestOpt x0 x0s)
    (hrun : IsRun P μ lam ε τ x0 R)
    (j : ℕ) (hserious : R.t P lam j ≤ ε / 2)
    (hbefore : j = 0 ∨ ε < P.φ (R.y j) - P.φ x0s) :
    ‖R.x j - R.x (j + 1)‖ ≤
      2 * Real.sqrt 2 *
        (max 1 (2 * lam * Lbar) * ‖x0 - x0s‖ + lam * Mbar) := by
  have h48 := gpb_a3_run48 P μ Mbar Lbar lam ε τ x0 x0s R hμ hM hL hA1 hA3 hlam hε hτ0 hτ1
    h29 hx0 hopt hrun j hserious hbefore
  obtain ⟨hserbr, -, hprox1, -, -⟩ := hrun.2.2 (j + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hserbr
  obtain ⟨hxc, hconv, hlu⟩ := hserbr hserious
  rw [hxc] at hprox1
  have hxjD : R.x j ∈ P.D := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, hrun.1]; exact hx0
    · exact (hrun.2.2 j h).2.2.1.1
  have hlow : ∀ u ∈ P.D, P.ellf u (R.x j) + P.h u ≤ R.Γ (j + 1) u := fun u hu => (hlu u hu).1
  have hup : ∀ u ∈ P.D, R.Γ (j + 1) u ≤ P.φ u := fun u hu => (hlu u hu).2
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hd0 : 0 ≤ ‖x0 - x0s‖ := norm_nonneg _
  have hDc : ‖R.x j - x0s‖ ≤ Real.sqrt 2 * ‖x0 - x0s‖ := h48
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [norm_sub_rev]
  by_cases hsm : 2 * lam * Lbar ≤ 1
  · have hb := gpb_a3_prox_bound P μ Mbar Lbar lam (R.Γ (j + 1)) (R.x j) (R.x (j + 1)) x0s
      hμ hM hL hA1 hA3 hlam hsm hconv.1 hlow hup hxjD hprox1 hopt.1
    rw [max_eq_left hsm]
    have : 2 * ‖R.x j - x0s‖ ≤ 2 * Real.sqrt 2 * ‖x0 - x0s‖ := by linarith
    nlinarith
  · push Not at hsm
    have hLpos : 0 < Lbar := by
      by_contra h
      push Not at h
      have : Lbar = 0 := le_antisymm h hL
      rw [this] at hsm; linarith
    set lam' := 1 / (2 * Lbar) with hlam'def
    have hlam' : 0 < lam' := by positivity
    have hsm' : 2 * lam' * Lbar ≤ 1 := by
      rw [hlam'def]; field_simp; exact le_rfl
    have hll : lam' ≤ lam := by
      rw [hlam'def, div_le_iff₀ (by positivity)]; linarith
    obtain ⟨w, hw⟩ := gpb_a3_prox_exists P μ lam lam' (R.Γ (j + 1)) (R.x j) (R.x (j + 1))
      hμ hconv hlam hlam' hxjD hprox1
    have hb := gpb_a3_prox_bound P μ Mbar Lbar lam' (R.Γ (j + 1)) (R.x j) w x0s
      hμ hM hL hA1 hA3 hlam' hsm' hconv.1 hlow hup hxjD hw hopt.1
    have hzsub := gpb_a3_subgrad P.D μ lam (R.Γ (j + 1)) (R.x j) (R.x (j + 1)) hconv.1 hlam hμ
      hprox1.1 hprox1.2
    have hwsub := gpb_a3_subgrad P.D μ lam' (R.Γ (j + 1)) (R.x j) w hconv.1 hlam' hμ
      hw.1 hw.2
    have hres := gpb_a3_resolvent P.D (R.Γ (j + 1)) (R.x j) (R.x (j + 1)) w lam lam' hlam' hll
      hprox1.1 hw.1 hzsub hwsub
    have hratio : lam / lam' = 2 * lam * Lbar := by rw [hlam'def]; field_simp
    rw [hratio] at hres
    rw [max_eq_right hsm.le]
    have hkey : 2 * lam * Lbar * lam' = lam := by rw [hlam'def]; field_simp
    have hwc0 : 0 ≤ ‖w - R.x j‖ := norm_nonneg _
    have h1 : 2 * lam * Lbar * ‖w - R.x j‖ ≤
        2 * lam * Lbar * (2 * ‖R.x j - x0s‖ + 2 * Real.sqrt 2 * lam' * Mbar) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    have h2 : 2 * lam * Lbar * (2 * ‖R.x j - x0s‖) ≤
        2 * lam * Lbar * (2 * (Real.sqrt 2 * ‖x0 - x0s‖)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : 2 * lam * Lbar * (2 * ‖R.x j - x0s‖ + 2 * Real.sqrt 2 * lam' * Mbar) =
        2 * lam * Lbar * (2 * ‖R.x j - x0s‖) + 2 * Real.sqrt 2 * Mbar * (2 * lam * Lbar * lam') := by
      ring
    rw [hkey] at e
    nlinarith
