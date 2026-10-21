-- Prove2me | solution 1 for RoboAdvising.Interaction.corner_case
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:03:50.460655+00:00
-- url     : https://prove2.me/submissions/cc255644-6ff7-47c9-8245-d67584ac6abe

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

set_option autoImplicit false
open RoboAdvising.Interaction

lemma ra_fd (P : Params) (hS : P.Standing) (φ : ℝ) (hφ : 0 < φ) :
    HasDerivAt (fAux P)
      (-(P.β*P.sig0) / (2 * Real.sqrt φ * φ) * (1 - (φ-1)/2*P.pe)
        - P.β*P.sig0*P.pe/(2*Real.sqrt φ)
        - (P.β*P.sig0)^2 * Real.sqrt φ / (2*φ^2*Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ)) * ((φ-1)/2*P.pe)
        + Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) / Real.sqrt φ * (P.pe/2)) φ := by
  obtain ⟨h0, hse, -⟩ := hS
  have hu : 0 < Real.sqrt φ := Real.sqrt_pos.2 hφ
  have hH : 0 < P.β^2*P.sig0^2/φ + P.se^2 := by positivity
  have h1 : HasDerivAt Real.sqrt (1/(2*Real.sqrt φ)) φ := Real.hasDerivAt_sqrt hφ.ne'
  have hA := (hasDerivAt_const φ (P.β*P.sig0)).div h1 hu.ne'
  have hT0 : HasDerivAt (fun x : ℝ => (x-1)/2) (1/2) φ :=
    ((hasDerivAt_id φ).sub_const 1).div_const 2
  have hL : HasDerivAt (fun x : ℝ => 1 - (x-1)/2*P.pe) (-(1/2*P.pe)) φ := by
    simpa using (hT0.mul_const P.pe).const_sub 1
  have hq := (hasDerivAt_const φ (P.β^2*P.sig0^2)).div (hasDerivAt_id φ) hφ.ne'
  have hB := (hq.add_const (P.se^2)).sqrt hH.ne'
  have hf := (hA.mul hL).add ((hB.mul hT0).mul_const P.pe)
  have hw : Real.sqrt (P.β^2*P.sig0^2/φ + P.se^2) = Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) / Real.sqrt φ := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  refine HasDerivAt.congr_deriv hf ?_
  simp only [id, Pi.div_apply]
  rw [hw]
  have hwpos : 0 < Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt φ ^ 2 = φ := Real.sq_sqrt hφ.le
  have e2 : P.β^2*P.sig0^2 = (P.β*P.sig0)^2 := by ring
  rw [e2]
  clear hf hA hB hq hL hT0 h1 hw hH
  generalize Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) = w at *
  generalize P.β*P.sig0 = a at *
  generalize Real.sqrt φ = u at *
  subst hsq
  field_simp
  ring

lemma ra_q (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (φ : ℝ) (hφ : 0 ≤ φ) :
    Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) =
      Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) / (P.β*P.sig0) := by
  obtain ⟨h0, hse, -⟩ := hS
  have ha : 0 < P.β * P.sig0 := mul_pos hβ h0
  have : 1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) = ((P.β*P.sig0)^2 + P.se^2*φ) / (P.β*P.sig0)^2 := by
    field_simp
  rw [this, Real.sqrt_div (by positivity), Real.sqrt_sq ha.le]

lemma ra_hasDerivAt_f (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe)
    (φ : ℝ) (hφ : 0 < φ) :
    HasDerivAt (fAux P) (1 / 2 * (P.β * P.sig0 * P.pe / φ ^ 2) * gAux P φ) φ := by
  have h := ra_fd P hS φ hφ
  have hS' := hS
  obtain ⟨h0, hse, -⟩ := hS
  refine HasDerivAt.congr_deriv h ?_
  have hq := ra_q P hS' hβ φ hφ.le
  unfold gAux
  rw [hq]
  have ha : 0 < P.β * P.sig0 := mul_pos hβ h0
  have hwpos : 0 < Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) := Real.sqrt_pos.2 (by positivity)
  have hu : 0 < Real.sqrt φ := Real.sqrt_pos.2 hφ
  have hsq : Real.sqrt φ ^ 2 = φ := Real.sq_sqrt hφ.le
  clear h hq hS'
  generalize Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) = w at *
  generalize P.β*P.sig0 = a at *
  generalize Real.sqrt φ = u at *
  generalize P.pe = p at *
  subst hsq
  field_simp
  ring


lemma ra_gd (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (φ : ℝ) (hφ : 0 < φ) :
    HasDerivAt (gAux P)
      (-(1 / (2 * Real.sqrt φ)) / P.pe
        + 1 / 2 * ((P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2)) / (2 * Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)))
              / Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 2 * Real.sqrt φ * (φ - 1)
            + (1 - 1 / Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)))
              * ((φ - 1) / (2 * Real.sqrt φ) + Real.sqrt φ))
        + (P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2)) / (2 * Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)))
            * (φ * Real.sqrt φ)
        + (Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) - 1)
            * (Real.sqrt φ + φ / (2 * Real.sqrt φ))) φ := by
  obtain ⟨h0, hse, -⟩ := hS
  have hu : 0 < Real.sqrt φ := Real.sqrt_pos.2 hφ
  have hH : 0 < 1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) := by positivity
  have h1 : HasDerivAt Real.sqrt (1/(2*Real.sqrt φ)) φ := Real.hasDerivAt_sqrt hφ.ne'
  have hI : HasDerivAt (fun x : ℝ => 1 + P.se ^ 2 * x / (P.β ^ 2 * P.sig0 ^ 2))
      (P.se ^ 2 * 1 / (P.β ^ 2 * P.sig0 ^ 2)) φ :=
    (((hasDerivAt_id φ).const_mul (P.se ^ 2)).div_const (P.β ^ 2 * P.sig0 ^ 2)).const_add 1
  have hq := hI.sqrt hH.ne'
  have hqpos : 0 < Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) := Real.sqrt_pos.2 hH
  have hinvq := (hasDerivAt_const φ (1:ℝ)).div hq hqpos.ne'
  have hT1 := (h1.div_const P.pe).neg
  have hT2 := (((hinvq.const_sub 1).const_mul (1/2 : ℝ)).mul h1).mul ((hasDerivAt_id φ).sub_const 1)
  have hT3 := (hq.sub_const 1).mul ((hasDerivAt_id φ).mul h1)
  have hf := (hT1.add hT2).add hT3
  refine HasDerivAt.congr_deriv hf ?_
  have hsq : Real.sqrt φ ^ 2 = φ := Real.sq_sqrt hφ.le
  have hqsq : Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 2
      = 1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) := Real.sq_sqrt hH.le
  simp only [id, Pi.div_apply, Pi.mul_apply]
  clear hf hT1 hT2 hT3 hinvq hq hI h1
  generalize Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) = q at *
  generalize Real.sqrt φ = u at *
  field_simp
  ring


lemma ra_ineq (u q r0 K p φ : ℝ) (hu : 1 ≤ u) (hφ : φ = u ^ 2) (hq : r0 ≤ q) (hr0 : 1 ≤ r0)
    (hK : 0 < K) (hp : 0 < p) :
    1 / 2 * (1 / u) * (-(1 / p) + (r0 - 1)) ≤
      -(1 / (2 * u)) / p + 1 / 2 * (K / (2 * q) / q ^ 2 * u * (φ - 1)
        + (1 - 1 / q) * ((φ - 1) / (2 * u) + u)) + K / (2 * q) * (φ * u)
        + (q - 1) * (u + φ / (2 * u)) := by
  have hu0 : 0 < u := by linarith
  have hq1 : 1 ≤ q := le_trans hr0 hq
  have hq0 : 0 < q := by linarith
  have hφ1 : 1 ≤ φ := by rw [hφ]; nlinarith
  have hφ0 : 0 < φ := by linarith
  have t1 : 0 ≤ K / (2 * q) / q ^ 2 * u * (φ - 1) := by
    have : 0 ≤ φ - 1 := by linarith
    positivity
  have t2 : 0 ≤ (1 - 1 / q) * ((φ - 1) / (2 * u) + u) := by
    have h1 : 0 ≤ 1 - 1 / q := by
      rw [sub_nonneg, div_le_one hq0]; exact hq1
    have : 0 ≤ φ - 1 := by linarith
    positivity
  have t3 : 0 ≤ K / (2 * q) * (φ * u) := by positivity
  have t4 : (r0 - 1) / (2 * u) ≤ (q - 1) * (u + φ / (2 * u)) := by
    have e1 : (r0 - 1) * (1 / (2 * u)) ≤ (r0 - 1) * u := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have e2 : (r0 - 1) * u ≤ (q - 1) * (u + φ / (2 * u)) := by
      have : 0 ≤ φ / (2 * u) := by positivity
      have e3 : (r0 - 1) * u ≤ (q - 1) * u := mul_le_mul_of_nonneg_right (by linarith) hu0.le
      have e4 : (q - 1) * u ≤ (q - 1) * (u + φ / (2 * u)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    calc (r0 - 1) / (2 * u) = (r0 - 1) * (1 / (2 * u)) := by ring
      _ ≤ _ := le_trans e1 e2
  have e : 1 / 2 * (1 / u) * (-(1 / p) + (r0 - 1)) = -(1 / (2 * u)) / p + (r0 - 1) / (2 * u) := by
    field_simp
  rw [e]
  nlinarith


lemma ra_g1 (P : Params) :
    gAux P 1 = -(1 / P.pe) + (Real.sqrt (1 + P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2)) - 1) := by
  unfold gAux
  simp only [Real.sqrt_one, mul_one, sub_self, mul_zero, add_zero]

lemma ra_gbound (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe)
    (φ : ℝ) (hφ : 1 ≤ φ) :
    ∃ d : ℝ, HasDerivAt (gAux P) d φ ∧ 1 / 2 * (1 / Real.sqrt φ) * gAux P 1 ≤ d := by
  have hS' := hS
  obtain ⟨h0, hse, -⟩ := hS
  have hφ0 : 0 < φ := by linarith
  refine ⟨_, ra_gd P hS' hβ φ hφ0, ?_⟩
  rw [ra_g1]
  have hK : 0 < P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2) := by positivity
  have hu : 1 ≤ Real.sqrt φ := by rw [Real.one_le_sqrt]; exact hφ
  have hr0 : 1 ≤ Real.sqrt (1 + P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2)) := by
    rw [Real.one_le_sqrt]; linarith
  have hq : Real.sqrt (1 + P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2)) ≤
      Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) := by
    apply Real.sqrt_le_sqrt
    have : P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2) ≤ P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) := by
      gcongr
      exact le_mul_of_one_le_right (sq_nonneg _) hφ
    linarith
  exact ra_ineq _ _ _ _ _ φ hu (Real.sq_sqrt hφ0.le).symm hq hr0 hK hpe

lemma ra_g_mono (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe)
    (h : 0 ≤ gAux P 1) : MonotoneOn (gAux P) (Set.Ici 1) := by
  have hd : ∀ φ : ℝ, 1 ≤ φ → HasDerivAt (gAux P) (deriv (gAux P) φ) φ := by
    intro φ hφ
    obtain ⟨d, hd, -⟩ := ra_gbound P hS hβ hpe φ hφ
    rw [hd.deriv]; exact hd
  apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (hd x (le_of_lt hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx1 : 1 ≤ x := le_of_lt hx
    obtain ⟨d, hd', hb⟩ := ra_gbound P hS hβ hpe x hx1
    rw [hd'.deriv]
    refine le_trans ?_ hb
    have : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    positivity


lemma ra_f_mono (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe)
    (S : Set ℝ) (hc : Convex ℝ S) (hS1 : S ⊆ Set.Ici 1)
    (hg : ∀ x ∈ S, 0 ≤ gAux P x) : MonotoneOn (fAux P) S := by
  have hd : ∀ φ ∈ S, HasDerivAt (fAux P) (1 / 2 * (P.β * P.sig0 * P.pe / φ ^ 2) * gAux P φ) φ := by
    intro φ hφ
    exact ra_hasDerivAt_f P hS hβ hpe φ (lt_of_lt_of_le one_pos (hS1 hφ))
  apply monotoneOn_of_deriv_nonneg hc
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxS := interior_subset hx
    rw [(hd x hxS).deriv]
    obtain ⟨h0, hse, hp0, hp1, hb0⟩ := hS
    have := hg x hxS
    have h1 : (0:ℝ) < x := lt_of_lt_of_le one_pos (hS1 hxS)
    have h2 : 0 < P.β * P.sig0 * P.pe / x ^ 2 := by positivity
    positivity

lemma ra_f_anti (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe)
    (S : Set ℝ) (hc : Convex ℝ S) (hS1 : S ⊆ Set.Ici 1)
    (hg : ∀ x ∈ S, gAux P x ≤ 0) : AntitoneOn (fAux P) S := by
  have hd : ∀ φ ∈ S, HasDerivAt (fAux P) (1 / 2 * (P.β * P.sig0 * P.pe / φ ^ 2) * gAux P φ) φ := by
    intro φ hφ
    exact ra_hasDerivAt_f P hS hβ hpe φ (lt_of_lt_of_le one_pos (hS1 hφ))
  apply antitoneOn_of_deriv_nonpos hc
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxS := interior_subset hx
    rw [(hd x hxS).deriv]
    obtain ⟨h0, hse, hp0, hp1, hb0⟩ := hS
    have := hg x hxS
    have h1 : (0:ℝ) < x := lt_of_lt_of_le one_pos (hS1 hxS)
    have h2 : 0 < P.β * P.sig0 * P.pe / x ^ 2 := by positivity
    have h3 : 0 < 1 / 2 * (P.β * P.sig0 * P.pe / x ^ 2) := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos h3.le this

theorem solution (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe) :
    (∀ φ : ℝ, 1 ≤ φ → ∃ d : ℝ, HasDerivAt (gAux P) d φ ∧
        1 / 2 * (1 / Real.sqrt φ) * gAux P 1 ≤ d) ∧
    (0 ≤ gAux P 1 →
      (∀ φ : ℝ, 1 ≤ φ → ∃ d : ℝ, HasDerivAt (fAux P) d φ ∧ 0 ≤ d) ∧
      IsMinOn (fAux P) (Set.Ici 1) 1) := by
  refine ⟨fun φ hφ => ra_gbound P hS hβ hpe φ hφ, fun h => ?_⟩
  have hgm := ra_g_mono P hS hβ hpe h
  have hg : ∀ x ∈ Set.Ici (1:ℝ), 0 ≤ gAux P x := fun x hx =>
    le_trans h (hgm (Set.mem_Ici.2 le_rfl) hx hx)
  refine ⟨fun φ hφ => ?_, ?_⟩
  · refine ⟨_, ra_hasDerivAt_f P hS hβ hpe φ (lt_of_lt_of_le one_pos hφ), ?_⟩
    obtain ⟨h0, hse, hp0, hp1, hb0⟩ := hS
    have := hg φ hφ
    have h1 : (0:ℝ) < φ := lt_of_lt_of_le one_pos hφ
    have h2 : 0 < P.β * P.sig0 * P.pe / φ ^ 2 := by positivity
    positivity
  · have hm := ra_f_mono P hS hβ hpe (Set.Ici 1) (convex_Ici 1) subset_rfl hg
    intro x hx
    exact hm (Set.mem_Ici.2 le_rfl) hx hx
