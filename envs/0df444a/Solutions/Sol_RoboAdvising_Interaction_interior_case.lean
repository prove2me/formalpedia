-- Prove2me | solution 1 for RoboAdvising.Interaction.interior_case
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:09:11.697413+00:00
-- url     : https://prove2.me/submissions/3d09286d-cd39-4a46-9ba1-e5f3e08bba1d

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


noncomputable def raGs (P : Params) (x : ℝ) : ℝ :=
  2 * Real.sqrt x * Real.sqrt (1 + P.se ^ 2 * x / (P.β ^ 2 * P.sig0 ^ 2))
    - 3 / 4 * Real.sqrt x
    - Real.sqrt x / Real.sqrt (1 + P.se ^ 2 * x / (P.β ^ 2 * P.sig0 ^ 2))
    - Real.sqrt x * (1 + P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2))
        / (4 * Real.sqrt (1 + P.se ^ 2 * x / (P.β ^ 2 * P.sig0 ^ 2)) ^ 3)
    - 1 / (4 * Real.sqrt x)
    + 1 / (4 * (Real.sqrt x * Real.sqrt (1 + P.se ^ 2 * x / (P.β ^ 2 * P.sig0 ^ 2))))
    - 1 / (2 * Real.sqrt x * P.pe)

lemma ra_gd_eq (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe) (φ : ℝ) (hφ : 0 < φ) :
    deriv (gAux P) φ = raGs P φ := by
  rw [(ra_gd P hS hβ φ hφ).deriv]
  obtain ⟨h0, hse, -⟩ := hS
  have hu : 0 < Real.sqrt φ := Real.sqrt_pos.2 hφ
  have hH : 0 < 1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) := by positivity
  have hqpos : 0 < Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) := Real.sqrt_pos.2 hH
  have hsq : Real.sqrt φ ^ 2 = φ := Real.sq_sqrt hφ.le
  have hqsq : Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 2
      = 1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) := Real.sq_sqrt hH.le
  unfold raGs
  have hK : P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) = P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2) * φ := by ring
  rw [hK] at hqsq hqpos ⊢
  clear hH hK
  generalize P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2) = K at *
  generalize Real.sqrt (1 + K * φ) = q at *
  generalize Real.sqrt φ = u at *
  have hK' : K = (q ^ 2 - 1) / φ := by
    field_simp; linarith
  subst hK'
  subst hsq
  field_simp
  ring


lemma ra_Gs_deriv (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe) (φ : ℝ) (hφ : 0 < φ) :
    HasDerivAt (raGs P)
      ((P.pe * (16 * Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 6 * Real.sqrt φ ^ 2
            - 3 * Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 5 * Real.sqrt φ ^ 2
            + Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 5
            - 8 * Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 4 * Real.sqrt φ ^ 2
            - 2 * Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 2 * Real.sqrt φ ^ 2
            - 4 * Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 2
            - 3 * Real.sqrt φ ^ 2 + 3)
          + 2 * Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 5)
        / (8 * Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 5 * Real.sqrt φ ^ 3 * P.pe)) φ := by
  obtain ⟨h0, hse, -⟩ := hS
  have hu : 0 < Real.sqrt φ := Real.sqrt_pos.2 hφ
  have hH : 0 < 1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) := by positivity
  have h1 : HasDerivAt Real.sqrt (1/(2*Real.sqrt φ)) φ := Real.hasDerivAt_sqrt hφ.ne'
  have hI : HasDerivAt (fun x : ℝ => 1 + P.se ^ 2 * x / (P.β ^ 2 * P.sig0 ^ 2))
      (P.se ^ 2 * 1 / (P.β ^ 2 * P.sig0 ^ 2)) φ :=
    (((hasDerivAt_id φ).const_mul (P.se ^ 2)).div_const (P.β ^ 2 * P.sig0 ^ 2)).const_add 1
  have hq := hI.sqrt hH.ne'
  have hqpos : 0 < Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) := Real.sqrt_pos.2 hH
  have hA := ((h1.const_mul 2).mul hq)
  have hB := h1.const_mul (3 / 4 : ℝ)
  have hC := h1.div hq hqpos.ne'
  have hD := (h1.mul_const (1 + P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2))).div (hq.pow 3 |>.const_mul 4)
    (by simp; exact hqpos.ne')
  have hE := (hasDerivAt_const φ (1:ℝ)).div (h1.const_mul 4) (by beta_reduce; positivity)
  have hF := (hasDerivAt_const φ (1:ℝ)).div ((h1.mul hq).const_mul 4)
    (by show (4:ℝ) * (Real.sqrt φ * Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2))) ≠ 0; positivity)
  have hG := (hasDerivAt_const φ (1:ℝ)).div ((h1.const_mul 2).mul_const P.pe) (by beta_reduce; positivity)
  have hf := (((((hA.sub hB).sub hC).sub hD).sub hE).add hF).sub hG
  refine HasDerivAt.congr_deriv hf ?_
  have hsq : Real.sqrt φ ^ 2 = φ := Real.sq_sqrt hφ.le
  have hqsq : Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) ^ 2
      = 1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) := Real.sq_sqrt hH.le
  simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub]
  clear hf hA hB hC hD hE hF hG hq hI h1
  have hK : P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) = P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2) * φ := by ring
  have hK2 : P.se ^ 2 * 1 / (P.β ^ 2 * P.sig0 ^ 2) = P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2) := by ring
  rw [hK] at hqsq hqpos hH ⊢
  rw [hK2]
  clear hK hK2 hH
  generalize P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2) = K at *
  generalize Real.sqrt (1 + K * φ) = q at *
  generalize Real.sqrt φ = u at *
  have hK' : K = (q ^ 2 - 1) / φ := by
    field_simp; linarith
  subst hK'
  subst hsq
  field_simp
  ring


lemma ra_N_pos (u q p : ℝ) (hu : 1 ≤ u) (hq : 1 ≤ q) (hp : 0 < p) :
    0 < (p * (16 * q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 2 + q ^ 5 - 8 * q ^ 4 * u ^ 2
            - 2 * q ^ 2 * u ^ 2 - 4 * q ^ 2 - 3 * u ^ 2 + 3) + 2 * q ^ 5)
        / (8 * q ^ 5 * u ^ 3 * p) := by
  have hq0 : 0 < q := by linarith
  have hu0 : 0 < u := by linarith
  apply div_pos _ (by positivity)
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have hq3 : 1 ≤ q ^ 3 := by nlinarith
  have hq4 : 1 ≤ q ^ 4 := by nlinarith
  have hq5 : 1 ≤ q ^ 5 := by nlinarith
  have hA : 0 ≤ 16 * q ^ 6 - 3 * q ^ 5 - 8 * q ^ 4 - 2 * q ^ 2 - 3 := by
    have : q ^ 6 = q * q ^ 5 := by ring
    have : q ^ 5 = q * q ^ 4 := by ring
    nlinarith
  have hB : 0 ≤ 8 * q ^ 4 - q ^ 3 - 4 * q ^ 2 - 3 := by
    have : q ^ 4 = q * q ^ 3 := by ring
    have : q ^ 3 = q * q ^ 2 := by ring
    nlinarith
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have hpoly : 0 ≤ 16 * q ^ 6 * u ^ 2 - 3 * q ^ 5 * u ^ 2 + q ^ 5 - 8 * q ^ 4 * u ^ 2
            - 2 * q ^ 2 * u ^ 2 - 4 * q ^ 2 - 3 * u ^ 2 + 3 := by
    have h1 : 0 ≤ (u ^ 2 - 1) * (16 * q ^ 6 - 3 * q ^ 5 - 8 * q ^ 4 - 2 * q ^ 2 - 3) :=
      mul_nonneg (by linarith) hA
    have h2 : 0 ≤ q ^ 2 * (8 * q ^ 4 - q ^ 3 - 4 * q ^ 2 - 3) := mul_nonneg (by positivity) hB
    nlinarith
  have := mul_nonneg hp.le hpoly
  have : 0 < 2 * q ^ 5 := by positivity
  linarith


lemma ra_g_strictConvex (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe) :
    StrictConvexOn ℝ (Set.Ici 1) (gAux P) := by
  have hS' := hS
  obtain ⟨h0, hse, -⟩ := hS
  have hGs : StrictMonoOn (raGs P) (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · intro x hx
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
      exact (ra_Gs_deriv P hS' hβ hpe x hx0).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx1 : (1:ℝ) < x := hx
      have hx0 : (0:ℝ) < x := by linarith
      rw [(ra_Gs_deriv P hS' hβ hpe x hx0).deriv]
      have hu : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx1.le
      have hq : 1 ≤ Real.sqrt (1 + P.se ^ 2 * x / (P.β ^ 2 * P.sig0 ^ 2)) := by
        rw [Real.one_le_sqrt]
        have : 0 ≤ P.se ^ 2 * x / (P.β ^ 2 * P.sig0 ^ 2) := by positivity
        linarith
      exact ra_N_pos _ _ _ hu hq hpe
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 1)
  · intro x hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
    exact (ra_gd P hS' hβ x hx0).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    intro a ha b hb hab
    have ha0 : (0:ℝ) < a := lt_trans one_pos ha
    have hb0 : (0:ℝ) < b := lt_trans one_pos hb
    rw [ra_gd_eq P hS' hβ hpe a ha0, ra_gd_eq P hS' hβ hpe b hb0]
    exact hGs (Set.mem_Ici.2 (le_of_lt ha)) (Set.mem_Ici.2 (le_of_lt hb)) hab


lemma ra_g_tendsto (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe) :
    Filter.Tendsto (gAux P) Filter.atTop Filter.atTop := by
  obtain ⟨h0, hse, -⟩ := hS
  have hD : 0 < P.β ^ 2 * P.sig0 ^ 2 := by positivity
  have hK : 0 < P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2) := by positivity
  set K := P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2) with hKdef
  have hev : ∀ᶠ φ in Filter.atTop, φ ≤ gAux P φ := by
    filter_upwards [Filter.eventually_ge_atTop (max 1 ((2 + 1 / P.pe) ^ 2 / K))] with φ hφ
    have hφ1 : 1 ≤ φ := le_trans (le_max_left _ _) hφ
    have hφ2 : (2 + 1 / P.pe) ^ 2 / K ≤ φ := le_trans (le_max_right _ _) hφ
    have hφ0 : 0 < φ := by linarith
    have hKφ : P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) = K * φ := by rw [hKdef]; ring
    have hu : 1 ≤ Real.sqrt φ := by rw [Real.one_le_sqrt]; exact hφ1
    have hu2 : Real.sqrt φ * Real.sqrt φ = φ := Real.mul_self_sqrt hφ0.le
    have hq1 : 2 + 1 / P.pe ≤ Real.sqrt (1 + K * φ) := by
      apply Real.le_sqrt_of_sq_le
      have : (2 + 1 / P.pe) ^ 2 ≤ K * φ := by
        rw [div_le_iff₀ hK] at hφ2; linarith
      linarith
    unfold gAux
    rw [hKφ]
    generalize Real.sqrt (1 + K * φ) = q at *
    generalize Real.sqrt φ = u at *
    have hq0 : 0 < q := by
      have : (0:ℝ) < 1 / P.pe := by positivity
      linarith
    have hqinv : 0 ≤ 1 - 1 / q := by
      rw [sub_nonneg, div_le_one hq0]; have : (0:ℝ) < 1 / P.pe := by positivity
      linarith
    have hmid : 0 ≤ 1 / 2 * (1 - 1 / q) * u * (φ - 1) := by
      have : 0 ≤ φ - 1 := by linarith
      have : 0 ≤ u := by linarith
      positivity
    have hpinv : 1 / P.pe * P.pe = 1 := by field_simp
    have h3 : (1 + 1 / P.pe) * (φ * u) ≤ (q - 1) * (φ * u) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : -(u / P.pe) = -(u * (1 / P.pe)) := by ring
    have h5 : u * (1 / P.pe) ≤ (1 / P.pe) * (φ * u) := by
      have h7 : 0 ≤ 1 / P.pe := by positivity
      have h8 : u ≤ φ * u := by nlinarith
      have := mul_le_mul_of_nonneg_left h8 h7
      linarith
    have h6 : φ ≤ φ * u := by nlinarith
    nlinarith
  exact Filter.tendsto_atTop_mono' _ hev Filter.tendsto_id


lemma ra_sc_lt_max (g : ℝ → ℝ) (S : Set ℝ) (hg : StrictConvexOn ℝ S g) {x y z : ℝ}
    (hx : x ∈ S) (hz : z ∈ S) (hxy : x < y) (hyz : y < z) : g y < max (g x) (g z) := by
  have hxz : x < z := hxy.trans hyz
  have hzx : 0 < z - x := by linarith
  have ha : 0 < (z - y) / (z - x) := div_pos (by linarith) hzx
  have hb : 0 < (y - x) / (z - x) := div_pos (by linarith) hzx
  have hab : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by field_simp; ring
  have h := hg.2 hx hz hxz.ne ha hb hab
  have hne : z - x ≠ 0 := hzx.ne'
  have hy : ((z - y) / (z - x)) • x + ((y - x) / (z - x)) • z = y := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [hy] at h
  simp only [smul_eq_mul] at h
  refine lt_of_lt_of_le h ?_
  have h1 : g x ≤ max (g x) (g z) := le_max_left _ _
  have h2 : g z ≤ max (g x) (g z) := le_max_right _ _
  have h3 := mul_le_mul_of_nonneg_left h1 ha.le
  have h4 := mul_le_mul_of_nonneg_left h2 hb.le
  have h5 : (z - y) / (z - x) * max (g x) (g z) + (y - x) / (z - x) * max (g x) (g z)
      = max (g x) (g z) := by rw [← add_mul, hab, one_mul]
  linarith

theorem solution (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe)
    (hg : gAux P 1 < 0) :
    StrictConvexOn ℝ (Set.Ici 1) (gAux P) ∧
    Filter.Tendsto (gAux P) Filter.atTop Filter.atTop ∧
    (∃! φ0 : ℝ, 1 ≤ φ0 ∧ gAux P φ0 = 0) ∧
    (∀ φ0 : ℝ, 1 ≤ φ0 → gAux P φ0 = 0 → IsMinOn (fAux P) (Set.Ici 1) φ0) := by
  have hsc := ra_g_strictConvex P hS hβ hpe
  have htend := ra_g_tendsto P hS hβ hpe
  have hcont : ContinuousOn (gAux P) (Set.Ici 1) := fun x hx =>
    (ra_gd P hS hβ x (lt_of_lt_of_le one_pos hx)).continuousAt.continuousWithinAt
  have hmem1 : (1:ℝ) ∈ Set.Ici (1:ℝ) := Set.mem_Ici.2 le_rfl
  -- no two zeros
  have hnoz : ∀ a b : ℝ, 1 ≤ a → a < b → gAux P a = 0 → gAux P b = 0 → False := by
    intro a b ha hab hga hgb
    have ha1 : 1 < a := by
      rcases ha.lt_or_eq with h | h
      · exact h
      · rw [← h] at hga; linarith
    have := ra_sc_lt_max (gAux P) _ hsc hmem1 (Set.mem_Ici.2 (le_trans ha hab.le)) ha1 hab
    rw [hga, hgb] at this
    have : max (gAux P 1) 0 = 0 := max_eq_right hg.le
    linarith
  have hsign : ∀ φ0 : ℝ, 1 ≤ φ0 → gAux P φ0 = 0 →
      (∀ φ ∈ Set.Icc 1 φ0, gAux P φ ≤ 0) ∧ (∀ φ, φ0 ≤ φ → 0 ≤ gAux P φ) := by
    intro φ0 h1 h0
    have hφ01 : 1 < φ0 := by
      rcases h1.lt_or_eq with h | h
      · exact h
      · rw [← h] at h0; linarith
    constructor
    · intro φ hφ
      rcases hφ.1.lt_or_eq with h | h
      · rcases hφ.2.lt_or_eq with h' | h'
        · have := ra_sc_lt_max (gAux P) _ hsc hmem1 (Set.mem_Ici.2 h1) h h'
          rw [h0, max_eq_right hg.le] at this
          exact this.le
        · rw [h', h0]
      · rw [← h]; exact hg.le
    · intro φ hφ
      rcases hφ.lt_or_eq with h | h
      · have := ra_sc_lt_max (gAux P) _ hsc hmem1 (Set.mem_Ici.2 (le_trans h1 h.le)) hφ01 h
        rw [h0] at this
        by_contra hc
        rw [not_le] at hc
        have : max (gAux P 1) (gAux P φ) < 0 := max_lt hg hc
        linarith
      · rw [← h, h0]
  refine ⟨hsc, htend, ?_, ?_⟩
  · obtain ⟨M, hM1, hM2⟩ := ((htend.eventually (Filter.eventually_ge_atTop 0)).and
      (Filter.eventually_ge_atTop 1)).exists
    have hIVT := intermediate_value_Icc hM2 (hcont.mono (Set.Icc_subset_Ici_self))
    obtain ⟨φ0, hφ0, hz⟩ := hIVT ⟨hg.le, hM1⟩
    refine ⟨φ0, ⟨hφ0.1, hz⟩, ?_⟩
    rintro y ⟨hy1, hy0⟩
    rcases lt_trichotomy y φ0 with h | h | h
    · exact absurd (hnoz y φ0 hy1 h hy0 hz) id
    · exact h
    · exact absurd (hnoz φ0 y hφ0.1 h hz hy0) id
  · intro φ0 h1 h0
    obtain ⟨hs1, hs2⟩ := hsign φ0 h1 h0
    rw [isMinOn_iff]
    intro x hx
    have hx1 : 1 ≤ x := hx
    rcases le_total x φ0 with h | h
    · have hanti := ra_f_anti P hS hβ hpe (Set.Icc 1 φ0) (convex_Icc _ _)
        (fun y hy => hy.1) hs1
      exact hanti ⟨hx1, h⟩ ⟨h1, le_rfl⟩ h
    · have hmono := ra_f_mono P hS hβ hpe (Set.Ici φ0) (convex_Ici _)
        (fun y hy => le_trans h1 hy) (fun y hy => hs2 y hy)
      exact hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
