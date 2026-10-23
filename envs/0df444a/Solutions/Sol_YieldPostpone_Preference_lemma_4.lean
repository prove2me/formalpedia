-- Prove2me | solution 1 for YieldPostpone.Preference.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:20:24.346988+00:00
-- url     : https://prove2.me/submissions/a643c6f7-07e6-4918-a458-49c963218258

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting
import Definitions.Def_YieldPostpone_Interplay_Setting
import Theorems.Thm_YieldPostpone_Interplay_lemma_4
import Theorems.Thm_YieldPostpone_Interplay_threshold_order

namespace YieldPostpone.PrefBridge

open YieldPostpone

/-- The Interplay copy of the same parameter vector. -/
def toI (P : Preference.Params) : Interplay.Params := ⟨P.a, P.b, P.α, P.θ⟩

/-- Profiles of the two settings have identical fields. -/
def pfI (σ : Preference.Profile) : Interplay.Profile := ⟨σ.w, σ.Q, σ.q, σ.p, σ.pr⟩

def pfR (σ : Interplay.Profile) : Preference.Profile := ⟨σ.w, σ.Q, σ.q, σ.p, σ.pr⟩

lemma valid_iff (P : Preference.Params) : P.Valid ↔ (toI P).Valid := Iff.rfl

lemma mu_eq (P : Preference.Params) : Preference.μ P = Interplay.μ (toI P) := rfl

lemma spe_DA (P : Preference.Params) (c : ℝ) (σ : Preference.Profile) :
    Preference.IsSPE P c .DA σ ↔ Interplay.IsSPE (toI P) c .DA (pfI σ) := by
  constructor
  · rintro ⟨-, h2, h3, h4, h5, h6⟩
    exact ⟨fun w q hw hq => ⟨fun _ => h2 rfl w q hw hq, fun h => absurd h (by decide)⟩,
      h3, h4, h5, h6⟩
  · rintro ⟨h1, h3, h4, h5, h6⟩
    exact ⟨fun h => absurd h (by decide), fun _ w q hw hq => (h1 w q hw hq).1 rfl, h3, h4, h5, h6⟩

lemma spe_DR (P : Preference.Params) (c : ℝ) (σ : Preference.Profile) :
    Preference.IsSPE P c .DR σ ↔ Interplay.IsSPE (toI P) c .DR (pfI σ) := by
  constructor
  · rintro ⟨-, h2, h3, h4, h5, h6⟩
    exact ⟨fun w q hw hq => ⟨fun _ => h2 rfl w q hw hq, fun h => absurd h (by decide)⟩,
      h3, h4, h5, h6⟩
  · rintro ⟨h1, h3, h4, h5, h6⟩
    exact ⟨fun h => absurd h (by decide), fun _ w q hw hq => (h1 w q hw hq).1 rfl, h3, h4, h5, h6⟩

lemma spe_OR_to (P : Preference.Params) (c : ℝ) (σ : Preference.Profile) :
    Preference.IsSPE P c .OR σ → Interplay.IsSPE (toI P) c .OR (pfI σ) := by
  rintro ⟨h1, -, h3, h4, h5, h6⟩
  exact ⟨fun w q _ _ => ⟨fun h => absurd h (by decide), fun _ => h1 rfl w q⟩, h3, h4, h5, h6⟩

/-- Pay-by-order existence transfer: reset production to `Q = q` off the relevant subgames. -/
lemma spe_OR_of (P : Preference.Params) (c : ℝ) (σ : Interplay.Profile)
    (hσ : Interplay.IsSPE (toI P) c .OR σ) :
    Preference.IsSPE P c .OR ⟨σ.w, fun _ q => q, σ.q, σ.p, σ.pr⟩ := by
  obtain ⟨h1, h3, h4, h5, h6⟩ := hσ
  have hQ : ∀ w q, Interplay.wAdm (toI P) c .OR w → 0 ≤ q → σ.Q w q = q :=
    fun w q hw hq => (h1 w q hw hq).2 rfl
  have hRP : ∀ w q' p', Interplay.wAdm (toI P) c .OR w → 0 ≤ q' →
      Preference.retailerProfit P .OR ⟨σ.w, fun _ q => q, σ.q, σ.p, σ.pr⟩ w q' p' =
        Interplay.retailerProfit (toI P) .OR σ w q' p' := by
    intro w q' p' hw hq'
    simp only [Preference.retailerProfit, Interplay.retailerProfit, hQ w q' hw hq']
    rfl
  have hSV : ∀ w, Interplay.wAdm (toI P) c .OR w →
      Preference.supplierValue P c .OR ⟨σ.w, fun _ q => q, σ.q, σ.p, σ.pr⟩ w =
        Interplay.supplierValue (toI P) c .OR σ w := by
    intro w hw
    simp only [Preference.supplierValue, Interplay.supplierValue,
      hQ w (σ.q w) hw (h4 w hw).1]
    rfl
  refine ⟨fun _ _ _ => rfl, fun h => absurd h (by decide), h3, fun w hw => ?_, h5, ?_⟩
  · obtain ⟨a1, a2, a3⟩ := h4 w hw
    refine ⟨a1, a2, fun q' p' hq' hp' => ?_⟩
    rw [hRP w q' p' hw hq', hRP w (σ.q w) (σ.p w) hw a1]
    exact a3 q' p' hq' hp'
  · intro w' hw'
    show Preference.supplierValue P c .OR ⟨σ.w, fun _ q => q, σ.q, σ.p, σ.pr⟩ w' ≤
      Preference.supplierValue P c .OR ⟨σ.w, fun _ q => q, σ.q, σ.p, σ.pr⟩ σ.w
    rw [hSV w' hw', hSV σ.w h5]
    exact h6 w' hw'

end YieldPostpone.PrefBridge

open YieldPostpone YieldPostpone.Preference YieldPostpone.PrefBridge

lemma cDR1_pos' (P : Params) (hP : P.Valid) : 0 < cDR1 P := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; nlinarith
  have hμ1 : μ P < 1 := by rw [hμ]; nlinarith
  set X := P.α * μ P * (1 - P.α) * (1 - P.θ) with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ 1 - P.α := by linarith
    have : 0 ≤ 1 - P.θ := by linarith
    positivity
  have hX1 : X < 1 / 4 := by
    have h1 : P.α * (1 - P.α) ≤ 1 / 4 := by nlinarith [sq_nonneg (P.α - 1 / 2)]
    have h2 : μ P * (1 - P.θ) < 1 := by nlinarith
    have h3 : 0 ≤ P.α * (1 - P.α) := by nlinarith
    have h4 : 0 ≤ μ P * (1 - P.θ) := by nlinarith
    calc X = (P.α * (1 - P.α)) * (μ P * (1 - P.θ)) := by rw [hX]; ring
      _ < 1 / 4 := by nlinarith
  have hsX : Real.sqrt X < 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hX0 hX1
  unfold cDR1
  apply div_pos
  · apply mul_pos (by have : 0 < 1 - P.θ := by linarith
                      positivity)
    nlinarith [sq_nonneg (μ P)]
  · apply mul_pos hb
    have : 0 < 1 - P.θ := by linarith
    positivity

lemma cDR2_pos' (P : Params) (hP : P.Valid) : 0 < cDR2 P := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; nlinarith
  have : 0 < 1 - P.θ := by linarith
  unfold cDR2; positivity

lemma cDR2_lt' (P : Params) (hP : P.Valid) : cDR2 P < P.a * μ P / P.b := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; nlinarith
  unfold cDR2
  rw [div_lt_div_iff₀ (by positivity) hb]
  have h1 : P.α * (1 - P.θ) < μ P + P.θ := by rw [hμ]; linarith
  have h2 : 0 < P.a * μ P * P.b := by positivity
  nlinarith [mul_lt_mul_of_pos_left h1 h2]

theorem solution (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    (∀ c : ℝ, 0 < c → c < P.a * μ P / P.b → ∃ σ : Profile, IsSPE P c .DR σ) ∧
    (∀ (c : ℝ) (σ : Profile), 0 < c → c < cDR1 P → IsSPE P c .DR σ →
      piR P c .DR σ = (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) ∧
      piS P c .DR σ = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) ∧
      CS P c .DR σ = (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2)) ∧
    (∀ (c : ℝ) (σ : Profile), cDR1 P < c → c < cDR2 P → IsSPE P c .DR σ →
      piR P c .DR σ = μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2
          / (4 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      piS P c .DR σ = μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c)
          / (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      CS P c .DR σ = μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2
          / (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ))) ∧
    (∀ (c : ℝ) (σ : Profile), cDR2 P < c → c < P.a * μ P / P.b → IsSPE P c .DR σ →
      piR P c .DR σ = (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      piS P c .DR σ = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      CS P c .DR σ = (P.a * μ P - P.b * c) ^ 2 / (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ))) := by
  have L := Interplay.lemma_4 (toI P) hP hα
  have T : cDR1 P < cDR2 P := (Interplay.threshold_order (toI P) hP hα).2.1
  have h1 := cDR1_pos' P hP
  have h2 := cDR2_lt' P hP
  refine ⟨fun c hc hcu => ?_, fun c σ hc hcX hσ => ?_, fun c σ hcX hcY hσ => ?_,
    fun c σ hcX hcu hσ => ?_⟩
  · obtain ⟨σ, hσ⟩ := (L c hc hcu).1
    exact ⟨pfR σ, (spe_DR P c (pfR σ)).2 hσ⟩
  · have hcu : c < P.a * μ P / P.b := by linarith
    exact ((L c hc hcu).2 (pfI σ) ((spe_DR P c σ).1 hσ)).1 hcX
  · have hc : 0 < c := by linarith
    have hcu : c < P.a * μ P / P.b := by linarith
    exact ((L c hc hcu).2 (pfI σ) ((spe_DR P c σ).1 hσ)).2.1 hcX hcY
  · have hc : 0 < c := by linarith
    exact ((L c hc hcu).2 (pfI σ) ((spe_DR P c σ).1 hσ)).2.2 hcX
