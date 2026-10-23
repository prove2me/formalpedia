-- Prove2me | solution 1 for YieldPostpone.Preference.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:21:10.242575+00:00
-- url     : https://prove2.me/submissions/581eec37-102d-4221-b564-30e32b99ca35

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting
import Definitions.Def_YieldPostpone_Interplay_Setting
import Theorems.Thm_YieldPostpone_Interplay_lemma_2

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

theorem solution (P : Params) (hP : P.Valid) :
    cOR P < P.a * μ P / P.b ∧
    (∀ c : ℝ, 0 < c → c < P.a * μ P / P.b → ∃ σ : Profile, IsSPE P c .OR σ) ∧
    (∀ (c : ℝ) (σ : Profile), 0 < c → c < cOR P → IsSPE P c .OR σ →
      piR P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (16 * P.b * P.α ^ 2 * (1 - P.θ))
          + P.a ^ 2 * P.θ / (4 * P.b) ∧
      piS P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2 * (1 - P.θ)) ∧
      CS P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (32 * P.b * P.α ^ 2 * (1 - P.θ))
          + P.a ^ 2 * P.θ / (8 * P.b)) ∧
    (∀ (c : ℝ) (σ : Profile), max 0 (cOR P) < c → c < P.a * μ P / P.b → IsSPE P c .OR σ →
      piR P c .OR σ = (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      piS P c .OR σ = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      CS P c .OR σ = (P.a * μ P - P.b * c) ^ 2 / (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ))) := by
  obtain ⟨L0, L⟩ := Interplay.lemma_2 (toI P) hP
  refine ⟨L0, fun c hc hcu => ?_, fun c σ hc hcX hσ => ?_, fun c σ hcX hcu hσ => ?_⟩
  · obtain ⟨σ, hσ⟩ := (L c hc hcu).1
    exact ⟨_, spe_OR_of P c σ hσ⟩
  · have hcu : c < P.a * μ P / P.b := lt_trans hcX L0
    exact ((L c hc hcu).2 (pfI σ) (spe_OR_to P c σ hσ)).1 (lt_of_lt_of_le hcX (le_max_right _ _))
  · have hc : 0 < c := lt_of_le_of_lt (le_max_left _ _) hcX
    exact ((L c hc hcu).2 (pfI σ) (spe_OR_to P c σ hσ)).2 hcX
