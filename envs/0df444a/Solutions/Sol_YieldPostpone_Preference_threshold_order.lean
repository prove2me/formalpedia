-- Prove2me | solution 1 for YieldPostpone.Preference.threshold_order
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:21:10.965276+00:00
-- url     : https://prove2.me/submissions/8e503cd8-14ca-460a-a2c1-586033aea1c1

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting
import Definitions.Def_YieldPostpone_Interplay_Setting
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

theorem solution (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    cOR P < 0 ∧ cDR1 P < cDR2 P ∧ cDR2 P < cDA P :=
  Interplay.threshold_order (toI P) hP hα
