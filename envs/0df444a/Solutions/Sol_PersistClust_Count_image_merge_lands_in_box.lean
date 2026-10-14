-- Prove2me | solution 1 for PersistClust.Count.image_merge_lands_in_box
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-13T17:23:33.1509+00:00
-- url     : https://prove2.me/submissions/eef8dd7f-bf26-4802-8b50-1e5904336dbc

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

theorem structMap_comp {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u)
    (C : comps stage J u) :
    structMap hLaw hst (structMap hLaw htu C) = structMap hLaw (le_trans hst htu) C := by
  have hjoin : J s (compRep stage J t (structMap hLaw htu C)) (compRep stage J u C) := by
    have h1 : (fun x => {y | J t x y}) (compRep stage J t (structMap hLaw htu C)) =
        {y | J t (compRep stage J u C) y} :=
      (compRep_spec stage J t (structMap hLaw htu C)).2.trans (structMap_val hLaw htu C)
    have h2 : J t (compRep stage J t (structMap hLaw htu C)) (compRep stage J u C) := by
      have h3 : compRep stage J u C ∈ {y | J t (compRep stage J u C) y} :=
        hLaw.refl (hLaw.antitone htu (compRep_spec stage J u C).1)
      rw [← h1] at h3
      exact h3
    exact hLaw.compat hst h2
  have hval : (structMap hLaw hst (structMap hLaw htu C)).val =
      (structMap hLaw (le_trans hst htu) C).val := by
    ext y
    exact ⟨fun h => hLaw.trans (hLaw.symm hjoin) h, fun h => hLaw.trans hjoin h⟩
  exact Subtype.ext hval

/-- Sync-high separation (contrapositive of the interleaving square (iv')):
X-cells whose 2eps-descents (to level u - eps - eps) are DISTINCT have
distinct images at level u - eps: if the images coincided, square (iv')
applied to each cell would force the two 2eps-descents to coincide.
With an X-merge at level delta this bounds the image merge level by
delta + eps. -/
theorem t5_syncHigh {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {u : ℝ} (hαu : α ≤ u) (hβε : α ≤ u - ε) (hle : u - ε - ε ≤ u)
    (C₁ C₂ : comps stageX JX u)
    (hne : structMap hLawX hle C₁ ≠ structMap hLawX hle C₂) :
    φ u hαu C₁ ≠ φ u hαu C₂ := by
  intro heq
  apply hne
  have h₁ := hSq4 u hαu hβε C₁
  have h₂ := hSq4 u hαu hβε C₂
  calc structMap hLawX hle C₁
      = ψ (u - ε) hβε (φ u hαu C₁) := h₁.symm
    _ = ψ (u - ε) hβε (φ u hαu C₂) := by rw [heq]
    _ = structMap hLawX hle C₂ := h₂

/-- Image coalescence lands in the ε-box (rankKill SLIVER-II equal-arm, R2 stage 1):
two X-cells A₁ A₂ at level β descending to DISTINCT d-cells M₁ ≠ M₂ (d ≤ β),
interleaved into Y by φ (square (i')) with a ψ-pullback (square (iv')), whose
β-images coincide after descending to level d−ε, have their 2→1 image coalescence
level pinned INSIDE the box [d−ε, d+ε]: there is m' with d−ε ≤ m' ≤ d+ε such that
the descended image pair coincides at every Y-level below m' (on the window),
differs at every level above m', and coincides at the d−ε seed. Mechanism: equal
ζ-descents (any ζ ∈ [d, β]) would chain via structMap_comp to equal d-descents,
i.e. M₁ = M₂ — down-persistence, NO critical-freeness (hAne); the Q-set of
coincidence levels is seeded at d and bounded by d+2ε (hAne at u−2ε + t5_syncHigh
+ square (i')); m' := sSup Q − ε, below via descent monotonicity + csSup_le,
above via le_csSup. -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {d β : ℝ} (hαd : α ≤ d) (hαβ : α ≤ β) (hdβ : d ≤ β)
    (A₁ A₂ : comps stageX JX β) (M₁ M₂ : comps stageX JX d)
    (hA₁d : structMap hLawX hdβ A₁ = M₁)
    (hA₂d : structMap hLawX hdβ A₂ = M₂)
    (hMne : M₁ ≠ M₂)
    (hseed : structMap hLawY (show d - ε ≤ β - ε by linarith) (φ β hαβ A₁) =
      structMap hLawY (show d - ε ≤ β - ε by linarith) (φ β hαβ A₂)) :
    ∃ (m' : ℝ), d - ε ≤ m' ∧ m' ≤ d + ε ∧
        (∀ (u : ℝ) (huε : u - ε ≤ β - ε) (hud : d ≤ u), u - ε < m' →
           structMap hLawY huε (φ β hαβ A₁) =
           structMap hLawY huε (φ β hαβ A₂)) ∧
        (∀ (u : ℝ) (huε : u - ε ≤ β - ε) (hud : d ≤ u), m' < u - ε →
           structMap hLawY huε (φ β hαβ A₁) ≠
           structMap hLawY huε (φ β hαβ A₂)) ∧
        structMap hLawY (show d - ε ≤ β - ε by linarith) (φ β hαβ A₁) =
          structMap hLawY (show d - ε ≤ β - ε by linarith)
            (φ β hαβ A₂) := by
  have hAne : ∀ (ζ : ℝ) (_ : d ≤ ζ) (hζβ : ζ ≤ β),
      structMap hLawX hζβ A₁ ≠ structMap hLawX hζβ A₂ := by
    intro ζ hζd hζβ heq
    have hc : structMap hLawX (show d ≤ β by linarith) A₁ =
        structMap hLawX (show d ≤ β by linarith) A₂ := by
      rw [← structMap_comp hLawX (show d ≤ ζ by linarith) hζβ A₁,
          ← structMap_comp hLawX (show d ≤ ζ by linarith) hζβ A₂]
      exact congrArg (structMap hLawX (show d ≤ ζ by linarith)) heq
    rw [hA₁d, hA₂d] at hc
    exact hMne hc
  set Q : Set ℝ := {u : ℝ | ∃ (hu : u - ε ≤ β - ε), d ≤ u ∧
      structMap hLawY hu (φ β hαβ A₁) =
      structMap hLawY hu (φ β hαβ A₂)} with hQdef
  have hQd : d ∈ Q := ⟨show d - ε ≤ β - ε by linarith, le_rfl,
    hseed⟩
  have hQne : Q.Nonempty := ⟨d, hQd⟩
  have hQbdd : BddAbove Q := ⟨β, fun u hu => by
    obtain ⟨huβ, -, -⟩ := hu
    linarith⟩
  have hQle : ∀ u ∈ Q, u ≤ d + 2 * ε := by
    intro u hu
    obtain ⟨huβ, hudo, hueq⟩ := hu
    by_contra hu2ε
    push_neg at hu2ε
    have hne : structMap hLawX (show u - ε - ε ≤ u by linarith)
        (structMap hLawX (show u ≤ β by linarith) A₁) ≠
      structMap hLawX (show u - ε - ε ≤ u by linarith)
        (structMap hLawX (show u ≤ β by linarith) A₂) := by
      have hc1 : structMap hLawX (show u - ε - ε ≤ u by linarith)
          (structMap hLawX (show u ≤ β by linarith) A₁) =
          structMap hLawX (show u - ε - ε ≤ β by linarith) A₁ :=
        structMap_comp hLawX (show u - ε - ε ≤ u by linarith)
          (show u ≤ β by linarith) A₁
      have hc2 : structMap hLawX (show u - ε - ε ≤ u by linarith)
          (structMap hLawX (show u ≤ β by linarith) A₂) =
          structMap hLawX (show u - ε - ε ≤ β by linarith) A₂ :=
        structMap_comp hLawX (show u - ε - ε ≤ u by linarith)
          (show u ≤ β by linarith) A₂
      rw [hc1, hc2]
      exact hAne (u - ε - ε) (by linarith) (by linarith)
    have hphi := t5_syncHigh hLawX hLawY hε φ ψ hSq4
      (show α ≤ u by linarith) (show α ≤ u - ε by linarith)
      (show u - ε - ε ≤ u by linarith)
      (structMap hLawX (show u ≤ β by linarith) A₁)
      (structMap hLawX (show u ≤ β by linarith) A₂) hne
    have hs1 := hSq1 u β (show α ≤ u by linarith) hαβ
      (show u ≤ β by linarith) A₁
    have hs2 := hSq1 u β (show α ≤ u by linarith) hαβ
      (show u ≤ β by linarith) A₂
    rw [hs1, hs2] at hphi
    exact hphi hueq
  have hsup : sSup Q ≤ d + 2 * ε := csSup_le hQne hQle
  have hinf : d ≤ sSup Q := le_csSup hQbdd hQd
  have hdown : ∀ u₁ u₂ : ℝ, (hu₁β : u₁ - ε ≤ β - ε) →
      (hu₁d : d ≤ u₁) → (hu₂d : d ≤ u₂) → (hu₁₂ : u₁ ≤ u₂) →
      (hu₂β : u₂ - ε ≤ β - ε) →
      structMap hLawY hu₂β (φ β hαβ A₁) =
      structMap hLawY hu₂β (φ β hαβ A₂) →
      structMap hLawY hu₁β (φ β hαβ A₁) =
      structMap hLawY hu₁β (φ β hαβ A₂) := by
    intro u₁ u₂ hu₁β hu₁d hu₂d hu₁₂ hu₂β heq
    have hcongr :=
      congrArg (structMap hLawY
        (show u₁ - ε ≤ u₂ - ε by linarith)) heq
    rw [structMap_comp hLawY (show u₁ - ε ≤ u₂ - ε by linarith)
        hu₂β (φ β hαβ A₁),
      structMap_comp hLawY (show u₁ - ε ≤ u₂ - ε by linarith)
        hu₂β (φ β hαβ A₂)] at hcongr
    exact hcongr
  refine ⟨sSup Q - ε, by linarith, by linarith, ?_, ?_, hseed⟩
  · intro u huε hud hum'
    by_contra hne
    have hQle' : ∀ w ∈ Q, w ≤ u := by
      intro w hw
      obtain ⟨hwβ, hwdo, hweq⟩ := hw
      by_contra hwu
      push_neg at hwu
      exact hne (hdown u w huε hud hwdo
        (le_of_lt hwu) hwβ hweq)
    have hcs := csSup_le hQne hQle'
    linarith
  · intro u huε hud hum'
    intro heq
    have hmem : u ∈ Q := ⟨huε, hud, heq⟩
    have hle := le_csSup hQbdd hmem
    linarith
