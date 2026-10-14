-- Prove2me | solution 1 for PersistClust.Count.window_ineq_Y
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T20:08:45.090988+00:00
-- url     : https://prove2.me/submissions/8c8354d2-be99-43f2-810e-01751ba5eacc

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

theorem rankFn_eq_structImage {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : t ≤ s) :
    rankFn stage J s t =
      (Set.univ.image (fun C : comps stage J s => (structMap hLaw hst C).val)).encard := by
  unfold rankFn
  congr 1
  ext S
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hprop : {y | J s x y} ∈ (fun x => {y | J s x y}) '' stage s := ⟨x, hx, rfl⟩
    refine ⟨⟨{y | J s x y}, hprop⟩, trivial, ?_⟩
    simp only [structMap_val]
    have hrep : J s (compRep stage J s ⟨{y | J s x y}, hprop⟩) x := by
      have h2 : (fun x => {y | J s x y}) (compRep stage J s ⟨{y | J s x y}, hprop⟩) =
          {y | J s x y} := (compRep_spec stage J s ⟨{y | J s x y}, hprop⟩).2
      have h3 : x ∈ (fun x => {y | J s x y}) (compRep stage J s ⟨{y | J s x y}, hprop⟩) := by
        rw [h2]; exact hLaw.refl hx
      exact h3
    ext y
    constructor
    · intro hy
      exact hLaw.trans (hLaw.symm (hLaw.compat hst hrep)) hy
    · intro hy
      exact hLaw.trans (hLaw.compat hst hrep) hy
  · rintro ⟨C, -, rfl⟩
    exact ⟨compRep stage J s C, (compRep_spec stage J s C).1, (structMap_val hLaw hst C).symm⟩

theorem rankFn_eq_structImage' {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : t ≤ s) :
    rankFn stage J s t =
      (Set.univ.image (fun C : comps stage J s => structMap hLaw hst C)).encard := by
  rw [rankFn_eq_structImage hLaw hst]
  rw [show (Set.univ.image (fun C : comps stage J s => (structMap hLaw hst C).val))
        = Subtype.val '' (Set.univ.image (fun C : comps stage J s => structMap hLaw hst C)) from by
      ext S; constructor
      · rintro ⟨C, -, rfl⟩; exact ⟨structMap hLaw hst C, ⟨C, trivial, rfl⟩, rfl⟩
      · rintro ⟨C, ⟨C', -, rfl⟩, rfl⟩; exact ⟨C', trivial, rfl⟩]
  exact Subtype.val_injective.encard_image
    ((fun C : comps stage J s => structMap hLaw hst C) '' Set.univ)

theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {s t : ℝ} (hst : t ≤ s) (hα : α ≤ t - ε) :
    rankFn stageY JY s ((t - ε) - ε) ≤ rankFn stageX JX (s - ε) (t - ε) := by
  have hβ : α ≤ t := by linarith
  have hαs : α ≤ s := by linarith
  have hX : (t - ε) - ε ≤ s := by linarith
  have hY : t - ε ≤ s - ε := by linarith
  have hgt : (t - ε) - ε ≤ t := by linarith
  rw [rankFn_eq_structImage' hLawY hX]
  have hA : (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hX C))
      = (fun v : comps stageY JY t => structMap hLawY hgt v) ''
        (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C)) := by
    ext R; constructor
    · rintro ⟨C, -, rfl⟩
      refine ⟨structMap hLawY hst C, ⟨C, trivial, rfl⟩, ?_⟩
      show structMap hLawY hgt (structMap hLawY hst C) = structMap hLawY hX C
      rw [structMap_comp hLawY hgt hst C]
    · rintro ⟨v, ⟨C, -, rfl⟩, rfl⟩
      refine ⟨C, trivial, ?_⟩
      show structMap hLawY hX C = structMap hLawY hgt (structMap hLawY hst C)
      exact (structMap_comp hLawY hgt hst C).symm
  have hB : (fun v : comps stageY JY t => structMap hLawY hgt v) ''
        (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C))
      = (fun w : comps stageX JX (t - ε) => φ (t - ε) hα w) ''
        ((fun v : comps stageY JY t => ψ t hβ v) ''
          (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C))) := by
    ext R; constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨ψ t hβ v, ⟨v, hv, rfl⟩, ?_⟩
      show φ (t - ε) hα (ψ t hβ v) = structMap hLawY hgt v
      rw [hSq3 t hβ hα v]
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨v, hv, ?_⟩
      show structMap hLawY hgt v = φ (t - ε) hα (ψ t hβ v)
      rw [hSq3 t hβ hα v]
  have hD : ((fun v : comps stageY JY t => ψ t hβ v) ''
        (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C)))
      ⊆ (fun C' : comps stageX JX (s - ε) => structMap hLawX hY C') '' Set.univ := by
    rintro R ⟨v, ⟨C, -, rfl⟩, rfl⟩
    refine ⟨ψ s hαs C, trivial, ?_⟩
    show structMap hLawX hY (ψ s hαs C) = ψ t hβ (structMap hLawY hst C)
    exact (hSq2 t s hβ hαs hst C).symm
  calc (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hX C)).encard
      = ((fun v : comps stageY JY t => structMap hLawY hgt v) ''
          (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C))).encard := by
        rw [hA]
    _ = ((fun w : comps stageX JX (t - ε) => φ (t - ε) hα w) ''
          ((fun v : comps stageY JY t => ψ t hβ v) ''
            (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C)))).encard := by
        rw [hB]
    _ ≤ ((fun v : comps stageY JY t => ψ t hβ v) ''
          (Set.univ.image (fun C : comps stageY JY s => structMap hLawY hst C))).encard :=
        Set.encard_image_le _ _
    _ ≤ ((fun C' : comps stageX JX (s - ε) => structMap hLawX hY C') '' Set.univ).encard :=
        Set.encard_le_encard hD
    _ = rankFn stageX JX (s - ε) (t - ε) := (rankFn_eq_structImage' hLawX hY).symm
