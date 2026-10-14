-- Prove2me | solution 1 for PersistClust.Count.window_ineq_X
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T20:04:51.257147+00:00
-- url     : https://prove2.me/submissions/47a5ce1e-b44c-46fd-9b40-849546c603f2

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
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {s t : ℝ} (hst : t ≤ s) (hα : α ≤ t - ε) :
    rankFn stageX JX s ((t - ε) - ε) ≤ rankFn stageY JY (s - ε) (t - ε) := by
  have hβ : α ≤ t := by linarith
  have hαs : α ≤ s := by linarith
  have hX : (t - ε) - ε ≤ s := by linarith
  have hY : t - ε ≤ s - ε := by linarith
  have hgt : (t - ε) - ε ≤ t := by linarith
  rw [rankFn_eq_structImage' hLawX hX]
  have hA : (Set.univ.image (fun C : comps stageX JX s => structMap hLawX hX C))
      = (fun v : comps stageX JX t => structMap hLawX hgt v) ''
        (Set.univ.image (fun C : comps stageX JX s => structMap hLawX hst C)) := by
    ext R; constructor
    · rintro ⟨C, -, rfl⟩
      refine ⟨structMap hLawX hst C, ⟨C, trivial, rfl⟩, ?_⟩
      show structMap hLawX hgt (structMap hLawX hst C) = structMap hLawX hX C
      rw [structMap_comp hLawX hgt hst C]
    · rintro ⟨v, ⟨C, -, rfl⟩, rfl⟩
      refine ⟨C, trivial, ?_⟩
      show structMap hLawX hX C = structMap hLawX hgt (structMap hLawX hst C)
      exact (structMap_comp hLawX hgt hst C).symm
  have hB : (fun v : comps stageX JX t => structMap hLawX hgt v) ''
        (Set.univ.image (fun C : comps stageX JX s => structMap hLawX hst C))
      = (fun w : comps stageY JY (t - ε) => ψ (t - ε) hα w) ''
        ((fun v : comps stageX JX t => φ t hβ v) ''
          (Set.univ.image (fun C : comps stageX JX s => structMap hLawX hst C))) := by
    ext R; constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨φ t hβ v, ⟨v, hv, rfl⟩, ?_⟩
      show ψ (t - ε) hα (φ t hβ v) = structMap hLawX hgt v
      rw [hSq4 t hβ hα v]
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨v, hv, ?_⟩
      show structMap hLawX hgt v = ψ (t - ε) hα (φ t hβ v)
      rw [hSq4 t hβ hα v]
  have hD : ((fun v : comps stageX JX t => φ t hβ v) ''
        (Set.univ.image (fun C : comps stageX JX s => structMap hLawX hst C)))
      ⊆ (fun C' : comps stageY JY (s - ε) => structMap hLawY hY C') '' Set.univ := by
    rintro R ⟨v, ⟨C, -, rfl⟩, rfl⟩
    refine ⟨φ s hαs C, trivial, ?_⟩
    show structMap hLawY hY (φ s hαs C) = φ t hβ (structMap hLawX hst C)
    exact (hSq1 t s hβ hαs hst C).symm
  calc (Set.univ.image (fun C : comps stageX JX s => structMap hLawX hX C)).encard
      = ((fun v : comps stageX JX t => structMap hLawX hgt v) ''
          (Set.univ.image (fun C : comps stageX JX s => structMap hLawX hst C))).encard := by
        rw [hA]
    _ = ((fun w : comps stageY JY (t - ε) => ψ (t - ε) hα w) ''
          ((fun v : comps stageX JX t => φ t hβ v) ''
            (Set.univ.image (fun C : comps stageX JX s => structMap hLawX hst C)))).encard := by
        rw [hB]
    _ ≤ ((fun v : comps stageX JX t => φ t hβ v) ''
          (Set.univ.image (fun C : comps stageX JX s => structMap hLawX hst C))).encard :=
        Set.encard_image_le _ _
    _ ≤ ((fun C' : comps stageY JY (s - ε) => structMap hLawY hY C') '' Set.univ).encard :=
        Set.encard_le_encard hD
    _ = rankFn stageY JY (s - ε) (t - ε) := (rankFn_eq_structImage' hLawY hY).symm
