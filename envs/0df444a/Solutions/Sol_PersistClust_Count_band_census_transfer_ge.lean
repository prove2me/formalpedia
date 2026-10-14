-- Prove2me | solution 1 for PersistClust.Count.band_census_transfer_ge
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-13T08:15:16.384908+00:00
-- url     : https://prove2.me/submissions/e9ac299e-6dcb-4bb1-a3bd-ef17a3f51747

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


theorem t3_structMap_id {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) :
    structMap hLaw le_rfl C = C :=
  Subtype.ext (compRep_spec stage J t C).2


theorem t3_crit_inj {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w w' : ℝ} (hww : w ≤ w')
    (hfree : ∀ τ ∈ critSet hTame, τ < w ∨ w' < τ) {C₁ C₂ : comps stage J w'}
    (h : structMap hLaw hww C₁ = structMap hLaw hww C₂) : C₁ = C₂ := by
  have hspec1 := compRep_spec stage J w' C₁
  have hspec2 := compRep_spec stage J w' C₂
  have hv : (structMap hLaw hww C₁).val = (structMap hLaw hww C₂).val :=
    congrArg Subtype.val h
  rw [structMap_val, structMap_val] at hv
  have hJw : J w (compRep stage J w' C₁) (compRep stage J w' C₂) := by
    have hmem : compRep stage J w' C₂ ∈ {z | J w (compRep stage J w' C₁) z} := by
      rw [hv]
      exact hLaw.refl (hLaw.antitone hww hspec2.1)
    exact hmem
  have hclause := (critSet_spec hTame w w' hww hfree).2
  have hJw' : J w' (compRep stage J w' C₁) (compRep stage J w' C₂) :=
    hclause (compRep stage J w' C₁) hspec1.1 (compRep stage J w' C₂) hspec2.1 hJw
  refine Subtype.ext ?_
  rw [← hspec1.2, ← hspec2.2]
  ext z
  exact ⟨fun hz => hLaw.trans (hLaw.symm hJw') hz, fun hz => hLaw.trans hJw' hz⟩


theorem t3_bSupThread {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w w' : ℝ} (hww : w ≤ w')
    (hfree : ∀ τ ∈ critSet hTame, τ < w ∨ w' < τ)
    {C'' : comps stage J w'} {C : comps stage J w}
    (h : structMap hLaw hww C'' = C) :
    birthSup hLaw w C = birthSup hLaw w' C'' := by
  classical
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  have hneC : (AncSet hLaw w C).Nonempty := ⟨w, le_rfl, C, t3_structMap_id hLaw w C⟩
  have hneC' : (AncSet hLaw w' C'').Nonempty := ⟨w', le_rfl, C'', t3_structMap_id hLaw w' C''⟩
  have hBddC : BddAbove (AncSet hLaw w C) := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  have hBddC' : BddAbove (AncSet hLaw w' C'') := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  refine le_antisymm (csSup_le hneC (fun u hu => ?_)) (csSup_le hneC' (fun v hv => ?_))
  · -- u ∈ AncSet(w,C) ⊢ u ≤ birthSup(w',C'')
    obtain ⟨huw, C₂, hC₂⟩ := hu
    by_cases huw' : u ≤ w'
    · have h2 : w' ≤ birthSup hLaw w' C'' :=
        (rfl : birthSup hLaw w' C'' = sSup (AncSet hLaw w' C'')).symm ▸
          (le_csSup hBddC' ⟨le_rfl, C'', t3_structMap_id hLaw w' C''⟩)
      linarith
    · push_neg at huw'
      have hC'₃ : structMap hLaw hww (structMap hLaw (le_of_lt huw') C₂) = C := by
        rw [structMap_comp hLaw hww (le_of_lt huw') C₂]
        exact hC₂
      have hpre : structMap hLaw hww (structMap hLaw (le_of_lt huw') C₂) =
          structMap hLaw hww C'' := hC'₃.trans h.symm
      have hC₃eq : structMap hLaw (le_of_lt huw') C₂ = C'' :=
        t3_crit_inj hLaw hTame hww hfree hpre
      have hmem : u ∈ AncSet hLaw w' C'' := ⟨le_of_lt huw', C₂, hC₃eq⟩
      exact (rfl : birthSup hLaw w' C'' = sSup (AncSet hLaw w' C'')).symm ▸ (le_csSup hBddC' hmem)
  · -- v ∈ AncSet(w',C'') ⊢ v ≤ birthSup(w,C)
    obtain ⟨hw'v, C_v, hC_v⟩ := hv
    have hvC : v ∈ AncSet hLaw w C := by
      refine ⟨le_trans hww hw'v, C_v, ?_⟩
      rw [← structMap_comp hLaw hww hw'v C_v, hC_v]
      exact h
    exact (rfl : birthSup hLaw w C = sSup (AncSet hLaw w C)).symm ▸ (le_csSup hBddC hvC)


theorem rungB_level_le_bSup {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {t : ℝ} (E : comps stage J t) :
    t ≤ birthSup hLaw t E := by
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  have hBdd : BddAbove (AncSet hLaw t E) := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  exact (rfl : birthSup hLaw t E = sSup (AncSet hLaw t E)).symm ▸
    (le_csSup hBdd ⟨le_rfl, E, t3_structMap_id hLaw t E⟩)


theorem rungB_bSup_descend_ge {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {t t' : ℝ} (hle : t' ≤ t) (E : comps stage J t) :
    birthSup hLaw t E ≤ birthSup hLaw t' (structMap hLaw hle E) := by
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  have hBddT : BddAbove (AncSet hLaw t' (structMap hLaw hle E)) := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle'
    push_neg at hle'
    exact hstage.ne_empty (hs₀ u hle'.le)
  have hne : (AncSet hLaw t E).Nonempty := ⟨t, le_rfl, E, t3_structMap_id hLaw t E⟩
  refine csSup_le hne ?_
  intro u hu
  obtain ⟨hw', E', hE'⟩ := hu
  exact (rfl : birthSup hLaw t' (structMap hLaw hle E)
      = sSup (AncSet hLaw t' (structMap hLaw hle E))).symm ▸
    (le_csSup hBddT ⟨le_trans hle hw', E', by rw [← hE', structMap_comp hLaw hle hw' E']⟩)


theorem t5_aliveUp {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {s₀ b : ℝ} {C₀ : comps stage J s₀}
    (hb : birthSup hLaw s₀ C₀ = b) {β : ℝ} (hs₀β : s₀ ≤ β) (hβb : β < b) :
    ∃ A : comps stage J β, birthSup hLaw β A = b ∧ structMap hLaw hs₀β A = C₀ := by
  obtain ⟨s₁, hs₁⟩ := hTame.2.2
  have hBdd : BddAbove (AncSet hLaw s₀ C₀) := by
    refine ⟨s₁, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₁ u hle.le)
  have hne : (AncSet hLaw s₀ C₀).Nonempty := ⟨s₀, le_rfl, C₀, t3_structMap_id hLaw s₀ C₀⟩
  have happrox : ∀ t : ℝ, t < b → ∃ u ∈ AncSet hLaw s₀ C₀, t < u := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have hle : sSup (AncSet hLaw s₀ C₀) ≤ t := csSup_le hne (fun u hu => hcon u hu)
    have hbr : sSup (AncSet hLaw s₀ C₀) = birthSup hLaw s₀ C₀ := rfl
    rw [hbr] at hle
    linarith
  obtain ⟨u₀, hu₀mem, hu₀lt⟩ := happrox β hβb
  obtain ⟨hu₀, A_u₀, hA_u₀⟩ := hu₀mem
  have hβu₀ : β ≤ u₀ := by linarith
  have hex : ∃ A : comps stage J β, structMap hLaw hs₀β A = C₀ :=
    ⟨structMap hLaw hβu₀ A_u₀, by rw [structMap_comp hLaw hs₀β hβu₀ A_u₀]; exact hA_u₀⟩
  haveI hcompsFin : Finite (comps stage J β) := (hTame.1 β).to_subtype
  obtain ⟨A_wit, hA_wit⟩ := hex
  haveI hPne : Nonempty {A : comps stage J β // structMap hLaw hs₀β A = C₀} :=
    ⟨⟨A_wit, hA_wit⟩⟩
  obtain ⟨Amax, hAmax⟩ := Finite.exists_max
    (fun A : {A : comps stage J β // structMap hLaw hs₀β A = C₀} => birthSup hLaw β A.val)
  refine ⟨Amax.val, ?_, Amax.property⟩
  have hle : birthSup hLaw β Amax.val ≤ b := by
    have h1 := rungB_bSup_descend_ge hLaw hTame hs₀β Amax.val
    rw [Amax.property] at h1
    exact h1.trans_eq hb
  have hge : b ≤ birthSup hLaw β Amax.val := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨u, humem, hut⟩ := happrox (birthSup hLaw β Amax.val) (by linarith)
    obtain ⟨huu, A_u, hA_u⟩ := humem
    have hmβ : β ≤ birthSup hLaw β Amax.val :=
      rungB_level_le_bSup hLaw hTame Amax.val
    have hβu : β ≤ u := by linarith
    have h1 : birthSup hLaw β (structMap hLaw hβu A_u) ≤ birthSup hLaw β Amax.val :=
      hAmax ⟨structMap hLaw hβu A_u, by rw [structMap_comp hLaw hs₀β hβu A_u]; exact hA_u⟩
    have h2 : birthSup hLaw u A_u ≤ birthSup hLaw β (structMap hLaw hβu A_u) :=
      rungB_bSup_descend_ge hLaw hTame hβu A_u
    have h3 : u ≤ birthSup hLaw u A_u :=
      rungB_level_le_bSup hLaw hTame A_u
    linarith
  exact le_antisymm hle hge


theorem t5_imageBirthStrongLower {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {β : ℝ} (hβ : α ≤ β) (C : comps stageX JX β) :
    birthSup hLawX β C - ε ≤ birthSup hLawY (β - ε) (φ β hβ C) := by
  obtain ⟨s₀, hs₀⟩ := hTameY.2.2
  have hBddY : BddAbove (AncSet hLawY (β - ε) (φ β hβ C)) := by
    refine ⟨s₀, fun w hw => ?_⟩
    obtain ⟨-, C₂, -⟩ := hw
    have hstage : (stageY w).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ w hle.le)
  have hneX : (AncSet hLawX β C).Nonempty := ⟨β, le_rfl, C, t3_structMap_id hLawX β C⟩
  have hmain : birthSup hLawX β C ≤ birthSup hLawY (β - ε) (φ β hβ C) + ε := by
    refine csSup_le hneX ?_
    intro u hu
    obtain ⟨huβ, C_u, hCu⟩ := hu
    have hαu : α ≤ u := le_trans hβ huβ
    have hpull : structMap hLawY (show β - ε ≤ u - ε by linarith) (φ u hαu C_u)
        = φ β hβ C := by
      have h1 := hSq1 β u hβ hαu huβ C_u
      rw [← hCu]
      exact h1.symm
    have hmemY : (u - ε) ∈ AncSet hLawY (β - ε) (φ β hβ C) :=
      ⟨show β - ε ≤ u - ε by linarith, φ u hαu C_u, hpull⟩
    have hle : u - ε ≤ birthSup hLawY (β - ε) (φ β hβ C) :=
      (rfl : birthSup hLawY (β - ε) (φ β hβ C)
        = sSup (AncSet hLawY (β - ε) (φ β hβ C))).symm ▸
        (le_csSup hBddY hmemY)
    linarith
  linarith


theorem t5_imageBirthUpper {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {β b : ℝ} (hβ : α ≤ β) (hβε : α ≤ β - ε)
    (C : comps stageX JX β)
    (hDesc : birthSup hLawX ((β - ε) - ε)
        (structMap hLawX (show (β - ε) - ε ≤ β by linarith) C) = b) :
    birthSup hLawY (β - ε) (φ β hβ C) ≤ b + ε := by
  have hne : (AncSet hLawY (β - ε) (φ β hβ C)).Nonempty :=
    ⟨β - ε, le_rfl, φ β hβ C, t3_structMap_id hLawY (β - ε) (φ β hβ C)⟩
  refine csSup_le hne ?_
  intro u hu
  obtain ⟨huu, D₁, hD₁⟩ := hu
  have hαu : α ≤ u := le_trans hβε huu
  have hii := hSq2 (β - ε) u hβε hαu huu D₁
  rw [hD₁] at hii
  have hiv := hSq4 β hβ hβε C
  have hEq : structMap hLawX (show (β - ε) - ε ≤ u - ε by linarith) (ψ u hαu D₁)
      = structMap hLawX (show (β - ε) - ε ≤ β by linarith) C :=
    hii.symm.trans hiv
  have h1 : u - ε ≤ birthSup hLawX (u - ε) (ψ u hαu D₁) :=
    rungB_level_le_bSup hLawX hTameX (ψ u hαu D₁)
  have h2 : birthSup hLawX (u - ε) (ψ u hαu D₁)
      ≤ birthSup hLawX ((β - ε) - ε)
          (structMap hLawX (show (β - ε) - ε ≤ u - ε by linarith) (ψ u hαu D₁)) :=
    rungB_bSup_descend_ge hLawX hTameX (show (β - ε) - ε ≤ u - ε by linarith) (ψ u hαu D₁)
  have h4 : u - ε ≤ b :=
    (h1.trans (h2.trans (congrArg (birthSup hLawX ((β - ε) - ε)) hEq).le)).trans
      (le_of_eq hDesc)
  linarith


theorem t5_imageThread_band {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b d η₀ δx β : ℝ}
    (hη₀δx : η₀ < δx)
    (hgapd : ∀ τ ∈ critSet hTameX, τ ≠ d → δx < |τ - d|)
    (hlim : d + η₀ + 2 * ε < b)
    (hαd : α < d)
    (hβlo : d + 2 * ε < β) (hβhi : β ≤ d + η₀ + 2 * ε)
    (C : comps stageX JX (d + η₀)) (hbC : birthSup hLawX (d + η₀) C = b) :
    ∃ I : comps stageY JY (β - ε),
      b - ε ≤ birthSup hLawY (β - ε) I ∧
      birthSup hLawY (β - ε) I ≤ b + ε ∧
      ψ (β - ε) (show α ≤ β - ε by linarith) I =
        structMap hLawX (show β - ε - ε ≤ d + η₀ by linarith) C := by
  -- (i) the aliveUp-lift of the census cell at level `d + η₀ + 2ε`
  obtain ⟨Al, hAlb, hAld⟩ := t5_aliveUp hLawX hTameX hbC
    (show d + η₀ ≤ d + η₀ + 2 * ε by linarith) hlim
  -- (ii) the source cell (the lift's descent to level β) still carries birth ≥ b
  have hSb : b ≤ birthSup hLawX β (structMap hLawX hβhi Al) := by
    have hr := rungB_bSup_descend_ge hLawX hTameX hβhi Al
    rw [hAlb] at hr
    exact hr
  -- (iii) the double-descent lands on the census cell's descent at level `β − 2ε`
  have hdoub : structMap hLawX (show β - ε - ε ≤ β by linarith)
      (structMap hLawX hβhi Al)
      = structMap hLawX (show β - ε - ε ≤ d + η₀ by linarith) C :=
    calc structMap hLawX (show β - ε - ε ≤ β by linarith) (structMap hLawX hβhi Al)
        = structMap hLawX (show β - ε - ε ≤ d + η₀ + 2 * ε by linarith) Al :=
          structMap_comp hLawX (show β - ε - ε ≤ β by linarith) hβhi Al
      _ = structMap hLawX (show β - ε - ε ≤ d + η₀ by linarith)
            (structMap hLawX (show d + η₀ ≤ d + η₀ + 2 * ε by linarith) Al) :=
          (structMap_comp hLawX (show β - ε - ε ≤ d + η₀ by linarith)
            (show d + η₀ ≤ d + η₀ + 2 * ε by linarith) Al).symm
      _ = structMap hLawX (show β - ε - ε ≤ d + η₀ by linarith) C :=
          congrArg (structMap hLawX (show β - ε - ε ≤ d + η₀ by linarith)) hAld
  -- (iv) the window `[β−2ε, d+η₀]` is crit-free (X-gap at `d`)
  have hfree : ∀ τ ∈ critSet hTameX, τ < β - ε - ε ∨ d + η₀ < τ := by
    intro τ hτ
    rcases le_or_gt τ d with hτd | hτd
    · left
      linarith
    · have hne : τ ≠ d := ne_of_gt hτd
      have hg := hgapd τ hτ hne
      rw [abs_of_pos (show 0 < τ - d by linarith)] at hg
      right
      linarith
  -- (v) the double-descent birth pin: exactly `b` (crit-free transport)
  have hDesc : birthSup hLawX (β - ε - ε)
      (structMap hLawX (show β - ε - ε ≤ β by linarith) (structMap hLawX hβhi Al)) = b := by
    have hth := t3_bSupThread hLawX hTameX (show β - ε - ε ≤ d + η₀ by linarith) hfree
      (C'' := C) rfl
    rw [hdoub]
    exact hth.trans hbC
  -- (vi) the image cell: band birth + ψ-pullback = the census cell's descent
  have hβα : α ≤ β := by linarith
  have hβε : α ≤ β - ε := by linarith
  refine ⟨φ β hβα (structMap hLawX hβhi Al), ?_, ?_, ?_⟩
  · have hlow := t5_imageBirthStrongLower hLawX hLawY hTameY φ hSq1 hβα
      (structMap hLawX hβhi Al)
    linarith
  · exact t5_imageBirthUpper hLawX hLawY hTameX hε φ ψ hSq2 hSq4 hβα hβε
      (structMap hLawX hβhi Al) hDesc
  · exact (hSq4 β hβα hβε (structMap hLawX hβhi Al)).trans hdoub


theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b d η₀ δx β : ℝ}
    (hη₀δx : η₀ < δx)
    (hgapd : ∀ τ ∈ critSet hTameX, τ ≠ d → δx < |τ - d|)
    (hlim : d + η₀ + 2 * ε < b)
    (hαd : α < d)
    (hNE : Nonempty (comps stageY JY (β - ε)))
    (hβlo : d + 2 * ε < β) (hβhi : β ≤ d + η₀ + 2 * ε) :
    ({C : comps stageX JX (d + η₀) | birthSup hLawX (d + η₀) C = b} :
        Set (comps stageX JX (d + η₀))).encard ≤
    ({I : comps stageY JY (β - ε) | b - ε ≤ birthSup hLawY (β - ε) I ∧
        birthSup hLawY (β - ε) I ≤ b + ε} : Set (comps stageY JY (β - ε))).encard := by
  -- per-cell supply (the level-parameterized image-thread pin)
  have hex : ∀ C : comps stageX JX (d + η₀), birthSup hLawX (d + η₀) C = b →
      ∃ I : comps stageY JY (β - ε), b - ε ≤ birthSup hLawY (β - ε) I ∧
        birthSup hLawY (β - ε) I ≤ b + ε ∧
        ψ (β - ε) (show α ≤ β - ε by linarith) I =
          structMap hLawX (show β - ε - ε ≤ d + η₀ by linarith) C :=
    fun C hbC => t5_imageThread_band hLawX hLawY hTameX hTameY hε φ ψ hSq1 hSq2 hSq4
      hη₀δx hgapd hlim hαd hβlo hβhi C hbC
  -- the choice map and its spec (the Nonempty instance feeds `Classical.epsilon`)
  haveI : Nonempty (comps stageY JY (β - ε)) := hNE
  set f : comps stageX JX (d + η₀) → comps stageY JY (β - ε) :=
    fun C => Classical.epsilon (fun I => b - ε ≤ birthSup hLawY (β - ε) I ∧
      birthSup hLawY (β - ε) I ≤ b + ε ∧
      ψ (β - ε) (show α ≤ β - ε by linarith) I =
        structMap hLawX (show β - ε - ε ≤ d + η₀ by linarith) C) with hfdef
  have hfspec : ∀ C : comps stageX JX (d + η₀), birthSup hLawX (d + η₀) C = b →
      b - ε ≤ birthSup hLawY (β - ε) (f C) ∧
        birthSup hLawY (β - ε) (f C) ≤ b + ε ∧
        ψ (β - ε) (show α ≤ β - ε by linarith) (f C) =
          structMap hLawX (show β - ε - ε ≤ d + η₀ by linarith) C :=
    fun C hbC => Classical.epsilon_spec (hex C hbC)
  -- crit-freeness of the descent window (X-gap at `d`)
  have hfree : ∀ τ ∈ critSet hTameX, τ < β - ε - ε ∨ d + η₀ < τ := by
    intro τ hτ
    rcases le_or_gt τ d with hτd | hτd
    · left
      linarith
    · have hne : τ ≠ d := ne_of_gt hτd
      have hg := hgapd τ hτ hne
      rw [abs_of_pos (show 0 < τ - d by linarith)] at hg
      right
      linarith
  -- the injection: membership by the pin, injectivity by ψ-pullback + `t3_crit_inj`
  refine Set.encard_le_encard_of_injOn (f := f) (fun C hC => ?_)
    (fun C₁ h₁ C₂ h₂ heq => ?_)
  · refine ⟨(hfspec C hC).1, (hfspec C hC).2.1⟩
  · have h₁b : birthSup hLawX (d + η₀) C₁ = b := h₁
    have h₂b : birthSup hLawX (d + η₀) C₂ = b := h₂
    have hpull₁ := (hfspec C₁ h₁b).2.2
    have hpull₂ := (hfspec C₂ h₂b).2.2
    rw [heq] at hpull₁
    exact t3_crit_inj hLawX hTameX (show β - ε - ε ≤ d + η₀ by linarith) hfree
      (hpull₁.symm.trans hpull₂)
