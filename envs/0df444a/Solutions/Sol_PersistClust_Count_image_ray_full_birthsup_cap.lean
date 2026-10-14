-- Prove2me | solution 1 for PersistClust.Count.image_ray_full_birthsup_cap
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-13T07:21:09.458538+00:00
-- url     : https://prove2.me/submissions/beb52cce-ebff-4cfe-af0d-417358c39f05

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

theorem t5_hDescPin {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {s₀ b : ℝ} {C₀ : comps stage J s₀} (hb : birthSup hLaw s₀ C₀ = b)
    {β s : ℝ} (hs₀β : s₀ ≤ β) (hβs : s ≤ β) (hs₀s : s₀ ≤ s)
    {A : comps stage J β} (hA : birthSup hLaw β A = b)
    (hP : structMap hLaw hs₀β A = C₀) :
    birthSup hLaw s (structMap hLaw hβs A) = b := by
  have h1 : birthSup hLaw β A ≤ birthSup hLaw s (structMap hLaw hβs A) :=
    rungB_bSup_descend_ge hLaw hTame hβs A
  have h2 : birthSup hLaw s (structMap hLaw hβs A)
      ≤ birthSup hLaw s₀ (structMap hLaw hs₀s (structMap hLaw hβs A)) :=
    rungB_bSup_descend_ge hLaw hTame hs₀s (structMap hLaw hβs A)
  have h3 : structMap hLaw hs₀s (structMap hLaw hβs A) = C₀ := by
    rw [structMap_comp hLaw hs₀s hβs A]
    exact hP
  rw [h3] at h2
  have h4 : birthSup hLaw s (structMap hLaw hβs A) ≤ b := h2.trans_eq hb
  have h5 : b ≤ birthSup hLaw s (structMap hLaw hβs A) := hA ▸ h1
  exact le_antisymm h4 h5

theorem t5_elderTrap {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b d β : ℝ} (hβ : α ≤ β) (hβε : α ≤ β - ε)
    {A : comps stageX JX β} (hA : birthSup hLawX β A = b)
    {s₀ : ℝ} {C₀ : comps stageX JX s₀} (hbC₀ : birthSup hLawX s₀ C₀ = b)
    (hs₀β : s₀ ≤ β) (hP : structMap hLawX hs₀β A = C₀)
    (hd : d + 2 * ε < β) {v : ℝ} (hv : d + ε < v) (hvE : v ≤ β - ε)
    (hvα : α ≤ v) (hvεα : α ≤ v - ε) (hs₀v : s₀ ≤ v - ε)
    {b3 : ℝ} (hM : birthSup hLawY v (structMap hLawY (show v ≤ β - ε by linarith)
        (φ β hβ A)) = b3) :
    b3 ≤ b + ε := by
  have hvεβ : v - ε ≤ β := by linarith
  -- identity (a) at v: ψ_v (descY (E, v)) = descX (A, v − ε).
  have hId : ψ v hvα (structMap hLawY (show v ≤ β - ε by linarith) (φ β hβ A))
      = structMap hLawX hvεβ A :=
    (hSq2 v (β - ε) hvα hβε (show v ≤ β - ε by linarith) (φ β hβ A)).trans
      ((congrArg (structMap hLawX (show v - ε ≤ (β - ε) - ε by linarith))
          (hSq4 β hβ hβε A)).trans
        (structMap_comp hLawX (show v - ε ≤ (β - ε) - ε by linarith)
          (show (β - ε) - ε ≤ β by linarith) A))
  -- the X-thread pin at level v − ε, from the census pin (design §2 / t5_hDescPin).
  have hCvB : birthSup hLawX (v - ε) (structMap hLawX hvεβ A) = b :=
    t5_hDescPin hLawX hTameX hbC₀ hs₀β (show v - ε ≤ β by linarith) hs₀v hA hP
  obtain ⟨stop, hstop⟩ := hTameX.2.2
  have hBddC : BddAbove (AncSet hLawX (v - ε) (structMap hLawX hvεβ A)) := by
    refine ⟨stop, fun w hw => ?_⟩
    obtain ⟨-, C₂, -⟩ := hw
    have hstage : (stageX w).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle'
    push_neg at hle'
    exact hstage.ne_empty (hstop w hle'.le)
  rw [← hM]
  have hne : (AncSet hLawY v (structMap hLawY (show v ≤ β - ε by linarith)
      (φ β hβ A))).Nonempty :=
    ⟨v, le_rfl, structMap hLawY (show v ≤ β - ε by linarith) (φ β hβ A),
      t3_structMap_id hLawY v (structMap hLawY (show v ≤ β - ε by linarith)
        (φ β hβ A))⟩
  refine csSup_le hne ?_
  intro u hu
  obtain ⟨huu, D₁, hD₁⟩ := hu
  have hαu : α ≤ u := le_trans hvα huu
  have hii := hSq2 v u hvα hαu huu D₁
  rw [hD₁] at hii
  have hEq : structMap hLawX (show v - ε ≤ u - ε by linarith) (ψ u hαu D₁)
      = structMap hLawX hvεβ A := hii.symm.trans hId
  have hmem : u - ε ∈ AncSet hLawX (v - ε) (structMap hLawX hvεβ A) :=
    ⟨show v - ε ≤ u - ε by linarith, ψ u hαu D₁, hEq⟩
  have hub : u - ε ≤ birthSup hLawX (v - ε) (structMap hLawX hvεβ A) :=
    (rfl : birthSup hLawX (v - ε) (structMap hLawX hvεβ A)
        = sSup (AncSet hLawX (v - ε) (structMap hLawX hvεβ A))).symm ▸
      le_csSup hBddC hmem
  rw [hCvB] at hub
  linarith

/-- Design part 4 (the FULL CAP): the X-ray of `A` is flat `= b` on the whole window
`(d, β]` — the pin-family pins it at every `s ∈ [d + η', β]`, and the crit-free window
`(d, d + η']` (no X-critical `τ ≠ d` within `δ₀` of `d`, and `η' < δ₀`) transports the pin
at `d + η'` down to any `s ∈ (d, d + η']` (`t3_bSupThread`). Hence `t5_elderTrap` applies at
EVERY probe `v ∈ (d + ε, β - ε]` with the anchor `s₀ := v - ε` (`hP := rfl`,
`hs₀v := le_rfl`), capping the Y-ray image `φ β A` by `b + ε` — no hazard zone. -/
theorem solution {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b d β : ℝ} (hαβ : α ≤ β) (hαd : α ≤ d) (hβε : α ≤ β - ε) (hd : d + 2 * ε < β)
    {A : comps stageX JX β} (hA : birthSup hLawX β A = b)
    {η' δ₀ : ℝ} (hη'0 : 0 < η') (hη'β : d + η' ≤ β) (hη'δ : η' < δ₀)
    (hgapd : ∀ τ ∈ critSet hTameX, τ ≠ d → δ₀ < |τ - d|)
    (hpin : ∀ s (hs : d + η' ≤ s) (hsβ : s ≤ β),
      birthSup hLawX s (structMap hLawX hsβ A) = b) :
    ∀ v, d + ε < v → v ≤ β - ε → ∀ hle : v ≤ β - ε,
      birthSup hLawY v (structMap hLawY hle (φ β hαβ A)) ≤ b + ε := by
  intro v hdv hvE hle
  have hvα : α ≤ v := by linarith
  have hvεα : α ≤ v - ε := by linarith
  have hs₀β : v - ε ≤ β := by linarith
  -- The anchor pin: the X-ray value at the anchor `s₀ := v - ε` is exactly `b`.
  have hbC₀ : birthSup hLawX (v - ε) (structMap hLawX hs₀β A) = b := by
    by_cases hcase : d + η' ≤ v - ε
    · exact hpin (v - ε) hcase hs₀β
    · -- `v - ε ∈ (d, d + η')`: transport the pin from `d + η'` down the crit-free
      -- window `[v - ε, d + η']` (any X-critical `τ` there has `0 < τ - d ≤ η' < δ₀`,
      -- contradicting the stable-`δ₀` gap at `d`).
      have hts : v - ε ≤ d + η' := by linarith
      have hgap : ∀ u ∈ critSet hTameX, u < v - ε ∨ d + η' < u := by
        intro u hu
        by_cases hUD : u = d
        · exact Or.inl (by linarith)
        · have hδ : δ₀ < |u - d| := hgapd u hu hUD
          by_cases h1 : v - ε ≤ u
          · by_cases h2 : u ≤ d + η'
            · exfalso
              rw [abs_of_nonneg (show 0 ≤ u - d by linarith)] at hδ
              linarith
            · exact Or.inr (by linarith)
          · exact Or.inl (by linarith)
      have hvc : birthSup hLawX (v - ε)
          (structMap hLawX hts (structMap hLawX hη'β A)) = b :=
        (t3_bSupThread hLawX hTameX hts hgap (C'' := structMap hLawX hη'β A) rfl).trans
          (hpin (d + η') le_rfl hη'β)
      have hjoin : structMap hLawX hs₀β A =
          structMap hLawX hts (structMap hLawX hη'β A) :=
        (structMap_comp hLawX hts hη'β A).symm
      rw [hjoin]
      exact hvc
  -- The trap: `t5_elderTrap` at probe `v` with the anchor `s₀ := v - ε` (its anchor
  -- condition `s₀ ≤ v - ε` is `le_rfl`, the descent-pin `hP` is `rfl`).
  exact t5_elderTrap hLawX hLawY hTameX hTameY hε φ ψ hSq2 hSq4 hαβ hβε hA
    hbC₀ hs₀β rfl hd hdv hvE hvα hvεα le_rfl
    (rfl : birthSup hLawY v (structMap hLawY hle (φ β hαβ A)) =
      birthSup hLawY v (structMap hLawY hle (φ β hαβ A)))
