-- Prove2me | solution 1 for SingularCardinals.scott
-- status  : ACCEPTED   (prove)
-- author  : @teargosling
-- created : 2026-11-26T05:53:19.024945+00:00
-- url     : https://prove2.me/submissions/6bb145c5-96bb-4c4b-a908-3e1ef46500e9

import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal
import Definitions.Def_SingularCardinals_largeCardinals

universe u

open Cardinal SingularCardinals

theorem solution (κ : Cardinal.{u}) (hκ : ℵ₀ < κ) (D : Ultrafilter Ordinal.{u})
    (hD : IsNormalMeasure κ D)
    (hgch : {α : Ordinal.{u} | α < κ.ord ∧ 2 ^ α.card = Order.succ α.card} ∈ D) :
    2 ^ κ = Order.succ κ := by
  classical
  apply le_antisymm _ (Order.succ_le_of_lt (Cardinal.cantor κ))
  let A₀ : Set Ordinal.{u} :=
    {α : Ordinal.{u} | α < κ.ord ∧ (2 : Cardinal.{u}) ^ α.card = Order.succ α.card}
  have hA₀ : A₀ ∈ D := hgch
  -- Snapshot encoding: for each `α ∈ A₀`, `#(Set α.ToType) = #((Order.succ α.card).ord.ToType)`.
  have he_nonempty : ∀ α ∈ A₀, Nonempty (Set α.ToType ≃ (Order.succ α.card).ord.ToType) := by
    intro α hα
    apply Cardinal.eq.mp
    rw [Cardinal.mk_set, Cardinal.mk_toType, Cardinal.mk_toType, Cardinal.card_ord, hα.2]
  let e : ∀ α, α ∈ A₀ → Set α.ToType ≃ (Order.succ α.card).ord.ToType :=
    fun α hα => Classical.choice (he_nonempty α hα)
  let restr (X : Set κ.ord.ToType) (α : Ordinal.{u}) (hα : α < κ.ord) : Set α.ToType :=
    {x : α.ToType |
      Ordinal.ToType.mk (o := κ.ord) ⟨x.toOrd.1, Set.mem_Iio.mpr ((Set.mem_Iio.mp x.toOrd.2).trans hα)⟩ ∈ X}
  let Φ (X : Set κ.ord.ToType) (α : Ordinal.{u}) : Ordinal.{u} :=
    if hα : α ∈ A₀ then (e α hα (restr X α hα.1)).toOrd.1 else 0
  have hΦ_lt : ∀ X α, α ∈ A₀ → Φ X α < (Order.succ α.card).ord := by
    intro X α hα
    simp only [Φ, dif_pos hα]
    exact (e α hα (restr X α hα.1)).toOrd.2
  have hΦ_inj : ∀ {X Y α} (hα : α ∈ A₀), Φ X α = Φ Y α → restr X α hα.1 = restr Y α hα.1 := by
    intro X Y α hα hEq
    simp only [Φ, dif_pos hα] at hEq
    have hOrd : (e α hα (restr X α hα.1)).toOrd = (e α hα (restr Y α hα.1)).toOrd :=
      Subtype.ext hEq
    exact (e α hα).injective (Ordinal.ToType.mk.symm.injective hOrd)
  -- Tail lemma: for every `γ < κ.ord`, `{α | γ < α} ∈ D`.
  have htail : ∀ γ : Ordinal.{u}, γ < κ.ord → {α : Ordinal.{u} | γ < α} ∈ D := by
    intro γ hγ
    have hlim : Order.IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ.le
    have hδ_lt : Order.succ γ < κ.ord := hlim.succ_lt hγ
    have hι_lt : #((Order.succ γ).ToType) < κ := by
      rw [Cardinal.mk_toType]
      exact Cardinal.lt_ord.mp hδ_lt
    let s : (Order.succ γ).ToType → Set Ordinal.{u} := fun i => ({i.toOrd.1} : Set Ordinal.{u})ᶜ
    have hs : ∀ i, s i ∈ (D : Filter Ordinal.{u}) := fun i =>
      Ultrafilter.compl_mem_iff_notMem.mpr (hD.nonprincipal i.toOrd.1)
    have hinter : (⋂ i, s i) ∈ (D : Filter Ordinal.{u}) := hD.complete _ s hι_lt hs
    refine Filter.mem_of_superset hinter ?_
    intro α hα
    by_contra hnot
    have hle : α ≤ γ := le_of_not_gt hnot
    have hlt : α < Order.succ γ := Order.lt_succ_of_le hle
    let i : (Order.succ γ).ToType := Ordinal.ToType.mk ⟨α, hlt⟩
    have hi : α ∈ s i := Set.mem_iInter.mp hα i
    have hi_eq : i.toOrd.1 = α := by
      show (Ordinal.ToType.mk.symm (Ordinal.ToType.mk ⟨α, hlt⟩)).1 = α
      rw [Ordinal.ToType.mk.symm_apply_apply]
    exact hi (by simp [hi_eq])
  -- Distinct subsets disagree on `Φ` on a set in `D`.
  have hΦ_ne_mem : ∀ {X Y : Set κ.ord.ToType}, X ≠ Y → {α : Ordinal.{u} | Φ X α ≠ Φ Y α} ∈ D := by
    intro X Y hne
    have hex : ∃ g : κ.ord.ToType, ¬ (g ∈ X ↔ g ∈ Y) := by
      by_contra h
      push Not at h
      exact hne (Set.ext h)
    obtain ⟨g, hg⟩ := hex
    have hmem : A₀ ∩ {α : Ordinal.{u} | g.toOrd.1 < α} ∈ D :=
      Filter.inter_mem hA₀ (htail g.toOrd.1 g.toOrd.2)
    refine Filter.mem_of_superset hmem ?_
    rintro α ⟨hα, hγα⟩ hEq
    have hrestr : restr X α hα.1 = restr Y α hα.1 := hΦ_inj hα hEq
    let x : α.ToType := Ordinal.ToType.mk ⟨g.toOrd.1, hγα⟩
    have hx_eq :
        Ordinal.ToType.mk (o := κ.ord) ⟨x.toOrd.1, Set.mem_Iio.mpr ((Set.mem_Iio.mp x.toOrd.2).trans hα.1)⟩ = g := by
      have h1 : x.toOrd.1 = g.toOrd.1 := by
        show (Ordinal.ToType.mk.symm (Ordinal.ToType.mk ⟨g.toOrd.1, hγα⟩)).1 = g.toOrd.1
        rw [Ordinal.ToType.mk.symm_apply_apply]
      have h2 : (⟨x.toOrd.1, Set.mem_Iio.mpr ((Set.mem_Iio.mp x.toOrd.2).trans hα.1)⟩ : Set.Iio κ.ord) = g.toOrd :=
        Subtype.ext h1
      rw [h2]
      exact Ordinal.ToType.mk.apply_symm_apply g
    have hiff : x ∈ restr X α hα.1 ↔ x ∈ restr Y α hα.1 := by rw [hrestr]
    simp only [restr, Set.mem_ofPred_eq, hx_eq] at hiff
    exact hg hiff
  -- Ultrafilter comparison relation on `Set κ.ord.ToType`.
  let ltD (X Y : Set κ.ord.ToType) : Prop := {α : Ordinal.{u} | Φ X α < Φ Y α} ∈ D
  have hcomp : ∀ {X Y : Set κ.ord.ToType}, X ≠ Y → ltD X Y ∨ ltD Y X := by
    intro X Y hne
    have hunion : {α : Ordinal.{u} | Φ X α < Φ Y α} ∪ {α : Ordinal.{u} | Φ Y α < Φ X α} ∈ D := by
      refine Filter.mem_of_superset (hΦ_ne_mem hne) ?_
      intro α hα
      exact lt_or_gt_of_ne hα
    exact Ultrafilter.union_mem_iff.mp hunion
  -- Step 2: every `Y` has at most `κ` predecessors under `ltD`.
  have hpred_le : ∀ Y : Set κ.ord.ToType, #{X : Set κ.ord.ToType | ltD X Y} ≤ κ := by
    intro Y
    let P : Set (Set κ.ord.ToType) := {X : Set κ.ord.ToType | ltD X Y}
    have hπ_nonempty : ∀ α ∈ A₀, Nonempty ((Φ Y α).ToType ↪ α.ToType) := by
      intro α hα
      apply (Cardinal.le_def _ _).mp
      rw [Cardinal.mk_toType, Cardinal.mk_toType]
      exact Order.lt_succ_iff.mp (Cardinal.lt_ord.mp (hΦ_lt Y α hα))
    let π : ∀ α, α ∈ A₀ → (Φ Y α).ToType ↪ α.ToType :=
      fun α hα => Classical.choice (hπ_nonempty α hα)
    let r (X : P) (α : Ordinal.{u}) : Ordinal.{u} :=
      if h : α ∈ A₀ ∧ Φ X.1 α < Φ Y α then
        (π α h.1 (Ordinal.ToType.mk ⟨Φ X.1 α, h.2⟩)).toOrd.1
      else 0
    have hex_β : ∀ X : P, ∃ β : Ordinal.{u}, β < κ.ord ∧ {α : Ordinal.{u} | r X α = β} ∈ D := by
      intro X
      have hB : A₀ ∩ {α : Ordinal.{u} | Φ X.1 α < Φ Y α} ∈ D := Filter.inter_mem hA₀ X.2
      have hreg : ∀ α ∈ A₀ ∩ {α : Ordinal.{u} | Φ X.1 α < Φ Y α}, r X α < α := by
        rintro α ⟨hα, hlt⟩
        have h : α ∈ A₀ ∧ Φ X.1 α < Φ Y α := ⟨hα, hlt⟩
        simp only [r, dif_pos h]
        exact (π α hα (Ordinal.ToType.mk ⟨Φ X.1 α, hlt⟩)).toOrd.2
      obtain ⟨β, hβ⟩ := hD.normal _ hB (r X) hreg
      have hne : ((A₀ ∩ {α : Ordinal.{u} | Φ X.1 α < Φ Y α}) ∩ {α : Ordinal.{u} | r X α = β}).Nonempty :=
        D.nonempty_of_mem (Filter.inter_mem hB hβ)
      obtain ⟨α₀, ⟨hα₀, hlt₀⟩, hEq₀⟩ := hne
      have hβ_lt : β < κ.ord := by
        rw [← hEq₀]
        exact (hreg α₀ ⟨hα₀, hlt₀⟩).trans hα₀.1
      exact ⟨β, hβ_lt, hβ⟩
    let β : P → Ordinal.{u} := fun X => Classical.choose (hex_β X)
    have hβ_lt : ∀ X : P, β X < κ.ord := fun X => (Classical.choose_spec (hex_β X)).1
    have hβ_mem : ∀ X : P, {α : Ordinal.{u} | r X α = β X} ∈ D :=
      fun X => (Classical.choose_spec (hex_β X)).2
    let code : P → κ.ord.ToType := fun X => Ordinal.ToType.mk ⟨β X, hβ_lt X⟩
    have hcode_inj : Function.Injective code := by
      intro X₁ X₂ hEq
      have hβ_eq : β X₁ = β X₂ := by
        have h1 : (⟨β X₁, hβ_lt X₁⟩ : Set.Iio κ.ord) = ⟨β X₂, hβ_lt X₂⟩ :=
          Ordinal.ToType.mk.injective hEq
        exact congrArg Subtype.val h1
      by_contra hne_sub
      have hne : X₁.1 ≠ X₂.1 := fun h => hne_sub (Subtype.ext h)
      have hC1 : A₀ ∩ {α : Ordinal.{u} | Φ X₁.1 α < Φ Y α} ∈ D := Filter.inter_mem hA₀ X₁.2
      have hC2 : A₀ ∩ {α : Ordinal.{u} | Φ X₂.1 α < Φ Y α} ∈ D := Filter.inter_mem hA₀ X₂.2
      have hC : ((A₀ ∩ {α : Ordinal.{u} | Φ X₁.1 α < Φ Y α}) ∩ {α : Ordinal.{u} | r X₁ α = β X₁}) ∩
          ((A₀ ∩ {α : Ordinal.{u} | Φ X₂.1 α < Φ Y α}) ∩ {α : Ordinal.{u} | r X₂ α = β X₂}) ∩
          {α : Ordinal.{u} | Φ X₁.1 α ≠ Φ X₂.1 α} ∈ D :=
        Filter.inter_mem
          (Filter.inter_mem (Filter.inter_mem hC1 (hβ_mem X₁)) (Filter.inter_mem hC2 (hβ_mem X₂)))
          (hΦ_ne_mem hne)
      obtain ⟨α, ⟨⟨⟨hα, hlt1⟩, hr1⟩, ⟨⟨_, hlt2⟩, hr2⟩⟩, hΦne⟩ := D.nonempty_of_mem hC
      have h1 : α ∈ A₀ ∧ Φ X₁.1 α < Φ Y α := ⟨hα, hlt1⟩
      have h2 : α ∈ A₀ ∧ Φ X₂.1 α < Φ Y α := ⟨hα, hlt2⟩
      have hr_eq : r X₁ α = r X₂ α := hr1.trans (hβ_eq.trans hr2.symm)
      simp only [r, dif_pos h1, dif_pos h2] at hr_eq
      have hOrd : (π α hα (Ordinal.ToType.mk ⟨Φ X₁.1 α, hlt1⟩)).toOrd =
          (π α hα (Ordinal.ToType.mk ⟨Φ X₂.1 α, hlt2⟩)).toOrd := Subtype.ext hr_eq
      have hπ_eq := Ordinal.ToType.mk.symm.injective hOrd
      have hmk_eq := (π α hα).injective hπ_eq
      have hsub_eq := Ordinal.ToType.mk.injective hmk_eq
      exact hΦne (congrArg Subtype.val hsub_eq)
    calc
      #P ≤ #(κ.ord.ToType) := Cardinal.mk_le_of_injective hcode_inj
      _ = κ := by rw [Cardinal.mk_toType, Cardinal.card_ord]
  -- Step 3: conclude `2 ^ κ ≤ Order.succ κ`.
  have hmk_pow : #(Set κ.ord.ToType) = (2 : Cardinal.{u}) ^ κ := by
    rw [Cardinal.mk_set, Cardinal.mk_toType, Cardinal.card_ord]
  rw [← hmk_pow]
  by_contra hnot
  have hgt : Order.succ κ < #(Set κ.ord.ToType) := lt_of_not_ge hnot
  obtain ⟨F, hF⟩ := Cardinal.le_mk_iff_exists_set.mp hgt.le
  let U : Set (Set κ.ord.ToType) := F ∪ ⋃ Y : F, {X : Set κ.ord.ToType | ltD X Y.1}
  have hκ_pos : κ ≠ 0 := (Cardinal.aleph0_pos.trans hκ).ne'
  have hsucc_inf : ℵ₀ ≤ Order.succ κ := hκ.le.trans (Order.le_succ κ)
  have hU_le : #U ≤ Order.succ κ := by
    have hUnion_le : #(⋃ Y : F, {X : Set κ.ord.ToType | ltD X Y.1}) ≤ Order.succ κ := by
      calc
        #(⋃ Y : F, {X : Set κ.ord.ToType | ltD X Y.1})
            ≤ Cardinal.sum (fun Y : F => #{X : Set κ.ord.ToType | ltD X Y.1}) :=
          Cardinal.mk_iUnion_le_sum_mk
        _ ≤ Cardinal.sum (fun _ : F => κ) := Cardinal.sum_le_sum _ _ (fun Y => hpred_le Y.1)
        _ = #F * κ := by simp [Cardinal.sum_const]
        _ = Order.succ κ * κ := by rw [hF]
        _ = Order.succ κ := Cardinal.mul_eq_left hsucc_inf (Order.le_succ κ) hκ_pos
    calc
      #U ≤ #F + #(⋃ Y : F, {X : Set κ.ord.ToType | ltD X Y.1}) := Cardinal.mk_union_le _ _
      _ ≤ Order.succ κ + Order.succ κ := add_le_add hF.le hUnion_le
      _ = Order.succ κ := Cardinal.add_eq_self hsucc_inf
  have hU_ne_univ : U ≠ Set.univ := by
    intro hUniv
    have hEq : #U = #(Set κ.ord.ToType) := by rw [hUniv, Cardinal.mk_univ]
    exact hgt.not_ge (hEq ▸ hU_le)
  have hZ_ex : ∃ Z : Set κ.ord.ToType, Z ∉ U := by
    by_contra h
    push Not at h
    exact hU_ne_univ (Set.eq_univ_iff_forall.mpr h)
  obtain ⟨Z, hZ⟩ := hZ_ex
  have hZF : Z ∉ F := fun h => hZ (Set.mem_union_left _ h)
  have hZ_not_lt : ∀ Y : F, ¬ ltD Z Y.1 := fun Y h =>
    hZ (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨Y, h⟩))
  have hF_sub : F ⊆ {X : Set κ.ord.ToType | ltD X Z} := by
    intro Y hYF
    have hne : Y ≠ Z := fun h => hZF (h ▸ hYF)
    rcases hcomp hne with hlt | hgt'
    · exact hlt
    · exact False.elim (hZ_not_lt ⟨Y, hYF⟩ hgt')
  have hle : Order.succ κ ≤ κ := by
    calc
      Order.succ κ = #F := hF.symm
      _ ≤ #{X : Set κ.ord.ToType | ltD X Z} := Cardinal.mk_le_mk_of_subset hF_sub
      _ ≤ κ := hpred_le Z
  exact (Order.lt_succ κ).not_ge hle
