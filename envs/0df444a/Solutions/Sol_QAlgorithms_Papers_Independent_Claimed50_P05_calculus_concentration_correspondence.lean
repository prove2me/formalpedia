-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_concentration_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:40:35.620959+00:00
-- url     : https://prove2.me/submissions/a69db415-07f1-4ded-a8d9-77a23def7ddd

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P05
universe u v w
variable {k : Type*} [RCLike k]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

theorem g58b_pullback (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (T : P05.Symbol Y k → P05.Symbol X k) (hT : SymbolHom T)
    (hbp : ∀ fn f, BP fn f → BP (fun n => T (fn n)) (T f)) :
    Calculus (fun f => F (T f)) := by
  obtain ⟨hcl, ⟨h1, hadd, hsc, hmul, hdom⟩, hbd, hw⟩ := hF
  obtain ⟨Tc, Tp, Tt, Ts⟩ := hT
  have hscal : ∀ (c : k) (f : P05.Symbol Y k), T (scalar c f) = scalar c (T f) := by
    intro c f
    have e1 : scalar c f = times (constant c) f := Subtype.ext rfl
    have e2 : scalar c (T f) = times (constant c) (T f) := Subtype.ext rfl
    rw [e1, e2, Tt, Tc]
  have hbs : ∀ f : P05.Symbol Y k, BoundedSymbol f → BoundedSymbol (T f) := by
    intro f ⟨c, hc⟩
    have : BP (fun _ : ℕ => f) f := ⟨fun x => tendsto_const_nhds, c, fun _ x => hc x⟩
    obtain ⟨-, c', hc'⟩ := hbp _ _ this
    exact ⟨c', fun x => hc' 0 x⟩
  refine ⟨fun f => hcl (T f), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [Tc]; exact h1
  · intro f g; simp only [Tp]; exact hadd _ _
  · intro c f; simp only [hscal]; exact hsc _ _
  · intro f g; simp only [Tt]; exact hmul _ _
  · intro f g; simp only [Tt]; exact hdom _ _
  · intro f hf
    obtain ⟨hb, hadj⟩ := hbd (T f) (hbs f hf)
    exact ⟨hb, by simp only [Ts]; exact hadj⟩
  · intro fn f hbpf
    exact hw _ _ (hbp fn f hbpf)

theorem g58b_value_eq {G : Relation H} (hfun : ∀ x y z, (x, y) ∈ G → (x, z) ∈ G → y = z)
    {x y : H} (h : (x, y) ∈ G) : value G x = y := by
  unfold value
  rw [dif_pos ⟨y, h⟩]
  exact hfun _ _ _ (Classical.choose_spec (⟨y, h⟩ : ∃ y, (x, y) ∈ G)) h

theorem g58b_eq_zero_of_sub {G : Relation H} (hG : ClosedOperator (k := k) G)
    (h : zeroGraph ⊆ G) : G = zeroGraph := by
  ext ⟨x, y⟩
  refine ⟨fun hxy => ?_, fun hz => h hz⟩
  have h0 : (x, (0 : H)) ∈ G := h (show (0 : H) = 0 from rfl)
  exact hG.2.2.2.2.2 x y 0 hxy h0

theorem g58b_zero_times (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (f g : P05.Symbol X k) (hg : F g = zeroGraph) : F (times f g) = zeroGraph := by
  apply g58b_eq_zero_of_sub (hF.1 _)
  intro p hp
  apply hF.2.1.2.2.2.1
  refine ⟨0, ?_, ?_⟩
  · rw [hg]; rfl
  · have := (hF.1 f).2.2.1
    have hp' : p.2 = 0 := hp
    rw [hp']; exact this

theorem g58b_zero_mul_right (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (f g : P05.Symbol X k) (hf : F f = zeroGraph) : F (times f g) = zeroGraph := by
  have e : times f g = times g f := Subtype.ext (funext fun x => mul_comm _ _)
  rw [e]; exact g58b_zero_times F hF g f hf

theorem g58b_zero_plus (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (f g : P05.Symbol X k) (hf : F f = zeroGraph) (hg : F g = zeroGraph) :
    F (plus f g) = zeroGraph := by
  apply g58b_eq_zero_of_sub (hF.1 _)
  intro p hp
  apply hF.2.1.2.1
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · rw [hf]; rfl
  · rw [hg]; rfl
  · have hp' : p.2 = 0 := hp
    rw [hp']; simp

theorem g58b_zero_scalar (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (c : k) (f : P05.Symbol X k) (hf : F f = zeroGraph) :
    F (scalar c f) = zeroGraph := by
  apply g58b_eq_zero_of_sub (hF.1 _)
  intro p hp
  apply hF.2.1.2.2.1
  refine ⟨0, ?_, ?_⟩
  · rw [hf]; rfl
  · have hp' : p.2 = 0 := hp
    rw [hp']; simp

theorem g58b_zero_const (F : P05.Symbol X k → Relation H) (hF : Calculus F) :
    F (constant 0) = zeroGraph := by
  have e : (constant 0 : P05.Symbol X k) = scalar 0 (constant 1) :=
    Subtype.ext (funext fun x => by simp [constant, scalar])
  rw [e]
  apply g58b_eq_zero_of_sub (hF.1 _)
  intro p hp
  apply hF.2.1.2.2.1
  refine ⟨p.1, ?_, ?_⟩
  · rw [hF.2.1.1]; rfl
  · have hp' : p.2 = 0 := hp
    rw [hp']; simp

theorem g58b_zero_of_value (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (f : P05.Symbol X k) (hb : BoundedSymbol f) (hv : ∀ y, value (F f) y = 0) :
    F f = zeroGraph := by
  obtain ⟨⟨T, hT⟩, -⟩ := hF.2.2.1 f hb
  have hfun := (hF.1 f).2.2.2.2.2
  apply g58b_eq_zero_of_sub (hF.1 _)
  intro p hp
  have hp' : p.2 = 0 := hp
  have h1 : (p.1, T p.1) ∈ F f := by rw [hT]; rfl
  have := g58b_value_eq hfun h1
  rw [hv] at this
  rw [hT]; show p.2 = T p.1; rw [hp', ← this]

theorem g58b_value_zeroGraph (y : H) : value (zeroGraph : Relation H) y = 0 :=
  g58b_value_eq (fun x y z (h1 : y = 0) (h2 : z = 0) => h1.trans h2.symm)
    (show (0 : H) = 0 from rfl)

theorem g58b_indicator_bounded (A : Set X) (hA : MeasurableSet A) :
    BoundedSymbol (indicator (k := k) A hA) := by
  refine ⟨1, fun x => ?_⟩
  simp only [P05.indicator, Set.indicator]
  split_ifs <;> simp

theorem g58b_null_sigma (F : P05.Symbol X k → Relation H) (hF : Calculus F) :
    Null F ∅ ∧
    (∀ A B : Set X, MeasurableSet A → A ⊆ B → Null F B → Null F A) ∧
    (∀ A : ℕ → Set X, (∀ n, Null F (A n)) → Null F (⋃ n, A n)) := by
  refine ⟨⟨MeasurableSet.empty, ?_⟩, ?_, ?_⟩
  · have e : (indicator (k := k) (∅ : Set X) MeasurableSet.empty) = constant 0 :=
      Subtype.ext (funext fun x => by simp [P05.indicator, constant])
    rw [e]; exact g58b_zero_const F hF
  · intro A B hA hAB ⟨hB, hFB⟩
    refine ⟨hA, ?_⟩
    have e : indicator (k := k) A hA = times (indicator A hA) (indicator B hB) := by
      apply Subtype.ext; funext x
      simp only [P05.indicator, times, Set.indicator]
      by_cases hx : x ∈ A
      · simp [hx, hAB hx]
      · simp [hx]
    rw [e]; exact g58b_zero_times F hF _ _ hFB
  · intro A hA
    choose hm hz using hA
    have hU : MeasurableSet (⋃ n, A n) := MeasurableSet.iUnion hm
    have hacc : ∀ n, MeasurableSet (Set.accumulate A n) := fun n => by
      rw [Set.accumulate_def]; exact MeasurableSet.biUnion (Set.to_countable _) (fun i _ => hm i)
    -- union of two
    have two : ∀ (B C : Set X) (hB : MeasurableSet B) (hC : MeasurableSet C),
        F (indicator (k := k) B hB) = zeroGraph → F (indicator (k := k) C hC) = zeroGraph →
        F (indicator (k := k) (B ∪ C) (hB.union hC)) = zeroGraph := by
      intro B C hB hC h1 h2
      have e : indicator (k := k) (B ∪ C) (hB.union hC) =
          plus (plus (indicator B hB) (indicator C hC))
            (scalar (-1) (times (indicator B hB) (indicator C hC))) := by
        apply Subtype.ext; funext x
        simp only [P05.indicator, plus, times, scalar, Set.indicator]
        by_cases hx : x ∈ B <;> by_cases hy : x ∈ C <;> simp [hx, hy]
      rw [e]
      exact g58b_zero_plus F hF _ _ (g58b_zero_plus F hF _ _ h1 h2)
        (g58b_zero_scalar F hF _ _ (g58b_zero_times F hF _ _ h2))
    have hn : ∀ n, F (indicator (k := k) (Set.accumulate A n) (hacc n)) = zeroGraph := by
      intro n
      induction n with
      | zero =>
        have e : indicator (k := k) (Set.accumulate A 0) (hacc 0) = P05.indicator (A 0) (hm 0) := by
          congr 1; exact Set.accumulate_zero_nat A
        rw [e]; exact hz 0
      | succ n ih =>
        have e : indicator (k := k) (Set.accumulate A (n + 1)) (hacc (n + 1)) =
            P05.indicator (Set.accumulate A n ∪ A (n + 1)) ((hacc n).union (hm (n + 1))) := by
          congr 1; exact Set.accumulate_succ A n
        rw [e]; exact two _ _ _ _ ih (hz _)
    refine ⟨hU, ?_⟩
    have hbp : BP (fun n => indicator (k := k) (Set.accumulate A n) (hacc n))
        (indicator (⋃ n, A n) hU) := by
      refine ⟨fun x => ?_, 1, fun n x => ?_⟩
      · by_cases hx : x ∈ ⋃ n, A n
        · obtain ⟨m, hm'⟩ := Set.mem_iUnion.mp hx
          apply tendsto_nhds_of_eventually_eq
          filter_upwards [Filter.eventually_ge_atTop m] with n hn
          have : x ∈ Set.accumulate A n := Set.mem_accumulate.mpr ⟨m, hn, hm'⟩
          simp [P05.indicator, Set.indicator, this, hx]
        · apply tendsto_nhds_of_eventually_eq
          filter_upwards with n
          have : x ∉ Set.accumulate A n := fun h => hx (Set.accumulate_subset_iUnion n h)
          simp [P05.indicator, Set.indicator, this, hx]
      · simp only [P05.indicator, Set.indicator]
        split_ifs <;> simp
    obtain ⟨-, -, hw⟩ := hF.2.2.2 _ _ hbp
    apply g58b_zero_of_value F hF _ (g58b_indicator_bounded _ hU)
    intro y
    have hlim := hw (value (F (indicator (⋃ n, A n) hU)) y) y
    simp only [hn, g58b_value_zeroGraph, inner_zero_right] at hlim
    have := tendsto_nhds_unique tendsto_const_nhds hlim
    exact inner_self_eq_zero.mp this.symm

theorem g58b_pullback2 (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (T : P05.Symbol Y k → P05.Symbol X k)
    (T1 : F (T (constant 1)) = identity)
    (Tp : ∀ f g, T (plus f g) = plus (T f) (T g))
    (Tt : ∀ f g, T (times f g) = times (T f) (T g))
    (Tsc : ∀ c f, T (scalar c f) = scalar c (T f))
    (Ts : ∀ f, T (starSymbol f) = starSymbol (T f))
    (hbp : ∀ fn f, BP fn f → BP (fun n => T (fn n)) (T f)) :
    Calculus (fun f => F (T f)) := by
  obtain ⟨hcl, ⟨h1, hadd, hsc, hmul, hdom⟩, hbd, hw⟩ := hF
  have hbs : ∀ f : P05.Symbol Y k, BoundedSymbol f → BoundedSymbol (T f) := by
    intro f ⟨c, hc⟩
    have : BP (fun _ : ℕ => f) f := ⟨fun x => tendsto_const_nhds, c, fun _ x => hc x⟩
    obtain ⟨-, c', hc'⟩ := hbp _ _ this
    exact ⟨c', fun x => hc' 0 x⟩
  refine ⟨fun f => hcl (T f), ⟨T1, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro f g; simp only [Tp]; exact hadd _ _
  · intro c f; simp only [Tsc]; exact hsc _ _
  · intro f g; simp only [Tt]; exact hmul _ _
  · intro f g; simp only [Tt]; exact hdom _ _
  · intro f hf
    obtain ⟨hb, hadj⟩ := hbd (T f) (hbs f hf)
    exact ⟨hb, by simp only [Ts]; exact hadj⟩
  · intro fn f hbpf
    exact hw _ _ (hbp fn f hbpf)

theorem g58b_plus_null (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (a b : P05.Symbol X k) (hb : F b = zeroGraph) : F (plus a b) = F a := by
  have sub : ∀ a b : P05.Symbol X k, F b = zeroGraph → F a ⊆ F (plus a b) := by
    intro a b hb p hp
    apply hF.2.1.2.1
    refine ⟨p.2, 0, hp, ?_, by simp⟩
    rw [hb]; rfl
  refine Set.Subset.antisymm ?_ (sub a b hb)
  have e : plus (plus a b) (scalar (-1) b) = a :=
    Subtype.ext (funext fun x => by simp only [plus, scalar]; ring)
  have := sub (plus a b) (scalar (-1) b) (g58b_zero_scalar F hF _ _ hb)
  rwa [e] at this

theorem g58b_conc_eq (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (S : Set X) (hS : MeasurableSet S) (hc : Concentrated F S) (f : P05.Symbol X k) :
    F f = F (times f (P05.indicator S hS)) := by
  obtain ⟨-, hSc, hz⟩ := hc
  have e : f = plus (times f (P05.indicator S hS)) (times f (P05.indicator Sᶜ hSc)) := by
    apply Subtype.ext; funext x
    simp only [plus, times, P05.indicator, Set.indicator]
    by_cases hx : x ∈ S <;> simp [hx]
  conv_lhs => rw [e]
  exact g58b_plus_null F hF _ _ (g58b_zero_times F hF _ _ hz)

theorem g58b_ez_apply (S : Set X) (hS : MeasurableSet S) (f : P05.Symbol S k) (x : X) :
    (extendZero S hS f).val x = if h : x ∈ S then f.val ⟨x, h⟩ else 0 := by
  simp only [extendZero]
  split_ifs with h
  · exact Subtype.val_injective.extend_apply f.val _ ⟨x, h⟩
  · rw [Function.extend_apply']
    rintro ⟨a, rfl⟩; exact h a.property

theorem g58b_correspondence (S : Set X) (hS : MeasurableSet S) :
    (∀ F : P05.Symbol X k → Relation H, Calculus F → Concentrated F S →
      Calculus (restrictBase F S hS) ∧ extendBase (restrictBase F S hS) = F) ∧
    (∀ G : P05.Symbol S k → Relation H, Calculus G →
      Calculus (extendBase G) ∧ Concentrated (extendBase G) S ∧
        restrictBase (extendBase G) S hS = G) := by
  have ezp : ∀ f g : P05.Symbol S k, extendZero S hS (plus f g) =
      plus (extendZero S hS f) (extendZero S hS g) := by
    intro f g; apply Subtype.ext; funext x
    simp only [plus, g58b_ez_apply]; split_ifs <;> simp
  have ezt : ∀ f g : P05.Symbol S k, extendZero S hS (times f g) =
      times (extendZero S hS f) (extendZero S hS g) := by
    intro f g; apply Subtype.ext; funext x
    simp only [times, g58b_ez_apply]; split_ifs <;> simp
  have ezsc : ∀ c (f : P05.Symbol S k), extendZero S hS (scalar c f) =
      scalar c (extendZero S hS f) := by
    intro c f; apply Subtype.ext; funext x
    simp only [scalar, g58b_ez_apply]; split_ifs <;> simp
  have ezs : ∀ f : P05.Symbol S k, extendZero S hS (starSymbol f) =
      starSymbol (extendZero S hS f) := by
    intro f; apply Subtype.ext; funext x
    simp only [starSymbol, g58b_ez_apply]; split_ifs <;> simp
  have ez1 : extendZero S hS (constant (1 : k)) = P05.indicator S hS := by
    apply Subtype.ext; funext x
    simp only [constant, g58b_ez_apply, P05.indicator, Set.indicator]; split_ifs <;> simp
  have ezbp : ∀ (fn : ℕ → P05.Symbol S k) (f : P05.Symbol S k), BP fn f → BP (fun n => extendZero S hS (fn n)) (extendZero S hS f) := by
    rintro fn f ⟨hpt, c, hc⟩
    refine ⟨fun x => ?_, max c 0, fun n x => ?_⟩
    · simp only [g58b_ez_apply]
      split_ifs with h
      · exact hpt ⟨x, h⟩
      · exact tendsto_const_nhds
    · simp only [g58b_ez_apply]
      split_ifs with h
      · exact (hc n _).trans (le_max_left _ _)
      · simp
  have cez : ∀ f : P05.Symbol S k, compose (extendZero S hS f) Subtype.val measurable_subtype_coe = f := by
    intro f; apply Subtype.ext; funext x
    simp only [compose, Function.comp_apply, g58b_ez_apply, dif_pos x.property]
  have ezc : ∀ f : P05.Symbol X k, extendZero S hS (compose f Subtype.val measurable_subtype_coe) =
      times f (P05.indicator S hS) := by
    intro f; apply Subtype.ext; funext x
    simp only [compose, times, g58b_ez_apply, P05.indicator, Set.indicator, Function.comp_apply]
    split_ifs <;> simp
  refine ⟨fun F hF hc => ⟨?_, ?_⟩, fun G hG => ⟨?_, ?_, ?_⟩⟩
  · refine g58b_pullback2 F hF (extendZero S hS) ?_ ezp ezt ezsc ezs ezbp
    rw [ez1]
    have e1 := g58b_conc_eq F hF S hS hc (constant 1)
    have e2 : times (constant (1 : k)) (P05.indicator S hS) = P05.indicator S hS :=
      Subtype.ext (funext fun x => one_mul _)
    rw [← e2, ← e1]; exact hF.2.1.1
  · funext f
    simp only [extendBase, restrictBase]
    rw [ezc, ← g58b_conc_eq F hF S hS hc]
  · refine g58b_pullback G hG (fun f => compose f Subtype.val measurable_subtype_coe)
      ⟨?_, ?_, ?_, ?_⟩ ?_
    · intro c; exact Subtype.ext rfl
    · intro f g; exact Subtype.ext rfl
    · intro f g; exact Subtype.ext rfl
    · intro f; exact Subtype.ext rfl
    · intro fn f ⟨hpt, c, hc⟩
      exact ⟨fun x => hpt x.val, c, fun n x => hc n x.val⟩
  · refine ⟨hS, hS.compl, ?_⟩
    simp only [extendBase]
    have e : compose (P05.indicator Sᶜ hS.compl) Subtype.val measurable_subtype_coe =
        (constant 0 : P05.Symbol S k) := by
      apply Subtype.ext; funext x
      simp [compose, P05.indicator, Set.indicator, constant, x.property]
    rw [e]; exact g58b_zero_const G hG
  · funext f
    simp only [extendBase, restrictBase]
    rw [cez]

theorem solution (S : Set X) (hS : MeasurableSet S) :
    (∀ F : P05.Symbol X k → Relation H, Calculus F → Concentrated F S →
      Calculus (restrictBase F S hS) ∧ extendBase (restrictBase F S hS) = F) ∧
    (∀ G : P05.Symbol S k → Relation H, Calculus G →
      Calculus (extendBase G) ∧ Concentrated (extendBase G) S ∧
        restrictBase (extendBase G) S hS = G) := g58b_correspondence (k := k) (H := H) S hS
