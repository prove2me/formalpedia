-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_coincidence_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T12:20:15.609983+00:00
-- url     : https://prove2.me/submissions/638fd8c9-d5b5-44ae-88da-f7ba22dacbaa

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

theorem g58b_reg_one (f : P05.Symbol X k) :
    times (plus (constant 1) (absolute f)) (regularizer f) = constant 1 := by
  apply Subtype.ext; funext x
  simp only [times, plus, constant, absolute, regularizer]
  have h : (1 : k) + ((‖f.val x‖ : ℝ) : k) = ((1 + ‖f.val x‖ : ℝ) : k) := by push_cast; ring
  rw [h]; exact mul_inv_cancel₀ (RCLike.ofReal_ne_zero.mpr (by positivity))

theorem g58b_reg_one' (f : P05.Symbol X k) :
    times (regularizer f) (plus (constant 1) (absolute f)) = constant 1 := by
  rw [show times (regularizer f) (plus (constant 1) (absolute f)) =
    times (plus (constant 1) (absolute f)) (regularizer f) from
    Subtype.ext (funext fun x => mul_comm _ _)]
  exact g58b_reg_one f

theorem g58b_reg_f (f : P05.Symbol X k) :
    times (plus (constant 1) (absolute f)) (times (regularizer f) f) = f := by
  have := congrArg (fun s : P05.Symbol X k => s.val) (g58b_reg_one f)
  apply Subtype.ext; funext x
  have hx := congrFun this x
  simp only [times, constant] at hx ⊢
  rw [← mul_assoc, hx, one_mul]

theorem g58b_reg_bdd (f : P05.Symbol X k) :
    BoundedSymbol (regularizer f) ∧ BoundedSymbol (times (regularizer f) f) := by
  refine ⟨⟨1, fun x => ?_⟩, ⟨1, fun x => ?_⟩⟩
  · simp only [regularizer, norm_inv, RCLike.norm_ofReal]
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith [norm_nonneg (f.val x)])
  · simp only [times, regularizer, norm_mul, norm_inv, RCLike.norm_ofReal]
    rw [abs_of_pos (by positivity), inv_mul_le_iff₀ (by positivity)]
    linarith [norm_nonneg (f.val x)]

theorem g58b_regularization (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k) :
    BoundedSymbol (regularizer f) ∧ BoundedSymbol (times (regularizer f) f) ∧
    BoundedOperator (k := k) (F (regularizer f)) ∧
    BoundedOperator (k := k) (F (times (regularizer f) f)) ∧
    InjectiveOperator (F (regularizer f)) ∧
    F f = mul (inverse (F (regularizer f))) (F (times (regularizer f) f)) ∧
    ∀ x y, (x, y) ∈ F f ↔
      ∃ z, (x, z) ∈ F (times (regularizer f) f) ∧ (y, z) ∈ F (regularizer f) := by
  obtain ⟨hcl, ⟨h1, hadd, hsc, hmul, hdom⟩, hbd, hw⟩ := hF
  obtain ⟨be, bef⟩ := g58b_reg_bdd f
  obtain ⟨⟨Te, hTe⟩, -⟩ := hbd _ be
  obtain ⟨⟨Tef, hTef⟩, -⟩ := hbd _ bef
  set g := plus (constant 1) (absolute f)
  -- (Te u, u) ∈ F g
  have step1 : ∀ u, (Te u, u) ∈ F g := by
    intro u
    have hu : u ∈ graphDomain (mul (F g) (F (regularizer f))) := by
      rw [hdom, hTe, g58b_reg_one, h1]
      exact ⟨⟨Te u, rfl⟩, ⟨u, rfl⟩⟩
    obtain ⟨w, z, hz, hzw⟩ := hu
    have hz' : z = Te u := by rw [hTe] at hz; exact hz
    have hw' : (u, w) ∈ F (times g (regularizer f)) := hmul _ _ ⟨z, hz, hzw⟩
    rw [g58b_reg_one, h1] at hw'
    have : w = u := hw'
    rw [hz', this] at hzw; exact hzw
  have hinj : InjectiveOperator (F (regularizer f)) := by
    intro x z y hx hz
    rw [hTe] at hx hz
    have e1 : y = Te x := hx
    have e2 : y = Te z := hz
    exact (hcl g).2.2.2.2.2 _ _ _ (step1 x) (e1 ▸ e2 ▸ step1 z)
  have key : ∀ x y, (x, y) ∈ F f ↔
      ∃ z, (x, z) ∈ F (times (regularizer f) f) ∧ (y, z) ∈ F (regularizer f) := by
    intro x y
    constructor
    · intro hxy
      refine ⟨Te y, hmul _ _ ⟨y, hxy, ?_⟩, ?_⟩
      · rw [hTe]; rfl
      · rw [hTe]; rfl
    · rintro ⟨z, hxz, hyz⟩
      have hz : z = Te y := by rw [hTe] at hyz; exact hyz
      have := hmul g (times (regularizer f) f)
        (show (x, y) ∈ mul _ _ from ⟨z, hxz, by rw [hz]; exact step1 y⟩)
      rwa [g58b_reg_f] at this
  refine ⟨be, bef, ⟨Te, hTe⟩, ⟨Tef, hTef⟩, hinj, ?_, key⟩
  ext ⟨x, y⟩
  rw [key]
  rfl

theorem g58b_bdd_unique (F G : P05.Symbol X k → Relation H)
    (hF : Calculus F) (hG : Calculus G)
    (h : ∀ f, BoundedSymbol f → F f = G f) : F = G := by
  funext f
  obtain ⟨be, bef⟩ := g58b_reg_bdd f
  rw [(g58b_regularization F hF f).2.2.2.2.2.1, (g58b_regularization G hG f).2.2.2.2.2.1,
    h _ be, h _ bef]

theorem g58b_graph_eq {G : Relation H} (hfun : ∀ x y z, (x, y) ∈ G → (x, z) ∈ G → y = z)
    {T : H →L[k] H} (h : boundedGraph T ⊆ G) : G = boundedGraph T := by
  ext ⟨x, y⟩
  refine ⟨fun hxy => ?_, fun hp => h hp⟩
  exact hfun _ _ _ hxy (h (show T x = T x from rfl))

theorem g58b_bdd_add (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f g : P05.Symbol X k)
    {S T : H →L[k] H} (hf : F f = boundedGraph S) (hg : F g = boundedGraph T) :
    F (plus f g) = boundedGraph (S + T) := by
  apply g58b_graph_eq (hF.1 _).2.2.2.2.2
  intro p hp
  apply hF.2.1.2.1
  refine ⟨S p.1, T p.1, ?_, ?_, hp⟩
  · rw [hf]; rfl
  · rw [hg]; rfl

theorem g58b_bdd_scalar (F : P05.Symbol X k → Relation H) (hF : Calculus F) (c : k)
    (f : P05.Symbol X k) {S : H →L[k] H} (hf : F f = boundedGraph S) :
    F (scalar c f) = boundedGraph (c • S) := by
  apply g58b_graph_eq (hF.1 _).2.2.2.2.2
  intro p hp
  apply hF.2.1.2.2.1
  refine ⟨S p.1, ?_, hp⟩
  rw [hf]; rfl

theorem g58b_value_graph (T : H →L[k] H) (y : H) : value (boundedGraph T) y = T y :=
  g58b_value_eq (fun x y z (h1 : y = T x) (h2 : z = T x) => h1.trans h2.symm)
    (show T y = T y from rfl)

def g58b_symS (s : SimpleFunc X k) : P05.Symbol X k := ⟨s, s.measurable⟩

theorem g58b_pvm_unique (F G : P05.Symbol X k → Relation H)
    (hF : Calculus F) (hG : Calculus G)
    (h : ∀ A (hA : MeasurableSet A), F (P05.indicator A hA) = G (P05.indicator A hA)) : F = G := by
  have simple : ∀ s : SimpleFunc X k, F (g58b_symS s) = G (g58b_symS s) := by
    intro s
    induction s using SimpleFunc.induction with
    | const c hs =>
      rename_i A
      have e : g58b_symS (SimpleFunc.piecewise A hs (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
          scalar c (P05.indicator A hs) := by
        apply Subtype.ext; funext x
        simp only [g58b_symS, SimpleFunc.coe_piecewise, SimpleFunc.coe_const, scalar,
          P05.indicator, Set.indicator, Set.piecewise, Function.const_apply]
        split_ifs <;> simp
      obtain ⟨⟨P, hP⟩, -⟩ := hF.2.2.1 _ (g58b_indicator_bounded (k := k) A hs)
      rw [e, g58b_bdd_scalar F hF c _ hP, g58b_bdd_scalar G hG c _ ((h A hs).symm.trans hP)]
    | add hdisj ihf ihg =>
      rename_i f g
      have e : g58b_symS (f + g) = plus (g58b_symS f) (g58b_symS g) := Subtype.ext rfl
      have bf : BoundedSymbol (g58b_symS f) := f.exists_forall_norm_le
      have bg : BoundedSymbol (g58b_symS g) := g.exists_forall_norm_le
      obtain ⟨⟨S, hS⟩, -⟩ := hF.2.2.1 _ bf
      obtain ⟨⟨T, hT⟩, -⟩ := hF.2.2.1 _ bg
      rw [e, g58b_bdd_add F hF _ _ hS hT, g58b_bdd_add G hG _ _ (ihf.symm.trans hS)
        (ihg.symm.trans hT)]
  apply g58b_bdd_unique F G hF hG
  intro f ⟨c, hc⟩
  set c' := max c 0
  have hc' : ∀ x, ‖f.val x‖ ≤ c' := fun x => (hc x).trans (le_max_left _ _)
  have hsm : StronglyMeasurable f.val := f.property.stronglyMeasurable
  set seq : ℕ → P05.Symbol X k := fun n => g58b_symS (hsm.approxBounded c' n)
  have hbp : BP seq f := ⟨fun x => hsm.tendsto_approxBounded_of_norm_le (hc' x),
    c', fun n x => hsm.norm_approxBounded_le (le_max_right _ _) n x⟩
  obtain ⟨-, -, hwF⟩ := hF.2.2.2 _ _ hbp
  obtain ⟨-, -, hwG⟩ := hG.2.2.2 _ _ hbp
  obtain ⟨⟨S, hS⟩, -⟩ := hF.2.2.1 _ ⟨c, hc⟩
  obtain ⟨⟨T, hT⟩, -⟩ := hG.2.2.1 _ ⟨c, hc⟩
  have hST : S = T := by
    ext y
    apply ext_inner_left k
    intro x
    have h1 := hwF x y
    have h2 := hwG x y
    simp only [seq, simple] at h1
    have := tendsto_nhds_unique h1 h2
    rwa [hS, hT, g58b_value_graph, g58b_value_graph] at this
  rw [hS, hT, hST]

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

theorem g58b_bs_times {a b : P05.Symbol X k} (ha : BoundedSymbol a) (hb : BoundedSymbol b) :
    BoundedSymbol (times a b) := by
  obtain ⟨ca, hca⟩ := ha
  obtain ⟨cb, hcb⟩ := hb
  refine ⟨max ca 0 * max cb 0, fun x => ?_⟩
  simp only [times, norm_mul]
  exact mul_le_mul ((hca x).trans (le_max_left _ _)) ((hcb x).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

theorem g58b_meas_ne (h : P05.Symbol X k) : MeasurableSet {x | ¬ h.val x = 0} :=
  (measurableSet_eq_fun h.property measurable_const).compl

theorem g58b_null_of_zero (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (h : P05.Symbol X k) (hz : F h = zeroGraph) : Null F {x | ¬ h.val x = 0} := by
  refine ⟨g58b_meas_ne h, ?_⟩
  have e : P05.indicator {x | ¬ h.val x = 0} (g58b_meas_ne h) = times (reciprocal h) h := by
    apply Subtype.ext; funext x
    by_cases hx : h.val x = 0
    · simp [P05.indicator, Set.indicator, times, reciprocal, hx]
    · simp [P05.indicator, Set.indicator, times, reciprocal, hx, inv_mul_cancel₀ hx]
  rw [e]; exact g58b_zero_times F hF _ _ hz

theorem g58b_zero_of_null (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (h : P05.Symbol X k) (hn : Null F {x | ¬ h.val x = 0}) : F h = zeroGraph := by
  obtain ⟨hm, hz⟩ := hn
  have e : h = times h (P05.indicator {x | ¬ h.val x = 0} hm) := by
    apply Subtype.ext; funext x
    by_cases hx : h.val x = 0
    · simp [P05.indicator, Set.indicator, times, hx]
    · simp [P05.indicator, Set.indicator, times, hx]
  rw [e]; exact g58b_zero_times F hF _ _ hz

theorem g58b_lin (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k)
    {x y z : H} (h1 : (x, y) ∈ F f) (h2 : (z, y) ∈ F f) : (x - z, (0 : H)) ∈ F f := by
  obtain ⟨-, -, -, hadd, hsm, -⟩ := hF.1 f
  have := hadd _ _ _ _ h1 (hsm (-1) _ _ h2)
  simp only [neg_one_smul, ← sub_eq_add_neg, sub_self] at this
  exact this

theorem g58b_nullchar (F : P05.Symbol X k → Relation H) (hF : Calculus F) :
    (∀ (f : P05.Symbol X k) (h : MeasurableSet {x | f.val x ≠ 0}),
      kernel (F f) = kernel (F (P05.indicator {x | f.val x ≠ 0} h))) ∧
    (∀ f, F f = zeroGraph ↔ Almost F (fun x => f.val x = 0)) ∧
    (∀ f g, F f = F g ↔ Almost F (fun x => f.val x = g.val x)) ∧
    (∀ f, InjectiveOperator (F f) ↔ Almost F (fun x => f.val x ≠ 0)) := by
  have hcl := hF.1
  have h1 := hF.2.1.1
  have hmul := hF.2.1.2.2.2.1
  have hdom := hF.2.1.2.2.2.2
  have hbd := hF.2.2.1
  have recip_ind : ∀ (f : P05.Symbol X k) (h : MeasurableSet {x | f.val x ≠ 0}),
      times (reciprocal f) f = P05.indicator {x | f.val x ≠ 0} h := by
    intro f h; apply Subtype.ext; funext x
    by_cases hx : f.val x = 0
    · simp [P05.indicator, Set.indicator, times, reciprocal, hx]
    · simp [P05.indicator, Set.indicator, times, reciprocal, hx, inv_mul_cancel₀ hx]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- kernels
    intro f h
    ext x
    simp only [kernel, Set.mem_setOf_eq]
    constructor
    · intro hx
      have := hmul (reciprocal f) f (show (x, (0 : H)) ∈ mul _ _ from ⟨0, hx, (hcl _).2.2.1⟩)
      rwa [recip_ind f h] at this
    · intro hx
      have e : times f (P05.indicator {x | f.val x ≠ 0} h) = f := by
        apply Subtype.ext; funext x
        by_cases hx : f.val x = 0
        · simp [P05.indicator, Set.indicator, times, hx]
        · simp [P05.indicator, Set.indicator, times, hx]
      have := hmul f _ (show (x, (0 : H)) ∈ mul _ _ from ⟨0, hx, (hcl _).2.2.1⟩)
      rwa [e] at this
  · intro f
    exact ⟨g58b_null_of_zero F hF f, g58b_zero_of_null F hF f⟩
  · intro f g
    constructor
    · intro hfg
      set e := times (regularizer f) (regularizer g)
      have be : BoundedSymbol e := g58b_bs_times (g58b_reg_bdd f).1 (g58b_reg_bdd g).1
      have ef : times f e = times (times (regularizer f) f) (regularizer g) :=
        Subtype.ext (funext fun x => by simp only [times, e]; ring)
      have eg : times g e = times (regularizer f) (times (regularizer g) g) :=
        Subtype.ext (funext fun x => by simp only [times, e]; ring)
      have bfe : BoundedSymbol (times f e) := by
        rw [ef]; exact g58b_bs_times (g58b_reg_bdd f).2 (g58b_reg_bdd g).1
      have bge : BoundedSymbol (times g e) := by
        rw [eg]; exact g58b_bs_times (g58b_reg_bdd f).1 (g58b_reg_bdd g).2
      obtain ⟨⟨Te, hTe⟩, -⟩ := hbd _ be
      obtain ⟨⟨Tf, hTf⟩, -⟩ := hbd _ bfe
      obtain ⟨⟨Tg, hTg⟩, -⟩ := hbd _ bge
      have key : ∀ (a : P05.Symbol X k) (Ta : H →L[k] H), F (times a e) = boundedGraph Ta →
          ∀ y, (Te y, Ta y) ∈ F a := by
        intro a Ta hTa y
        have hy : y ∈ graphDomain (mul (F a) (F e)) := by
          rw [hdom, hTe, hTa]; exact ⟨⟨Te y, rfl⟩, ⟨Ta y, rfl⟩⟩
        obtain ⟨w, z, hz, hzw⟩ := hy
        have hz' : z = Te y := by rw [hTe] at hz; exact hz
        have hw : (y, w) ∈ F (times a e) := hmul _ _ ⟨z, hz, hzw⟩
        rw [hTa] at hw
        have hw' : w = Ta y := hw
        rw [← hz', ← hw']; exact hzw
      have hTfg : Tf = Tg := by
        ext y
        have a1 := key f Tf hTf y
        have a2 := key g Tg hTg y
        rw [← hfg] at a2
        exact (hcl f).2.2.2.2.2 _ _ _ a1 a2
      set d := times (plus f (scalar (-1) g)) e
      have ed : d = plus (times f e) (scalar (-1) (times g e)) :=
        Subtype.ext (funext fun x => by simp only [d, times, plus, scalar]; ring)
      have hd : F d = zeroGraph := by
        rw [ed, g58b_bdd_add F hF _ _ hTf (g58b_bdd_scalar F hF (-1) _ hTg), hTfg]
        ext ⟨u, v⟩
        simp [boundedGraph, zeroGraph]
      have hn := g58b_null_of_zero F hF d hd
      have eset : {x | ¬ d.val x = 0} = {x | ¬ (fun x => f.val x = g.val x) x} := by
        ext x
        simp only [d, e, times, plus, scalar, regularizer, Set.mem_setOf_eq]
        have h1 : ((1 + ‖f.val x‖ : ℝ) : k)⁻¹ ≠ 0 :=
          inv_ne_zero (RCLike.ofReal_ne_zero.mpr (by positivity))
        have h2 : ((1 + ‖g.val x‖ : ℝ) : k)⁻¹ ≠ 0 :=
          inv_ne_zero (RCLike.ofReal_ne_zero.mpr (by positivity))
        rw [mul_eq_zero, mul_eq_zero, not_or, not_or]
        simp only [h1, h2, not_false_eq_true, and_true]
        constructor
        · intro hne heq; apply hne; rw [heq]; ring
        · intro hne heq; apply hne; linear_combination heq
      unfold Almost
      rw [← eset]; exact hn
    · rintro ⟨hm, hz⟩
      have e : f = plus g (times (plus f (scalar (-1) g))
          (P05.indicator {x | ¬ (fun x => f.val x = g.val x) x} hm)) := by
        apply Subtype.ext; funext x
        by_cases hx : f.val x = g.val x
        · simp [P05.indicator, Set.indicator, times, plus, scalar, hx]
        · simp only [P05.indicator, Set.indicator, times, plus, scalar, Set.mem_setOf_eq, hx,
            not_false_eq_true, if_true]
          ring
      rw [e, g58b_plus_null F hF _ _ (g58b_zero_times F hF _ _ hz)]
  · intro f
    have hN : MeasurableSet {x | f.val x ≠ 0} := g58b_meas_ne f
    constructor
    · intro hinj
      set Z := {x | ¬ (fun x => f.val x ≠ 0) x}
      have hZ : MeasurableSet Z := (g58b_meas_ne f).compl
      refine ⟨hZ, ?_⟩
      obtain ⟨⟨P, hP⟩, -⟩ := hbd _ (g58b_indicator_bounded (k := k) Z hZ)
      have e0 : times f (P05.indicator Z hZ) = constant 0 := by
        apply Subtype.ext; funext x
        by_cases hx : f.val x = 0
        · simp [P05.indicator, Set.indicator, times, constant, Z, hx]
        · simp [P05.indicator, Set.indicator, times, constant, Z, hx]
      have hPy : ∀ y, P y = 0 := by
        intro y
        have hy : y ∈ graphDomain (mul (F f) (F (P05.indicator Z hZ))) := by
          rw [hdom, hP, e0, g58b_zero_const F hF]
          exact ⟨⟨P y, rfl⟩, ⟨0, rfl⟩⟩
        obtain ⟨w, z, hz, hzw⟩ := hy
        have hz' : z = P y := by rw [hP] at hz; exact hz
        have hw : (y, w) ∈ F (times f (P05.indicator Z hZ)) := hmul _ _ ⟨z, hz, hzw⟩
        rw [e0, g58b_zero_const F hF] at hw
        have hw' : w = 0 := hw
        rw [hz', hw'] at hzw
        exact hinj _ _ _ hzw (hcl f).2.2.1
      rw [hP]
      ext ⟨u, v⟩
      simp only [boundedGraph, zeroGraph, Set.mem_setOf_eq, hPy]
    · rintro ⟨hZ, hz⟩
      intro x z y hx hz'
      have h0 := g58b_lin F hF f hx hz'
      have := hmul (reciprocal f) f (show (x - z, (0 : H)) ∈ mul _ _ from ⟨0, h0, (hcl _).2.2.1⟩)
      rw [recip_ind f hN] at this
      have e1 : plus (P05.indicator (k := k) {x | f.val x ≠ 0} hN)
          (P05.indicator (k := k) {x | ¬ (fun x => f.val x ≠ 0) x} hZ) = constant 1 := by
        apply Subtype.ext; funext w
        by_cases hw : f.val w = 0
        · simp [P05.indicator, Set.indicator, plus, constant, hw]
        · simp [P05.indicator, Set.indicator, plus, constant, hw]
      have hid : F (P05.indicator {x | f.val x ≠ 0} hN) = identity := by
        rw [← g58b_plus_null F hF _ _ hz, e1, h1]
      rw [hid] at this
      have : (0 : H) = x - z := this
      exact (sub_eq_zero.mp this.symm)

section g58bU
variable (U : H ≃ₗᵢ[k] K)

theorem g58b_tinner (x : K) (v : H) : inner k x (U v) = inner k (U.symm x) v := by
  conv_lhs => rw [← U.apply_symm_apply x]
  exact U.inner_map_map _ _

theorem g58b_t_mem (A : Relation H) (x y : H) :
    (U x, U y) ∈ unitaryGraphTransport U A ↔ (x, y) ∈ A := by
  simp [unitaryGraphTransport]

theorem g58b_t_add (A B : Relation H) :
    unitaryGraphTransport U (add A B) = add (unitaryGraphTransport U A) (unitaryGraphTransport U B) := by
  ext ⟨x, y⟩
  simp only [unitaryGraphTransport, add, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    refine ⟨U a, U b, by simpa using ha, by simpa using hb, ?_⟩
    rw [← U.apply_symm_apply y, hab, map_add]
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨U.symm a, U.symm b, ha, hb, by rw [hab, map_add]⟩

theorem g58b_t_scale (c : k) (A : Relation H) :
    unitaryGraphTransport U (scale c A) = scale c (unitaryGraphTransport U A) := by
  ext ⟨x, y⟩
  simp only [unitaryGraphTransport, scale, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, hab⟩
    refine ⟨U a, by simpa using ha, ?_⟩
    rw [← U.apply_symm_apply y, hab, map_smul]
  · rintro ⟨a, ha, hab⟩
    exact ⟨U.symm a, ha, by rw [hab, map_smul]⟩

theorem g58b_t_mul (A B : Relation H) :
    unitaryGraphTransport U (mul A B) = mul (unitaryGraphTransport U A) (unitaryGraphTransport U B) := by
  ext ⟨x, y⟩
  simp only [unitaryGraphTransport, mul, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, h1, h2⟩
    exact ⟨U z, by simpa using h1, by simpa using h2⟩
  · rintro ⟨z, h1, h2⟩
    exact ⟨U.symm z, h1, h2⟩

theorem g58b_t_dom (A : Relation H) :
    graphDomain (unitaryGraphTransport U A) = U.symm ⁻¹' graphDomain A := by
  ext x
  simp only [graphDomain, unitaryGraphTransport, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨_, hy⟩
  · rintro ⟨y, hy⟩; exact ⟨U y, by simpa using hy⟩

theorem g58b_t_mono {A B : Relation H} (h : A ⊆ B) :
    unitaryGraphTransport U A ⊆ unitaryGraphTransport U B := fun _ hp => h hp

theorem g58b_t_identity : unitaryGraphTransport U (identity : Relation H) = identity := by
  ext ⟨x, y⟩
  simp only [unitaryGraphTransport, identity, Set.mem_setOf_eq]
  exact U.symm.injective.eq_iff

theorem g58b_t_bounded (T : H →L[k] H) :
    unitaryGraphTransport U (boundedGraph T) =
      boundedGraph ((U.toContinuousLinearEquiv : H →L[k] K).comp
        (T.comp (U.symm.toContinuousLinearEquiv : K →L[k] H))) := by
  ext ⟨x, y⟩
  simp only [unitaryGraphTransport, boundedGraph, Set.mem_setOf_eq]
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

theorem g58b_t_adjoint (A : Relation H) :
    graphAdjoint (k := k) (unitaryGraphTransport U A) =
      unitaryGraphTransport U (graphAdjoint (k := k) A) := by
  ext ⟨u, w⟩
  simp only [graphAdjoint, unitaryGraphTransport, Set.mem_setOf_eq]
  constructor
  · intro h x y hxy
    have := h (U x) (U y) (by simpa using hxy)
    rwa [U.inner_map_eq_flip, U.inner_map_eq_flip] at this
  · intro h x y hxy
    have := h _ _ hxy
    rwa [← U.inner_map_eq_flip, ← U.inner_map_eq_flip, U.apply_symm_apply,
      U.apply_symm_apply] at this

theorem g58b_t_value (A : Relation H) (hfun : ∀ x y z, (x, y) ∈ A → (x, z) ∈ A → y = z)
    (y : K) : value (unitaryGraphTransport U A) y = U (value A (U.symm y)) := by
  by_cases h : ∃ w, (U.symm y, w) ∈ A
  · obtain ⟨w, hw⟩ := h
    have hfun' : ∀ x y z, (x, y) ∈ unitaryGraphTransport U A →
        (x, z) ∈ unitaryGraphTransport U A → y = z := fun x y z h1 h2 =>
      U.symm.injective (hfun _ _ _ h1 h2)
    have h1 : (y, U w) ∈ unitaryGraphTransport U A := by
      show (U.symm y, U.symm (U w)) ∈ A; simpa using hw
    rw [g58b_value_eq hfun' h1, g58b_value_eq hfun hw]
  · have h' : ¬ ∃ w, (y, w) ∈ unitaryGraphTransport U A := fun ⟨w, hw⟩ => h ⟨_, hw⟩
    unfold value
    rw [dif_neg h', dif_neg h, map_zero]

theorem g58b_t_closed (A : Relation H) (hA : ClosedOperator (k := k) A) :
    ClosedOperator (k := k) (unitaryGraphTransport U A) := by
  obtain ⟨-, hcl, h0, hadd, hsm, hfun⟩ := hA
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous (fun p : K × K => (U.symm p.1, U.symm p.2)) := by fun_prop
    exact hcl.preimage hc
  · show (U.symm 0, U.symm 0) ∈ A; simpa using h0
  · intro x y x2 y2 h1 h2
    show (U.symm (x + x2), U.symm (y + y2)) ∈ A
    rw [map_add, map_add]; exact hadd _ _ _ _ h1 h2
  · intro c x y h
    show (U.symm (c • x), U.symm (c • y)) ∈ A
    rw [map_smul, map_smul]; exact hsm _ _ _ h
  · intro x y z h1 h2
    exact U.symm.injective (hfun _ _ _ h1 h2)

end g58bU

theorem g58b_unitary (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (U : H ≃ₗᵢ[k] K) : Calculus (fun f => unitaryGraphTransport U (F f)) := by
  obtain ⟨hcl, ⟨h1, hadd, hsc, hmul, hdom⟩, hbd, hw⟩ := hF
  refine ⟨fun f => g58b_t_closed U _ (hcl f), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [h1, g58b_t_identity]
  · intro f g; rw [← g58b_t_add]; exact g58b_t_mono U (hadd f g)
  · intro c f; rw [← g58b_t_scale]; exact g58b_t_mono U (hsc c f)
  · intro f g; rw [← g58b_t_mul]; exact g58b_t_mono U (hmul f g)
  · intro f g
    simp only
    rw [← g58b_t_mul, g58b_t_dom, g58b_t_dom, g58b_t_dom, hdom, Set.preimage_inter]
  · intro f hf
    obtain ⟨⟨T, hT⟩, hadj⟩ := hbd f hf
    refine ⟨⟨_, by show unitaryGraphTransport U (F f) = _; rw [hT]; exact g58b_t_bounded U T⟩, ?_⟩
    simp only
    rw [g58b_t_adjoint, hadj]
  · intro fn f hbp
    obtain ⟨hbn, hbf, hlim⟩ := hw fn f hbp
    have bnd : ∀ g, BoundedOperator (k := k) (F g) →
        BoundedOperator (k := k) (unitaryGraphTransport U (F g)) := by
      rintro g ⟨T, hT⟩; exact ⟨_, by rw [hT]; exact g58b_t_bounded U T⟩
    refine ⟨fun n => bnd _ (hbn n), bnd _ hbf, fun x y => ?_⟩
    simp only
    rw [g58b_t_value U _ (hcl f).2.2.2.2.2, g58b_tinner]
    have : ∀ n, inner k x (value (unitaryGraphTransport U (F (fn n))) y) =
        inner k (U.symm x) (value (F (fn n)) (U.symm y)) := fun n => by
      rw [g58b_t_value U _ (hcl _).2.2.2.2.2, g58b_tinner]
    simp only [this]
    exact hlim _ _

theorem g58b_adj_graph (S : H →L[k] H) :
    graphAdjoint (k := k) (boundedGraph S) = boundedGraph (ContinuousLinearMap.adjoint S) := by
  ext ⟨u, w⟩
  simp only [graphAdjoint, boundedGraph, Set.mem_setOf_eq]
  constructor
  · intro h
    apply ext_inner_left k
    intro x
    rw [h x (S x) rfl, ContinuousLinearMap.adjoint_inner_right]
  · intro h x y hy
    rw [h, hy, ContinuousLinearMap.adjoint_inner_right]

theorem g58b_graph_inj {S T : H →L[k] H} (h : boundedGraph S = boundedGraph T) : S = T := by
  ext x
  have : (x, S x) ∈ boundedGraph T := h ▸ (show S x = S x from rfl)
  exact this

theorem g58b_bdd_mul (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f g : P05.Symbol X k)
    {S T : H →L[k] H} (hf : F f = boundedGraph S) (hg : F g = boundedGraph T) :
    F (times f g) = boundedGraph (S.comp T) := by
  apply g58b_graph_eq (hF.1 _).2.2.2.2.2
  intro p hp
  apply hF.2.1.2.2.2.1
  refine ⟨T p.1, ?_, ?_⟩
  · rw [hg]; rfl
  · rw [hf]; exact hp

theorem g58b_bdd_star (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k)
    (hb : BoundedSymbol f) {S : H →L[k] H} (hf : F f = boundedGraph S) :
    F (starSymbol f) = boundedGraph (ContinuousLinearMap.adjoint S) := by
  rw [← (hF.2.2.1 f hb).2, hf, g58b_adj_graph]

theorem g58b_sq (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k)
    (hb : BoundedSymbol f) {S : H →L[k] H} (hf : F f = boundedGraph S) :
    F (times (starSymbol f) f) = boundedGraph ((ContinuousLinearMap.adjoint S).comp S) :=
  g58b_bdd_mul F hF _ _ (g58b_bdd_star F hF f hb hf) hf

theorem g58b_re_sq (S : H →L[k] H) (x : H) :
    RCLike.re (inner k x (((ContinuousLinearMap.adjoint S).comp S) x)) = ‖S x‖ ^ 2 := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq]

theorem g58b_first (F : P05.Symbol X k → Relation H) (hF : Calculus F) :
    (∀ c f, c ≠ 0 ∨ BoundedOperator (k := k) (F f) → F (scalar c f) = scale c (F f)) ∧
    (∀ f g, BoundedOperator (k := k) (F g) →
      add (F f) (F g) = F (plus f g) ∧ mul (F f) (F g) = F (times f g) ∧
      mul (F g) (F f) ⊆ mul (F f) (F g)) ∧
    (∀ f, (∀ x, f.val x ≠ 0) → InjectiveOperator (F f) ∧ inverse (F f) = F (reciprocal f)) ∧
    (∀ f, Dense (graphDomain (F f))) ∧
    (∀ f, BoundedSymbol f → NormBound (k := k) (F f) (symbolNorm f)) ∧
    (∀ fn f, BP fn f → Strong (k := k) (fun n => F (fn n)) (F f)) := by
  have hcl := hF.1
  have h1 := hF.2.1.1
  have hadd := hF.2.1.2.1
  have hsc := hF.2.1.2.2.1
  have hmul := hF.2.1.2.2.2.1
  have hdom := hF.2.1.2.2.2.2
  have hbd := hF.2.2.1
  have hw := hF.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- scalars
    rintro c f (hc | ⟨T, hT⟩)
    · refine Set.Subset.antisymm ?_ (hsc c f)
      intro p hp
      have e : scalar c⁻¹ (scalar c f) = f :=
        Subtype.ext (funext fun x => by simp only [scalar]; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul])
      have := hsc c⁻¹ (scalar c f) (show (p.1, c⁻¹ • p.2) ∈ scale c⁻¹ _ from ⟨p.2, hp, rfl⟩)
      rw [e] at this
      exact ⟨c⁻¹ • p.2, this, by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
    · by_cases hc : c = 0
      · subst hc
        have e : scalar 0 f = constant 0 := Subtype.ext (funext fun x => by simp [scalar, constant])
        rw [e, g58b_zero_const F hF, hT]
        ext ⟨u, v⟩
        simp only [zeroGraph, scale, boundedGraph, Set.mem_setOf_eq, zero_smul]
        exact ⟨fun h => ⟨T u, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
      · refine Set.Subset.antisymm ?_ (hsc c f)
        intro p hp
        have e : scalar c⁻¹ (scalar c f) = f :=
          Subtype.ext (funext fun x => by simp only [scalar]; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul])
        have := hsc c⁻¹ (scalar c f) (show (p.1, c⁻¹ • p.2) ∈ scale c⁻¹ _ from ⟨p.2, hp, rfl⟩)
        rw [e] at this
        exact ⟨c⁻¹ • p.2, this, by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  · rintro f g ⟨T, hT⟩
    refine ⟨Set.Subset.antisymm (hadd f g) ?_, Set.Subset.antisymm (hmul f g) ?_, ?_⟩
    · intro p hp
      have hneg := g58b_bdd_scalar F hF (-1) g hT
      have e : plus (plus f g) (scalar (-1) g) = f :=
        Subtype.ext (funext fun x => by simp only [plus, scalar]; ring)
      have := hadd (plus f g) (scalar (-1) g)
        (show (p.1, p.2 - T p.1) ∈ add _ _ from ⟨p.2, (-1 : k) • T p.1, hp, by rw [hneg]; rfl,
          by rw [neg_one_smul, sub_eq_add_neg]⟩)
      rw [e] at this
      refine ⟨p.2 - T p.1, T p.1, this, by rw [hT]; rfl, by abel⟩
    · intro p hp
      have hx : p.1 ∈ graphDomain (mul (F f) (F g)) := by
        rw [hdom, hT]; exact ⟨⟨T p.1, rfl⟩, ⟨p.2, hp⟩⟩
      obtain ⟨w, z, hz, hzw⟩ := hx
      have := hmul f g ⟨z, hz, hzw⟩
      have hw' : w = p.2 := (hcl _).2.2.2.2.2 _ _ _ this hp
      exact ⟨z, hz, hw' ▸ hzw⟩
    · intro p hp
      have h1' := hmul g f hp
      have e : times g f = times f g := Subtype.ext (funext fun x => mul_comm _ _)
      rw [e] at h1'
      have hx : p.1 ∈ graphDomain (mul (F f) (F g)) := by
        rw [hdom, hT]; exact ⟨⟨T p.1, rfl⟩, ⟨p.2, h1'⟩⟩
      obtain ⟨w, z, hz, hzw⟩ := hx
      have := hmul f g ⟨z, hz, hzw⟩
      have hw' : w = p.2 := (hcl _).2.2.2.2.2 _ _ _ this h1'
      exact ⟨z, hz, hw' ▸ hzw⟩
  · intro f hf
    have one1 : times (reciprocal f) f = constant 1 :=
      Subtype.ext (funext fun x => by simp only [times, reciprocal, constant]; exact inv_mul_cancel₀ (hf x))
    have one2 : times f (reciprocal f) = constant 1 :=
      Subtype.ext (funext fun x => by simp only [times, reciprocal, constant]; exact mul_inv_cancel₀ (hf x))
    refine ⟨?_, ?_⟩
    · rw [(g58b_nullchar F hF).2.2.2 f]
      have e : {x | ¬ (fun x => f.val x ≠ 0) x} = (∅ : Set X) := by
        ext x; simp [hf x]
      unfold Almost; rw [e]; exact (g58b_null_sigma F hF).1
    · ext ⟨u, v⟩
      simp only [inverse, Set.mem_setOf_eq]
      constructor
      · intro h
        have hx : v ∈ graphDomain (mul (F (reciprocal f)) (F f)) := by
          rw [hdom, one1, h1]; exact ⟨⟨u, h⟩, ⟨v, rfl⟩⟩
        obtain ⟨w, z, hz, hzw⟩ := hx
        have hz' : z = u := (hcl _).2.2.2.2.2 _ _ _ hz h
        have := hmul _ _ ⟨z, hz, hzw⟩
        rw [one1, h1] at this
        have hw : w = v := this
        rw [hz', hw] at hzw; exact hzw
      · intro h
        have hx : u ∈ graphDomain (mul (F f) (F (reciprocal f))) := by
          rw [hdom, one2, h1]; exact ⟨⟨v, h⟩, ⟨u, rfl⟩⟩
        obtain ⟨w, z, hz, hzw⟩ := hx
        have hz' : z = v := (hcl _).2.2.2.2.2 _ _ _ hz h
        have := hmul _ _ ⟨z, hz, hzw⟩
        rw [one2, h1] at this
        have hw : w = u := this
        rw [hz', hw] at hzw; exact hzw
  · -- dense domains
    intro f
    obtain ⟨be, bef, -, -, hinj, -, -⟩ := g58b_regularization F hF f
    obtain ⟨⟨Te, hTe⟩, -⟩ := hbd _ be
    have hstar : starSymbol (regularizer f) = regularizer f :=
      Subtype.ext (funext fun x => by simp [starSymbol, regularizer])
    have hsa : ContinuousLinearMap.adjoint Te = Te := by
      have := g58b_bdd_star F hF _ be hTe
      rw [hstar, hTe] at this
      exact (g58b_graph_inj this).symm
    have hrange : ∀ x, Te x ∈ graphDomain (F f) := by
      intro x
      have bfe : BoundedSymbol (times f (regularizer f)) := by
        have e : times f (regularizer f) = times (regularizer f) f :=
          Subtype.ext (funext fun x => mul_comm _ _)
        rw [e]; exact bef
      obtain ⟨⟨Tfe, hTfe⟩, -⟩ := hbd _ bfe
      have hx : x ∈ graphDomain (mul (F f) (F (regularizer f))) := by
        rw [hdom, hTe, hTfe]; exact ⟨⟨Te x, rfl⟩, ⟨Tfe x, rfl⟩⟩
      obtain ⟨w, z, hz, hzw⟩ := hx
      have hz' : z = Te x := by rw [hTe] at hz; exact hz
      exact ⟨w, hz' ▸ hzw⟩
    have hd : Dense ((LinearMap.range Te.toLinearMap : Submodule k H) : Set H) := by
      rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
        Submodule.eq_bot_iff]
      intro y hy
      rw [Submodule.mem_orthogonal] at hy
      have h0 : Te y = 0 := by
        apply ext_inner_left k
        intro x
        have := hy (Te x) ⟨x, rfl⟩
        rw [inner_zero_right, ← hsa, ContinuousLinearMap.adjoint_inner_right]
        exact this
      have := hinj y 0 0 (by rw [hTe]; exact h0.symm) (by rw [hTe]; exact (map_zero Te).symm)
      exact this
    refine hd.mono ?_
    rintro _ ⟨x, rfl⟩
    exact hrange x
  · -- norm bound
    intro f hb
    obtain ⟨⟨S, hS⟩, -⟩ := hbd _ hb
    obtain ⟨c0, hc0⟩ := hb
    set c := symbolNorm f
    have hbdd : BddAbove (Set.range fun x => ‖f.val x‖) := ⟨c0, by rintro _ ⟨x, rfl⟩; exact hc0 x⟩
    have hle : ∀ x, ‖f.val x‖ ≤ c := fun x => le_csSup hbdd ⟨x, rfl⟩
    have hc : 0 ≤ c := by
      by_cases hX : Nonempty X
      · obtain ⟨x⟩ := hX; exact (norm_nonneg _).trans (hle x)
      · have : Set.range (fun x => ‖f.val x‖) = ∅ := by
          rw [Set.range_eq_empty_iff]; exact not_nonempty_iff.mp hX
        simp only [c, symbolNorm, this, Real.sSup_empty, le_refl]
    let h : P05.Symbol X k := ⟨fun x => ((Real.sqrt (c ^ 2 - ‖f.val x‖ ^ 2) : ℝ) : k), by
      have hf := f.property; fun_prop⟩
    have hbh : BoundedSymbol h := ⟨c, fun x => by
      simp only [h, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [Real.sqrt_le_left hc]
      nlinarith [norm_nonneg (f.val x)]⟩
    obtain ⟨⟨R, hR⟩, -⟩ := hbd _ hbh
    have esum : plus (times (starSymbol f) f) (times (starSymbol h) h) = constant ((c ^ 2 : ℝ) : k) := by
      apply Subtype.ext; funext x
      simp only [plus, times, starSymbol, constant, h]
      rw [RCLike.star_def, RCLike.conj_mul, RCLike.conj_ofReal, ← RCLike.ofReal_mul,
        Real.mul_self_sqrt (by nlinarith [hle x, norm_nonneg (f.val x)])]
      push_cast; ring
    have hconst : F (constant ((c ^ 2 : ℝ) : k)) =
        boundedGraph (((c ^ 2 : ℝ) : k) • ContinuousLinearMap.id k H) := by
      have e : (constant ((c ^ 2 : ℝ) : k) : P05.Symbol X k) = scalar ((c ^ 2 : ℝ) : k) (constant (1 : k)) :=
        Subtype.ext (funext fun x => by simp [constant, scalar])
      rw [e]
      apply g58b_graph_eq (hcl _).2.2.2.2.2
      intro p hp
      apply hsc
      refine ⟨p.1, by rw [h1]; rfl, ?_⟩
      exact hp
    have hsum := g58b_bdd_add F hF _ _ (g58b_sq F hF f ⟨c0, hc0⟩ hS) (g58b_sq F hF h hbh hR)
    rw [esum, hconst] at hsum
    have hop := (g58b_graph_inj hsum)
    refine ⟨S, hS, ContinuousLinearMap.opNorm_le_bound _ hc (fun x => ?_)⟩
    have hx := congrArg (fun T : H →L[k] H => RCLike.re (inner k x (T x))) hop
    simp only [ContinuousLinearMap.add_apply] at hx
    rw [inner_add_right, map_add, g58b_re_sq, g58b_re_sq] at hx
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, inner_smul_right,
      inner_self_eq_norm_sq_to_K] at hx
    have hx' : ‖S x‖ ^ 2 + ‖R x‖ ^ 2 = c ^ 2 * ‖x‖ ^ 2 := by
      rw [← hx, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
    have : ‖S x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by nlinarith [sq_nonneg ‖R x‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero).mp this
  · -- strong convergence
    rintro fn f ⟨hpt, c, hc⟩
    have hcf : ∀ x, ‖f.val x‖ ≤ c := fun x => le_of_tendsto' ((hpt x).norm) (fun n => hc n x)
    have bn : ∀ n, BoundedSymbol (fn n) := fun n => ⟨c, hc n⟩
    choose Tn hTn using fun n => (hbd (fn n) (bn n)).1
    obtain ⟨T, hT⟩ := (hbd f ⟨c, hcf⟩).1
    refine ⟨fun n => ⟨Tn n, hTn n⟩, ⟨T, hT⟩, fun x => ?_⟩
    simp only [hTn, hT, g58b_value_graph]
    set d : ℕ → P05.Symbol X k := fun n => plus (fn n) (scalar (-1) f)
    have hd : ∀ n, F (d n) = boundedGraph (Tn n + (-1 : k) • T) := fun n =>
      g58b_bdd_add F hF _ _ (hTn n) (g58b_bdd_scalar F hF (-1) f hT)
    have hdb : ∀ n x, ‖(d n).val x‖ ≤ 2 * max c 0 := by
      intro n x
      simp only [d, plus, scalar, neg_one_mul]
      calc ‖(fn n).val x + -f.val x‖ ≤ ‖(fn n).val x‖ + ‖f.val x‖ := by
            rw [← norm_neg (f.val x)]; exact norm_add_le _ _
        _ ≤ max c 0 + max c 0 := add_le_add ((hc n x).trans (le_max_left _ _))
            ((hcf x).trans (le_max_left _ _))
        _ = 2 * max c 0 := by ring
    have hbd' : ∀ n, BoundedSymbol (d n) := fun n => ⟨_, hdb n⟩
    set q : ℕ → P05.Symbol X k := fun n => times (starSymbol (d n)) (d n)
    have hq : ∀ n, F (q n) = boundedGraph ((ContinuousLinearMap.adjoint (Tn n + (-1 : k) • T)).comp
        (Tn n + (-1 : k) • T)) := fun n => g58b_sq F hF _ (hbd' n) (hd n)
    have hqv : ∀ n y, (q n).val y = ((‖(d n).val y‖ ^ 2 : ℝ) : k) := by
      intro n y
      simp only [q, times, starSymbol]
      rw [RCLike.star_def, RCLike.conj_mul]; push_cast; ring
    have hbpq : BP q (constant 0) := by
      refine ⟨fun y => ?_, (2 * max c 0) ^ 2, fun n y => ?_⟩
      · simp only [hqv, constant]
        have h1 : Tendsto (fun n => (d n).val y) atTop (𝓝 0) := by
          have := (hpt y).sub_const (f.val y)
          simp only [sub_self] at this
          refine this.congr (fun n => ?_)
          simp only [d, plus, scalar]; ring
        have h2 := ((h1.norm).pow 2)
        simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h2
        have h3 : Tendsto (fun n => ((‖(d n).val y‖ ^ 2 : ℝ) : k)) atTop (𝓝 ((0 : ℝ) : k)) :=
          ((RCLike.continuous_ofReal (K := k)).tendsto 0).comp h2
        rw [RCLike.ofReal_zero] at h3
        exact h3
      · rw [hqv, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hdb n y) 2
    obtain ⟨-, -, hwq⟩ := hw _ _ hbpq
    have hlim := hwq x x
    simp only [hq, g58b_value_graph, g58b_zero_const F hF, g58b_value_zeroGraph,
      inner_zero_right] at hlim
    have hre := (RCLike.continuous_re.tendsto _).comp hlim
    simp only [Function.comp_def, g58b_re_sq, map_zero] at hre
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hs := (Real.continuous_sqrt.tendsto _).comp hre
    simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at hs
    refine hs.congr (fun n => ?_)
    simp only [ContinuousLinearMap.add_apply, neg_one_smul, ContinuousLinearMap.neg_apply,
      sub_eq_add_neg]

theorem g58b_add_comm (A B : Relation H) : add A B = add B A := by
  ext ⟨x, y⟩
  simp only [add, Set.mem_setOf_eq]
  constructor <;> rintro ⟨a, b, ha, hb, h⟩ <;> exact ⟨b, a, hb, ha, by rw [h, add_comm]⟩

theorem g58b_resolvent_eq (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (f : P05.Symbol X k) (z : k) :
    resolventShift z (F f) = F (plus (constant z) (scalar (-1) f)) := by
  obtain ⟨hsc, hbmul, -⟩ := g58b_first F hF
  have hb1 : BoundedOperator (k := k) (F (constant 1)) :=
    (hF.2.2.1 _ ⟨‖(1 : k)‖, fun _ => le_rfl⟩).1
  have e1 : scale z (identity : Relation H) = F (constant z) := by
    have : (constant z : P05.Symbol X k) = scalar z (constant 1) :=
      Subtype.ext (funext fun x => by simp [constant, scalar])
    rw [this, hsc z (constant 1) (Or.inr hb1), hF.2.1.1]
  have e2 : scale (-1 : k) (F f) = F (scalar (-1) f) := (hsc (-1) f (Or.inl (by norm_num))).symm
  have hb : BoundedOperator (k := k) (F (constant z)) := (hF.2.2.1 _ ⟨‖z‖, fun _ => le_rfl⟩).1
  unfold resolventShift
  rw [e1, e2, g58b_add_comm, (hbmul _ _ hb).1]
  congr 1
  exact Subtype.ext (funext fun x => add_comm _ _)

theorem g58b_nb_le (F : P05.Symbol X k → Relation H) (hF : Calculus F) (w : P05.Symbol X k)
    {W : H →L[k] H} (hW : F w = boundedGraph W) (c : ℝ) (hc : 0 ≤ c)
    (hle : ∀ x, ‖w.val x‖ ≤ c) : ‖W‖ ≤ c := by
  obtain ⟨T, hT, hTn⟩ := (g58b_first F hF).2.2.2.2.1 w ⟨c, hle⟩
  have : W = T := g58b_graph_inj (hW.symm.trans hT)
  rw [this]
  exact hTn.trans (Real.sSup_le (by rintro _ ⟨x, rfl⟩; exact hle x) hc)

theorem g58b_res_iff (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (f : P05.Symbol X k) (z : k) :
    z ∈ resolventSet (k := k) (F f) ↔ ∃ ε > 0,
      F (P05.indicator (f.val ⁻¹' Metric.ball z ε) (f.property measurableSet_ball)) = zeroGraph := by
  obtain ⟨hsc, hbmul, hrec, -, -, -⟩ := g58b_first F hF
  set zf := plus (constant z) (scalar (-1) f)
  have hzf : ∀ x, zf.val x = z - f.val x := fun x => by
    simp only [zf, plus, constant, scalar]; ring
  show BoundedOperator (k := k) (inverse (resolventShift z (F f))) ↔ _
  rw [g58b_resolvent_eq F hF f z]
  constructor
  · rintro ⟨R, hR⟩
    set ε : ℝ := 1 / (‖R‖ + 1)
    have hε : 0 < ε := by positivity
    refine ⟨ε, hε, ?_⟩
    set N := f.val ⁻¹' Metric.ball z ε
    have hNm : MeasurableSet N := f.property measurableSet_ball
    obtain ⟨⟨P, hP⟩, -⟩ := hF.2.2.1 _ (g58b_indicator_bounded (k := k) N hNm)
    set w := times zf (P05.indicator N hNm)
    have hwle : ∀ x, ‖w.val x‖ ≤ ε := by
      intro x
      simp only [w, times, P05.indicator, Set.indicator, hzf]
      split_ifs with hx
      · rw [mul_one, ← dist_eq_norm, dist_comm]; exact (Metric.mem_ball.mp hx).le
      · simp [hε.le]
    obtain ⟨⟨W, hW⟩, -⟩ := hF.2.2.1 _ ⟨ε, hwle⟩
    have hWn := g58b_nb_le F hF w hW ε hε.le hwle
    have hmulw : mul (F zf) (F (P05.indicator N hNm)) = F w := (hbmul _ _ ⟨P, hP⟩).2.1
    have hPy : ∀ y, P y = R (W y) := by
      intro y
      have h1 : (y, W y) ∈ F w := by rw [hW]; rfl
      rw [← hmulw] at h1
      obtain ⟨u, hu, hu2⟩ := h1
      have hu' : u = P y := by rw [hP] at hu; exact hu
      have : (W y, u) ∈ inverse (F zf) := hu2
      rw [hR] at this
      rw [← hu']; exact this
    have hWP : ∀ y, W (P y) = W y := by
      have e : times w (P05.indicator N hNm) = w := by
        apply Subtype.ext; funext x
        simp only [w, times, P05.indicator, Set.indicator]
        split_ifs <;> simp
      have := g58b_bdd_mul F hF _ _ hW hP
      rw [e, hW] at this
      intro y
      exact (congrArg (fun T : H →L[k] H => T y) (g58b_graph_inj this)).symm
    have hP0 : ∀ y, P y = 0 := by
      intro y
      have h1 : ‖P y‖ ≤ ‖R‖ * ε * ‖P y‖ := by
        calc ‖P y‖ = ‖R (W (P y))‖ := by rw [hWP, hPy]
          _ ≤ ‖R‖ * ‖W (P y)‖ := R.le_opNorm _
          _ ≤ ‖R‖ * (ε * ‖P y‖) := by
              gcongr; exact (W.le_opNorm _).trans (by gcongr)
          _ = ‖R‖ * ε * ‖P y‖ := by ring
      have h2 : ‖R‖ * ε < 1 := by
        simp only [ε]; rw [mul_one_div, div_lt_one (by positivity)]; linarith
      have : ‖P y‖ ≤ 0 := by nlinarith [norm_nonneg (P y)]
      exact norm_le_zero_iff.mp this
    rw [hP]
    ext ⟨u, v⟩
    simp only [boundedGraph, zeroGraph, Set.mem_setOf_eq, hP0]
  · rintro ⟨ε, hε, hN⟩
    set δ := min ε (1 / 2)
    have hδ : 0 < δ := by positivity
    have hNm : MeasurableSet (f.val ⁻¹' Metric.ball z δ) := f.property measurableSet_ball
    obtain ⟨_, hN'⟩ := (g58b_null_sigma F hF).2.1 _ _ hNm
      (Set.preimage_mono (Metric.ball_subset_ball (min_le_left _ _)))
      ⟨f.property measurableSet_ball, hN⟩
    set h := plus zf (P05.indicator _ hNm)
    have hFh : F h = F zf := g58b_plus_null F hF _ _ hN'
    have hlow : ∀ x, δ ≤ ‖h.val x‖ := by
      intro x
      simp only [h, plus, P05.indicator, Set.indicator, hzf]
      split_ifs with hx
      · have hd : ‖z - f.val x‖ < δ := by
          rw [← dist_eq_norm, dist_comm]; exact Metric.mem_ball.mp hx
        have h3 : (1 : k) = (z - f.val x + 1) + (-(z - f.val x)) := by ring
        have := norm_add_le (z - f.val x + 1) (-(z - f.val x))
        rw [← h3, norm_neg, norm_one] at this
        have hδ2 : δ ≤ 1 / 2 := min_le_right _ _
        linarith
      · rw [add_zero, ← dist_eq_norm, dist_comm]
        exact not_lt.mp hx
    have hne : ∀ x, h.val x ≠ 0 := fun x hx => by
      have := hlow x; rw [hx, norm_zero] at this; linarith
    have hrb : BoundedSymbol (reciprocal h) := ⟨δ⁻¹, fun x => by
      simp only [reciprocal, norm_inv]
      exact inv_anti₀ hδ (hlow x)⟩
    rw [← hFh, (hrec h hne).2]
    exact (hF.2.2.1 _ hrb).1

theorem g58b_spectral_support (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (f : P05.Symbol X k) :
    pointSpectrum (k := k) (F f) ⊆ Set.range f.val ∧
    spectrumOf (k := k) (F f) = calculusSupport (push F f.val f.property) ∧
    spectrumOf (k := k) (F f) ⊆ closure (Set.range f.val) ∧
    Concentrated (push F f.val f.property) (spectrumOf (k := k) (F f)) := by
  obtain ⟨hsc, hbmul, hrec, -, -, -⟩ := g58b_first F hF
  set G := push F f.val f.property
  have hG : Calculus G := by
    refine g58b_pullback F hF (fun g => compose g f.val f.property) ⟨?_, ?_, ?_, ?_⟩ ?_
    · intro c; exact Subtype.ext rfl
    · intro a b; exact Subtype.ext rfl
    · intro a b; exact Subtype.ext rfl
    · intro a; exact Subtype.ext rfl
    · intro fn g ⟨hpt, c, hc⟩
      exact ⟨fun x => hpt (f.val x), c, fun n x => hc n (f.val x)⟩
  have nullG : ∀ (U : Set k) (hU : MeasurableSet U),
      G (P05.indicator U hU) = F (P05.indicator (f.val ⁻¹' U) (f.property hU)) := by
    intro U hU
    show F (compose _ _ _) = _
    congr 1
  have hres : resolventSet (k := k) (F f) = ⋃₀ {U : Set k | IsOpen U ∧ Null G U} := by
    ext z
    rw [g58b_res_iff F hF f z]
    constructor
    · rintro ⟨ε, hε, hN⟩
      exact ⟨Metric.ball z ε, ⟨Metric.isOpen_ball, measurableSet_ball,
        by rw [nullG _ measurableSet_ball]; exact hN⟩,
        Metric.mem_ball_self hε⟩
    · rintro ⟨U, ⟨hUo, hUn⟩, hzU⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo z hzU
      obtain ⟨_, hz⟩ := (g58b_null_sigma G hG).2.1 _ _
        (measurableSet_ball : MeasurableSet (Metric.ball z ε)) hball hUn
      refine ⟨ε, hε, ?_⟩
      rw [← nullG _ measurableSet_ball]; exact hz
  have hspec : spectrumOf (k := k) (F f) = calculusSupport G := by
    unfold spectrumOf calculusSupport; rw [hres]
  refine ⟨?_, hspec, ?_, ?_⟩
  · rintro z ⟨x, hx0, hx⟩
    by_contra hz
    have hne : ∀ y, (plus (constant z) (scalar (-1) f)).val y ≠ 0 := by
      intro y hy
      apply hz
      refine ⟨y, ?_⟩
      simp only [plus, constant, scalar] at hy
      linear_combination -hy
    have hmem : (x, (0 : H)) ∈ resolventShift z (F f) := by
      refine ⟨z • x, (-1 : k) • (z • x), ⟨x, rfl, rfl⟩, ⟨z • x, hx, rfl⟩, ?_⟩
      simp
    rw [g58b_resolvent_eq F hF f z] at hmem
    exact hx0 ((hrec _ hne).1 _ _ _ hmem (hF.1 _).2.2.1)
  · intro z hz
    by_contra hcl
    apply hz
    rw [Metric.mem_closure_iff] at hcl
    push_neg at hcl
    obtain ⟨ε, hε, hfar⟩ := hcl
    rw [g58b_res_iff F hF f z]
    refine ⟨ε, hε, ?_⟩
    have e : P05.indicator (k := k) (f.val ⁻¹' Metric.ball z ε) (f.property measurableSet_ball) =
        constant 0 := by
      apply Subtype.ext; funext x
      have : f.val x ∉ Metric.ball z ε := by
        rw [Metric.mem_ball, dist_comm]; exact not_lt.mpr (hfar _ ⟨x, rfl⟩)
      simp [P05.indicator, Set.indicator, constant, this]
    rw [e]; exact g58b_zero_const F hF
  · have hopen : IsOpen (resolventSet (k := k) (F f)) := by
      rw [hres]; exact isOpen_sUnion (fun U hU => hU.1)
    have hcm : MeasurableSet (spectrumOf (k := k) (F f)) :=
      hopen.isClosed_compl.measurableSet
    refine ⟨hcm, ?_⟩
    have hc : (spectrumOf (k := k) (F f))ᶜ = ⋃₀ {U : Set k | IsOpen U ∧ Null G U} := by
      unfold spectrumOf; rw [compl_compl, hres]
    rw [hc]
    obtain ⟨T, hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable
      {U : Set k | IsOpen U ∧ Null G U} (fun U hU => hU.1)
    rw [← hTU]
    rcases Set.eq_empty_or_nonempty T with hT | hT
    · rw [hT, Set.sUnion_empty]; exact (g58b_null_sigma G hG).1
    · obtain ⟨g, rfl⟩ := hTc.exists_eq_range hT
      rw [Set.sUnion_range]
      exact (g58b_null_sigma G hG).2.2 _ (fun n => (hTS ⟨n, rfl⟩).2)

theorem g58b_sa_null (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k)
    (hsa : graphAdjoint (k := k) (F f) = F f) : Null F {x | ¬ star (f.val x) = f.val x} := by
  have hcl := hF.1
  have hmul := hF.2.1.2.2.2.1
  have hdom := hF.2.1.2.2.2.2
  have hbd := hF.2.2.1
  obtain ⟨be, bef, -, -, -, -, -⟩ := g58b_regularization F hF f
  set e := regularizer f
  obtain ⟨⟨Te, hTe⟩, -⟩ := hbd _ be
  have hstar : starSymbol e = e :=
    Subtype.ext (funext fun x => by simp [starSymbol, e, regularizer])
  have hTsa : ContinuousLinearMap.adjoint Te = Te := by
    have := g58b_bdd_star F hF _ be hTe
    rw [hstar, hTe] at this
    exact (g58b_graph_inj this).symm
  have efe : times f e = times e f := Subtype.ext (funext fun x => mul_comm _ _)
  have bfe : BoundedSymbol (times f e) := by rw [efe]; exact bef
  obtain ⟨⟨B, hB⟩, -⟩ := hbd _ bfe
  have hBs := g58b_bdd_star F hF _ bfe hB
  have h1 : ∀ y, (Te y, B y) ∈ F f := by
    intro y
    have hy : y ∈ graphDomain (mul (F f) (F e)) := by
      rw [hdom, hTe, hB]; exact ⟨⟨Te y, rfl⟩, ⟨B y, rfl⟩⟩
    obtain ⟨w, z, hz, hzw⟩ := hy
    have hz' : z = Te y := by rw [hTe] at hz; exact hz
    have hw : (y, w) ∈ F (times f e) := hmul _ _ ⟨z, hz, hzw⟩
    rw [hB] at hw
    have hw' : w = B y := hw
    rw [← hz', ← hw']; exact hzw
  have h2 : ∀ y, (Te y, (ContinuousLinearMap.adjoint B) y) ∈ F f := by
    intro y
    rw [← hsa]
    intro x w hxw
    have hTw : (x, Te w) ∈ F (times e f) := hmul _ _ ⟨w, hxw, by rw [hTe]; rfl⟩
    rw [← efe, hB] at hTw
    have hTw' : Te w = B x := hTw
    rw [ContinuousLinearMap.adjoint_inner_right, ← hTsa, ContinuousLinearMap.adjoint_inner_right,
      hTw']
  have hBB : ContinuousLinearMap.adjoint B = B := by
    ext y; exact (hcl f).2.2.2.2.2 _ _ _ (h2 y) (h1 y)
  set d := plus (times f e) (scalar (-1) (starSymbol (times f e)))
  have hd : F d = zeroGraph := by
    rw [g58b_bdd_add F hF _ _ hB (g58b_bdd_scalar F hF (-1) _ hBs), hBB]
    ext ⟨u, v⟩
    simp [boundedGraph, zeroGraph]
  have hn := g58b_null_of_zero F hF d hd
  have eset : {x | ¬ d.val x = 0} = {x | ¬ star (f.val x) = f.val x} := by
    ext x
    simp only [d, e, plus, times, scalar, starSymbol, regularizer, Set.mem_setOf_eq, star_mul',
      RCLike.star_def, RCLike.conj_ofReal, map_inv₀]
    have hr : ((1 + ‖f.val x‖ : ℝ) : k)⁻¹ ≠ 0 :=
      inv_ne_zero (RCLike.ofReal_ne_zero.mpr (by positivity))
    constructor
    · intro hne heq; apply hne; rw [heq]; ring
    · intro hne heq; apply hne
      have : (f.val x - (starRingEnd k) (f.val x)) * ((1 + ‖f.val x‖ : ℝ) : k)⁻¹ = 0 := by
        rw [← heq]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact (sub_eq_zero.mp h).symm
      · exact absurd h hr
  rw [← eset]; exact hn

theorem g58b_real_locus {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {d : ℕ} (F : P05.Symbol (Fin d → ℂ) ℂ → Relation E) (hF : Calculus F)
    (h : ∀ j, SelfAdjoint (k := ℂ) (F (fullCoordinate j))) :
    Concentrated F {z | ∀ j, (z j).im = 0} := by
  have hm : ∀ j : Fin d, MeasurableSet {z : Fin d → ℂ | (z j).im = 0} := fun j =>
    measurableSet_eq_fun (Complex.measurable_im.comp (measurable_pi_apply j)) measurable_const
  have hS : MeasurableSet {z : Fin d → ℂ | ∀ j, (z j).im = 0} := by
    have : {z : Fin d → ℂ | ∀ j, (z j).im = 0} = ⋂ j, {z | (z j).im = 0} := by
      ext z; simp
    rw [this]; exact MeasurableSet.iInter hm
  refine ⟨hS, ?_⟩
  have hnull : ∀ j : Fin d, Null F {z : Fin d → ℂ | ¬ (z j).im = 0} := by
    intro j
    have := g58b_sa_null F hF (fullCoordinate j) (h j).2.2
    have e : {x : Fin d → ℂ | ¬ star ((fullCoordinate j).val x) = (fullCoordinate j).val x} =
        {z | ¬ (z j).im = 0} := by
      ext z
      simp only [fullCoordinate, Set.mem_setOf_eq]
      rw [show star (z j) = (starRingEnd ℂ) (z j) from rfl, Complex.conj_eq_iff_im]
    rwa [e] at this
  set A : ℕ → Set (Fin d → ℂ) := fun n => if hn : n < d then {z | ¬ (z ⟨n, hn⟩).im = 0} else ∅
  have hA : ∀ n, Null F (A n) := by
    intro n
    simp only [A]
    split_ifs with hn
    · exact hnull _
    · exact (g58b_null_sigma F hF).1
  have e : {z : Fin d → ℂ | ∀ j, (z j).im = 0}ᶜ = ⋃ n, A n := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, Set.mem_iUnion, A]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j.val, by rw [dif_pos j.isLt]; exact hj⟩
    · rintro ⟨n, hn⟩
      split_ifs at hn with h'
      · exact ⟨_, hn⟩
      · exact absurd hn (Set.notMem_empty z)
  rw [e]
  exact (g58b_null_sigma F hF).2.2 _ hA

theorem g58b_ess_iff (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k) (z : k) :
    z ∈ essentialRange F f ↔ z ∉ resolventSet (k := k) (F f) := by
  have hmc : ∀ e : ℝ, MeasurableSet {x | ‖f.val x - z‖ ≤ e} := fun e =>
    measurableSet_le (f.property.sub_const z).norm measurable_const
  rw [g58b_res_iff F hF f z]
  constructor
  · rintro hz ⟨ε, hε, hN⟩
    apply hz (ε / 2) (by positivity)
    refine (g58b_null_sigma F hF).2.1 _ _ (hmc _) ?_ ⟨f.property measurableSet_ball, hN⟩
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    show f.val x ∈ Metric.ball z ε
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  · intro h e he hnull
    apply h
    refine ⟨e, he, ?_⟩
    obtain ⟨_, h2⟩ := (g58b_null_sigma F hF).2.1 _ _ (f.property measurableSet_ball) (fun x hx => by
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hx
      exact le_of_lt hx) hnull
    exact h2

theorem g58b_idem (F : P05.Symbol X k → Relation H) (hF : Calculus F) (A : Set X)
    (hA : MeasurableSet A) {P : H →L[k] H} (hP : F (P05.indicator A hA) = boundedGraph P) :
    ∀ x, P (P x) = P x := by
  have e : times (P05.indicator (k := k) A hA) (P05.indicator A hA) = P05.indicator A hA := by
    apply Subtype.ext; funext y
    simp only [times, P05.indicator, Set.indicator]
    split_ifs <;> simp
  have := g58b_bdd_mul F hF _ _ hP hP
  rw [e, hP] at this
  intro x
  exact (congrArg (fun T : H →L[k] H => T x) (g58b_graph_inj this)).symm

theorem g58b_approx (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k) :
    approximateSpectrum (k := k) (F f) = essentialRange F f := by
  obtain ⟨-, hbmul, -⟩ := g58b_first F hF
  ext z
  rw [g58b_ess_iff F hF f z]
  constructor
  · intro hz hres
    obtain ⟨R, hR⟩ := hres
    rw [g58b_resolvent_eq F hF f z] at hR
    obtain ⟨x, y, hxy, hx1, hlt⟩ := hz (1 / (‖R‖ + 1)) (by positivity)
    have hmem : (x, z • x + (-1 : k) • y) ∈ resolventShift z (F f) :=
      ⟨z • x, (-1 : k) • y, ⟨x, rfl, rfl⟩, ⟨y, hxy, rfl⟩, rfl⟩
    rw [g58b_resolvent_eq F hF f z] at hmem
    have : (z • x + (-1 : k) • y, x) ∈ inverse (F (plus (constant z) (scalar (-1) f))) := hmem
    rw [hR] at this
    have hx : x = R (z • x + (-1 : k) • y) := this
    have h1 : ‖x‖ ≤ ‖R‖ * ‖y - z • x‖ := by
      conv_lhs => rw [hx]
      refine (R.le_opNorm _).trans (le_of_eq ?_)
      congr 1
      rw [← norm_neg]; congr 1; simp [sub_eq_add_neg, add_comm]
    rw [hx1] at h1
    have h2 : ‖R‖ * ‖y - z • x‖ ≤ ‖R‖ * (1 / (‖R‖ + 1)) :=
      mul_le_mul_of_nonneg_left hlt.le (norm_nonneg _)
    have h3 : ‖R‖ * (1 / (‖R‖ + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]; linarith
    linarith
  · intro hz e he
    have hess := (g58b_ess_iff F hF f z).mpr hz
    set N := {x | ‖f.val x - z‖ ≤ e / 2}
    have hN : MeasurableSet N := measurableSet_le (f.property.sub_const z).norm measurable_const
    have hnn := hess (e / 2) (by positivity)
    obtain ⟨⟨P, hP⟩, -⟩ := hF.2.2.1 _ (g58b_indicator_bounded (k := k) N hN)
    have hPne : ∃ y, P y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hnn
      refine ⟨hN, ?_⟩
      rw [hP]; ext ⟨u, v⟩; simp [boundedGraph, zeroGraph, hcon]
    obtain ⟨y, hy⟩ := hPne
    set x := (‖P y‖⁻¹ : k) • P y
    have hx1 : ‖x‖ = 1 := by
      simp only [x, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)
    have hPx : P x = x := by
      simp only [x, map_smul, g58b_idem F hF N hN hP]
    have hbV : ∀ t, ‖(times f (P05.indicator N hN)).val t‖ ≤ ‖z‖ + e / 2 := by
      intro t
      simp only [times, P05.indicator, Set.indicator, N, Set.mem_setOf_eq]
      split_ifs with ht
      · rw [mul_one]
        calc ‖f.val t‖ = ‖(f.val t - z) + z‖ := by ring_nf
          _ ≤ ‖f.val t - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ ‖z‖ + e / 2 := by linarith
      · simp; positivity
    obtain ⟨⟨V, hV⟩, -⟩ := hF.2.2.1 _ ⟨_, hbV⟩
    have hxV : (x, V x) ∈ F f := by
      have h1 : (x, V x) ∈ F (times f (P05.indicator N hN)) := by rw [hV]; rfl
      rw [← (hbmul _ _ ⟨P, hP⟩).2.1] at h1
      obtain ⟨u, hu, hu2⟩ := h1
      have : u = P x := by rw [hP] at hu; exact hu
      rw [this, hPx] at hu2; exact hu2
    have hW := g58b_bdd_add F hF _ _ hV (g58b_bdd_scalar F hF (-1) _
      (g58b_bdd_scalar F hF z _ hP))
    have hwb : ∀ t, ‖(plus (times f (P05.indicator N hN))
        (scalar (-1) (scalar z (P05.indicator N hN)))).val t‖ ≤ e / 2 := by
      intro t
      simp only [plus, times, scalar, P05.indicator, Set.indicator, N, Set.mem_setOf_eq]
      split_ifs with ht
      · calc ‖f.val t * 1 + -1 * (z * 1)‖ = ‖f.val t - z‖ := by ring_nf
          _ ≤ e / 2 := ht
      · simp; positivity
    have hWn := g58b_nb_le F hF _ hW (e / 2) (by positivity) hwb
    refine ⟨x, V x, hxV, hx1, ?_⟩
    have : V x - z • x = (V + (-1 : k) • (z • P)) x := by
      simp [hPx, sub_eq_add_neg]
    rw [this]
    calc ‖(V + (-1 : k) • (z • P)) x‖ ≤ ‖V + (-1 : k) • (z • P)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ e / 2 * 1 := by rw [hx1]; gcongr
      _ < e := by linarith

theorem g58b_normbound_iff (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k)
    (c : ℝ) (hc : 0 ≤ c) :
    NormBound (k := k) (F f) c ↔ Almost F (fun x => ‖f.val x‖ ≤ c) := by
  obtain ⟨-, hbmul, -⟩ := g58b_first F hF
  constructor
  · rintro ⟨T, hT, hTn⟩
    set Nm : ℕ → Set X := fun m => {x | c + 1 / ((m : ℝ) + 1) ≤ ‖f.val x‖}
    have hNm : ∀ m, MeasurableSet (Nm m) := fun m =>
      measurableSet_le measurable_const f.property.norm
    have hnull : ∀ m, Null F (Nm m) := by
      intro m
      refine ⟨hNm m, ?_⟩
      set δ : ℝ := c + 1 / ((m : ℝ) + 1)
      have hδ : 0 < δ := by positivity
      obtain ⟨⟨P, hP⟩, -⟩ := hF.2.2.1 _ (g58b_indicator_bounded (k := k) _ (hNm m))
      set u : P05.Symbol X k := times (P05.indicator (Nm m) (hNm m)) (reciprocal f)
      have hub : ∀ t, ‖u.val t‖ ≤ δ⁻¹ := by
        intro t
        simp only [u, times, reciprocal, P05.indicator, Set.indicator, Nm, Set.mem_setOf_eq]
        split_ifs with ht
        · rw [one_mul, norm_inv]; exact inv_anti₀ hδ ht
        · simp; positivity
      obtain ⟨⟨U, hU⟩, -⟩ := hF.2.2.1 _ ⟨_, hub⟩
      have hUn := g58b_nb_le F hF u hU δ⁻¹ (by positivity) hub
      have e1 : times u f = P05.indicator (Nm m) (hNm m) := by
        apply Subtype.ext; funext t
        simp only [u, times, reciprocal, P05.indicator, Set.indicator, Nm, Set.mem_setOf_eq]
        split_ifs with ht
        · have : f.val t ≠ 0 := by
            intro h0; rw [h0, norm_zero] at ht
            have : 0 < c + 1 / ((m : ℝ) + 1) := by positivity
            linarith
          rw [one_mul, inv_mul_cancel₀ this]
        · simp
      have hPUT : ∀ y, P y = U (T y) := by
        have := g58b_bdd_mul F hF _ _ hU hT
        rw [e1, hP] at this
        intro y; exact congrArg (fun A : H →L[k] H => A y) (g58b_graph_inj this)
      have hP0 : ∀ y, P y = 0 := by
        intro y
        have h1 : ‖P y‖ ≤ δ⁻¹ * c * ‖P y‖ := by
          calc ‖P y‖ = ‖U (T (P y))‖ := by rw [← hPUT, g58b_idem F hF _ _ hP]
            _ ≤ ‖U‖ * ‖T (P y)‖ := U.le_opNorm _
            _ ≤ δ⁻¹ * (c * ‖P y‖) := by
                gcongr
                exact (T.le_opNorm _).trans (by gcongr)
            _ = δ⁻¹ * c * ‖P y‖ := by ring
        have h2 : δ⁻¹ * c < 1 := by
          rw [inv_mul_lt_iff₀ hδ, mul_one]
          simp only [δ]; have : 0 < 1 / ((m : ℝ) + 1) := by positivity
          linarith
        have : ‖P y‖ ≤ 0 := by nlinarith [norm_nonneg (P y)]
        exact norm_le_zero_iff.mp this
      rw [hP]; ext ⟨a, b⟩; simp [boundedGraph, zeroGraph, hP0]
    have e : {x | ¬ (fun x => ‖f.val x‖ ≤ c) x} = ⋃ m, Nm m := by
      ext x
      simp only [Set.mem_setOf_eq, not_le, Set.mem_iUnion, Nm]
      constructor
      · intro hx
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        exact ⟨m, by linarith⟩
      · rintro ⟨m, hm⟩
        have : 0 < 1 / ((m : ℝ) + 1) := by positivity
        linarith
    unfold Almost; rw [e]
    exact (g58b_null_sigma F hF).2.2 _ hnull
  · rintro ⟨hm, hz⟩
    set M := {x | ¬ (fun x => ‖f.val x‖ ≤ c) x}
    have hMc : MeasurableSet Mᶜ := hm.compl
    have e : f = plus (times f (P05.indicator Mᶜ hMc)) (times f (P05.indicator M hm)) := by
      apply Subtype.ext; funext x
      simp only [plus, times, P05.indicator, Set.indicator]
      by_cases hx : x ∈ M <;> simp [hx]
    have hFf : F f = F (times f (P05.indicator Mᶜ hMc)) := by
      conv_lhs => rw [e]
      exact g58b_plus_null F hF _ _ (g58b_zero_times F hF _ _ hz)
    have hb : ∀ t, ‖(times f (P05.indicator Mᶜ hMc)).val t‖ ≤ c := by
      intro t
      simp only [times, P05.indicator, Set.indicator, M, Set.mem_compl_iff, Set.mem_setOf_eq,
        not_not]
      split_ifs with ht
      · rw [mul_one]; exact ht
      · simp [hc]
    obtain ⟨⟨W, hW⟩, -⟩ := hF.2.2.1 _ ⟨c, hb⟩
    exact ⟨W, hFf.trans hW, g58b_nb_le F hF _ hW c hc hb⟩

theorem g58b_sa_of_real (F : P05.Symbol X k → Relation H) (hF : Calculus F) (g : P05.Symbol X k)
    (hreal : ∀ x, star (g.val x) = g.val x) : SelfAdjoint (k := k) (F g) := by
  obtain ⟨-, -, -, hdense, -, -⟩ := g58b_first F hF
  have hcl := hF.1
  have h1 := hF.2.1.1
  have hadd := hF.2.1.2.1
  have hmul := hF.2.1.2.2.2.1
  have hdom := hF.2.1.2.2.2.2
  have hbd := hF.2.2.1
  obtain ⟨be, bef, -, -, -, -, hchar⟩ := g58b_regularization F hF g
  set e := regularizer g
  obtain ⟨⟨Te, hTe⟩, -⟩ := hbd _ be
  have hstar : starSymbol e = e :=
    Subtype.ext (funext fun x => by simp [starSymbol, e, regularizer])
  have hTsa : ContinuousLinearMap.adjoint Te = Te := by
    have := g58b_bdd_star F hF _ be hTe
    rw [hstar, hTe] at this
    exact (g58b_graph_inj this).symm
  have efe : times g e = times e g := Subtype.ext (funext fun x => mul_comm _ _)
  have bfe : BoundedSymbol (times g e) := by rw [efe]; exact bef
  obtain ⟨⟨B, hB⟩, -⟩ := hbd _ bfe
  have hBsa : ContinuousLinearMap.adjoint B = B := by
    have := g58b_bdd_star F hF _ bfe hB
    have hs : starSymbol (times g e) = times g e := Subtype.ext (funext fun x => by
      simp only [starSymbol, times, star_mul', hreal]
      rw [show star (e.val x) = e.val x from congrFun (congrArg Subtype.val hstar) x])
    rw [hs, hB] at this
    exact (g58b_graph_inj this).symm
  have hcomm : ∀ y, Te (B y) = B (Te y) := by
    have h1' := g58b_bdd_mul F hF _ _ hTe hB
    have h2' := g58b_bdd_mul F hF _ _ hB hTe
    have : times e (times g e) = times (times g e) e := Subtype.ext (funext fun x => mul_comm _ _)
    rw [this, h2'] at h1'
    intro y; exact (congrArg (fun A : H →L[k] H => A y) (g58b_graph_inj h1')).symm
  have hi : ∀ y, (Te y, B y) ∈ F g := by
    intro y
    have hy : y ∈ graphDomain (mul (F g) (F e)) := by
      rw [hdom, hTe, hB]; exact ⟨⟨Te y, rfl⟩, ⟨B y, rfl⟩⟩
    obtain ⟨w, z, hz, hzw⟩ := hy
    have hz' : z = Te y := by rw [hTe] at hz; exact hz
    have hw : (y, w) ∈ F (times g e) := hmul _ _ ⟨z, hz, hzw⟩
    rw [hB] at hw
    have hw' : w = B y := hw
    rw [← hz', ← hw']; exact hzw
  -- domain of F g lies in the range of Te
  set G1 := plus (constant (1 : k)) (absolute g)
  set s := times (starSymbol g) (reciprocal (absolute g))
  have hsb : ∀ t, ‖s.val t‖ ≤ 1 := by
    intro t
    simp only [s, times, starSymbol, reciprocal, absolute, norm_mul, norm_star, norm_inv,
      RCLike.norm_ofReal, abs_norm]
    by_cases h0 : ‖g.val t‖ = 0
    · simp [h0]
    · rw [mul_inv_cancel₀ h0]
  obtain ⟨⟨Sop, hSop⟩, -⟩ := hbd _ ⟨1, hsb⟩
  have hsg : times s g = absolute g := by
    apply Subtype.ext; funext t
    simp only [s, times, starSymbol, reciprocal, absolute]
    by_cases h0 : g.val t = 0
    · simp [h0]
    · rw [mul_comm, ← mul_assoc, RCLike.star_def, RCLike.mul_conj]
      have : (‖g.val t‖ : k) ≠ 0 := RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)
      field_simp
  have hran : ∀ x y, (x, y) ∈ F g → ∃ m, x = Te m := by
    intro x y hxy
    have h2 : (x, Sop y) ∈ F (absolute g) := by
      rw [← hsg]; exact hmul _ _ ⟨y, hxy, by rw [hSop]; rfl⟩
    have h3 : (x, x + Sop y) ∈ F G1 := hadd _ _ ⟨x, Sop y, by rw [h1]; rfl, h2, rfl⟩
    refine ⟨x + Sop y, ?_⟩
    have h4 := hmul e G1 (show (x, Te (x + Sop y)) ∈ mul (F e) (F G1) from
      ⟨x + Sop y, h3, by rw [hTe]; rfl⟩)
    rw [g58b_reg_one', h1] at h4
    exact h4.symm
  refine ⟨hcl g, hdense g, ?_⟩
  ext ⟨u, w⟩
  simp only [graphAdjoint, Set.mem_setOf_eq]
  constructor
  · intro h
    have hTw : Te w = B u := by
      apply ext_inner_left k
      intro v
      have := h _ _ (hi v)
      rw [← hTsa, ContinuousLinearMap.adjoint_inner_right, this,
        ← ContinuousLinearMap.adjoint_inner_right, hBsa]
    rw [hchar]
    refine ⟨B u, ?_, by rw [hTe]; exact hTw.symm⟩
    rw [← efe, hB]; rfl
  · intro huw x y hxy
    obtain ⟨m, rfl⟩ := hran _ _ hxy
    obtain ⟨m', rfl⟩ := hran _ _ huw
    have hy : y = B m := (hcl g).2.2.2.2.2 _ _ _ hxy (hi m)
    have hw : w = B m' := (hcl g).2.2.2.2.2 _ _ _ huw (hi m')
    have l1 : inner k (Te m) (B m') = inner k m (Te (B m')) := by
      have := ContinuousLinearMap.adjoint_inner_left Te (B m') m
      rwa [hTsa] at this
    have l2 : inner k (B m) (Te m') = inner k m (B (Te m')) := by
      have := ContinuousLinearMap.adjoint_inner_left B (Te m') m
      rwa [hBsa] at this
    rw [hy, hw, l1, l2, hcomm]

theorem g58b_mul_graph (A B : H →L[k] H) :
    mul (boundedGraph A) (boundedGraph B) = boundedGraph (A.comp B) := by
  ext ⟨x, y⟩
  simp only [mul, boundedGraph, Set.mem_setOf_eq, ContinuousLinearMap.comp_apply]
  constructor
  · rintro ⟨z, hz, hy⟩; rw [hy, hz]
  · intro h; exact ⟨B x, rfl, h⟩

theorem g58b_part_proto (F : P05.Symbol X k → Relation H) (hF : Calculus F) (S : Submodule k H) :
    ProtoCalculus (part F S) := by
  obtain ⟨hcl, ⟨h1, hadd, hsc, hmul, hdom⟩, -, -⟩ := hF
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext ⟨u, w⟩
    simp only [part, Set.mem_setOf_eq, h1, identity]
    exact Subtype.ext_iff.symm
  · rintro f g ⟨u, w⟩ ⟨a, b, ha, hb, hw⟩
    exact hadd f g ⟨a.val, b.val, ha, hb, by rw [hw]; rfl⟩
  · rintro c f ⟨u, w⟩ ⟨a, ha, hw⟩
    exact hsc c f ⟨a.val, ha, by rw [hw]; rfl⟩
  · rintro f g ⟨u, w⟩ ⟨a, ha, hw⟩
    exact hmul f g ⟨a.val, ha, hw⟩
  · intro f g
    ext u
    simp only [graphDomain, mul, part, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨w, a, ha, hw⟩
      exact ⟨⟨a, ha⟩, ⟨w, hmul f g ⟨a.val, ha, hw⟩⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨w, hw⟩⟩
      have hx : u.val ∈ graphDomain (mul (F f) (F g)) := by
        rw [hdom]; exact ⟨⟨a.val, ha⟩, ⟨w.val, hw⟩⟩
      obtain ⟨w', z, hz, hzw⟩ := hx
      have e1 : z = a.val := (hcl g).2.2.2.2.2 _ _ _ hz ha
      have e2 : w' = w.val := (hcl _).2.2.2.2.2 _ _ _ (hmul f g ⟨z, hz, hzw⟩) hw
      refine ⟨w, a, ha, ?_⟩
      rw [← e1, ← e2]; exact hzw

theorem g58b_closed_subspace (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (S : Submodule k H) (hS : IsClosed (S : Set H)) (P : H →L[k] H)
    (hP : ProjectionOnto (k := k) (boundedGraph P) (S : Set H)) :
    ProtoCalculus (part F S) ∧
    ((Calculus (part F S) ↔ ∀ f, BoundedSymbol f → BoundedOperator (k := k) (part F S f)) ∧
     (Calculus (part F S) ↔ ∀ f, BoundedSymbol f →
       ∀ x y, x ∈ S → (x, y) ∈ F f → y ∈ S) ∧
     (Calculus (part F S) ↔ ∀ f, BoundedSymbol f → mul (F f) (boundedGraph P) = mul (boundedGraph P) (F f))) := by
  haveI : CompleteSpace S := hS.completeSpace_coe
  have hproto := g58b_part_proto F hF S
  obtain ⟨⟨-, hPadj, hPid⟩, hPr⟩ := hP
  have hPsa : ContinuousLinearMap.adjoint P = P := by
    rw [g58b_adj_graph] at hPadj; exact g58b_graph_inj hPadj
  have hPP : ∀ x, P (P x) = P x := by
    rw [g58b_mul_graph] at hPid
    intro x; exact congrArg (fun T : H →L[k] H => T x) (g58b_graph_inj hPid)
  have hPS : ∀ x, x ∈ S ↔ ∃ z, x = P z := by
    intro x
    rw [← SetLike.mem_coe, ← hPr]; rfl
  have hPfix : ∀ x, x ∈ S → P x = x := by
    intro x hx; obtain ⟨z, rfl⟩ := (hPS x).mp hx; exact hPP z
  have hcl := hF.1
  -- (Calc → a)
  have Ca : Calculus (part F S) → ∀ f, BoundedSymbol f → BoundedOperator (k := k) (part F S f) :=
    fun hC f hf => (hC.2.2.1 f hf).1
  -- (a → b)
  have ab : (∀ f, BoundedSymbol f → BoundedOperator (k := k) (part F S f)) →
      ∀ f, BoundedSymbol f → ∀ x y, x ∈ S → (x, y) ∈ F f → y ∈ S := by
    intro ha f hf x y hx hxy
    obtain ⟨R, hR⟩ := ha f hf
    have : ((⟨x, hx⟩ : S), R ⟨x, hx⟩) ∈ part F S f := by rw [hR]; rfl
    have e : y = (R ⟨x, hx⟩).val := (hcl f).2.2.2.2.2 _ _ _ hxy this
    rw [e]; exact (R ⟨x, hx⟩).property
  -- (b → c)
  have bc : (∀ f, BoundedSymbol f → ∀ x y, x ∈ S → (x, y) ∈ F f → y ∈ S) →
      ∀ f, BoundedSymbol f → mul (F f) (boundedGraph P) = mul (boundedGraph P) (F f) := by
    intro hb f hf
    obtain ⟨⟨T, hT⟩, -⟩ := hF.2.2.1 f hf
    have hTs := g58b_bdd_star F hF f hf hT
    have bs : BoundedSymbol (starSymbol f) := by
      obtain ⟨c, hc⟩ := hf; exact ⟨c, fun x => by simp only [starSymbol, norm_star]; exact hc x⟩
    have invT : ∀ x ∈ S, T x ∈ S := fun x hx => hb f hf x (T x) hx (by rw [hT]; rfl)
    have invTs : ∀ x ∈ S, (ContinuousLinearMap.adjoint T) x ∈ S := fun x hx =>
      hb _ bs x _ hx (by rw [hTs]; rfl)
    have hPmem : ∀ x, P x ∈ S := fun x => (hPS _).mpr ⟨x, rfl⟩
    have hperp : ∀ x, ∀ s ∈ S, inner k s (x - P x) = 0 := by
      intro x s hs
      obtain ⟨s', rfl⟩ := (hPS s).mp hs
      rw [← hPsa, ContinuousLinearMap.adjoint_inner_left, hPsa, map_sub, hPP, sub_self,
        inner_zero_right]
    have hPT : ∀ x, P (T (x - P x)) = 0 := by
      intro x
      apply ext_inner_left k
      intro y
      rw [inner_zero_right, ← hPsa, ContinuousLinearMap.adjoint_inner_right, hPsa,
        ← ContinuousLinearMap.adjoint_inner_left]
      exact hperp x _ (invTs _ (hPmem y))
    have hcomm : T.comp P = P.comp T := by
      ext x
      simp only [ContinuousLinearMap.comp_apply]
      have : T x = T (P x) + T (x - P x) := by rw [← map_add]; congr 1; abel
      rw [this, map_add, hPT, add_zero, hPfix _ (invT _ (hPmem x))]
    rw [hT, g58b_mul_graph, g58b_mul_graph, hcomm]
  -- (c → b)
  have cb : (∀ f, BoundedSymbol f → mul (F f) (boundedGraph P) = mul (boundedGraph P) (F f)) →
      ∀ f, BoundedSymbol f → ∀ x y, x ∈ S → (x, y) ∈ F f → y ∈ S := by
    intro hc f hf x y hx hxy
    obtain ⟨⟨T, hT⟩, -⟩ := hF.2.2.1 f hf
    have h := hc f hf
    rw [hT, g58b_mul_graph, g58b_mul_graph] at h
    have hcomm := g58b_graph_inj h
    rw [hT] at hxy
    have hy : y = T x := hxy
    rw [hy, ← hPfix x hx]
    have := congrArg (fun A : H →L[k] H => A x) hcomm
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this]; exact (hPS _).mpr ⟨_, rfl⟩
  -- (b → Calc)
  have bC : (∀ f, BoundedSymbol f → ∀ x y, x ∈ S → (x, y) ∈ F f → y ∈ S) → Calculus (part F S) := by
    intro hb
    have bdd : ∀ f, BoundedSymbol f → ∃ T : H →L[k] H, F f = boundedGraph T ∧
        ∃ R : S →L[k] S, part F S f = boundedGraph R ∧ ∀ x : S, (R x).val = T x.val := by
      intro f hf
      obtain ⟨⟨T, hT⟩, -⟩ := hF.2.2.1 f hf
      have invT : ∀ x : S, T x.val ∈ S := fun x => hb f hf x.val _ x.property (by rw [hT]; rfl)
      refine ⟨T, hT, (T.comp S.subtypeL).codRestrict S invT, ?_, fun x => rfl⟩
      ext ⟨u, w⟩
      simp only [part, Set.mem_setOf_eq, hT, boundedGraph]
      rw [Subtype.ext_iff]; rfl
    refine ⟨fun f => ⟨inferInstance, ?_, ?_, ?_, ?_, ?_⟩, hproto, fun f hf => ?_, fun fn f hbp => ?_⟩
    · have hc : Continuous (fun p : S × S => (p.1.val, p.2.val)) := by fun_prop
      exact (hcl f).2.1.preimage hc
    · exact (hcl f).2.2.1
    · intro x y x2 y2 h1 h2; exact (hcl f).2.2.2.1 _ _ _ _ h1 h2
    · intro c x y h; exact (hcl f).2.2.2.2.1 c _ _ h
    · intro x y z h1 h2; exact Subtype.ext ((hcl f).2.2.2.2.2 _ _ _ h1 h2)
    · obtain ⟨T, hT, R, hR, hRT⟩ := bdd f hf
      have bs : BoundedSymbol (starSymbol f) := by
        obtain ⟨c, hc⟩ := hf; exact ⟨c, fun x => by simp only [starSymbol, norm_star]; exact hc x⟩
      have hTs := g58b_bdd_star F hF f hf hT
      refine ⟨⟨R, hR⟩, ?_⟩
      ext ⟨u, w⟩
      rw [hR]
      simp only [graphAdjoint, part, boundedGraph, Set.mem_setOf_eq, hTs]
      constructor
      · intro h
        have key : ∀ x : S, inner k (x : H) (w.val - (ContinuousLinearMap.adjoint T) u.val) = 0 := by
          intro x
          have := h x (R x) rfl
          rw [Submodule.coe_inner, Submodule.coe_inner, hRT] at this
          rw [inner_sub_right, ContinuousLinearMap.adjoint_inner_right, this, sub_self]
        have hmem : w.val - (ContinuousLinearMap.adjoint T) u.val ∈ S :=
          S.sub_mem w.property (hb _ bs _ _ u.property (by rw [hTs]; rfl))
        have := key ⟨_, hmem⟩
        rw [inner_self_eq_zero, sub_eq_zero] at this
        exact this
      · intro h x y hy
        rw [Submodule.coe_inner, Submodule.coe_inner, h, hy, hRT,
          ContinuousLinearMap.adjoint_inner_right]
    · have bn : ∀ n, BoundedSymbol (fn n) := fun n => ⟨_, hbp.2.choose_spec n⟩
      have bf : BoundedSymbol f := by
        obtain ⟨hpt, c, hc⟩ := hbp
        exact ⟨c, fun x => le_of_tendsto' ((hpt x).norm) (fun n => hc n x)⟩
      choose Tn hTn Rn hRn hRTn using fun n => bdd (fn n) (bn n)
      obtain ⟨T, hT, R, hR, hRT⟩ := bdd f bf
      obtain ⟨-, -, hw⟩ := hF.2.2.2 fn f hbp
      refine ⟨fun n => ⟨Rn n, hRn n⟩, ⟨R, hR⟩, fun x y => ?_⟩
      simp only [hRn, hR, g58b_value_graph, Submodule.coe_inner, hRTn, hRT]
      have := hw x.val y.val
      simp only [hTn, hT, g58b_value_graph] at this
      exact this
  refine ⟨hproto, ⟨fun hC => Ca hC, fun ha => bC (ab ha)⟩, ⟨fun hC => ab (Ca hC), bC⟩,
    ⟨fun hC => bc (ab (Ca hC)), fun hc => bC (cb hc)⟩⟩

theorem g58b_spectral_properties (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (f : P05.Symbol X k) (c : ℝ) (hc : 0 ≤ c) (z : k) :
    (spectrumOf (k := k) (F f) = approximateSpectrum (k := k) (F f) ∧
      approximateSpectrum (k := k) (F f) = essentialRange F f) ∧
    Almost F (fun x => f.val x ∈ essentialRange F f) ∧
    (NormBound (k := k) (F f) c ↔ Almost F (fun x => ‖f.val x‖ ≤ c)) ∧
    (SelfAdjoint (k := k) (F f) ↔ Almost F (fun x => star (f.val x) = f.val x)) ∧
    ((z ∈ pointSpectrum (k := k) (F f) ↔ ¬ Null F {x | f.val x = z}) ∧
      ∀ hz : MeasurableSet {x | f.val x = z},
        ProjectionOnto (k := k) (F (P05.indicator {x | f.val x = z} hz))
          (kernel (resolventShift z (F f)))) := by
  have hspec : spectrumOf (k := k) (F f) = essentialRange F f := by
    ext w; rw [g58b_ess_iff F hF f w]; rfl
  have happ := g58b_approx F hF f
  have hM : MeasurableSet {x | f.val x = z} := measurableSet_eq_fun f.property measurable_const
  -- kernel of the resolvent shift
  set zf := plus (constant z) (scalar (-1) f)
  have hzfm : MeasurableSet {x | zf.val x ≠ 0} := g58b_meas_ne zf
  have eind : P05.indicator (k := k) {x | zf.val x ≠ 0} hzfm = P05.indicator {x | f.val x = z}ᶜ hM.compl := by
    congr 1
    ext x
    simp only [zf, plus, constant, scalar, Set.mem_setOf_eq, Set.mem_compl_iff, ne_eq]
    constructor
    · intro h h'; apply h; rw [h']; ring
    · intro h h'; apply h; linear_combination -h'
  have hker : kernel (resolventShift z (F f)) = kernel (F (P05.indicator {x | f.val x = z}ᶜ hM.compl)) := by
    rw [g58b_resolvent_eq F hF f z, (g58b_nullchar F hF).1 zf hzfm, eind]
  obtain ⟨⟨P, hP⟩, -⟩ := hF.2.2.1 _ (g58b_indicator_bounded (k := k) _ hM)
  obtain ⟨⟨Q, hQ⟩, -⟩ := hF.2.2.1 _ (g58b_indicator_bounded (k := k) _ hM.compl)
  have hPQ : ∀ y, P y + Q y = y := by
    have e : plus (P05.indicator (k := k) {x | f.val x = z} hM) (P05.indicator _ hM.compl) =
        constant 1 := by
      apply Subtype.ext; funext x
      by_cases hx : f.val x = z <;> simp [P05.indicator, Set.indicator, constant, plus, hx]
    have := g58b_bdd_add F hF _ _ hP hQ
    rw [e, hF.2.1.1] at this
    intro y
    have h2 : (y, y) ∈ boundedGraph (P + Q) := by rw [← this]; rfl
    exact h2.symm
  have hQP : ∀ y, Q (P y) = 0 := by
    have e : times (P05.indicator (k := k) {x | f.val x = z}ᶜ hM.compl)
        (P05.indicator {x | f.val x = z} hM) = constant 0 := by
      apply Subtype.ext; funext x
      by_cases hx : f.val x = z <;> simp [P05.indicator, Set.indicator, constant, times, hx]
    have := g58b_bdd_mul F hF _ _ hQ hP
    rw [e, g58b_zero_const F hF] at this
    intro y
    have h2 : (y, Q (P y)) ∈ (zeroGraph : Relation H) := by rw [this]; rfl
    exact h2
  have hrange : rangeOf (F (P05.indicator {x | f.val x = z} hM)) =
      kernel (resolventShift z (F f)) := by
    rw [hker, hP, hQ]
    ext y
    simp only [rangeOf, kernel, boundedGraph, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, rfl⟩; exact (hQP x).symm
    · intro h; refine ⟨y, ?_⟩
      have := hPQ y; rw [← h, add_zero] at this; exact this.symm
  have hproj : ProjectionOnto (k := k) (F (P05.indicator {x | f.val x = z} hM))
      (kernel (resolventShift z (F f))) := by
    refine ⟨⟨⟨P, hP⟩, ?_, ?_⟩, hrange⟩
    · rw [(hF.2.2.1 _ (g58b_indicator_bounded _ _)).2]
      congr 1
      apply Subtype.ext; funext x
      simp only [starSymbol, P05.indicator, Set.indicator]
      split_ifs <;> simp
    · rw [hP, g58b_mul_graph]
      congr 1
      ext y; exact g58b_idem F hF _ _ hP y
  refine ⟨⟨hspec.trans happ.symm, happ⟩, ?_, g58b_normbound_iff F hF f c hc, ?_, ⟨?_, fun _ => hproj⟩⟩
  · -- almost everywhere in the essential range
    obtain ⟨-, -, -, hconc⟩ := g58b_spectral_support F hF f
    obtain ⟨-, hm, hz⟩ := hconc
    have eS : (f.val ⁻¹' (spectrumOf (k := k) (F f))ᶜ) =
        {x | ¬ (fun x => f.val x ∈ essentialRange F f) x} := by rw [hspec]; rfl
    have hm' : MeasurableSet {x | ¬ (fun x => f.val x ∈ essentialRange F f) x} :=
      eS ▸ f.property hm
    refine ⟨hm', ?_⟩
    have e : P05.indicator (k := k) {x | ¬ (fun x => f.val x ∈ essentialRange F f) x} hm' =
        compose (P05.indicator (spectrumOf (k := k) (F f))ᶜ hm) f.val f.property := by
      apply Subtype.ext; funext x
      simp only [compose, Function.comp_apply, P05.indicator, Set.indicator, hspec,
        Set.mem_compl_iff, Set.mem_setOf_eq]
    rw [e]; exact hz
  · constructor
    · intro h; exact g58b_sa_null F hF f h.2.2
    · intro h
      set g : P05.Symbol X k := ⟨fun x => ((RCLike.re (f.val x) : ℝ) : k), by
        have hf := f.property; fun_prop⟩
      have hfg : F f = F g := by
        rw [(g58b_nullchar F hF).2.2.1 f g]
        unfold Almost
        have e : {x | ¬ (fun x => f.val x = g.val x) x} = {x | ¬ (fun x => star (f.val x) = f.val x) x} := by
          ext x
          simp only [g, Set.mem_setOf_eq]
          rw [RCLike.star_def, RCLike.conj_eq_iff_re, eq_comm]
        rw [e]; exact h
      rw [hfg]
      exact g58b_sa_of_real F hF g (fun x => by simp [g])
  · -- point spectrum
    have hNull : Null F {x | f.val x = z} ↔ P = 0 := by
      constructor
      · rintro ⟨_, h0⟩
        rw [hP] at h0
        ext y
        have : (y, P y) ∈ (zeroGraph : Relation H) := by rw [← h0]; rfl
        exact this
      · intro h0
        refine ⟨hM, ?_⟩
        rw [hP, h0]; ext ⟨u, v⟩; simp [boundedGraph, zeroGraph]
    have hpt : ∀ x, (x, z • x) ∈ F f ↔ x ∈ kernel (resolventShift z (F f)) := by
      intro x
      simp only [kernel, Set.mem_setOf_eq]
      constructor
      · intro h
        exact ⟨z • x, (-1 : k) • (z • x), ⟨x, rfl, rfl⟩, ⟨z • x, h, rfl⟩, by simp⟩
      · rintro ⟨a, b, ⟨a', ha', ha⟩, ⟨b', hb', hb⟩, hab⟩
        have ha1 : a' = x := ha'
        have ha2 : a = z • a' := ha
        have hb2 : b = (-1 : k) • b' := hb
        have hab2 : (0 : H) = a + b := hab
        rw [ha2, ha1, hb2] at hab2
        have this : b' = z • x := by
          have h2 : z • x + (-1 : k) • b' = 0 := hab2.symm
          rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h2
          exact h2.symm
        rw [← this]; exact hb'
    rw [hNull]
    constructor
    · rintro ⟨x, hx0, hx⟩ hP0
      have hk := (hpt x).mp hx
      rw [← hrange, hP] at hk
      obtain ⟨y, hy⟩ := hk
      apply hx0
      have hy' : x = P y := hy
      rw [hy', hP0]; rfl
    · intro hP0
      obtain ⟨y, hy⟩ : ∃ y, P y ≠ 0 := by
        by_contra hcon; push_neg at hcon; exact hP0 (ContinuousLinearMap.ext hcon)
      refine ⟨P y, hy, (hpt _).mpr ?_⟩
      rw [← hrange, hP]; exact ⟨y, rfl⟩

theorem g58b_loc_facts (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k)
    (A : Set X) (hA : MeasurableSet A) {P : H →L[k] H} (hP : F (P05.indicator A hA) = boundedGraph P) :
    (∀ x y, (x, y) ∈ F (times f (P05.indicator A hA)) ↔ (P x, y) ∈ F f) ∧
    (∀ x y, (x, y) ∈ F f → (P x, P y) ∈ F f) ∧ (∀ x, P (P x) = P x) := by
  obtain ⟨-, hbmul, -⟩ := g58b_first F hF
  have hb : BoundedOperator (k := k) (F (P05.indicator A hA)) := ⟨P, hP⟩
  have ha : ∀ x y, (x, y) ∈ F (times f (P05.indicator A hA)) ↔ (P x, y) ∈ F f := by
    intro x y
    rw [← (hbmul f _ hb).2.1, hP]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = P x := hz
      rw [← this]; exact hzy
    · intro h; exact ⟨P x, rfl, h⟩
  refine ⟨ha, ?_, ?_⟩
  · intro x y hxy
    have h1 : (x, P y) ∈ mul (F (P05.indicator A hA)) (F f) := ⟨y, hxy, by rw [hP]; rfl⟩
    have := (hbmul f _ hb).2.2 h1
    rw [(hbmul f _ hb).2.1, ha] at this
    exact this
  · intro x
    have e : times (P05.indicator (k := k) A hA) (P05.indicator A hA) = P05.indicator A hA := by
      apply Subtype.ext; funext y
      simp only [times, P05.indicator, Set.indicator]
      split_ifs <;> simp
    have := g58b_bdd_mul F hF _ _ hP hP
    rw [e, hP] at this
    have := congrArg (fun T : H →L[k] H => T x) (g58b_graph_inj this)
    exact this.symm

theorem g58b_localized (F : P05.Symbol X k → Relation H) (G : P05.Symbol X k → Relation K)
    (hF : Calculus F) (hG : Calculus G) (T : H →L[k] K) (f : P05.Symbol X k)
    (A : Set X) (hA : MeasurableSet A) :
    ∃ (P : H →L[k] H) (Q : K →L[k] K),
      F (P05.indicator A hA) = boundedGraph P ∧ G (P05.indicator A hA) = boundedGraph Q ∧
      (Intertwines F G T f → Intertwines F G (Q.comp (T.comp P)) (times f (P05.indicator A hA))) ∧
      (Intertwines F G (Q.comp (T.comp P)) (times f (P05.indicator A hA)) →
        Intertwines F G (Q.comp (T.comp P)) f) := by
  obtain ⟨⟨P, hP⟩, -⟩ := hF.2.2.1 _ (g58b_indicator_bounded (k := k) A hA)
  obtain ⟨⟨Q, hQ⟩, -⟩ := hG.2.2.1 _ (g58b_indicator_bounded (k := k) A hA)
  obtain ⟨Fa, Fb, Fc⟩ := g58b_loc_facts F hF f A hA hP
  obtain ⟨Ga, Gb, Gc⟩ := g58b_loc_facts G hG f A hA hQ
  have hfunF := (hF.1 f).2.2.2.2.2
  refine ⟨P, Q, hP, hQ, ?_, ?_⟩
  · intro hint x y hxy
    rw [Fa] at hxy
    have hPy : P y = y := by
      have := Fb _ _ hxy
      rw [Fc] at this
      exact hfunF _ _ _ this hxy
    have h1 := Gb _ _ (hint _ _ hxy)
    rw [Ga]
    simp only [ContinuousLinearMap.comp_apply, Gc, hPy]
    exact h1
  · intro hint x y hxy
    have h1 := Fb _ _ hxy
    have h2 : (x, P y) ∈ F (times f (P05.indicator A hA)) := by rw [Fa]; exact h1
    have h3 := hint _ _ h2
    rw [Ga] at h3
    simp only [ContinuousLinearMap.comp_apply, Gc, Fc] at h3
    exact h3

def g58b_symLS {d : ℕ} (f : Fin d → P05.Symbol X k) : List (Fin d) → P05.Symbol X k
  | [] => constant 0
  | j :: l => plus (f j) (g58b_symLS f l)

def g58b_symP {d : ℕ} (f : Fin d → P05.Symbol X k) : List (Fin d) → P05.Symbol X k
  | [] => constant 1
  | j :: l => times (f j) (g58b_symP f l)

theorem g58b_symLS_val {d : ℕ} (f : Fin d → P05.Symbol X k) (l : List (Fin d)) (t : X) :
    (g58b_symLS f l).val t = (l.map fun j => (f j).val t).sum := by
  induction l with
  | nil => simp [g58b_symLS, constant]
  | cons j l ih => simp [g58b_symLS, plus, ih]

theorem g58b_symP_val {d : ℕ} (f : Fin d → P05.Symbol X k) (l : List (Fin d)) (t : X) :
    (g58b_symP f l).val t = (l.map fun j => (f j).val t).prod := by
  induction l with
  | nil => simp [g58b_symP, constant]
  | cons j l ih => simp [g58b_symP, times, ih]

theorem g58b_finite_ops (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    {d : ℕ} (f : Fin d → P05.Symbol X k) :
    (∀ j, GraphCore (F (f j)) (⋂ i, graphDomain (F (f i)))) ∧
    closure (sumGraphs ((List.finRange d).map fun j => F (f j))) = F (tupleSum f) ∧
    closure (productGraphs ((List.finRange d).map fun j => F (f j))) = F (tupleProduct f) := by
  obtain ⟨-, -, -, -, -, hstrong⟩ := g58b_first F hF
  set N : ℕ → Set X := fun n => {t | ∀ i, ‖(f i).val t‖ ≤ n}
  have hN : ∀ n, MeasurableSet (N n) := by
    intro n
    have : N n = ⋂ i, {t | ‖(f i).val t‖ ≤ n} := by ext t; simp [N]
    rw [this]; exact MeasurableSet.iInter fun i => measurableSet_le (f i).property.norm measurable_const
  choose P hP using fun n => (hF.2.2.1 _ (g58b_indicator_bounded (k := k) (N n) (hN n))).1
  have hconv : ∀ z, Tendsto (fun n => P n z) atTop (𝓝 z) := by
    have hbp : BP (fun n => P05.indicator (k := k) (N n) (hN n)) (constant 1) := by
      refine ⟨fun t => ?_, 1, fun n t => ?_⟩
      · apply tendsto_nhds_of_eventually_eq
        obtain ⟨m, hm⟩ := exists_nat_ge (∑ i, ‖(f i).val t‖)
        filter_upwards [Filter.eventually_ge_atTop m] with n hn
        have : t ∈ N n := fun i => by
          have h1 : ‖(f i).val t‖ ≤ ∑ i, ‖(f i).val t‖ :=
            Finset.single_le_sum (f := fun i => ‖(f i).val t‖) (fun i _ => norm_nonneg _)
              (Finset.mem_univ i)
          have h2 : (m : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        simp [P05.indicator, Set.indicator, this, constant]
      · simp only [P05.indicator, Set.indicator]; split_ifs <;> simp
    intro z
    have := (hstrong _ _ hbp).2.2 z
    simp only [hP, g58b_value_graph, hF.2.1.1] at this
    rwa [g58b_value_eq (fun x y z (h1 : y = x) (h2 : z = x) => h1.trans h2.symm)
      (show z = z from rfl)] at this
  have facts := fun (g : P05.Symbol X k) (n : ℕ) => g58b_loc_facts F hF g (N n) (hN n) (hP n)
  have hdomP : ∀ n x i, P n x ∈ graphDomain (F (f i)) := by
    intro n x i
    have hb : ∀ t, ‖(times (f i) (P05.indicator (N n) (hN n))).val t‖ ≤ n := by
      intro t
      simp only [times, P05.indicator, Set.indicator, N, Set.mem_setOf_eq]
      split_ifs with ht
      · rw [mul_one]; exact ht i
      · simp
    obtain ⟨⟨V, hV⟩, -⟩ := hF.2.2.1 _ ⟨_, hb⟩
    have : (x, V x) ∈ F (times (f i) (P05.indicator (N n) (hN n))) := by rw [hV]; rfl
    exact ⟨_, ((facts (f i) n).1 x (V x)).mp this⟩
  have CL : ∀ (S : Set (H × H)) (x y : H), (∀ n, (P n x, P n y) ∈ S) → (x, y) ∈ closure S := by
    intro S x y h
    exact mem_closure_of_tendsto ((hconv x).prodMk_nhds (hconv y)) (Filter.Eventually.of_forall h)
  have closeEq : ∀ (S : Set (H × H)) (g : P05.Symbol X k), S ⊆ F g →
      (∀ n x, P n x ∈ graphDomain S) → closure S = F g := by
    intro S g hS hdomS
    refine Set.Subset.antisymm (closure_minimal hS (hF.1 g).2.1) ?_
    rintro ⟨x, y⟩ hxy
    apply CL
    intro n
    obtain ⟨w, hw⟩ := hdomS n x
    have h1 := (facts g n).2.1 x y hxy
    have : w = P n y := (hF.1 g).2.2.2.2.2 _ _ _ (hS hw) h1
    rw [← this]; exact hw
  refine ⟨fun j => ⟨Set.iInter_subset _ j, ?_⟩, ?_, ?_⟩
  · refine Set.Subset.antisymm (closure_minimal (fun p hp => hp.1) (hF.1 _).2.1) ?_
    rintro ⟨x, y⟩ hxy
    apply CL
    intro n
    exact ⟨(facts (f j) n).2.1 x y hxy, Set.mem_iInter.mpr fun i => hdomP n x i⟩
  · have hsub : ∀ l : List (Fin d), sumGraphs (l.map fun j => F (f j)) ⊆ F (g58b_symLS f l) := by
      intro l
      induction l with
      | nil => simp only [List.map_nil, sumGraphs, g58b_symLS]; rw [g58b_zero_const F hF]
      | cons j l ih =>
        rintro ⟨x, y⟩ ⟨a, b, ha, hb, hab⟩
        exact hF.2.1.2.1 _ _ ⟨a, b, ha, ih hb, hab⟩
    have hdomS : ∀ (l : List (Fin d)) n x, P n x ∈ graphDomain (sumGraphs (l.map fun j => F (f j))) := by
      intro l n x
      induction l with
      | nil => exact ⟨0, rfl⟩
      | cons j l ih =>
        obtain ⟨a, ha⟩ := hdomP n x j
        obtain ⟨b, hb⟩ := ih
        exact ⟨a + b, a, b, ha, hb, rfl⟩
    have e : g58b_symLS f (List.finRange d) = tupleSum f := by
      apply Subtype.ext; funext t
      rw [g58b_symLS_val]; simp only [tupleSum]; rw [Fin.sum_univ_def]
    rw [← e]
    exact closeEq _ _ (hsub _) (hdomS _)
  · have hsub : ∀ l : List (Fin d), productGraphs (l.map fun j => F (f j)) ⊆ F (g58b_symP f l) := by
      intro l
      induction l with
      | nil => simp only [List.map_nil, productGraphs, g58b_symP]; rw [hF.2.1.1]
      | cons j l ih =>
        rintro ⟨x, y⟩ ⟨z, hz, hzy⟩
        exact hF.2.1.2.2.2.1 _ _ ⟨z, ih hz, hzy⟩
    have hdomPr : ∀ (l : List (Fin d)) n x, ∃ w, (P n x, w) ∈ productGraphs (l.map fun j => F (f j)) ∧
        P n w = w := by
      intro l n x
      induction l with
      | nil => exact ⟨P n x, rfl, g58b_idem F hF (N n) (hN n) (hP n) x⟩
      | cons j l ih =>
        obtain ⟨w, hw, hPw⟩ := ih
        have hwd : w ∈ graphDomain (F (f j)) := by rw [← hPw]; exact hdomP n w j
        obtain ⟨v, hv⟩ := hwd
        have h1 := (facts (f j) n).2.1 w v hv
        rw [hPw] at h1
        have hPv : P n v = v := (hF.1 _).2.2.2.2.2 _ _ _ h1 hv
        exact ⟨v, ⟨w, hw, hv⟩, hPv⟩
    have e : g58b_symP f (List.finRange d) = tupleProduct f := by
      apply Subtype.ext; funext t
      rw [g58b_symP_val]; simp only [tupleProduct]; rw [Fin.prod_univ_def]
    rw [← e]
    refine closeEq _ _ (hsub _) (fun n x => ?_)
    obtain ⟨w, hw, -⟩ := hdomPr _ n x
    exact ⟨w, hw⟩

theorem g58b_poly_lower (p : Polynomial k) (hp : p ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : k, ‖z‖ ^ p.natDegree ≤ C * (1 + ‖p.eval z‖) := by
  set n := p.natDegree
  set cn := p.coeff n
  have hcn : cn ≠ 0 := by simp only [cn, n]; exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hcn' : 0 < ‖cn‖ := norm_pos_iff.mpr hcn
  set M := ∑ j ∈ Finset.range n, ‖p.coeff j‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  set R := max 1 (2 * M / ‖cn‖)
  have hR1 : 1 ≤ R := le_max_left _ _
  refine ⟨max (R ^ n) (2 / ‖cn‖), by positivity, fun z => ?_⟩
  have hmax1 : R ^ n ≤ max (R ^ n) (2 / ‖cn‖) := le_max_left _ _
  have hmax2 : 2 / ‖cn‖ ≤ max (R ^ n) (2 / ‖cn‖) := le_max_right _ _
  have hpe : ‖p.eval z‖ ≥ 0 := norm_nonneg _
  by_cases hz : ‖z‖ ≤ R
  · calc ‖z‖ ^ n ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg _) hz n
      _ ≤ max (R ^ n) (2 / ‖cn‖) := hmax1
      _ ≤ max (R ^ n) (2 / ‖cn‖) * (1 + ‖p.eval z‖) := by
          have : 0 ≤ max (R ^ n) (2 / ‖cn‖) := by positivity
          nlinarith
  · push_neg at hz
    have hz1 : 1 ≤ ‖z‖ := hR1.trans hz.le
    have hzM : 2 * M / ‖cn‖ ≤ ‖z‖ := (le_max_right _ _).trans hz.le
    have hsplit : p.eval z = cn * z ^ n + ∑ j ∈ Finset.range n, p.coeff j * z ^ j := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, add_comm]
    have hlow : ‖∑ j ∈ Finset.range n, p.coeff j * z ^ j‖ * ‖z‖ ≤ M * ‖z‖ ^ n := by
      calc ‖∑ j ∈ Finset.range n, p.coeff j * z ^ j‖ * ‖z‖
          ≤ (∑ j ∈ Finset.range n, ‖p.coeff j‖ * ‖z‖ ^ j) * ‖z‖ := by
            gcongr
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            congr 1; funext j; rw [norm_mul, norm_pow]
        _ = ∑ j ∈ Finset.range n, ‖p.coeff j‖ * (‖z‖ ^ j * ‖z‖) := by
            rw [Finset.sum_mul]; congr 1; funext j; ring
        _ ≤ ∑ j ∈ Finset.range n, ‖p.coeff j‖ * ‖z‖ ^ n := by
            gcongr with j hj
            rw [← pow_succ]
            exact pow_le_pow_right₀ hz1 (Finset.mem_range.mp hj)
        _ = M * ‖z‖ ^ n := by rw [← Finset.sum_mul]
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
    have hMz : M ≤ ‖cn‖ * ‖z‖ / 2 := by
      rw [div_le_iff₀ hcn'] at hzM; linarith
    have hlow2 : ‖∑ j ∈ Finset.range n, p.coeff j * z ^ j‖ ≤ ‖cn‖ * ‖z‖ ^ n / 2 := by
      have h1 : ‖∑ j ∈ Finset.range n, p.coeff j * z ^ j‖ * ‖z‖ ≤ ‖cn‖ * ‖z‖ / 2 * ‖z‖ ^ n :=
        hlow.trans (mul_le_mul_of_nonneg_right hMz (by positivity))
      have h2 : ‖cn‖ * ‖z‖ / 2 * ‖z‖ ^ n = (‖cn‖ * ‖z‖ ^ n / 2) * ‖z‖ := by ring
      rw [h2] at h1
      exact le_of_mul_le_mul_right h1 hzpos
    have htri : ‖cn * z ^ n‖ ≤ ‖p.eval z‖ + ‖∑ j ∈ Finset.range n, p.coeff j * z ^ j‖ := by
      have : cn * z ^ n = p.eval z - ∑ j ∈ Finset.range n, p.coeff j * z ^ j := by
        rw [hsplit]; ring
      rw [this]; exact norm_sub_le _ _
    rw [norm_mul, norm_pow] at htri
    have : ‖z‖ ^ n ≤ 2 / ‖cn‖ * ‖p.eval z‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hcn']
      nlinarith
    calc ‖z‖ ^ n ≤ 2 / ‖cn‖ * ‖p.eval z‖ := this
      _ ≤ max (R ^ n) (2 / ‖cn‖) * ‖p.eval z‖ := by gcongr
      _ ≤ max (R ^ n) (2 / ‖cn‖) * (1 + ‖p.eval z‖) := by
          have : 0 ≤ max (R ^ n) (2 / ‖cn‖) := by positivity
          nlinarith

theorem g58b_dom_D (F : P05.Symbol X k → Relation H) (hF : Calculus F) (a b : P05.Symbol X k)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ x, ‖a.val x‖ ≤ C * (1 + ‖b.val x‖)) :
    graphDomain (F b) ⊆ graphDomain (F a) := by
  have h1 := hF.2.1.1
  have hadd := hF.2.1.2.1
  have hmul := hF.2.1.2.2.2.1
  have hbd := hF.2.2.1
  set G1 := plus (constant (1 : k)) (absolute b)
  set s := times (starSymbol b) (reciprocal (absolute b))
  have hsb : ∀ t, ‖s.val t‖ ≤ 1 := by
    intro t
    simp only [s, times, starSymbol, reciprocal, absolute, norm_mul, norm_star, norm_inv,
      RCLike.norm_ofReal, abs_norm]
    by_cases h0 : ‖b.val t‖ = 0
    · simp [h0]
    · rw [mul_inv_cancel₀ h0]
  obtain ⟨⟨Sop, hSop⟩, -⟩ := hbd _ ⟨1, hsb⟩
  have hsg : times s b = absolute b := by
    apply Subtype.ext; funext t
    simp only [s, times, starSymbol, reciprocal, absolute]
    by_cases h0 : b.val t = 0
    · simp [h0]
    · rw [mul_comm, ← mul_assoc, RCLike.star_def, RCLike.mul_conj]
      have : (‖b.val t‖ : k) ≠ 0 := RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)
      field_simp
  set u := times a (regularizer b)
  have hub : ∀ t, ‖u.val t‖ ≤ C := by
    intro t
    simp only [u, times, regularizer, norm_mul, norm_inv, RCLike.norm_ofReal]
    rw [abs_of_pos (by positivity), mul_inv_le_iff₀ (by positivity)]
    exact h t
  obtain ⟨⟨U, hU⟩, -⟩ := hbd _ ⟨C, hub⟩
  have hua : times u G1 = a := by
    have := congrArg Subtype.val (g58b_reg_one' b)
    apply Subtype.ext; funext t
    have ht := congrFun this t
    simp only [u, G1, times, constant] at ht ⊢
    rw [mul_assoc, ht, mul_one]
  rintro x ⟨y, hxy⟩
  have h2 : (x, Sop y) ∈ F (absolute b) := by
    rw [← hsg]; exact hmul _ _ ⟨y, hxy, by rw [hSop]; rfl⟩
  have h3 : (x, x + Sop y) ∈ F G1 := hadd _ _ ⟨x, Sop y, by rw [h1]; rfl, h2, rfl⟩
  have h4 := hmul u G1 (show (x, U (x + Sop y)) ∈ mul (F u) (F G1) from
    ⟨x + Sop y, h3, by rw [hU]; rfl⟩)
  rw [hua] at h4
  exact ⟨_, h4⟩

theorem g58b_eq_of_sub {A B : Relation H} (hAB : A ⊆ B)
    (hfun : ∀ x y z, (x, y) ∈ B → (x, z) ∈ B → y = z)
    (hdom : graphDomain B ⊆ graphDomain A) : A = B := by
  refine Set.Subset.antisymm hAB ?_
  rintro ⟨x, y⟩ hxy
  obtain ⟨y', hy'⟩ := hdom ⟨y, hxy⟩
  have : y' = y := hfun _ _ _ (hAB hy') hxy
  rw [← this]; exact hy'

def g58b_pw (f : P05.Symbol X k) (j : ℕ) : P05.Symbol X k :=
  ⟨fun x => f.val x ^ j, f.property.pow_const j⟩

theorem g58b_pow_le (r : ℝ) (hr : 0 ≤ r) {j n : ℕ} (hjn : j ≤ n) : r ^ j ≤ 1 * (1 + r ^ n) := by
  rw [one_mul]
  by_cases h1 : r ≤ 1
  · have := pow_le_one₀ hr h1 (n := j); have := pow_nonneg hr n; linarith
  · push_neg at h1
    have := pow_le_pow_right₀ h1.le hjn; linarith

theorem g58b_graphPower (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k) :
    ∀ j, graphPower (F f) j = F (g58b_pw f j) := by
  intro j
  induction j with
  | zero =>
    have e : g58b_pw f 0 = constant 1 := Subtype.ext (funext fun x => by simp [g58b_pw, constant])
    rw [e, hF.2.1.1]; rfl
  | succ j ih =>
    have e : times f (g58b_pw f j) = g58b_pw f (j + 1) :=
      Subtype.ext (funext fun x => by simp only [times, g58b_pw]; ring)
    show mul (F f) (graphPower (F f) j) = _
    rw [ih]
    apply g58b_eq_of_sub
    · rw [← e]; exact hF.2.1.2.2.2.1 _ _
    · exact (hF.1 _).2.2.2.2.2
    · rw [hF.2.1.2.2.2.2, e]
      intro x hx
      refine ⟨g58b_dom_D F hF _ _ 1 zero_le_one (fun t => ?_) hx, hx⟩
      simp only [g58b_pw, norm_pow]
      exact g58b_pow_le _ (norm_nonneg _) (Nat.le_succ j)

def g58b_symL (p : Polynomial k) (f : P05.Symbol X k) : List ℕ → P05.Symbol X k
  | [] => constant 0
  | j :: l => plus (scalar (p.coeff j) (g58b_pw f j)) (g58b_symL p f l)

theorem g58b_symL_val (p : Polynomial k) (f : P05.Symbol X k) (l : List ℕ) (x : X) :
    (g58b_symL p f l).val x = (l.map (fun j => p.coeff j * f.val x ^ j)).sum := by
  induction l with
  | nil => simp [g58b_symL, constant]
  | cons j l ih => simp [g58b_symL, plus, scalar, g58b_pw, ih]

theorem g58b_sumGraphs (F : P05.Symbol X k → Relation H) (hF : Calculus F) (p : Polynomial k)
    (f : P05.Symbol X k) (l : List ℕ) :
    sumGraphs (l.map fun j => scale (p.coeff j) (graphPower (F f) j)) ⊆ F (g58b_symL p f l) ∧
    graphDomain (sumGraphs (l.map fun j => scale (p.coeff j) (graphPower (F f) j))) =
      ⋂ j ∈ l, graphDomain (F (g58b_pw f j)) := by
  induction l with
  | nil =>
    refine ⟨?_, ?_⟩
    · simp only [List.map_nil, sumGraphs, g58b_symL]; rw [g58b_zero_const F hF]
    · ext x; simp [sumGraphs, graphDomain, zeroGraph]
  | cons j l ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [List.map_cons, sumGraphs, g58b_symL]
    rw [g58b_graphPower F hF f j]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, y⟩ ⟨a, b, ha, hb, hab⟩
      exact hF.2.1.2.1 _ _ ⟨a, b, hF.2.1.2.2.1 _ _ ha, ih1 hb, hab⟩
    · ext x
      simp only [List.mem_cons, Set.iInter_iInter_eq_or_left, Set.mem_inter_iff]
      rw [← ih2]
      simp only [graphDomain, add, scale, Set.mem_setOf_eq]
      constructor
      · rintro ⟨w, a, b, ⟨y, hy, -⟩, hb, -⟩
        exact ⟨⟨y, hy⟩, ⟨b, hb⟩⟩
      · rintro ⟨⟨y, hy⟩, ⟨b, hb⟩⟩
        exact ⟨_, _, b, ⟨y, hy, rfl⟩, hb, rfl⟩

theorem g58b_domination (F : P05.Symbol X k → Relation H) (hF : Calculus F) :
    (∀ f g, (∀ x, ‖f.val x‖ ≤ ‖g.val x‖) →
      graphDomain (F g) ⊆ graphDomain (F f) ∧
      ∀ x y z, (x, y) ∈ F f → (x, z) ∈ F g → ‖y‖ ≤ ‖z‖) ∧
    (∀ f, graphDomain (F f) = graphDomain (F (absolute f)) ∧
      ∀ x y z, (x, y) ∈ F f → (x, z) ∈ F (absolute f) → ‖y‖ = ‖z‖) ∧
    (∀ (f : P05.Symbol X k) (p : Polynomial k) (n : ℕ), p ≠ 0 → p.natDegree = n →
      F (polynomialSymbol p f) = polynomialGraph p (F f) ∧
      graphDomain (F (polynomialSymbol p f)) = graphDomain (graphPower (F f) n)) := by
  have part1 : ∀ f g : P05.Symbol X k, (∀ x, ‖f.val x‖ ≤ ‖g.val x‖) →
      graphDomain (F g) ⊆ graphDomain (F f) ∧
      ∀ x y z, (x, y) ∈ F f → (x, z) ∈ F g → ‖y‖ ≤ ‖z‖ := by
    intro f g hfg
    set h := times f (reciprocal g)
    have hhb : ∀ t, ‖h.val t‖ ≤ 1 := by
      intro t
      simp only [h, times, reciprocal, norm_mul, norm_inv]
      by_cases h0 : ‖g.val t‖ = 0
      · simp [h0]
      · rw [mul_inv_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)), one_mul]
        exact hfg t
    obtain ⟨⟨Hh, hHh⟩, -⟩ := hF.2.2.1 _ ⟨1, hhb⟩
    have hHn := g58b_nb_le F hF h hHh 1 zero_le_one hhb
    have hhg : times h g = f := by
      apply Subtype.ext; funext t
      simp only [h, times, reciprocal]
      by_cases h0 : g.val t = 0
      · have : f.val t = 0 := by
          have := hfg t; rw [h0, norm_zero] at this; exact norm_le_zero_iff.mp this
        simp [h0, this]
      · rw [mul_assoc, inv_mul_cancel₀ h0, mul_one]
    have key : ∀ x z, (x, z) ∈ F g → (x, Hh z) ∈ F f := by
      intro x z hxz
      have := hF.2.1.2.2.2.1 h g (show (x, Hh z) ∈ mul (F h) (F g) from ⟨z, hxz, by rw [hHh]; rfl⟩)
      rwa [hhg] at this
    refine ⟨fun x ⟨z, hz⟩ => ⟨_, key x z hz⟩, fun x y z hxy hxz => ?_⟩
    have : y = Hh z := (hF.1 f).2.2.2.2.2 _ _ _ hxy (key x z hxz)
    rw [this]
    calc ‖Hh z‖ ≤ ‖Hh‖ * ‖z‖ := Hh.le_opNorm z
      _ ≤ 1 * ‖z‖ := by gcongr
      _ = ‖z‖ := one_mul _
  have habs : ∀ (f : P05.Symbol X k) x, ‖(absolute f).val x‖ = ‖f.val x‖ := by
    intro f x; simp [absolute]
  refine ⟨part1, fun f => ?_, ?_⟩
  · obtain ⟨d1, n1⟩ := part1 f (absolute f) (fun x => (habs f x).ge)
    obtain ⟨d2, n2⟩ := part1 (absolute f) f (fun x => (habs f x).le)
    exact ⟨Set.Subset.antisymm d2 d1, fun x y z h1 h2 => le_antisymm (n1 x y z h1 h2) (n2 x z y h2 h1)⟩
  · intro f p n hp hn
    obtain ⟨hs, hd⟩ := g58b_sumGraphs F hF p f (List.range (p.natDegree + 1))
    have esym : g58b_symL p f (List.range (p.natDegree + 1)) = polynomialSymbol p f := by
      apply Subtype.ext; funext x
      rw [g58b_symL_val]
      simp only [polynomialSymbol]
      rw [Polynomial.eval_eq_sum_range]
      rfl
    rw [esym] at hs
    have hdpow : ⋂ j ∈ List.range (p.natDegree + 1), graphDomain (F (g58b_pw f j)) =
        graphDomain (F (g58b_pw f n)) := by
      ext x
      simp only [Set.mem_iInter, List.mem_range]
      constructor
      · intro h; exact h n (by omega)
      · intro h j hj
        refine g58b_dom_D F hF _ _ 1 zero_le_one (fun t => ?_) h
        simp only [g58b_pw, norm_pow]
        exact g58b_pow_le _ (norm_nonneg _) (by omega)
    rw [hdpow] at hd
    obtain ⟨C, hC, hCb⟩ := g58b_poly_lower p hp
    have hdom2 : graphDomain (F (polynomialSymbol p f)) ⊆ graphDomain (F (g58b_pw f n)) := by
      refine g58b_dom_D F hF _ _ C hC (fun t => ?_)
      simp only [g58b_pw, polynomialSymbol, norm_pow]
      rw [← hn]; exact hCb _
    have heq : polynomialGraph p (F f) = F (polynomialSymbol p f) := by
      apply g58b_eq_of_sub hs (hF.1 _).2.2.2.2.2
      rw [hd]; exact hdom2
    refine ⟨heq.symm, ?_⟩
    rw [← heq]
    show graphDomain (sumGraphs _) = _
    rw [hd, g58b_graphPower F hF f n]

theorem g58b_projection_measure (F : P05.Symbol X k → Relation H) (hF : Calculus F) :
    PVM (k := k) (fun A => F (P05.indicator A.val A.property)) := by
  obtain ⟨-, hbmul, -, -, -, hstrong⟩ := g58b_first F hF
  refine ⟨inferInstance, fun A => ⟨(hF.2.2.1 _ (g58b_indicator_bounded _ _)).1, ?_, ?_⟩, ?_, ?_⟩
  · rw [(hF.2.2.1 _ (g58b_indicator_bounded _ _)).2]
    congr 1
    apply Subtype.ext; funext x
    simp only [starSymbol, P05.indicator, Set.indicator]
    split_ifs <;> simp
  · rw [(hbmul _ _ (hF.2.2.1 _ (g58b_indicator_bounded _ _)).1).2.1]
    congr 1
    apply Subtype.ext; funext x
    simp only [times, P05.indicator, Set.indicator]
    split_ifs <;> simp
  · show F (P05.indicator Set.univ MeasurableSet.univ) = identity
    have e : P05.indicator (k := k) (Set.univ : Set X) MeasurableSet.univ = constant 1 :=
      Subtype.ext (funext fun x => by simp [P05.indicator, constant])
    rw [e]; exact hF.2.1.1
  · intro A hA hdisj x
    set B : ℕ → Set X := fun n => ⋃ j ∈ Finset.range n, A j
    have hB : ∀ n, MeasurableSet (B n) := fun n =>
      Finset.measurableSet_biUnion _ (fun j _ => hA j)
    have hsum : ∀ n, value (F (P05.indicator (B n) (hB n))) x =
        ∑ j ∈ Finset.range n, value (F (P05.indicator (A j) (hA j))) x := by
      intro n
      induction n with
      | zero =>
        have e : P05.indicator (k := k) (B 0) (hB 0) = constant 0 :=
          Subtype.ext (funext fun x => by simp [P05.indicator, constant, B])
        rw [e, g58b_zero_const F hF, g58b_value_zeroGraph, Finset.sum_range_zero]
      | succ n ih =>
        obtain ⟨⟨S, hS⟩, -⟩ := hF.2.2.1 _ (g58b_indicator_bounded (k := k) (B n) (hB n))
        obtain ⟨⟨T, hT⟩, -⟩ := hF.2.2.1 _ (g58b_indicator_bounded (k := k) (A n) (hA n))
        have e : P05.indicator (k := k) (B (n + 1)) (hB (n + 1)) =
            plus (P05.indicator (B n) (hB n)) (P05.indicator (A n) (hA n)) := by
          apply Subtype.ext; funext y
          simp only [plus, P05.indicator, Set.indicator, B, Finset.range_add_one,
            Finset.set_biUnion_insert, Set.mem_union, Set.mem_iUnion, Finset.mem_range,
            exists_prop]
          by_cases h1 : y ∈ A n
          · have h2 : ¬ ∃ j, j < n ∧ y ∈ A j := by
              rintro ⟨j, hj, hy⟩
              exact Set.disjoint_left.mp (hdisj (Nat.ne_of_lt hj)) hy h1
            simp [h1, h2]
            exact ⟨n, le_rfl, h1⟩
          · have h3 : (∃ i ≤ n, y ∈ A i) ↔ (∃ i < n, y ∈ A i) :=
              ⟨fun ⟨i, hi, hy⟩ => ⟨i, lt_of_le_of_ne hi (fun h => h1 (h ▸ hy)), hy⟩,
                fun ⟨i, hi, hy⟩ => ⟨i, hi.le, hy⟩⟩
            simp [h1, h3]
        rw [Finset.sum_range_succ, ← ih, e, g58b_bdd_add F hF _ _ hS hT, hS, hT,
          g58b_value_graph, g58b_value_graph, g58b_value_graph, ContinuousLinearMap.add_apply]
    simp only
    simp only [← hsum]
    have hbp : BP (fun n => P05.indicator (k := k) (B n) (hB n))
        (P05.indicator (⋃ n, A n) (MeasurableSet.iUnion hA)) := by
      refine ⟨fun y => ?_, 1, fun n y => ?_⟩
      · by_cases hy : y ∈ ⋃ n, A n
        · obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
          apply tendsto_nhds_of_eventually_eq
          filter_upwards [Filter.eventually_gt_atTop m] with n hn
          have : y ∈ B n := Set.mem_biUnion (Finset.mem_range.mpr hn) hm
          simp [P05.indicator, Set.indicator, this, hy]
        · apply tendsto_nhds_of_eventually_eq
          filter_upwards with n
          have : y ∉ B n := fun h => hy (by
            obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.mp h
            exact Set.mem_iUnion.mpr ⟨j, hj⟩)
          simp [P05.indicator, Set.indicator, this, hy]
      · simp only [P05.indicator, Set.indicator]
        split_ifs <;> simp
    exact (hstrong _ _ hbp).2.2 x

theorem g58b_trunc (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k) :
    ∃ (N : ℕ → Set X) (hN : ∀ n, MeasurableSet (N n)) (P : ℕ → H →L[k] H),
      (∀ n, F (P05.indicator (N n) (hN n)) = boundedGraph (P n)) ∧
      (∀ z, Tendsto (fun n => P n z) atTop (𝓝 z)) ∧ (∀ n t, t ∈ N n → ‖f.val t‖ ≤ n) := by
  obtain ⟨-, -, -, -, -, hstrong⟩ := g58b_first F hF
  set N : ℕ → Set X := fun n => {t | ‖f.val t‖ ≤ n}
  have hN : ∀ n, MeasurableSet (N n) := fun n => measurableSet_le f.property.norm measurable_const
  choose P hP using fun n => (hF.2.2.1 _ (g58b_indicator_bounded (k := k) (N n) (hN n))).1
  refine ⟨N, hN, P, hP, ?_, fun n t ht => ht⟩
  have hbp : BP (fun n => P05.indicator (k := k) (N n) (hN n)) (constant 1) := by
    refine ⟨fun t => ?_, 1, fun n t => ?_⟩
    · apply tendsto_nhds_of_eventually_eq
      obtain ⟨m, hm⟩ := exists_nat_ge (‖f.val t‖)
      filter_upwards [Filter.eventually_ge_atTop m] with n hn
      have : t ∈ N n := by
        show ‖f.val t‖ ≤ n
        have h2 : (m : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp [P05.indicator, Set.indicator, this, constant]
    · simp only [P05.indicator, Set.indicator]; split_ifs <;> simp
  intro z
  have := (hstrong _ _ hbp).2.2 z
  simp only [hP, g58b_value_graph, hF.2.1.1] at this
  rwa [g58b_value_eq (fun x y z (h1 : y = x) (h2 : z = x) => h1.trans h2.symm)
    (show z = z from rfl)] at this

theorem g58b_ind_sa (F : P05.Symbol X k → Relation H) (hF : Calculus F) (A : Set X)
    (hA : MeasurableSet A) {P : H →L[k] H} (hP : F (P05.indicator A hA) = boundedGraph P) :
    ContinuousLinearMap.adjoint P = P := by
  have := g58b_bdd_star F hF _ (g58b_indicator_bounded _ _) hP
  have e : starSymbol (P05.indicator (k := k) A hA) = P05.indicator A hA := by
    apply Subtype.ext; funext x
    simp only [starSymbol, P05.indicator, Set.indicator]
    split_ifs <;> simp
  rw [e, hP] at this
  exact (g58b_graph_inj this).symm

theorem g58b_adjoint_all (F : P05.Symbol X k → Relation H) (hF : Calculus F) (f : P05.Symbol X k) :
    graphAdjoint (k := k) (F f) = F (starSymbol f) := by
  obtain ⟨N, hN, P, hP, hconv, hbN⟩ := g58b_trunc F hF f
  -- per-n data
  have data : ∀ n, ∃ T : H →L[k] H, (∀ x, (P n x, T x) ∈ F f) ∧
      (∀ x y, (x, y) ∈ F f → T x = P n y) ∧
      (∀ x, (P n x, (ContinuousLinearMap.adjoint T) x) ∈ F (starSymbol f)) ∧
      (∀ x y, (x, y) ∈ F (starSymbol f) → (ContinuousLinearMap.adjoint T) x = P n y) := by
    intro n
    have hb : ∀ t, ‖(times f (P05.indicator (N n) (hN n))).val t‖ ≤ n := by
      intro t
      simp only [times, P05.indicator, Set.indicator]
      split_ifs with ht
      · rw [mul_one]; exact hbN n t ht
      · simp
    have bfa : BoundedSymbol (times f (P05.indicator (N n) (hN n))) := ⟨_, hb⟩
    obtain ⟨⟨T, hT⟩, -⟩ := hF.2.2.1 _ bfa
    have hTs := g58b_bdd_star F hF _ bfa hT
    have es : starSymbol (times f (P05.indicator (N n) (hN n))) =
        times (starSymbol f) (P05.indicator (N n) (hN n)) := by
      apply Subtype.ext; funext t
      simp only [starSymbol, times, P05.indicator, Set.indicator, star_mul']
      split_ifs <;> simp
    rw [es] at hTs
    obtain ⟨Fa, Fb, -⟩ := g58b_loc_facts F hF f (N n) (hN n) (hP n)
    obtain ⟨Ga, Gb, -⟩ := g58b_loc_facts F hF (starSymbol f) (N n) (hN n) (hP n)
    refine ⟨T, fun x => (Fa x (T x)).mp (by rw [hT]; rfl), fun x y hxy => ?_,
      fun x => (Ga x _).mp (by rw [hTs]; rfl), fun x y hxy => ?_⟩
    · have := (Fa x (P n y)).mpr (Fb x y hxy)
      rw [hT] at this; exact this.symm
    · have := (Ga x (P n y)).mpr (Gb x y hxy)
      rw [hTs] at this; exact this.symm
  ext ⟨x, y⟩
  simp only [graphAdjoint, Set.mem_setOf_eq]
  constructor
  · intro h
    have hn : ∀ n, (P n x, P n y) ∈ F (starSymbol f) := by
      intro n
      obtain ⟨T, h1, -, h3, -⟩ := data n
      have : P n y = (ContinuousLinearMap.adjoint T) x := by
        apply ext_inner_left k
        intro w
        rw [← ContinuousLinearMap.adjoint_inner_left, g58b_ind_sa F hF _ _ (hP n),
          h _ _ (h1 w), ContinuousLinearMap.adjoint_inner_right]
      rw [this]; exact h3 x
    exact (hF.1 _).2.1.mem_of_tendsto ((hconv x).prodMk_nhds (hconv y))
      (Filter.Eventually.of_forall hn)
  · intro hxy u v huv
    have hlim1 : Tendsto (fun n => inner k u (P n y)) atTop (𝓝 (inner k u y)) :=
      ((continuous_const.inner continuous_id).tendsto y).comp (hconv y)
    have hlim2 : Tendsto (fun n => inner k v (P n x)) atTop (𝓝 (inner k v x)) :=
      ((continuous_const.inner continuous_id).tendsto x).comp (hconv x)
    have heq : ∀ n, inner k u (P n y) = inner k v (P n x) := by
      intro n
      obtain ⟨T, -, h2, -, h4⟩ := data n
      rw [← h4 x y hxy, ContinuousLinearMap.adjoint_inner_right, h2 u v huv,
        ← ContinuousLinearMap.adjoint_inner_left, g58b_ind_sa F hF _ _ (hP n)]
    simp only [heq] at hlim1
    exact tendsto_nhds_unique hlim1 hlim2

theorem g58b_add_zero_rel (B : Relation H) : add B zeroGraph = B := by
  ext ⟨x, y⟩
  simp only [add, zeroGraph, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b, ha, hb, h⟩; have : b = 0 := hb; rw [h, this, add_zero]; exact ha
  · intro h; exact ⟨y, 0, h, rfl, by simp⟩

theorem g58b_mul_id_rel (B : Relation H) : mul B identity = B := by
  ext ⟨x, y⟩
  simp only [mul, identity, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, h⟩; have : z = x := hz; rw [this] at h; exact h
  · intro h; exact ⟨x, rfl, h⟩

theorem g58b_mul_star_eq (F : P05.Symbol X k → Relation H) (hF : Calculus F) (a b : P05.Symbol X k)
    (hab : ∀ t, ‖b.val t‖ ≤ 1 * (1 + ‖(times a b).val t‖)) :
    mul (F a) (F b) = F (times a b) := by
  apply g58b_eq_of_sub (hF.2.1.2.2.2.1 a b) (hF.1 _).2.2.2.2.2
  rw [hF.2.1.2.2.2.2]
  intro x hx
  exact ⟨g58b_dom_D F hF _ _ 1 zero_le_one hab hx, hx⟩

theorem g58b_nonneg_form (F : P05.Symbol X k → Relation H) (hF : Calculus F) (h : P05.Symbol X k)
    (hre : ∀ t, star (h.val t) = h.val t) (hpos : ∀ t, 0 ≤ RCLike.re (h.val t))
    (x w : H) (hxw : (x, w) ∈ F h) : 0 ≤ RCLike.re (inner k x w) := by
  set r : P05.Symbol X k := ⟨fun t => ((Real.sqrt (RCLike.re (h.val t)) : ℝ) : k), by
    have hh := h.property; fun_prop⟩
  have hreal : ∀ t, ((RCLike.re (h.val t) : ℝ) : k) = h.val t := fun t =>
    (RCLike.conj_eq_iff_re.mp (by rw [← RCLike.star_def]; exact hre t))
  have hrr : times r r = h := by
    apply Subtype.ext; funext t
    simp only [times, r]
    rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hpos t), hreal]
  have hrsa := g58b_sa_of_real F hF r (fun t => by simp [r])
  have hdr : x ∈ graphDomain (F r) := by
    refine g58b_dom_D F hF r h 1 zero_le_one (fun t => ?_) ⟨w, hxw⟩
    simp only [r, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _), one_mul]
    have h1 : RCLike.re (h.val t) ≤ ‖h.val t‖ := RCLike.re_le_norm _
    have h2 : Real.sqrt (RCLike.re (h.val t)) ≤ 1 + RCLike.re (h.val t) := by
      rw [Real.sqrt_le_left (by linarith [hpos t])]; nlinarith [hpos t]
    linarith
  have hx : x ∈ graphDomain (mul (F r) (F r)) := by
    rw [hF.2.1.2.2.2.2, hrr]; exact ⟨hdr, ⟨w, hxw⟩⟩
  obtain ⟨u, v, hv, hvu⟩ := hx
  have hu : u = w := by
    have := hF.2.1.2.2.2.1 r r ⟨v, hv, hvu⟩
    rw [hrr] at this; exact (hF.1 h).2.2.2.2.2 _ _ _ this hxw
  have hadj : (x, v) ∈ graphAdjoint (k := k) (F r) := by rw [hrsa.2.2]; exact hv
  have := hadj v u hvu
  rw [← hu, ← inner_conj_symm, ← this, inner_self_eq_norm_sq_to_K]
  rw [show (starRingEnd k) ((‖v‖ : k) ^ 2) = ((‖v‖ ^ 2 : ℝ) : k) by
    rw [← RCLike.ofReal_pow, RCLike.conj_ofReal], RCLike.ofReal_re]
  positivity

theorem g58b_further (F : P05.Symbol X k → Relation H) (hF : Calculus F) :
    (∀ f g, GraphCore (F g) (graphDomain (F f) ∩ graphDomain (F g))) ∧
    (∀ f g, closure (add (F f) (F g)) = F (plus f g) ∧
      closure (mul (F f) (F g)) = F (times f g)) ∧
    (∀ f, graphAdjoint (k := k) (F f) = F (starSymbol f)) ∧
    (∀ f, Normal (k := k) (F f) ∧
      mul (F (starSymbol f)) (F f) = F (times (absolute f) (absolute f))) ∧
    ((∀ f, RealValued f → SelfAdjoint (k := k) (F f)) ∧
      ∀ f g, RealValued f → RealValued g → RealLE f g →
        ∀ x y z, (x, y) ∈ F f → (x, z) ∈ F g →
          RCLike.re (inner k x y) ≤ RCLike.re (inner k x z)) ∧
    (BoundedRestrictionHom F ∧
      ∀ fn f, Pointwise fn f → (∃ c : ℝ, ∀ n, NormBound (k := k) (F (fn n)) c) →
        BoundedOperator (k := k) (F f) ∧ Strong (k := k) (fun n => F (fn n)) (F f)) := by
  obtain ⟨hsc, hbmul, -, hdense, -, hstrong⟩ := g58b_first F hF
  have hadjAll := g58b_adjoint_all F hF
  refine ⟨?_, ?_, hadjAll, ?_, ⟨fun f hf => g58b_sa_of_real F hF f hf, ?_⟩, ?_, ?_⟩
  · intro f g
    have := (g58b_finite_ops F hF ![f, g]).1 1
    have e : (⋂ i, graphDomain (F (![f, g] i))) = graphDomain (F f) ∩ graphDomain (F g) := by
      ext x; simp [Fin.forall_fin_two]
    rw [e] at this
    simpa using this
  · intro f g
    obtain ⟨-, h2, h3⟩ := g58b_finite_ops F hF ![f, g]
    have es : tupleSum ![f, g] = plus f g := Subtype.ext (funext fun t => by
      simp [tupleSum, plus, Fin.sum_univ_two])
    have ep : tupleProduct ![f, g] = times f g := Subtype.ext (funext fun t => by
      simp [tupleProduct, times, Fin.prod_univ_two])
    simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
      sumGraphs, productGraphs, es, ep] at h2 h3
    simp only [Fin.succ_zero_eq_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, List.map_cons, List.map_nil, Fin.cast_eq_self, sumGraphs,
      productGraphs, g58b_add_zero_rel, g58b_mul_id_rel] at h2 h3
    exact ⟨h2, h3⟩
  · intro f
    have hb1 : ∀ t, ‖f.val t‖ ≤ 1 * (1 + ‖(times (starSymbol f) f).val t‖) := by
      intro t; simp only [times, starSymbol, norm_mul, norm_star, one_mul]
      nlinarith [norm_nonneg (f.val t)]
    have hb2 : ∀ t, ‖(starSymbol f).val t‖ ≤ 1 * (1 + ‖(times f (starSymbol f)).val t‖) := by
      intro t; simp only [times, starSymbol, norm_mul, norm_star, one_mul]
      nlinarith [norm_nonneg (f.val t)]
    have e1 := g58b_mul_star_eq F hF _ _ hb1
    have e2 := g58b_mul_star_eq F hF _ _ hb2
    have ec : times f (starSymbol f) = times (starSymbol f) f :=
      Subtype.ext (funext fun t => mul_comm _ _)
    have eab : times (starSymbol f) f = times (absolute f) (absolute f) := by
      apply Subtype.ext; funext t
      simp only [times, starSymbol, absolute]
      rw [RCLike.star_def, RCLike.conj_mul]; ring
    refine ⟨⟨hF.1 f, hdense f, ?_⟩, by rw [e1, eab]⟩
    rw [hadjAll, e1, e2, ec]
  · intro f g hf hg hfg x y z hxy hxz
    set h := plus g (scalar (-1) f)
    have hmem : (x, z + (-1 : k) • y) ∈ F h :=
      hF.2.1.2.1 _ _ ⟨z, (-1 : k) • y, hxz, hF.2.1.2.2.1 _ _ ⟨y, hxy, rfl⟩, rfl⟩
    have hre : ∀ t, star (h.val t) = h.val t := fun t => by
      simp only [h, plus, scalar, star_add, star_mul', hf t, hg t, star_neg, star_one]
    have hpos : ∀ t, 0 ≤ RCLike.re (h.val t) := fun t => by
      simp only [h, plus, scalar, map_add, neg_one_mul, map_neg]; linarith [hfg t]
    have := g58b_nonneg_form F hF h hre hpos x _ hmem
    rw [inner_add_right, inner_smul_right, map_add] at this
    simp only [neg_one_mul, map_neg] at this
    linarith
  · refine ⟨fun c => ?_, fun f g hf hg => ?_, fun c f hf => ?_, fun f hf => ?_⟩
    · have hb1 : BoundedOperator (k := k) (F (constant 1)) :=
        (hF.2.2.1 _ ⟨‖(1 : k)‖, fun _ => le_rfl⟩).1
      have e : (constant c : P05.Symbol X k) = scalar c (constant 1) :=
        Subtype.ext (funext fun x => by simp [constant, scalar])
      refine ⟨?_, (hF.2.2.1 _ ⟨‖c‖, fun _ => le_rfl⟩).1⟩
      rw [e, hsc c (constant 1) (Or.inr hb1), hF.2.1.1]
    · obtain ⟨S, hS⟩ := hf
      obtain ⟨T, hT⟩ := hg
      refine ⟨⟨_, g58b_bdd_add F hF _ _ hS hT⟩, ⟨_, g58b_bdd_mul F hF _ _ hS hT⟩,
        ((hbmul f g ⟨T, hT⟩).1).symm, ((hbmul f g ⟨T, hT⟩).2.1).symm⟩
    · obtain ⟨S, hS⟩ := hf
      exact ⟨⟨_, g58b_bdd_scalar F hF c f hS⟩, hsc c f (Or.inr ⟨S, hS⟩)⟩
    · obtain ⟨S, hS⟩ := hf
      rw [← hadjAll f, hS, g58b_adj_graph]
      exact ⟨⟨_, rfl⟩, rfl⟩
  · rintro fn f hpt ⟨c, hc⟩
    have hc0 : 0 ≤ c := by obtain ⟨T, -, hT⟩ := hc 0; exact (norm_nonneg _).trans hT
    have hal : ∀ n, Almost F (fun x => ‖(fn n).val x‖ ≤ c) := fun n =>
      (g58b_normbound_iff F hF (fn n) c hc0).mp (hc n)
    set Mn : ℕ → Set X := fun n => {x | ¬ (fun x => ‖(fn n).val x‖ ≤ c) x}
    have hMn : ∀ n, Null F (Mn n) := hal
    have hMnull := (g58b_null_sigma F hF).2.2 Mn hMn
    obtain ⟨hM, hMz⟩ := hMnull
    set M := ⋃ n, Mn n
    have hMc : MeasurableSet Mᶜ := hM.compl
    have trunc : ∀ g : P05.Symbol X k, F g = F (times g (P05.indicator Mᶜ hMc)) := by
      intro g
      have e : g = plus (times g (P05.indicator Mᶜ hMc)) (times g (P05.indicator M hM)) := by
        apply Subtype.ext; funext x
        simp only [plus, times, P05.indicator, Set.indicator]
        by_cases hx : x ∈ M <;> simp [hx]
      conv_lhs => rw [e]
      exact g58b_plus_null F hF _ _ (g58b_zero_times F hF _ _ hMz)
    have hbp : BP (fun n => times (fn n) (P05.indicator Mᶜ hMc)) (times f (P05.indicator Mᶜ hMc)) := by
      refine ⟨fun t => ?_, c, fun n t => ?_⟩
      · simp only [times, P05.indicator, Set.indicator]
        split_ifs
        · simpa using hpt t
        · simp
      · simp only [times, P05.indicator, Set.indicator]
        split_ifs with ht
        · rw [mul_one]
          have : t ∉ Mn n := fun h' => ht (Set.mem_iUnion.mpr ⟨n, h'⟩)
          simpa [Mn] using this
        · simp [hc0]
    have hs := hstrong _ _ hbp
    simp only [← trunc] at hs
    exact ⟨hs.2.1, hs⟩

section g58bCo
variable (F G : P05.Symbol X k → Relation H) (hF : Calculus F) (hG : Calculus G)
include hF hG

theorem g58b_co_plus {f g : P05.Symbol X k} (hf : F f = G f) (hg : F g = G g) :
    F (plus f g) = G (plus f g) := by
  rw [← ((g58b_further F hF).2.1 f g).1, ← ((g58b_further G hG).2.1 f g).1, hf, hg]

theorem g58b_co_times {f g : P05.Symbol X k} (hf : F f = G f) (hg : F g = G g) :
    F (times f g) = G (times f g) := by
  rw [← ((g58b_further F hF).2.1 f g).2, ← ((g58b_further G hG).2.1 f g).2, hf, hg]

theorem g58b_co_star {f : P05.Symbol X k} (hf : F f = G f) :
    F (starSymbol f) = G (starSymbol f) := by
  rw [← g58b_adjoint_all F hF, ← g58b_adjoint_all G hG, hf]

theorem g58b_co_const (c : k) : F (constant c) = G (constant c) := by
  rw [((g58b_further F hF).2.2.2.2.2.1.1 c).1, ((g58b_further G hG).2.2.2.2.2.1.1 c).1]

theorem g58b_co_scalar (c : k) {f : P05.Symbol X k} (hf : F f = G f) :
    F (scalar c f) = G (scalar c f) := by
  have e : scalar c f = times (constant c) f := Subtype.ext rfl
  rw [e]; exact g58b_co_times F G hF hG (g58b_co_const F G hF hG c) hf

theorem g58b_co_recip {f : P05.Symbol X k} (hf : F f = G f) (hne : ∀ x, f.val x ≠ 0) :
    F (reciprocal f) = G (reciprocal f) := by
  rw [← ((g58b_first F hF).2.2.1 f hne).2, ← ((g58b_first G hG).2.2.1 f hne).2, hf]

theorem g58b_co_bp {fn : ℕ → P05.Symbol X k} {f : P05.Symbol X k} (hfn : ∀ n, F (fn n) = G (fn n))
    (hbp : BP fn f) : F f = G f := by
  obtain ⟨-, ⟨S, hS⟩, hwF⟩ := hF.2.2.2 _ _ hbp
  obtain ⟨-, ⟨T, hT⟩, hwG⟩ := hG.2.2.2 _ _ hbp
  have hST : S = T := by
    ext y
    apply ext_inner_left k
    intro x
    have h1 := hwF x y
    have h2 := hwG x y
    simp only [hfn] at h1
    have := tendsto_nhds_unique h1 h2
    rwa [hS, hT, g58b_value_graph, g58b_value_graph] at this
  rw [hS, hT, hST]

omit hG in
theorem g58b_genreg (e f : P05.Symbol X k) (hne : ∀ x, e.val x ≠ 0)
    (be : BoundedSymbol e) (bef : BoundedSymbol (times e f)) (x y : H) :
    (x, y) ∈ F f ↔ ∃ z, (x, z) ∈ F (times e f) ∧ (y, z) ∈ F e := by
  obtain ⟨hcl, ⟨h1, hadd, hsc, hmul, hdom⟩, hbd, hw⟩ := hF
  obtain ⟨⟨Te, hTe⟩, -⟩ := hbd _ be
  set g := reciprocal e
  have hge : times g e = constant 1 :=
    Subtype.ext (funext fun t => by simp only [times, g, reciprocal, constant]; exact inv_mul_cancel₀ (hne t))
  have hgef : times g (times e f) = f :=
    Subtype.ext (funext fun t => by
      simp only [times, g, reciprocal]; rw [← mul_assoc, inv_mul_cancel₀ (hne t), one_mul])
  have step1 : ∀ u, (Te u, u) ∈ F g := by
    intro u
    have hu : u ∈ graphDomain (mul (F g) (F e)) := by
      rw [hdom, hTe, hge, h1]
      exact ⟨⟨Te u, rfl⟩, ⟨u, rfl⟩⟩
    obtain ⟨w, z, hz, hzw⟩ := hu
    have hz' : z = Te u := by rw [hTe] at hz; exact hz
    have hw' : (u, w) ∈ F (times g e) := hmul _ _ ⟨z, hz, hzw⟩
    rw [hge, h1] at hw'
    have : w = u := hw'
    rw [hz', this] at hzw; exact hzw
  constructor
  · intro hxy
    refine ⟨Te y, hmul _ _ ⟨y, hxy, ?_⟩, ?_⟩
    · rw [hTe]; rfl
    · rw [hTe]; rfl
  · rintro ⟨z, hxz, hyz⟩
    have hz : z = Te y := by rw [hTe] at hyz; exact hyz
    have := hmul g (times e f) (show (x, y) ∈ mul _ _ from ⟨z, hxz, by rw [hz]; exact step1 y⟩)
    rwa [hgef] at this

theorem g58b_co_reg (e f : P05.Symbol X k) (hne : ∀ x, e.val x ≠ 0)
    (be : BoundedSymbol e) (bef : BoundedSymbol (times e f))
    (h1 : F e = G e) (h2 : F (times e f) = G (times e f)) : F f = G f := by
  ext ⟨x, y⟩
  rw [g58b_genreg F hF e f hne be bef, g58b_genreg G hG e f hne be bef, h1, h2]

def g58b_q (f : P05.Symbol X k) : P05.Symbol X k :=
  reciprocal (plus (constant 1) (times (starSymbol f) f))

omit hF hG in
theorem g58b_q_val (f : P05.Symbol X k) (t : X) :
    (g58b_q f).val t = (((1 + ‖f.val t‖ ^ 2 : ℝ) : k))⁻¹ := by
  simp only [g58b_q, reciprocal, plus, constant, times, starSymbol]
  rw [RCLike.star_def, RCLike.conj_mul]; push_cast; ring

omit hF hG in
theorem g58b_q_ne (f : P05.Symbol X k) (t : X) : (g58b_q f).val t ≠ 0 := by
  rw [g58b_q_val]; exact inv_ne_zero (RCLike.ofReal_ne_zero.mpr (by positivity))

omit hF hG in
theorem g58b_q_bdd (f : P05.Symbol X k) (t : X) :
    ‖(g58b_q f).val t‖ ≤ 1 ∧ ‖(times (g58b_q f) f).val t‖ ≤ 1 := by
  simp only [times, g58b_q_val, norm_mul, norm_inv, RCLike.norm_ofReal]
  rw [abs_of_pos (by positivity)]
  constructor
  · exact inv_le_one_of_one_le₀ (by nlinarith [norm_nonneg (f.val t)])
  · rw [inv_mul_le_iff₀ (by positivity)]; nlinarith [norm_nonneg (f.val t), sq_nonneg (‖f.val t‖ - 1)]

theorem g58b_co_q {f : P05.Symbol X k} (hf : F f = G f) : F (g58b_q f) = G (g58b_q f) := by
  apply g58b_co_recip F G hF hG
  · exact g58b_co_plus F G hF hG (g58b_co_const F G hF hG 1)
      (g58b_co_times F G hF hG (g58b_co_star F G hF hG hf) hf)
  · intro t
    have := g58b_q_ne f t
    simp only [g58b_q, reciprocal] at this
    exact fun h => this (by rw [h, inv_zero])

theorem g58b_co_lim {fn : ℕ → P05.Symbol X k} {f : P05.Symbol X k} (hfn : ∀ n, F (fn n) = G (fn n))
    (hpt : Pointwise fn f) : F f = G f := by
  have hcq : Continuous (fun z : k => (((1 + ‖z‖ ^ 2 : ℝ) : k))⁻¹) := by
    have : ∀ z : k, ((1 + ‖z‖ ^ 2 : ℝ) : k) ≠ 0 := fun z => RCLike.ofReal_ne_zero.mpr (by positivity)
    exact Continuous.inv₀ (by fun_prop) this
  have bq : BP (fun n => g58b_q (fn n)) (g58b_q f) := by
    refine ⟨fun t => ?_, 1, fun n t => (g58b_q_bdd _ t).1⟩
    simp only [g58b_q_val]
    exact (hcq.tendsto _).comp (hpt t)
  have bqf : BP (fun n => times (g58b_q (fn n)) (fn n)) (times (g58b_q f) f) := by
    refine ⟨fun t => ?_, 1, fun n t => (g58b_q_bdd _ t).2⟩
    simp only [times, g58b_q_val]
    exact ((hcq.tendsto _).comp (hpt t)).mul (hpt t)
  have h1 := g58b_co_bp F G hF hG (fun n => g58b_co_q F G hF hG (hfn n)) bq
  have h2 := g58b_co_bp F G hF hG (fun n => g58b_co_times F G hF hG
    (g58b_co_q F G hF hG (hfn n)) (hfn n)) bqf
  exact g58b_co_reg F G hF hG _ _ (g58b_q_ne f) ⟨1, fun t => (g58b_q_bdd f t).1⟩
    ⟨1, fun t => (g58b_q_bdd f t).2⟩ h1 h2

end g58bCo

noncomputable def g58b_heron (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (g58b_heron a n + a / g58b_heron a n) / 2

theorem g58b_heron_pos (a : ℝ) (ha : 0 ≤ a) : ∀ n, 0 < g58b_heron a n := by
  intro n; induction n with
  | zero => simp [g58b_heron]
  | succ n ih => simp only [g58b_heron]; have := div_nonneg ha ih.le; linarith

theorem g58b_heron_ge (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : Real.sqrt a ≤ g58b_heron a (n + 1) := by
  have hp := g58b_heron_pos a ha n
  simp only [g58b_heron]
  set h := g58b_heron a n
  have hr := Real.sq_sqrt ha
  have h1 : 2 * Real.sqrt a - h ≤ a / h := by
    rw [le_div_iff₀ hp]; nlinarith [sq_nonneg (h - Real.sqrt a)]
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

theorem g58b_heron_tendsto (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n => g58b_heron a n) atTop (𝓝 (Real.sqrt a)) := by
  set r := Real.sqrt a
  have hr0 : 0 ≤ r := Real.sqrt_nonneg a
  have hr := Real.sq_sqrt ha
  have contr : ∀ n, g58b_heron a (n + 2) - r ≤ (g58b_heron a (n + 1) - r) / 2 := by
    intro n
    have hp := g58b_heron_pos a ha (n + 1)
    have hge := g58b_heron_ge a ha n
    show (g58b_heron a (n + 1) + a / g58b_heron a (n + 1)) / 2 - r ≤ _
    have : a / g58b_heron a (n + 1) ≤ r := by
      rw [div_le_iff₀ hp]; nlinarith [mul_le_mul_of_nonneg_left hge hr0]
    linarith
  have bound : ∀ n, g58b_heron a (n + 1) - r ≤ (g58b_heron a 1 - r) * (1 / 2) ^ n := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      calc g58b_heron a (n + 2) - r ≤ (g58b_heron a (n + 1) - r) / 2 := contr n
        _ ≤ (g58b_heron a 1 - r) * (1 / 2) ^ n / 2 := by linarith
        _ = (g58b_heron a 1 - r) * (1 / 2) ^ (n + 1) := by ring
  have h1 : Tendsto (fun n => g58b_heron a (n + 1) - r) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sub_nonneg.mpr (g58b_heron_ge a ha n)) bound
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num : (1:ℝ) / 2 < 1)).const_mul (g58b_heron a 1 - r)
    simpa using this
  have h2 : Tendsto (fun n => g58b_heron a (n + 1)) atTop (𝓝 r) := by
    have := h1.add_const r; simpa using this
  exact (tendsto_add_atTop_iff_nat 1).mp h2

theorem g58b_ratio_tendsto (m : ℝ) (hm : 0 ≤ m) :
    Tendsto (fun n : ℕ => (n : ℝ) * m / (1 + (n : ℝ) * m)) atTop (𝓝 (if 0 < m then 1 else 0)) := by
  split_ifs with hpos
  · have h1 : Tendsto (fun n : ℕ => 1 + (n : ℝ) * m) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hpos)
    have h2 := (tendsto_inv_atTop_zero.comp h1)
    have h3 : Tendsto (fun n : ℕ => 1 - (1 + (n : ℝ) * m)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub h2
    refine h3.congr (fun n => ?_)
    have : (1 + (n : ℝ) * m) ≠ 0 := by positivity
    field_simp; ring
  · have : m = 0 := le_antisymm (not_lt.mp hpos) hm
    subst this; simp

section g58bCo2
variable (F G : P05.Symbol X k → Relation H) (hF : Calculus F) (hG : Calculus G)
include hF hG

theorem g58b_co_abs {f : P05.Symbol X k} (hf : F f = G f) :
    F (absolute f) = G (absolute f) := by
  set s := times (starSymbol f) f
  have hs : F s = G s := g58b_co_times F G hF hG (g58b_co_star F G hF hG hf) hf
  have hsv : ∀ t, s.val t = ((‖f.val t‖ ^ 2 : ℝ) : k) := fun t => by
    simp only [s, times, starSymbol]; rw [RCLike.star_def, RCLike.conj_mul]; push_cast; ring
  let xs : ℕ → P05.Symbol X k := fun n => Nat.rec (constant 1)
    (fun _ x => scalar (1 / 2) (plus x (times s (reciprocal x)))) n
  have hxv : ∀ n t, (xs n).val t = ((g58b_heron (‖f.val t‖ ^ 2) n : ℝ) : k) := by
    intro n t; induction n with
    | zero => simp [xs, constant, g58b_heron]
    | succ n ih =>
      show (scalar (1 / 2) (plus (xs n) (times s (reciprocal (xs n))))).val t = _
      simp only [scalar, plus, times, reciprocal, ih, hsv, g58b_heron]
      push_cast; ring
  have hxE : ∀ n, F (xs n) = G (xs n) := by
    intro n; induction n with
    | zero => exact g58b_co_const F G hF hG 1
    | succ n ih =>
      show F (scalar (1 / 2) (plus (xs n) (times s (reciprocal (xs n))))) = _
      refine g58b_co_scalar F G hF hG _ (g58b_co_plus F G hF hG ih
        (g58b_co_times F G hF hG hs (g58b_co_recip F G hF hG ih fun t => ?_)))
      rw [hxv]; exact RCLike.ofReal_ne_zero.mpr (g58b_heron_pos _ (by positivity) n).ne'
  refine g58b_co_lim F G hF hG hxE (fun t => ?_)
  simp only [hxv, absolute]
  have := (RCLike.continuous_ofReal (K := k)).tendsto _ |>.comp
    (g58b_heron_tendsto (‖f.val t‖ ^ 2) (by positivity))
  rwa [Real.sqrt_sq (norm_nonneg _)] at this

theorem g58b_co_union (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (h : ∀ n, F (P05.indicator (A n) (hA n)) = G (P05.indicator (A n) (hA n))) :
    F (P05.indicator (⋃ n, A n) (MeasurableSet.iUnion hA)) =
      G (P05.indicator (⋃ n, A n) (MeasurableSet.iUnion hA)) := by
  have hacc : ∀ n, MeasurableSet (Set.accumulate A n) := fun n => by
    rw [Set.accumulate_def]; exact MeasurableSet.biUnion (Set.to_countable _) (fun i _ => hA i)
  have two : ∀ (B C : Set X) (hB : MeasurableSet B) (hC : MeasurableSet C),
      F (P05.indicator (k := k) B hB) = G (P05.indicator B hB) →
      F (P05.indicator (k := k) C hC) = G (P05.indicator C hC) →
      F (P05.indicator (k := k) (B ∪ C) (hB.union hC)) = G (P05.indicator (B ∪ C) (hB.union hC)) := by
    intro B C hB hC h1 h2
    have e : P05.indicator (k := k) (B ∪ C) (hB.union hC) =
        plus (plus (P05.indicator B hB) (P05.indicator C hC))
          (scalar (-1) (times (P05.indicator B hB) (P05.indicator C hC))) := by
      apply Subtype.ext; funext x
      simp only [P05.indicator, plus, times, scalar, Set.indicator]
      by_cases hx : x ∈ B <;> by_cases hy : x ∈ C <;> simp [hx, hy]
    rw [e]
    exact g58b_co_plus F G hF hG (g58b_co_plus F G hF hG h1 h2)
      (g58b_co_scalar F G hF hG _ (g58b_co_times F G hF hG h1 h2))
  have hn : ∀ n, F (P05.indicator (k := k) (Set.accumulate A n) (hacc n)) =
      G (P05.indicator (Set.accumulate A n) (hacc n)) := by
    intro n
    induction n with
    | zero =>
      have e : P05.indicator (k := k) (Set.accumulate A 0) (hacc 0) = P05.indicator (A 0) (hA 0) := by
        congr 1; exact Set.accumulate_zero_nat A
      rw [e]; exact h 0
    | succ n ih =>
      have e : P05.indicator (k := k) (Set.accumulate A (n + 1)) (hacc (n + 1)) =
          P05.indicator (Set.accumulate A n ∪ A (n + 1)) ((hacc n).union (hA (n + 1))) := by
        congr 1; exact Set.accumulate_succ A n
      rw [e]; exact two _ _ _ _ ih (h _)
  refine g58b_co_bp F G hF hG hn ⟨fun x => ?_, 1, fun n x => ?_⟩
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
  · simp only [P05.indicator, Set.indicator]; split_ifs <;> simp

theorem g58b_co_compl (A : Set X) (hA : MeasurableSet A)
    (h : F (P05.indicator A hA) = G (P05.indicator A hA)) :
    F (P05.indicator Aᶜ hA.compl) = G (P05.indicator Aᶜ hA.compl) := by
  have e : P05.indicator (k := k) Aᶜ hA.compl = plus (constant 1) (scalar (-1) (P05.indicator A hA)) := by
    apply Subtype.ext; funext x
    by_cases hx : x ∈ A <;> simp [P05.indicator, Set.indicator, plus, scalar, constant, hx]
  rw [e]; exact g58b_co_plus F G hF hG (g58b_co_const F G hF hG 1) (g58b_co_scalar F G hF hG _ h)

theorem g58b_co_ball {f : P05.Symbol X k} (hf : F f = G f) (c : k) (r : ℝ) (hr : 0 < r) :
    F (P05.indicator (f.val ⁻¹' Metric.ball c r) (f.property measurableSet_ball)) =
      G (P05.indicator (f.val ⁻¹' Metric.ball c r) (f.property measurableSet_ball)) := by
  set d := plus f (constant (-c))
  have hd : F d = G d := g58b_co_plus F G hF hG hf (g58b_co_const F G hF hG _)
  set g := plus (constant ((r ^ 2 : ℝ) : k)) (scalar (-1) (times (starSymbol d) d))
  have hg : F g = G g := g58b_co_plus F G hF hG (g58b_co_const F G hF hG _)
    (g58b_co_scalar F G hF hG _ (g58b_co_times F G hF hG (g58b_co_star F G hF hG hd) hd))
  set γ : X → ℝ := fun t => r ^ 2 - ‖f.val t - c‖ ^ 2
  have hgv : ∀ t, g.val t = ((γ t : ℝ) : k) := fun t => by
    simp only [g, d, plus, constant, scalar, times, starSymbol, γ]
    rw [RCLike.star_def, RCLike.conj_mul]; push_cast; ring
  set tp := scalar (1 / 2) (plus g (absolute g))
  have htp : F tp = G tp := g58b_co_scalar F G hF hG _ (g58b_co_plus F G hF hG hg (g58b_co_abs F G hF hG hg))
  have htpv : ∀ t, tp.val t = ((max (γ t) 0 : ℝ) : k) := fun t => by
    simp only [tp, scalar, plus, absolute, hgv, RCLike.norm_ofReal]
    rcases le_total 0 (γ t) with h0 | h0
    · rw [abs_of_nonneg h0, max_eq_left h0]; push_cast; ring
    · rw [abs_of_nonpos h0, max_eq_right h0]; push_cast; ring
  let hn : ℕ → P05.Symbol X k := fun n =>
    times (scalar (n : k) tp) (reciprocal (plus (constant 1) (scalar (n : k) tp)))
  have hnE : ∀ n, F (hn n) = G (hn n) := by
    intro n
    refine g58b_co_times F G hF hG (g58b_co_scalar F G hF hG _ htp) (g58b_co_recip F G hF hG
      (g58b_co_plus F G hF hG (g58b_co_const F G hF hG 1) (g58b_co_scalar F G hF hG _ htp)) fun t => ?_)
    simp only [plus, constant, scalar, htpv]
    have : (0 : ℝ) < 1 + (n : ℝ) * max (γ t) 0 := by positivity
    intro h0; apply this.ne'
    have : ((1 + (n : ℝ) * max (γ t) 0 : ℝ) : k) = 0 := by push_cast; exact h0
    exact_mod_cast this
  refine g58b_co_lim F G hF hG hnE (fun t => ?_)
  have hv : ∀ n, (hn n).val t = (((n : ℝ) * max (γ t) 0 / (1 + (n : ℝ) * max (γ t) 0) : ℝ) : k) := by
    intro n; simp only [hn, times, scalar, plus, constant, reciprocal, htpv]; push_cast; ring
  simp only [hv]
  have hlim := ((RCLike.continuous_ofReal (K := k)).tendsto _).comp
    (g58b_ratio_tendsto (max (γ t) 0) (le_max_right _ _))
  have key : ‖f.val t - c‖ < r ↔ 0 < max (r ^ 2 - ‖f.val t - c‖ ^ 2) 0 := by
    rw [lt_max_iff]
    constructor
    · intro h; left; nlinarith [norm_nonneg (f.val t - c)]
    · rintro (h | h)
      · by_contra hc; push_neg at hc; nlinarith
      · exact absurd h (lt_irrefl 0)
  have e : (P05.indicator (k := k) (f.val ⁻¹' Metric.ball c r) (f.property measurableSet_ball)).val t =
      (((if 0 < max (γ t) 0 then 1 else 0 : ℝ)) : k) := by
    simp only [P05.indicator, Set.indicator, Set.mem_preimage, Metric.mem_ball, dist_eq_norm, γ]
    by_cases hb : ‖f.val t - c‖ < r
    · rw [if_pos hb, if_pos (key.mp hb)]; simp
    · rw [if_neg hb, if_neg (fun h => hb (key.mpr h))]; simp
  rw [e]; exact hlim

theorem g58b_co_preimage {f : P05.Symbol X k} (hf : F f = G f) (B : Set k) (hB : MeasurableSet B) :
    F (P05.indicator (f.val ⁻¹' B) (hB.preimage f.property)) =
      G (P05.indicator (f.val ⁻¹' B) (hB.preimage f.property)) := by
  let Q : Set k → Prop := fun s => ∃ h : MeasurableSet (f.val ⁻¹' s),
    F (P05.indicator (f.val ⁻¹' s) h) = G (P05.indicator (f.val ⁻¹' s) h)
  have hopen : ∀ U : Set k, IsOpen U → Q U := by
    intro U hU
    have hUm : MeasurableSet (f.val ⁻¹' U) := hU.measurableSet.preimage f.property
    refine ⟨hUm, ?_⟩
    set S := {V : Set k | ∃ c r, 0 < r ∧ V = Metric.ball c r ∧ V ⊆ U}
    have hSU : ⋃₀ S = U := by
      ext z; constructor
      · rintro ⟨V, ⟨c, r, -, -, hV⟩, hz⟩; exact hV hz
      · intro hz
        obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU z hz
        exact ⟨_, ⟨z, ε, hε, rfl, hb⟩, Metric.mem_ball_self hε⟩
    obtain ⟨T, hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable S (by
      rintro V ⟨c, r, -, rfl, -⟩; exact Metric.isOpen_ball)
    rw [hSU] at hTU
    rcases Set.eq_empty_or_nonempty T with hT | hT
    · have e : P05.indicator (k := k) (f.val ⁻¹' U) hUm = constant 0 := by
        apply Subtype.ext; funext t
        have : f.val t ∉ U := by rw [← hTU, hT, Set.sUnion_empty]; exact id
        simp [P05.indicator, Set.indicator, this, constant]
      rw [e]; exact g58b_co_const F G hF hG 0
    · obtain ⟨gs, rfl⟩ := hTc.exists_eq_range hT
      have hball : ∀ n, ∃ c r, 0 < r ∧ gs n = Metric.ball c r := fun n => by
        obtain ⟨c, r, hr, h, -⟩ := hTS ⟨n, rfl⟩; exact ⟨c, r, hr, h⟩
      choose cs rs hrs hgs using hball
      have hm : ∀ n, MeasurableSet (f.val ⁻¹' gs n) := fun n => by
        rw [hgs n]; exact f.property measurableSet_ball
      have hU' : f.val ⁻¹' U = ⋃ n, f.val ⁻¹' gs n := by
        rw [← hTU, Set.sUnion_range, Set.preimage_iUnion]
      have := g58b_co_union F G hF hG (fun n => f.val ⁻¹' gs n) hm (fun n => by
        have e : P05.indicator (k := k) (f.val ⁻¹' gs n) (hm n) =
            P05.indicator (f.val ⁻¹' Metric.ball (cs n) (rs n)) (f.property measurableSet_ball) := by
          congr 1; rw [hgs n]
        rw [e]; exact g58b_co_ball F G hF hG hf _ _ (hrs n))
      have e : P05.indicator (k := k) (f.val ⁻¹' U) hUm = P05.indicator (⋃ n, f.val ⁻¹' gs n)
          (MeasurableSet.iUnion hm) := by congr 1
      rw [e]; exact this
  have hB' : MeasurableSet[borel k] B := by rw [← BorelSpace.measurable_eq]; exact hB
  have main : Q B := by
    refine MeasurableSpace.generateFrom_induction {s : Set k | IsOpen s} (fun s _ => Q s)
      (fun t ht _ => hopen t ht) ?_ ?_ ?_ B hB'
    · refine ⟨MeasurableSet.empty, ?_⟩
      have e : P05.indicator (k := k) (f.val ⁻¹' (∅ : Set k)) MeasurableSet.empty = constant 0 :=
        Subtype.ext (funext fun t => by simp [P05.indicator, constant])
      rw [e]; exact g58b_co_const F G hF hG 0
    · rintro t - ⟨ht, h⟩
      refine ⟨ht.compl, ?_⟩
      exact g58b_co_compl F G hF hG _ ht h
    · rintro s - hs
      choose hm hE using hs
      have hm' : MeasurableSet (⋃ i, f.val ⁻¹' s i) := MeasurableSet.iUnion hm
      refine ⟨by rw [Set.preimage_iUnion]; exact hm', ?_⟩
      have e : P05.indicator (k := k) (f.val ⁻¹' ⋃ i, s i) (by rw [Set.preimage_iUnion]; exact hm') =
          P05.indicator (⋃ i, f.val ⁻¹' s i) hm' := by congr 1; exact Set.preimage_iUnion
      rw [e]; exact g58b_co_union F G hF hG _ hm hE
  obtain ⟨_, h⟩ := main
  exact h

end g58bCo2

theorem g58b_coincidence (F G : P05.Symbol X k → Relation H)
    (hF : Calculus F) (hG : Calculus G) : EightProperties {f | F f = G f} := by
  have hreal : ∀ f : P05.Symbol X k, RealValued f → ∀ t, f.val t = ((RCLike.re (f.val t) : ℝ) : k) :=
    fun f hf t => (RCLike.conj_eq_iff_re.mp (by rw [← RCLike.star_def]; exact hf t)).symm
  have hqe : ∀ f : P05.Symbol X k, quadraticRegularizer f = g58b_q f := fun f =>
    Subtype.ext (funext fun t => by rw [g58b_q_val]; rfl)
  refine ⟨⟨fun c => g58b_co_const F G hF hG c, fun f g hf hg =>
      ⟨g58b_co_plus F G hF hG hf hg, g58b_co_times F G hF hG hf hg⟩,
      fun f hf => g58b_co_star F G hF hG hf⟩,
    fun f hf hne => g58b_co_recip F G hF hG hf hne, fun f => ?_,
    fun fn f hfn hpt => g58b_co_lim F G hF hG hfn hpt,
    fun f hf => g58b_co_abs F G hF hG hf, ?_, ⟨?_, fun A hA h => g58b_co_compl F G hF hG A hA h,
      fun A hA h => g58b_co_union F G hF hG A hA h⟩,
    fun f hf B hB => g58b_co_preimage F G hF hG hf B hB⟩
  · rw [hqe]
    constructor
    · intro hf
      have hq := g58b_co_q F G hF hG hf
      exact ⟨g58b_co_times F G hF hG hf hq, hq⟩
    · rintro ⟨h1, h2⟩
      have e : times f (g58b_q f) = times (g58b_q f) f := Subtype.ext (funext fun t => mul_comm _ _)
      rw [e] at h1
      exact g58b_co_reg F G hF hG _ _ (g58b_q_ne f) ⟨1, fun t => (g58b_q_bdd f t).1⟩
        ⟨1, fun t => (g58b_q_bdd f t).2⟩ h2 h1
  · intro f g hf hg rf rg
    have hd := g58b_co_abs F G hF hG (g58b_co_plus F G hF hG hf (g58b_co_scalar F G hF hG (-1) hg))
    have hs := g58b_co_plus F G hF hG hf hg
    have habs : ∀ t, ‖f.val t + -1 * g.val t‖ = |RCLike.re (f.val t) - RCLike.re (g.val t)| := by
      intro t
      rw [hreal f rf t, hreal g rg t, neg_one_mul, ← sub_eq_add_neg, ← RCLike.ofReal_sub,
        RCLike.norm_ofReal]
      simp
    constructor
    · have e : realMax f g = scalar (1 / 2) (plus (plus f g) (absolute (plus f (scalar (-1) g)))) := by
        apply Subtype.ext; funext t
        simp only [realMax, scalar, plus, absolute]
        rw [habs t, hreal f rf t, hreal g rg t]
        simp only [RCLike.ofReal_re]
        rcases le_total (RCLike.re (f.val t)) (RCLike.re (g.val t)) with h | h
        · rw [max_eq_right h, abs_of_nonpos (by linarith)]; push_cast; ring
        · rw [max_eq_left h, abs_of_nonneg (by linarith)]; push_cast; ring
      show F (realMax f g) = G (realMax f g)
      rw [e]; exact g58b_co_scalar F G hF hG _ (g58b_co_plus F G hF hG hs hd)
    · have e : realMin f g = scalar (1 / 2) (plus (plus f g)
          (scalar (-1) (absolute (plus f (scalar (-1) g))))) := by
        apply Subtype.ext; funext t
        simp only [realMin, scalar, plus, absolute]
        rw [habs t, hreal f rf t, hreal g rg t]
        simp only [RCLike.ofReal_re]
        rcases le_total (RCLike.re (f.val t)) (RCLike.re (g.val t)) with h | h
        · rw [min_eq_left h, abs_of_nonpos (by linarith)]; push_cast; ring
        · rw [min_eq_right h, abs_of_nonneg (by linarith)]; push_cast; ring
      show F (realMin f g) = G (realMin f g)
      rw [e]; exact g58b_co_scalar F G hF hG _ (g58b_co_plus F G hF hG hs
        (g58b_co_scalar F G hF hG _ hd))
  · have e : P05.indicator (k := k) (Set.univ : Set X) MeasurableSet.univ = constant 1 :=
      Subtype.ext (funext fun x => by simp [P05.indicator, constant])
    show F _ = G _
    rw [e]; exact g58b_co_const F G hF hG 1

theorem solution (F G : P05.Symbol X k → Relation H)
    (hF : Calculus F) (hG : Calculus G) : EightProperties {f | F f = G f} := g58b_coincidence F G hF hG
