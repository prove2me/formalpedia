-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_localized_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:03:22.455997+00:00
-- url     : https://prove2.me/submissions/2f3a1e80-1e28-4fbe-ab52-c290ff388f92

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

theorem solution (F : P05.Symbol X k → Relation H) (G : P05.Symbol X k → Relation K)
    (hF : Calculus F) (hG : Calculus G) (T : H →L[k] K) (f : P05.Symbol X k)
    (A : Set X) (hA : MeasurableSet A) :
    ∃ (P : H →L[k] H) (Q : K →L[k] K),
      F (P05.indicator A hA) = boundedGraph P ∧ G (P05.indicator A hA) = boundedGraph Q ∧
      (Intertwines F G T f → Intertwines F G (Q.comp (T.comp P)) (times f (P05.indicator A hA))) ∧
      (Intertwines F G (Q.comp (T.comp P)) (times f (P05.indicator A hA)) →
        Intertwines F G (Q.comp (T.comp P)) f) := g58b_localized F G hF hG T f A hA
