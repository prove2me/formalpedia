-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_pvm_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:37:20.602332+00:00
-- url     : https://prove2.me/submissions/b4fcd969-ed02-4869-8149-ccafe39ed6a5

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

theorem solution (F G : P05.Symbol X k → Relation H)
    (hF : Calculus F) (hG : Calculus G)
    (h : ∀ A (hA : MeasurableSet A), F (P05.indicator A hA) = G (P05.indicator A hA)) : F = G :=
  g58b_pvm_unique F G hF hG h
