-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_null_characterizations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:43:57.272035+00:00
-- url     : https://prove2.me/submissions/458de2d3-31c1-4bef-9ac4-c1c7242f7149

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

theorem solution (F : P05.Symbol X k → Relation H) (hF : Calculus F) :
    (∀ (f : P05.Symbol X k) (h : MeasurableSet {x | f.val x ≠ 0}),
      kernel (F f) = kernel (F (P05.indicator {x | f.val x ≠ 0} h))) ∧
    (∀ f, F f = zeroGraph ↔ Almost F (fun x => f.val x = 0)) ∧
    (∀ f g, F f = F g ↔ Almost F (fun x => f.val x = g.val x)) ∧
    (∀ f, InjectiveOperator (F f) ↔ Almost F (fun x => f.val x ≠ 0)) := g58b_nullchar F hF
