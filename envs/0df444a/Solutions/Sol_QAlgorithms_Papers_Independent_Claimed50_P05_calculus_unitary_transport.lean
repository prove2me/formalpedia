-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.calculus_unitary_transport
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:33:27.35292+00:00
-- url     : https://prove2.me/submissions/bf524648-36af-4d27-961e-4282fc09800d

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

theorem solution (F : P05.Symbol X k → Relation H) (hF : Calculus F)
    (U : H ≃ₗᵢ[k] K) : Calculus (fun f => unitaryGraphTransport U (F f)) := g58b_unitary F hF U
