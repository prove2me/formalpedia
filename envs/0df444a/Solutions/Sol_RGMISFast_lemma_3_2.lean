-- Prove2me | solution 1 for RGMISFast.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T23:31:56.628011+00:00
-- url     : https://prove2.me/submissions/e46d778d-e91c-4abf-95e5-f9a47be3618c

import Theorems.Thm_RGMISFast_lemma_5_2
import Definitions.Def_RGMISFast_AdmissibleTree
import Definitions.Def_RGMISFast_GoodEvent
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

 theorem settling_le_rank {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (v : V) :
    tau G r v ≤ r v := by
  classical
  by_cases hv : inMIS G r v = true
  · apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨v, by simp [hv], rfl⟩
  · have he := inMIS_eq G r v
    have hvf : inMIS G r v = false := Bool.eq_false_iff.mpr hv
    rw [hvf] at he
    obtain ⟨w, _, hw⟩ := List.all_eq_false.mp he.symm
    have hwyes : inMIS G r w.val = true := by simpa using hw
    have ha := (mem_lowerNbrs G r).1 w.property
    have hmin : tau G r v ≤ r w.val := by
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨w.val, by simp [ha.1,hwyes], rfl⟩
    exact hmin.trans ha.2.le

 theorem ancestor_closed_connected {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (u : V)
    (T : AdmissibleTree G r u) (S : Finset V) (hS : S ⊆ T.nodes)
    (hne : S.Nonempty) (hpar : ∀ w ∈ S, w ≠ u → T.par w ∈ S) :
    IsRootConnected G u S := by
  have hall : ∀ n, ∀ w ∈ S, T.depth w = n → u ∈ S ∧ (restrictTo G ↑S).Reachable u w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw hd
      by_cases he : w = u
      · subst w
        exact ⟨hw,SimpleGraph.Reachable.refl _⟩
      · have hp := hpar w hw he
        obtain ⟨hu,hr⟩ := ih (T.depth (T.par w)) (by simpa [hd] using T.depth_lt w (hS hw) he)
          (T.par w) hp rfl
        refine ⟨hu,hr.trans ?_⟩
        exact SimpleGraph.Adj.reachable (show (restrictTo G ↑S).Adj (T.par w) w from
          ⟨T.par_adj w (hS hw) he,hp,hw⟩)
  obtain ⟨w,hw⟩ := hne
  exact ⟨(hall _ w hw rfl).1,fun x hx => (hall _ x hx rfl).2⟩

 theorem prefix_connected {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (u : V)
    (T : AdmissibleTree G r u) (t : ℝ) (hne : (T.prefix t).Nonempty) :
    IsRootConnected G u (T.prefix t) := by
  apply ancestor_closed_connected G r u T (T.prefix t) (Finset.filter_subset _ _) hne
  intro w hw hwu
  obtain ⟨hw,ht⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨T.par_mem w hw hwu,
    ht.trans ((settling_le_rank G r w).trans (T.rank_le w hw hwu))⟩


lemma prefix_top_subset {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) : T.prefix a0 ⊆ C0 G r u := by
  classical
  intro w hw
  have hp := prefix_connected G r u T a0 ⟨w,hw⟩
  have hu : a0 ≤ tau G r u := (Finset.mem_filter.mp hp.1).2
  simp only [C0, if_pos hu, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(Finset.mem_filter.mp hw).2, (hp.2 w hw).mono ?_⟩
  intro x y hxy
  exact ⟨hxy.1,(Finset.mem_filter.mp hxy.2.1).2,(Finset.mem_filter.mp hxy.2.2).2⟩


lemma top_charge_card {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) : Sm r (T.prefix (am 0)) 0 = (T.prefix a0).card := by
  have ha : a0 ≠ 0 := (Real.exp_pos 2).ne'
  have he : am 0 = a0 := by simp [am]
  unfold Sm S
  rw [he]
  have hs : (∑ v ∈ T.prefix a0, rbar r v) = (T.prefix a0).card*a0 := by
    have hh : ∀ v ∈ T.prefix a0, rbar r v = a0 := by
      intro v hv
      exact min_eq_right ((Finset.mem_filter.mp hv).2.trans (settling_le_rank G r v))
    simp_rw [Finset.sum_congr rfl hh]
    simp
  rw [hs]
  field_simp

lemma top_charge_bound {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (L : ℝ) (htop : TopEvent G u L r) :
    Sm r (T.prefix (am 0)) 0 ≤ 1+L := by
  rw [top_charge_card]
  exact (Nat.cast_le.mpr (Finset.card_le_card (prefix_top_subset T))).trans htop


open RGMISFast
set_option autoImplicit false

lemma reachable_crossing {V : Type*} [DecidableEq V] (H : SimpleGraph V)
    (A : Finset V) {u v : V} (hu : u ∈ A) (hv : v ∉ A) (hr : H.Reachable u v) :
    ∃ x ∈ A, ∃ y, y ∉ A ∧ H.Adj x y := by
  classical
  by_contra! hn
  have closed : ∀ x y, x ∈ A → H.Adj x y → y ∈ A := by
    intro x y hx hxy
    by_contra hy
    exact hn x hx y hy hxy
  have hall : ∀ {x y : V}, H.Walk x y → x ∈ A → y ∈ A := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z h p ih => exact fun hx => ih (closed x y hx h)
  obtain ⟨p⟩ := hr
  exact hv (hall p hu)

lemma top_component_seed {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (u : V)
    (k : ℕ) (hk : k+1 ≤ (C0 G r u).card) :
    ∃ A : Finset V, IsRootConnected G u A ∧ A.card = k+1 ∧ ActiveAt G r a0 A := by
  classical
  have hu : a0 ≤ tau G r u := by
    by_contra hn
    simp [C0,hn] at hk
  have hmem : ∀ v, v ∈ C0 G r u ↔ a0 ≤ tau G r v ∧
      (restrictTo G {x | a0 ≤ tau G r x}).Reachable u v := by
    intro v
    simp [C0,hu]
  have huc : u ∈ C0 G r u := (hmem u).mpr ⟨hu,.refl _⟩
  have hex : ∀ n : ℕ, n+1 ≤ (C0 G r u).card →
      ∃ A : Finset V, A ⊆ C0 G r u ∧ IsRootConnected G u A ∧ A.card = n+1 := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨{u},?_,?_,by simp⟩
      · simpa using huc
      · refine ⟨by simp,?_⟩
        intro x hx
        simpa only [Finset.mem_singleton.mp hx] using
          (SimpleGraph.Reachable.refl (G := restrictTo G (↑({u}:Finset V))) u)
    | succ n ih =>
      intro hn
      obtain ⟨A,hAc,hA,hcard⟩ := ih (by omega)
      have hlt : A.card < (C0 G r u).card := by omega
      obtain ⟨v,hvc,hva⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      obtain ⟨x,hx,y,hy,hxy⟩ := reachable_crossing
        (restrictTo G {x | a0 ≤ tau G r x}) A hA.1 hva ((hmem v).mp hvc).2
      have hyc : y ∈ C0 G r u := (hmem y).mpr
        ⟨hxy.2.2, ((hmem x).mp (hAc hx)).2.trans hxy.reachable⟩
      have hmono : restrictTo G (↑A) ≤ restrictTo G (↑(insert y A)) := by
        intro p q hpq
        exact ⟨hpq.1,Finset.mem_insert_of_mem hpq.2.1,Finset.mem_insert_of_mem hpq.2.2⟩
      refine ⟨insert y A,Finset.insert_subset hyc hAc,?_,?_⟩
      · refine ⟨Finset.mem_insert_of_mem hA.1,?_⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with he | hz
        · subst z
          exact ((hA.2 x hx).mono hmono).trans
            (show (restrictTo G (↑(insert y A))).Adj x y from
              ⟨hxy.1,Finset.mem_insert_of_mem hx,Finset.mem_insert_self _ _⟩).reachable
        · exact (hA.2 z hz).mono hmono
      · rw [Finset.card_insert_of_notMem hy,hcard]
  obtain ⟨A,hAc,hA,hcard⟩ := hex k hk
  exact ⟨A,hA,hcard,fun v hv => ((hmem v).mp (hAc hv)).1⟩

lemma top_component_Y_pos {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (u : V)
    (k : ℕ) (hk : k+1 ≤ (C0 G r u).card) : 1 ≤ Y G u k a0 r := by
  classical
  obtain ⟨A,hA,hcard,hact⟩ := top_component_seed G r u k hk
  exact Finset.card_pos.mpr ⟨A,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hA,hcard,hact⟩⟩
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

lemma top_tail_from_moments {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (hY : ∀ k : ℕ, Measurable (fun r : V → ℝ => Y G u k a0 r) ∧
      ∫⁻ r, (Y G u k a0 r : ℝ≥0∞) ∂(rankLaw V) ≤
        ENNReal.ofReal ((Real.exp 1 / a0)^k)) (L : ℝ) :
    rankLaw V {r | ¬ TopEvent G u L r} ≤ ENNReal.ofReal (Real.exp (-L)) := by
  classical
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) := isProbabilityMeasure_expMeasure (by norm_num)
  have : IsProbabilityMeasure (rankLaw V) := by unfold rankLaw; infer_instance
  by_cases hL : 0 ≤ L
  · let k := ⌈L⌉₊
    have hkge : L ≤ (k:ℝ) := Nat.le_ceil L
    have hklt : (k:ℝ) < L+1 := Nat.ceil_lt_add_one hL
    have hmeas := (hY k).1
    have hm : Measurable (fun r : V → ℝ => (Y G u k a0 r : ℝ≥0∞)) := by fun_prop
    have hmark : rankLaw V {r | ¬ TopEvent G u L r} ≤
        ∫⁻ r, (Y G u k a0 r : ℝ≥0∞) ∂(rankLaw V) := by
      apply meas_le_lintegral₀ hm.aemeasurable
      intro r hr
      have hcard : 1+L < ((C0 G r u).card:ℝ) := lt_of_not_ge hr
      have hk : k < (C0 G r u).card := by
        have hh : (k:ℝ) < ((C0 G r u).card:ℝ) := by linarith
        exact_mod_cast hh
      exact_mod_cast top_component_Y_pos G r u k (by omega)
    have he : (Real.exp 1 / a0)^k = Real.exp (-(k:ℝ)) := by
      unfold a0
      rw [← Real.exp_sub]
      norm_num only [show (1:ℝ)-2 = -1 by norm_num]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ ≤ _ := hmark
      _ ≤ _ := (hY k).2
      _ = ENNReal.ofReal (Real.exp (-(k:ℝ))) := by rw [he]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
  · calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        exact Real.one_le_exp (by linarith)

lemma top_tree_consequences {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (L : ℝ)
    (r : V → ℝ) (htop : TopEvent G u L r) (T : AdmissibleTree G r u) :
    Sm r (T.prefix (am 0)) 0 = ((T.prefix (am 0)).card : ℝ) ∧
      ((T.prefix (am 0)).card : ℝ) ≤ 1+L := by
  have hc : Sm r (T.prefix (am 0)) 0 = ((T.prefix (am 0)).card : ℝ) := by
    simpa only [am, pow_zero, inv_one, mul_one] using top_charge_card T
  exact ⟨hc, hc ▸ top_charge_bound T L htop⟩
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (L : ℝ) :
    rankLaw V {r | ¬ TopEvent G u L r} ≤ ENNReal.ofReal (Real.exp (-L)) ∧
    ∀ r : V → ℝ, Function.Injective r → (∀ v, 0 ≤ r v) → TopEvent G u L r →
      ∀ T : AdmissibleTree G r u,
        Sm r (T.prefix (am 0)) 0 = ((T.prefix (am 0)).card : ℝ) ∧
        ((T.prefix (am 0)).card : ℝ) ≤ 1 + L := by
  refine ⟨top_tail_from_moments G u (fun k => lemma_5_2 G u a0 (Real.exp_pos 2) k) L, ?_⟩
  intro r _ _ ht T
  exact top_tree_consequences G u L r ht T

