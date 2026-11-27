-- Prove2me | solution 1 for OpaquePricing.Dominance.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:21:30.1661+00:00
-- url     : https://prove2.me/submissions/6b4978d7-6618-490e-8b52-46e37bd9ccd4

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_OneOpaque

open MeasureTheory

open OpaquePricing
open OpaquePricing.Dominance
open OpaquePricing.Dominance.Supplement

theorem solution {N : ℕ} (hN : 2 ≤ N) (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (α : ℝ) (hα : α ∈ Set.Icc 0 1)
    (hex : Exchangeable μ) (htwo : TwoValued μ) :
    ENNReal.ofReal (719 / 1000 : ℝ) * optDP μ ≤ optOne μ α := by
      obtain ⟨a, b, hab, hsupp⟩ := htwo
      have hle1 : ∀ p r : ℝ, 0 ≤ p → 0 ≤ r → expOne μ α p r ≤ optOne μ α := fun p r hp hr =>
        le_iSup₂_of_le (f := fun p r => ⨆ (_ : 0 ≤ p ∧ 0 ≤ r), expOne μ α p r) p r
          (le_iSup_of_le ⟨hp, hr⟩ le_rfl)
      have hmix : ∀ p r : ℝ, ∀ X : ENNReal,
          X ≤ ∫⁻ v, ENNReal.ofReal (oneRevenue pessValue p r v) ∂μ →
          X ≤ ∫⁻ v, ENNReal.ofReal (oneRevenue rnValue p r v) ∂μ → X ≤ expOne μ α p r := by
        intro p r X h1 h2
        have hsum : ENNReal.ofReal α + ENNReal.ofReal (1 - α) = 1 := by
          rw [← ENNReal.ofReal_add hα.1 (by linarith [hα.2])]; simp
        calc X = (ENNReal.ofReal α + ENNReal.ofReal (1 - α)) * X := by rw [hsum, one_mul]
          _ = ENNReal.ofReal α * X + ENNReal.ofReal (1 - α) * X := add_mul _ _ _
          _ ≤ _ := by unfold expOne; gcongr
      have L2 : ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (u price : ι → ℝ) (o : ι), o ∈ s → 0 ≤ u o →
          (∀ o' ∈ s, u o' ≤ u o) → price o ≤ menuRevenue s u price := by
        intro ι _ s u price o hos hu hmax
        simp only [menuRevenue]
        split_ifs with h
        · exact Finset.le_sup' price (Finset.mem_filter.2 ⟨hos, hu, hmax⟩)
        · exact absurd ⟨o, Finset.mem_filter.2 ⟨hos, hu, hmax⟩⟩ h
      have L3 : ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (u price : ι → ℝ) (M : ℝ), 0 ≤ M →
          (∀ o ∈ s, 0 ≤ u o → (∀ o' ∈ s, u o' ≤ u o) → price o ≤ M) → menuRevenue s u price ≤ M := by
        intro ι _ s u price M hM h
        simp only [menuRevenue]
        split_ifs with hn
        · exact Finset.sup'_le _ _ (fun o ho => by
            obtain ⟨h1, h2, h3⟩ := by simpa only [Finset.mem_filter] using ho
            exact h o h1 h2 h3)
        · exact hM
      have L1 : ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (u price : ι → ℝ) (m : ℝ) (o : ι), o ∈ s →
          0 ≤ u o → (∀ o' ∈ s, m ≤ price o') → m ≤ menuRevenue s u price := by
        intro ι _ s u price m o hos hu hm
        obtain ⟨w, hw, hwmax⟩ := Finset.exists_max_image s u ⟨o, hos⟩
        exact le_trans (hm w hw) (L2 s u price w hw (le_trans hu (hwmax o hos)) hwmax)
      have hNpos : 0 < N := by omega
      have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNr
      set i0 : Fin N := ⟨0, hNpos⟩ with hi0
      have hgood : ∀ᵐ v ∂μ, (∀ i, 0 ≤ v i) ∧ (∀ i, v i = a ∨ v i = b) := hμ.and hsupp
      have hb0 : 0 ≤ b := by
        obtain ⟨v, hv1, hv2⟩ := hgood.exists
        rcases hv2 i0 with h | h
        · linarith [hv1 i0]
        · linarith [hv1 i0]
      have hK : Measurable (fun v : Fin N → ℝ => highCount b v) := by
        have : (fun v : Fin N → ℝ => highCount b v) = fun v => ∑ i : Fin N, (if v i = b then 1 else 0 : ℕ) := by
          funext v; rw [highCount, Finset.card_filter]
        rw [this]
        refine Finset.measurable_sum _ (fun i _ => ?_)
        exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply i) measurable_const) measurable_const measurable_const
      have hKle : ∀ v : Fin N → ℝ, highCount b v ≤ N := by
        intro v
        unfold highCount
        calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_filter_le _ _
          _ = N := by simp
      set π : ℕ → ℝ := fun k => (μ {v | highCount b v = k}).toReal with hπdef
      have hπ0 : ∀ k, 0 ≤ π k := fun k => ENNReal.toReal_nonneg
      have hE : ∀ g : ℕ → ℝ, (∀ k, 0 ≤ g k) → ∫⁻ v, ENNReal.ofReal (g (highCount b v)) ∂μ
          = ENNReal.ofReal (∑ k ∈ Finset.range (N+1), g k * π k) := by
        intro g hg
        have hms : ∀ k : ℕ, MeasurableSet {v : Fin N → ℝ | highCount b v = k} := fun k =>
          hK (measurableSet_singleton k)
        have h1 : ∀ v, ENNReal.ofReal (g (highCount b v)) = ∑ k ∈ Finset.range (N+1),
            {v : Fin N → ℝ | highCount b v = k}.indicator (fun _ => ENNReal.ofReal (g k)) v := by
          intro v
          rw [Finset.sum_eq_single (highCount b v)]
          · simp [Set.indicator]
          · intro k _ hk; simp [Set.indicator, Ne.symm hk]
          · intro h; exfalso; apply h; simp only [Finset.mem_range]; have := hKle v; omega
        rw [lintegral_congr h1, lintegral_finset_sum _ (fun k _ => measurable_const.indicator (hms k))]
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hg k) (hπ0 k))]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [lintegral_indicator_const (hms k), ENNReal.ofReal_mul (hg k), hπdef]
        simp only
        rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
      have hπ1 : ∑ k ∈ Finset.range (N+1), π k = 1 := by
        have := hE (fun _ => 1) (fun _ => zero_le_one)
        simp only [ENNReal.ofReal_one, lintegral_const, measure_univ, one_mul, mul_one] at this
        have h2 := congrArg ENNReal.toReal this
        rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun k _ => hπ0 k))] at h2
        simpa using h2.symm
      have hsumv : ∀ v : Fin N → ℝ, (∀ i, v i = a ∨ v i = b) →
          ∑ i, v i = N * a + (b - a) * highCount b v := by
        intro v hv
        have : ∀ i, v i = a + (b - a) * (if v i = b then 1 else 0) := by
          intro i; rcases hv i with h | h
          · have : v i ≠ b := by rw [h]; exact ne_of_lt hab
            rw [if_neg this, h]; ring
          · simp [h]
        rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [highCount, Finset.sum_boole]
      have hKge : ∀ (v : Fin N → ℝ) i, v i = b → 1 ≤ highCount b v := by
        intro v i h
        unfold highCount
        exact Finset.card_pos.2 ⟨i, by simp [h]⟩
      have hKpos : ∀ v : Fin N → ℝ, 1 ≤ highCount b v → ∃ i, v i = b := by
        intro v h
        unfold highCount at h
        obtain ⟨i, hi⟩ := Finset.card_pos.1 h
        exact ⟨i, (Finset.mem_filter.1 hi).2⟩
      have hKltN : ∀ v : Fin N → ℝ, (∀ i, v i = a ∨ v i = b) → highCount b v < N → ∃ j, v j = a := by
        intro v hv h
        by_contra hne
        push_neg at hne
        have : highCount b v = N := by
          unfold highCount
          rw [Finset.filter_true_of_mem (fun i _ => (hv i).resolve_left (hne i))]
          simp
        omega
      have hsing : ∀ i : Fin N, ({i} : Finset (Fin N)) ∈ oneOptions N := by
        intro i; simp [oneOptions, opqOptions]
      have huniv : (Finset.univ : Finset (Fin N)) ∈ oneOptions N := by
        simp [oneOptions, opqOptions, Finset.univ_nonempty_iff]; exact ⟨i0⟩
      have hcases : ∀ S ∈ oneOptions N, (∃ j, S = {j}) ∨ S = Finset.univ := by
        intro S hS
        simp only [oneOptions, Finset.mem_filter] at hS
        rcases hS.2 with h | h
        · exact Or.inl (Finset.card_eq_one.1 h)
        · exact Or.inr h
      have hpr1 : ∀ (p r : ℝ) (i : Fin N), opqPrice p (fun _ => r) ({i} : Finset (Fin N)) = p := by
        intro p r i; simp [opqPrice]
      have hpru : ∀ (p r : ℝ), opqPrice p (fun _ => r) (Finset.univ : Finset (Fin N)) = r := by
        intro p r; simp [opqPrice]; omega
      have hpess1 : ∀ (v : Fin N → ℝ) i, pessValue v {i} = v i := by
        intro v i; simp [pessValue]
      have hrn1 : ∀ (v : Fin N → ℝ) i, rnValue v {i} = v i := by
        intro v i; simp [rnValue]
      have hpessu : ∀ (v : Fin N → ℝ), (∀ i, v i = a ∨ v i = b) → a ≤ pessValue v Finset.univ ∧
          (∀ j, pessValue v Finset.univ ≤ v j) := by
        intro v hv
        have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨i0, Finset.mem_univ _⟩
        simp only [pessValue, dif_pos hne]
        refine ⟨Finset.le_inf' _ _ (fun j _ => ?_), fun j => Finset.inf'_le _ (Finset.mem_univ j)⟩
        rcases hv j with h | h <;> linarith
      have hrnu : ∀ (v : Fin N → ℝ), (∀ i, v i = a ∨ v i = b) →
          rnValue v Finset.univ = a + (b - a) * highCount b v / N := by
        intro v hv
        simp only [rnValue, hsumv v hv, Finset.card_univ, Fintype.card_fin]
        field_simp
      have hptθ : ∀ (val : (Fin N → ℝ) → Finset (Fin N) → ℝ) (θ : ℝ) (v : Fin N → ℝ), 0 ≤ θ → θ < 1 →
          (∀ i, v i = a ∨ v i = b) → (∀ i, val v {i} = v i) → a ≤ val v Finset.univ →
          (1 ≤ highCount b v ∧ (highCount b v : ℝ) ≤ θ * N → val v Finset.univ ≤ a + (b - a) * θ) →
          a + (b - a) * (1 - θ) * (if 1 ≤ highCount b v ∧ (highCount b v : ℝ) ≤ θ * N then 1 else 0)
            ≤ oneRevenue val (b - (b - a) * θ) a v := by
        intro val θ v hθ0 hθ1 hv hval1 hvalu hvalE
        have hpa : a ≤ b - (b - a) * θ := by nlinarith
        unfold oneRevenue
        by_cases hEv : 1 ≤ highCount b v ∧ (highCount b v : ℝ) ≤ θ * N
        · rw [if_pos hEv]
          obtain ⟨i, hi⟩ := hKpos v hEv.1
          have := L2 (oneOptions N) (fun S => val v S - opqPrice (b - (b - a) * θ) (fun _ => a) S)
            (opqPrice (b - (b - a) * θ) (fun _ => a)) {i} (hsing i) (by
              simp only [hval1, hpr1, hi]; nlinarith) (by
              intro S hS
              rcases hcases S hS with ⟨j, rfl⟩ | rfl
              · simp only [hval1, hpr1, hi]; rcases hv j with h | h <;> rw [h] <;> linarith
              · simp only [hval1, hpr1, hi, hpru]; linarith [hvalE hEv])
          rw [hpr1] at this
          linarith
        · rw [if_neg hEv]
          have := L1 (oneOptions N) (fun S => val v S - opqPrice (b - (b - a) * θ) (fun _ => a) S)
            (opqPrice (b - (b - a) * θ) (fun _ => a)) a Finset.univ huniv (by
              simp only [hpru]; linarith) (by
              intro S hS
              rcases hcases S hS with ⟨j, rfl⟩ | rfl
              · rw [hpr1]; exact hpa
              · rw [hpru])
          linarith
      have hptB : ∀ (val : (Fin N → ℝ) → Finset (Fin N) → ℝ) (v : Fin N → ℝ),
          (∀ i, v i = a ∨ v i = b) → (∀ i, val v {i} = v i) → val v Finset.univ ≤ b →
          ENNReal.ofReal (b * (if 1 ≤ highCount b v then 1 else 0)) ≤ ENNReal.ofReal (oneRevenue val b b v) := by
        intro val v hv hval1 hvalu
        by_cases hk : 1 ≤ highCount b v
        · rw [if_pos hk, mul_one]
          apply ENNReal.ofReal_le_ofReal
          obtain ⟨i, hi⟩ := hKpos v hk
          have := L2 (oneOptions N) (fun S => val v S - opqPrice b (fun _ => b) S)
            (opqPrice b (fun _ => b)) {i} (hsing i) (by
              simp only [hval1, hpr1, hi]; linarith) (by
              intro S hS
              rcases hcases S hS with ⟨j, rfl⟩ | rfl
              · simp only [hval1, hpr1, hi]; rcases hv j with h | h <;> rw [h] <;> linarith
              · simp only [hval1, hpr1, hi, hpru]; linarith)
          rw [hpr1] at this
          exact this
        · rw [if_neg hk, mul_zero, ENNReal.ofReal_zero]; exact bot_le
      have hDPpt : ∀ (p : Fin N → ℝ) (v : Fin N → ℝ), (∀ i, 0 ≤ p i) → (∀ i, v i = a ∨ v i = b) →
          ((∀ i, a < p i) → dpRevenue p v ≤ b * (if 1 ≤ highCount b v then 1 else 0)) ∧
          (∀ j, p j ≤ a → dpRevenue p v ≤ a + (b - a) * (if v j = a ∧ 1 ≤ highCount b v then 1 else 0)) := by
        intro p v hp hv
        have hvb : ∀ i, v i ≤ b := fun i => by rcases hv i with h | h <;> linarith
        constructor
        · intro hpa
          unfold dpRevenue
          apply L3 _ _ _ _ (by split_ifs <;> linarith)
          intro w _ hw _
          have hvw : v w = b := (hv w).resolve_left (by intro h; linarith [hpa w])
          rw [if_pos (hKge v w hvw)]; linarith
        · intro j hj
          unfold dpRevenue
          apply L3 _ _ _ _ (by split_ifs <;> nlinarith [hp j])
          intro w _ hw hmax
          have hm := hmax j (Finset.mem_univ j)
          by_cases hvj : v j = a
          · by_cases hk : 1 ≤ highCount b v
            · rw [if_pos ⟨hvj, hk⟩]; linarith [hvb w]
            · rw [if_neg (fun h => hk h.2)]
              have : v w = a := (hv w).resolve_right (fun h => hk (hKge v w h))
              linarith
          · have hvj' : v j = b := (hv j).resolve_left hvj
            rw [if_neg (fun h => hvj h.1)]; linarith [hvb w]
      set Q : ℝ := ∑ k ∈ Finset.range (N+1), (if 1 ≤ k then (1:ℝ) else 0) * π k with hQdef
      have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun k _ => mul_nonneg (by split_ifs <;> norm_num) (hπ0 k))
      have hoptB : ENNReal.ofReal (b * Q) ≤ optOne μ α := by
        have hg : ∀ k, 0 ≤ b * (if 1 ≤ k then (1:ℝ) else 0) := fun k => mul_nonneg hb0 (by split_ifs <;> norm_num)
        have hsum : b * Q = ∑ k ∈ Finset.range (N+1), b * (if 1 ≤ k then (1:ℝ) else 0) * π k := by
          rw [hQdef, Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
        rw [hsum, ← hE _ hg]
        refine le_trans ?_ (hle1 b b hb0 hb0)
        apply hmix
        · refine lintegral_mono_ae (hgood.mono fun v hv => ?_)
          exact hptB pessValue v hv.2 (hpess1 v) (le_trans ((hpessu v hv.2).2 i0) (by rcases hv.2 i0 with h | h <;> linarith))
        · refine lintegral_mono_ae (hgood.mono fun v hv => ?_)
          refine hptB rnValue v hv.2 (hrn1 v) ?_
          rw [hrnu v hv.2]
          have : (highCount b v : ℝ) ≤ N := by exact_mod_cast hKle v
          have : (b - a) * highCount b v / N ≤ b - a := by
            rw [div_le_iff₀ hNr]; nlinarith
          linarith
      by_cases ha : 0 ≤ a
      swap
      · have hDP : optDP μ ≤ ENNReal.ofReal (b * Q) := by
          refine iSup₂_le (fun p hp => ?_)
          have hg : ∀ k, 0 ≤ b * (if 1 ≤ k then (1:ℝ) else 0) := fun k => mul_nonneg hb0 (by split_ifs <;> norm_num)
          have hsum : b * Q = ∑ k ∈ Finset.range (N+1), b * (if 1 ≤ k then (1:ℝ) else 0) * π k := by
            rw [hQdef, Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
          rw [hsum, ← hE _ hg]
          refine lintegral_mono_ae (hgood.mono fun v hv => ENNReal.ofReal_le_ofReal ?_)
          exact (hDPpt p v hp hv.2).1 (fun i => by linarith [hp i])
        calc ENNReal.ofReal (719 / 1000 : ℝ) * optDP μ ≤ 1 * optDP μ := by
              gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
          _ ≤ optOne μ α := by rw [one_mul]; exact le_trans hDP hoptB
      set h : Fin N → (Fin N → ℝ) → ENNReal := fun i v =>
        ENNReal.ofReal (a + (b - a) * (if v i = a ∧ 1 ≤ highCount b v then 1 else 0)) with hhdef
      have hhm : ∀ i, Measurable (h i) := by
        intro i
        refine ENNReal.measurable_ofReal.comp (measurable_const.add (measurable_const.mul ?_))
        refine Measurable.ite ?_ measurable_const measurable_const
        exact (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).inter
          (hK (MeasurableSet.of_discrete (s := {k : ℕ | 1 ≤ k})))
      have hKperm : ∀ (σ : Equiv.Perm (Fin N)) (v : Fin N → ℝ), highCount b (v ∘ σ) = highCount b v := by
        intro σ v
        simp only [highCount, Finset.card_filter, Function.comp]
        exact Equiv.sum_comp σ (fun i => if v i = b then 1 else 0)
      have hHeq : ∀ j, ∫⁻ v, h j v ∂μ = ∫⁻ v, h i0 v ∂μ := by
        intro j
        have hφ : Measurable (fun v : Fin N → ℝ => v ∘ (Equiv.swap i0 j)) :=
          measurable_pi_lambda _ (fun i => measurable_pi_apply _)
        conv_rhs => rw [← hex (Equiv.swap i0 j)]
        rw [lintegral_map (hhm i0) hφ]
        refine lintegral_congr (fun v => ?_)
        simp only [hhdef, Function.comp, Equiv.swap_apply_left]
        rw [hKperm]
      set gS : ℕ → ℝ := fun k => N * a + (b - a) * (if 1 ≤ k ∧ k ≤ N then ((N:ℝ) - k) else 0) with hgSdef
      have hgS0 : ∀ k, 0 ≤ gS k := by
        intro k; simp only [hgSdef]
        have : 0 ≤ (if 1 ≤ k ∧ k ≤ N then ((N:ℝ) - k) else 0) := by
          split_ifs with hk
          · have : (k:ℝ) ≤ N := by exact_mod_cast hk.2
            linarith
          · exact le_refl _
        have : 0 ≤ (N:ℝ) * a := mul_nonneg hNr.le ha
        nlinarith
      have hcount : ∀ v : Fin N → ℝ, (∀ i, v i = a ∨ v i = b) →
          ((Finset.univ.filter (fun i => v i = a)).card : ℝ) = N - highCount b v := by
        intro v hv
        have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
          (p := fun i => v i = b)
        have h2 : Finset.univ.filter (fun i => ¬ v i = b) = Finset.univ.filter (fun i => v i = a) := by
          refine Finset.filter_congr (fun i _ => ?_)
          constructor
          · intro hne; exact (hv i).resolve_right hne
          · intro he; rw [he]; exact ne_of_lt hab
        rw [h2] at h1
        simp only [Finset.card_univ, Fintype.card_fin] at h1
        unfold highCount
        have : ((Finset.univ.filter (fun i => v i = b)).card : ℝ) + (Finset.univ.filter (fun i => v i = a)).card = N := by
          exact_mod_cast h1
        linarith
      have hHsum : (N : ENNReal) * ∫⁻ v, h i0 v ∂μ = ENNReal.ofReal (∑ k ∈ Finset.range (N+1), gS k * π k) := by
        rw [← hE gS hgS0]
        have : (N : ENNReal) * ∫⁻ v, h i0 v ∂μ = ∑ i : Fin N, ∫⁻ v, h i v ∂μ := by
          rw [Finset.sum_congr rfl (fun i _ => hHeq i)]; simp
        rw [this, ← lintegral_finset_sum _ (fun i _ => hhm i)]
        refine lintegral_congr_ae (hgood.mono fun v hv => ?_)
        simp only [hhdef]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> nlinarith)]
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hgSdef]
        congr 1
        by_cases hk : 1 ≤ highCount b v
        · have hk2 : highCount b v ≤ N := hKle v
          simp only [hk, and_true, hk2, true_and, if_true]
          rw [Finset.sum_boole]
          rw [hcount v hv.2]
        · simp [hk]
      set Dmix : ℝ := (∑ k ∈ Finset.range (N+1), gS k * π k) / N with hDmixdef
      have hHi0 : ∫⁻ v, h i0 v ∂μ = ENNReal.ofReal Dmix := by
        have hN' : (N : ENNReal) ≠ 0 := by exact_mod_cast hNpos.ne'
        have hNt : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
        rw [hDmixdef, ENNReal.ofReal_div_of_pos hNr, ← hHsum, ENNReal.ofReal_natCast,
          mul_comm, ENNReal.mul_div_cancel_right hN' hNt]
      have hDP : optDP μ ≤ ENNReal.ofReal (max (b * Q) Dmix) := by
        refine iSup₂_le (fun p hp => ?_)
        by_cases hall : ∀ i, a < p i
        · have hg : ∀ k, 0 ≤ b * (if 1 ≤ k then (1:ℝ) else 0) := fun k => mul_nonneg hb0 (by split_ifs <;> norm_num)
          have hsum : b * Q = ∑ k ∈ Finset.range (N+1), b * (if 1 ≤ k then (1:ℝ) else 0) * π k := by
            rw [hQdef, Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
          refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_max_left _ _))
          rw [hsum, ← hE _ hg]
          refine lintegral_mono_ae (hgood.mono fun v hv => ENNReal.ofReal_le_ofReal ?_)
          exact (hDPpt p v hp hv.2).1 hall
        · push_neg at hall
          obtain ⟨j, hj⟩ := hall
          refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_max_right _ _))
          rw [← hHi0, ← hHeq j]
          refine lintegral_mono_ae (hgood.mono fun v hv => ENNReal.ofReal_le_ofReal ?_)
          exact (hDPpt p v hp hv.2).2 j hj
      set F : ℝ → ℝ := fun θ => ∑ k ∈ Finset.range (N+1),
        (if 1 ≤ k ∧ (k:ℝ) ≤ θ * N then (1:ℝ) else 0) * π k with hFdef
      have hF0 : ∀ θ, 0 ≤ F θ := fun θ =>
        Finset.sum_nonneg (fun k _ => mul_nonneg (by split_ifs <;> norm_num) (hπ0 k))
      have hoptθ : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → ENNReal.ofReal (a + (b - a) * (1 - θ) * F θ) ≤ optOne μ α := by
        intro θ hθ0 hθ1
        have hg : ∀ k : ℕ, 0 ≤ a + (b - a) * (1 - θ) * (if 1 ≤ k ∧ (k:ℝ) ≤ θ * N then (1:ℝ) else 0) := by
          intro k; have : 0 ≤ (b - a) * (1 - θ) := mul_nonneg (by linarith) (by linarith)
          split_ifs <;> nlinarith
        have hsum : a + (b - a) * (1 - θ) * F θ = ∑ k ∈ Finset.range (N+1),
            (a + (b - a) * (1 - θ) * (if 1 ≤ k ∧ (k:ℝ) ≤ θ * N then (1:ℝ) else 0)) * π k := by
          have : ∀ k ∈ Finset.range (N+1), (a + (b - a) * (1 - θ) * (if 1 ≤ k ∧ (k:ℝ) ≤ θ * N then (1:ℝ) else 0)) * π k
              = a * π k + (b - a) * (1 - θ) * ((if 1 ≤ k ∧ (k:ℝ) ≤ θ * N then (1:ℝ) else 0) * π k) :=
            fun k _ => by ring
          rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hπ1, hFdef]
          ring
        have hp0 : 0 ≤ b - (b - a) * θ := by nlinarith
        rw [hsum, ← hE _ hg]
        refine le_trans ?_ (hle1 _ a hp0 ha)
        apply hmix
        · refine lintegral_mono_ae (hgood.mono fun v hv => ENNReal.ofReal_le_ofReal ?_)
          refine hptθ pessValue θ v hθ0 hθ1 hv.2 (hpess1 v) (hpessu v hv.2).1 (fun hEv => ?_)
          have hlt : highCount b v < N := by
            have : (highCount b v : ℝ) < N := by nlinarith [hEv.2]
            exact_mod_cast this
          obtain ⟨j, hj⟩ := hKltN v hv.2 hlt
          have := (hpessu v hv.2).2 j
          have : 0 ≤ (b - a) * θ := mul_nonneg (by linarith) hθ0
          linarith
        · refine lintegral_mono_ae (hgood.mono fun v hv => ENNReal.ofReal_le_ofReal ?_)
          refine hptθ rnValue θ v hθ0 hθ1 hv.2 (hrn1 v) ?_ (fun hEv => ?_)
          · rw [hrnu v hv.2]
            have : 0 ≤ (b - a) * highCount b v / N :=
              div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hNr.le
            linarith
          · rw [hrnu v hv.2]
            have : (b - a) * highCount b v / N ≤ (b - a) * θ := by
              rw [div_le_iff₀ hNr]; nlinarith [hEv.2]
            linarith
      set T : ℝ → ℝ := fun θ => ∑ k ∈ Finset.range (N+1),
        (if 1 ≤ k ∧ k ≤ N then 1 - max ((k:ℝ) / N) θ else 0) * π k with hTdef
      have hTc : ∀ θ' θ : ℝ, 0 ≤ θ' → θ' ≤ θ → T θ' ≤ T θ + (θ - θ') * F θ := by
        intro θ' θ h0 hle
        rw [hTdef, hFdef, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum (fun k _ => ?_)
        have key : (if 1 ≤ k ∧ k ≤ N then 1 - max ((k:ℝ) / N) θ' else 0) ≤
            (if 1 ≤ k ∧ k ≤ N then 1 - max ((k:ℝ) / N) θ else 0) +
            (θ - θ') * (if 1 ≤ k ∧ (k:ℝ) ≤ θ * N then (1:ℝ) else 0) := by
          by_cases hk : 1 ≤ k ∧ k ≤ N
          · rw [if_pos hk, if_pos hk]
            by_cases hk2 : 1 ≤ k ∧ (k:ℝ) ≤ θ * N
            · rw [if_pos hk2]
              have : (k:ℝ) / N ≤ θ := by rw [div_le_iff₀ hNr]; exact hk2.2
              have h1 : max ((k:ℝ) / N) θ = θ := max_eq_right this
              have h2 : θ' ≤ max ((k:ℝ) / N) θ' := le_max_right _ _
              linarith
            · rw [if_neg hk2]
              have : θ < (k:ℝ) / N := by
                rw [lt_div_iff₀ hNr]; by_contra hc; push_neg at hc; exact hk2 ⟨hk.1, hc⟩
              rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
          · rw [if_neg hk, if_neg hk]
            split_ifs <;> nlinarith
        nlinarith [hπ0 k]
      have hTQ : ∀ θ : ℝ, θ ≤ 1 → T θ ≤ (1 - θ) * Q := by
        intro θ h1
        rw [hTdef, hQdef, Finset.mul_sum]
        refine Finset.sum_le_sum (fun k _ => ?_)
        have key : (if 1 ≤ k ∧ k ≤ N then 1 - max ((k:ℝ) / N) θ else 0) ≤ (1 - θ) * (if 1 ≤ k then (1:ℝ) else 0) := by
          by_cases hk : 1 ≤ k ∧ k ≤ N
          · rw [if_pos hk, if_pos hk.1]; have := le_max_right ((k:ℝ) / N) θ; linarith
          · rw [if_neg hk]; split_ifs <;> nlinarith
        nlinarith [hπ0 k]
      have hDT : Dmix = a + (b - a) * T 0 := by
        rw [hDmixdef, div_eq_iff hNne]
        have : ∀ k ∈ Finset.range (N+1), gS k * π k = N * (a * π k + (b - a) *
            ((if 1 ≤ k ∧ k ≤ N then 1 - max ((k:ℝ) / N) 0 else 0) * π k)) := by
          intro k _
          simp only [hgSdef]
          by_cases hk : 1 ≤ k ∧ k ≤ N
          · rw [if_pos hk, if_pos hk, max_eq_left (div_nonneg (Nat.cast_nonneg _) hNr.le)]
            field_simp
          · rw [if_neg hk, if_neg hk]; ring
        rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hπ1, hTdef]
        ring
      have hmulc : ∀ x y : ℝ, x ≤ y → (b - a) * x ≤ (b - a) * y := fun x y hxy =>
        mul_le_mul_of_nonneg_left hxy (by linarith)
      have hcF : ∀ θ, 0 ≤ (b - a) * F θ := fun θ => mul_nonneg (by linarith) (hF0 θ)
      have haQ : 0 ≤ a * Q := mul_nonneg ha hQ0
      calc ENNReal.ofReal (719 / 1000 : ℝ) * optDP μ ≤ ENNReal.ofReal (719 / 1000 : ℝ) * ENNReal.ofReal (max (b * Q) Dmix) := by gcongr
        _ = ENNReal.ofReal (719 / 1000 * max (b * Q) Dmix) := (ENNReal.ofReal_mul (by norm_num)).symm
        _ ≤ optOne μ α := by
          rcases le_total Dmix (b * Q) with hc | hc
          · rw [max_eq_left hc]
            exact le_trans (ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hb0 hQ0])) hoptB
          · rw [max_eq_right hc]
            by_contra hlt
            push_neg at hlt
            have hget : ∀ L : ℝ, ENNReal.ofReal L ≤ optOne μ α → L < 719 / 1000 * Dmix := fun L hL =>
              (ENNReal.ofReal_lt_ofReal_iff'.1 (lt_of_le_of_lt hL hlt)).1
            have hO1 := hget _ (hoptθ (1/10) (by norm_num) (by norm_num))
            have hO2 := hget _ (hoptθ (19/100) (by norm_num) (by norm_num))
            have hO3 := hget _ (hoptθ (26/100) (by norm_num) (by norm_num))
            have hO4 := hget _ (hoptθ (34/100) (by norm_num) (by norm_num))
            have hO5 := hget _ (hoptθ (2/5) (by norm_num) (by norm_num))
            have hO6 := hget _ (hoptθ (46/100) (by norm_num) (by norm_num))
            have hO7 := hget _ (hoptθ (52/100) (by norm_num) (by norm_num))
            have hO8 := hget _ (hoptθ (57/100) (by norm_num) (by norm_num))
            have hO9 := hget _ (hoptθ (61/100) (by norm_num) (by norm_num))
            have hC1 := hmulc _ _ (hTc (0) (1/10) (by norm_num) (by norm_num))
            have hQ1 := hmulc _ _ (hTQ (1/10) (by norm_num))
            have hC2 := hmulc _ _ (hTc (1/10) (19/100) (by norm_num) (by norm_num))
            have hQ2 := hmulc _ _ (hTQ (19/100) (by norm_num))
            have hC3 := hmulc _ _ (hTc (19/100) (26/100) (by norm_num) (by norm_num))
            have hQ3 := hmulc _ _ (hTQ (26/100) (by norm_num))
            have hC4 := hmulc _ _ (hTc (26/100) (34/100) (by norm_num) (by norm_num))
            have hQ4 := hmulc _ _ (hTQ (34/100) (by norm_num))
            have hC5 := hmulc _ _ (hTc (34/100) (2/5) (by norm_num) (by norm_num))
            have hQ5 := hmulc _ _ (hTQ (2/5) (by norm_num))
            have hC6 := hmulc _ _ (hTc (2/5) (46/100) (by norm_num) (by norm_num))
            have hQ6 := hmulc _ _ (hTQ (46/100) (by norm_num))
            have hC7 := hmulc _ _ (hTc (46/100) (52/100) (by norm_num) (by norm_num))
            have hQ7 := hmulc _ _ (hTQ (52/100) (by norm_num))
            have hC8 := hmulc _ _ (hTc (52/100) (57/100) (by norm_num) (by norm_num))
            have hQ8 := hmulc _ _ (hTQ (57/100) (by norm_num))
            have hC9 := hmulc _ _ (hTc (57/100) (61/100) (by norm_num) (by norm_num))
            have hQ9 := hmulc _ _ (hTQ (61/100) (by norm_num))
            have hBB := hget _ hoptB
            linarith [hcF (1/10), hcF (19/100), hcF (26/100), hcF (34/100), hcF (2/5), hcF (46/100), hcF (52/100), hcF (57/100), hcF (61/100), haQ, hDT, hc, hBB, hO1, hC1, hQ1, hO2, hC2, hQ2, hO3, hC3, hQ3, hO4, hC4, hQ4, hO5, hC5, hQ5, hO6, hC6, hQ6, hO7, hC7, hQ7, hO8, hC8, hQ8, hO9, hC9, hQ9]
