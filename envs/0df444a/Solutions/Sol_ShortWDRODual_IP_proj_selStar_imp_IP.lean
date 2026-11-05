-- Prove2me | solution 1 for ShortWDRODual.IP.proj_selStar_imp_IP
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:24:47.225687+00:00
-- url     : https://prove2.me/submissions/5a9a2e43-c702-4896-872b-972271db50fa

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting
import Theorems.Thm_ShortWDRODual_IP_extIntegral_le_supFn
import Theorems.Thm_ShortWDRODual_IP_proj_supFn_nullMeasurable

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.IP Filter Topology
open scoped ENNReal

theorem PSI_extInt_mono {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → EReal}
    (h : ∀ᵐ x ∂μ, f x ≤ g x) : extIntegral μ f ≤ extIntegral μ g := by
  unfold extIntegral
  apply EReal.sub_le_sub
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (h.mono fun x hx => EReal.toENNReal_le_toENNReal hx))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (h.mono fun x hx => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hx)))

theorem PSI_extInt_le_of_trunc {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → EReal) (hF : Measurable F) (S : EReal)
    (h : ∀ k : ℕ, extIntegral μ (fun x => min (F x - ((2 / ((k : ℝ) + 1) : ℝ) : EReal))
      (((k : ℝ) + 1 : ℝ) : EReal)) ≤ S) :
    extIntegral μ F ≤ S := by
  set ε : ℕ → ℝ := fun k => 2 / ((k : ℝ) + 1) with hε
  set K : ℕ → ℝ := fun k => (k : ℝ) + 1 with hK
  have hεpos : ∀ k, 0 < ε k := fun k => by simp only [hε]; positivity
  have hKpos : ∀ k, 0 < K k := fun k => by simp only [hK]; positivity
  set H : ℕ → α → EReal := fun k x => min (F x - ((ε k : ℝ) : EReal)) ((K k : ℝ) : EReal)
    with hH
  have hHmeas : ∀ k, Measurable (H k) := fun k =>
    (hF.sub measurable_const).min measurable_const
  by_cases hb : ∫⁻ x, (-F x).toENNReal ∂μ = ⊤
  · unfold extIntegral
    rw [hb, EReal.coe_ennreal_top, EReal.sub_top]
    exact bot_le
  set b := ∫⁻ x, (-F x).toENNReal ∂μ with hbdef
  set B := b.toReal with hBdef
  have hbB : (b : EReal) = (B : EReal) := (EReal.coe_ennreal_toReal hb).symm
  have hmin : ∀ a b : ℝ, ((min a b : ℝ) : EReal) = min (a : EReal) (b : EReal) :=
    fun a b => EReal.coe_strictMono.monotone.map_min
  -- (i) negative parts
  have hneg_pt : ∀ k x, (-(H k x)).toENNReal ≤ (-F x).toENNReal + ENNReal.ofReal (ε k) := by
    intro k x
    simp only [hH]
    induction F x using EReal.rec with
    | bot => simp
    | top =>
      rw [EReal.top_sub_coe, min_eq_right le_top, EReal.toENNReal_of_nonpos]
      · exact bot_le
      · rw [← EReal.coe_neg]; exact_mod_cast (neg_neg_of_pos (hKpos k)).le
    | coe r =>
      rw [← EReal.coe_sub, ← hmin, ← EReal.coe_neg, ← EReal.coe_neg,
        EReal.real_coe_toENNReal, EReal.real_coe_toENNReal]
      refine le_trans ?_ ENNReal.ofReal_add_le
      rw [ENNReal.ofReal_le_ofReal_iff']
      rcases le_total (r - ε k) (K k) with hle | hle
      · left; rw [min_eq_left hle]; linarith
      · right; rw [min_eq_right hle]; linarith [hKpos k]
  have hneg : ∀ k, ∫⁻ x, (-(H k x)).toENNReal ∂μ ≤ b + ENNReal.ofReal (ε k) := by
    intro k
    calc ∫⁻ x, (-(H k x)).toENNReal ∂μ
        ≤ ∫⁻ x, ((-F x).toENNReal + ENNReal.ofReal (ε k)) ∂μ := lintegral_mono (hneg_pt k)
      _ = b + ENNReal.ofReal (ε k) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  -- (ii) positive parts converge
  have hmono : ∀ x, Monotone fun k => (H k x).toENNReal := by
    intro x k l hkl
    apply EReal.toENNReal_le_toENNReal
    apply min_le_min
    · apply EReal.sub_le_sub le_rfl
      have : ε l ≤ ε k := by
        simp only [hε]
        gcongr
      exact_mod_cast this
    · have : K k ≤ K l := by simp only [hK]; gcongr
      exact_mod_cast this
  have hlimpt : ∀ x, Tendsto (fun k => H k x) atTop (𝓝 (F x)) := by
    intro x
    have hε0 : Tendsto ε atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
      simpa [hε, mul_one_div, div_eq_mul_inv] using this
    simp only [hH]
    induction F x using EReal.rec with
    | bot => simp
    | top =>
      simp only [EReal.top_sub_coe, min_eq_right (le_top : _ ≤ (⊤ : EReal))]
      have : Tendsto (fun k : ℕ => K k) atTop atTop := by
        simp only [hK]
        exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      exact EReal.tendsto_coe_nhds_top_iff.mpr this
    | coe r =>
      have hev : ∀ᶠ k in atTop, min ((r : EReal) - ((ε k : ℝ) : EReal)) ((K k : ℝ) : EReal) =
          ((r - ε k : ℝ) : EReal) := by
        have : ∀ᶠ k : ℕ in atTop, r ≤ K k := by
          have hK' : Tendsto (fun k : ℕ => K k) atTop atTop := by
            simp only [hK]
            exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
          exact hK'.eventually_ge_atTop r
        filter_upwards [this] with k hk
        rw [← EReal.coe_sub, ← hmin, min_eq_left (by linarith [hεpos k])]
      refine Tendsto.congr' (EventuallyEq.symm hev) ?_
      apply EReal.tendsto_coe.mpr
      simpa using (tendsto_const_nhds (x := r)).sub hε0
  have hpos_tend : Tendsto (fun k => ∫⁻ x, (H k x).toENNReal ∂μ) atTop
      (𝓝 (∫⁻ x, (F x).toENNReal ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun k => (measurable_ereal_toENNReal.comp (hHmeas k)).aemeasurable)
      (Eventually.of_forall hmono) (Eventually.of_forall fun x => ?_)
    exact (EReal.continuous_toENNReal.tendsto _).comp (hlimpt x)
  -- (iii) the bound for each `k`
  have hbound : ∀ k, ((∫⁻ x, (H k x).toENNReal ∂μ : ℝ≥0∞) : EReal) ≤
      S + ((B + ε k : ℝ) : EReal) := by
    intro k
    have hk := h k
    have hbk : ((∫⁻ x, (-(H k x)).toENNReal ∂μ : ℝ≥0∞) : EReal) ≤ ((B + ε k : ℝ) : EReal) := by
      calc ((∫⁻ x, (-(H k x)).toENNReal ∂μ : ℝ≥0∞) : EReal)
          ≤ ((b + ENNReal.ofReal (ε k) : ℝ≥0∞) : EReal) :=
            EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hneg k)
        _ = ((B + ε k : ℝ) : EReal) := by
            rw [EReal.coe_ennreal_add, hbB, EReal.coe_ennreal_ofReal,
              max_eq_left (hεpos k).le, EReal.coe_add]
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    exact le_trans (EReal.sub_le_sub le_rfl hbk) hk
  -- (iv) pass to the limit
  have hlim2 : Tendsto (fun k => S + ((B + ε k : ℝ) : EReal)) atTop (𝓝 (S + (B : EReal))) := by
    have hε0 : Tendsto ε atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
      simpa [hε, mul_one_div, div_eq_mul_inv] using this
    have h1 : Tendsto (fun k => ((B + ε k : ℝ) : EReal)) atTop (𝓝 (B : EReal)) := by
      apply EReal.tendsto_coe.mpr
      simpa using (tendsto_const_nhds (x := B)).add hε0
    have hca := EReal.continuousAt_add (p := (S, (B : EReal)))
      (Or.inr (EReal.coe_ne_bot B)) (Or.inr (EReal.coe_ne_top B))
    exact hca.tendsto.comp (tendsto_const_nhds.prodMk_nhds h1)
  have hfin : ((∫⁻ x, (F x).toENNReal ∂μ : ℝ≥0∞) : EReal) ≤ S + (B : EReal) :=
    le_of_tendsto_of_tendsto' ((continuous_coe_ennreal_ereal.tendsto _).comp hpos_tend)
      hlim2 hbound
  unfold extIntegral
  rw [← hbdef, hbB]
  rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
  exact hfin

theorem solution {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat] (hProj : Proj Phat) (hSel : SelStar Phat) :
    ∀ φ : X × X → EReal, DiagDomFun φ → (∀ p, φ p ≠ ⊤) → ShortWDRODual.Legendre.IP Phat φ := by
  classical
  intro φ hφ hφtop
  have hnm := proj_supFn_nullMeasurable Phat hProj φ hφ hφtop
  refine ⟨hφ.1, hφtop, hnm, le_antisymm ?_
    (iSup₂_le fun γ hγ => extIntegral_le_supFn Phat φ hφ.1 hφtop hnm γ hγ)⟩
  set Φ := ShortWDRODual.Legendre.supFn φ with hΦdef
  set S := ⨆ γ ∈ ShortWDRODual.Legendre.couplingsFst Phat, extIntegral γ φ with hSdef
  have hΦae : AEMeasurable Φ Phat := hnm.aemeasurable
  set Φ' := hΦae.mk Φ with hΦ'def
  have hΦ'm : Measurable Φ' := hΦae.measurable_mk
  have hΦeq : Φ =ᵐ[Phat] Φ' := hΦae.ae_eq_mk
  have hEq : extIntegral Phat Φ = extIntegral Phat Φ' := by
    have h1 : (fun x => (Φ x).toENNReal) =ᵐ[Phat] fun x => (Φ' x).toENNReal :=
      hΦeq.mono fun x hx => by simp only [hx]
    have h2 : (fun x => (-Φ x).toENNReal) =ᵐ[Phat] fun x => (-Φ' x).toENNReal :=
      hΦeq.mono fun x hx => by simp only [hx]
    unfold extIntegral
    rw [lintegral_congr_ae h1, lintegral_congr_ae h2]
  rw [hEq]
  by_cases hb : ∫⁻ x, (-Φ' x).toENNReal ∂Phat = ⊤
  · unfold extIntegral
    rw [hb, EReal.coe_ennreal_top, EReal.sub_top]
    exact bot_le
  have hnbot : ∀ᵐ x ∂Phat, Φ' x ≠ ⊥ := by
    have := ae_lt_top' (measurable_ereal_toENNReal.comp hΦ'm.neg).aemeasurable hb
    filter_upwards [this] with x hx h
    simp [h] at hx
  have hgood : ∀ᵐ x ∂Phat, Φ x = Φ' x ∧ Φ' x ≠ ⊥ := by
    filter_upwards [hΦeq, hnbot] with x h1 h2 using ⟨h1, h2⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (s := {x | ¬ (Φ x = Φ' x ∧ Φ' x ≠ ⊥)}) (ae_iff.mp hgood)
  set G := Nᶜ with hGdef
  have hGm : MeasurableSet G := hNm.compl
  have hG : ∀ x ∈ G, Φ x = Φ' x ∧ Φ' x ≠ ⊥ := by
    intro x hx
    by_contra h
    exact hx (hNsub h)
  have hGae : ∀ᵐ x ∂Phat, x ∈ G := measure_eq_zero_iff_ae_notMem.mp hN0
  apply PSI_extInt_le_of_trunc Phat Φ' hΦ'm S
  intro k
  set δ : ℝ := 1 / ((k : ℝ) + 1) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  set K : ℝ := (k : ℝ) + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have h2δ : (2 / ((k : ℝ) + 1)) = 2 * δ := by rw [hδ]; ring
  -- the pieces
  let fl : X → ℤ := fun x => ⌊(Φ' x).toReal / δ⌋
  have hflm : Measurable fl :=
    ((measurable_ereal_toReal.comp hΦ'm).div_const δ).floor
  let B : Option ℤ → Set X := fun i => match i with
    | none => G ∩ {x | Φ' x = ⊤}
    | some n => G ∩ ({x | Φ' x ≠ ⊤} ∩ {x | fl x = n})
  let lev : Option ℤ → EReal := fun i => match i with
    | none => ((K : ℝ) : EReal)
    | some n => ((((n : ℝ) - 1) * δ : ℝ) : EReal)
  let g : X → EReal := fun x =>
    if Φ' x = ⊤ then ((K : ℝ) : EReal) else (((((fl x : ℤ) : ℝ) - 1) * δ : ℝ) : EReal)
  have htopm : MeasurableSet {x | Φ' x = ⊤} := hΦ'm (measurableSet_singleton ⊤)
  have hBm : ∀ i, MeasurableSet (B i) := by
    intro i
    cases i with
    | none => exact hGm.inter htopm
    | some n => exact hGm.inter (htopm.compl.inter (hflm (measurableSet_singleton n)))
  have hlev : ∀ i, ∀ x ∈ B i, lev i < Φ x := by
    intro i x hx
    cases i with
    | none =>
      obtain ⟨hxG, hxt⟩ := hx
      rw [(hG x hxG).1]
      simp only [Set.mem_ofPred_eq] at hxt
      simp only [lev, hxt]
      exact EReal.coe_lt_top _
    | some n =>
      obtain ⟨hxG, hxt, hxn⟩ := hx
      obtain ⟨h1, h2⟩ := hG x hxG
      rw [h1]
      simp only [Set.mem_ofPred_eq] at hxt hxn
      have hr : ((Φ' x).toReal : EReal) = Φ' x := EReal.coe_toReal hxt h2
      rw [← hr]
      simp only [lev]
      apply EReal.coe_lt_coe_iff.mpr
      have hfl : (n : ℝ) ≤ (Φ' x).toReal / δ := by
        rw [← hxn]; exact Int.floor_le _
      have : (n : ℝ) * δ ≤ (Φ' x).toReal := by
        have := mul_le_mul_of_nonneg_right hfl hδpos.le
        rwa [div_mul_cancel₀ _ hδpos.ne'] at this
      nlinarith
  have hgB : ∀ i, ∀ x ∈ B i, g x = lev i := by
    intro i x hx
    cases i with
    | none =>
      obtain ⟨-, hxt⟩ := hx
      simp only [Set.mem_ofPred_eq] at hxt
      simp only [g, lev, hxt, if_true]
    | some n =>
      obtain ⟨-, hxt, hxn⟩ := hx
      simp only [Set.mem_ofPred_eq] at hxt hxn
      simp only [g, lev, hxt, if_false, hxn]
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hxi hxj
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some m => exact hxj.2.1 hxi.2
    | some n =>
      cases j with
      | none => exact hxi.2.1 hxj.2
      | some m =>
        apply hij
        have h1 : fl x = n := hxi.2.2
        have h2 : fl x = m := hxj.2.2
        rw [← h1, ← h2]
  have hcover : ∀ x ∈ G, ∃ i, x ∈ B i := by
    intro x hx
    by_cases ht : Φ' x = ⊤
    · exact ⟨none, hx, ht⟩
    · exact ⟨some (fl x), hx, ht, rfl⟩
  have hgm : Measurable g := by
    refine Measurable.ite htopm measurable_const ?_
    exact measurable_coe_real_ereal.comp
      (((measurable_from_top.comp hflm).sub_const 1).mul_const δ)
  have hgh : ∀ x ∈ G, min (Φ' x - (((2 / ((k : ℝ) + 1)) : ℝ) : EReal)) ((((k : ℝ) + 1 : ℝ)) : EReal)
      ≤ g x := by
    intro x hx
    by_cases ht : Φ' x = ⊤
    · simp only [g, ht, if_true]
      exact min_le_right _ _
    · simp only [g, ht, if_false]
      refine (min_le_left _ _).trans ?_
      have h2 := (hG x hx).2
      have hr : ((Φ' x).toReal : EReal) = Φ' x := EReal.coe_toReal ht h2
      rw [← hr, ← EReal.coe_sub]
      apply EReal.coe_le_coe_iff.mpr
      rw [h2δ]
      have hfl : (Φ' x).toReal / δ < (fl x : ℝ) + 1 := Int.lt_floor_add_one _
      have : (Φ' x).toReal < ((fl x : ℝ) + 1) * δ := by
        have := mul_lt_mul_of_pos_right hfl hδpos
        rwa [div_mul_cancel₀ _ hδpos.ne'] at this
      nlinarith
  -- the set-valued maps and their selections
  let E : Option ℤ → X → Set X := fun i xh =>
    if xh ∈ B i then {x | lev i < φ (xh, x)} else (B i)ᶜ
  have hsupFn : ∀ xh, Φ xh = ⨆ x, φ (xh, x) := fun xh => rfl
  have hEdd : ∀ i, DiagDomSetFun (E i) := by
    intro i
    have hlevm : MeasurableSet {p : X × X | lev i < φ p} :=
      measurableSet_lt measurable_const hφ.1
    refine ⟨fun xh => ⟨?_, ?_⟩, ?_, ?_⟩
    · by_cases h : xh ∈ B i
      · simp only [E, h, if_true]
        exact measurable_prodMk_left hlevm
      · simp only [E, h, if_false]
        exact (hBm i).compl
    · by_cases h : xh ∈ B i
      · simp only [E, h, if_true]
        have := hlev i xh h
        rw [hsupFn, lt_iSup_iff] at this
        exact this
      · simp only [E, h, if_false]
        exact ⟨xh, h⟩
    · have : graph (E i) = ((B i)ᶜ ×ˢ (B i)ᶜ) ∪ ((B i ×ˢ Set.univ) ∩ {p | lev i < φ p}) := by
        ext ⟨xh, x⟩
        by_cases h : xh ∈ B i
        · simp [graph, E, h]
        · simp [graph, E, h]
      rw [this]
      exact (((hBm i).compl.prod (hBm i).compl)).union (((hBm i).prod MeasurableSet.univ).inter hlevm)
    · intro xh x hx
      by_cases hxh : xh ∈ B i
      · simp only [E, hxh, if_true, Set.mem_ofPred_eq] at hx
        by_cases hxB : x ∈ B i
        · simp only [E, hxB, if_true, Set.mem_ofPred_eq]
          exact lt_of_lt_of_le hx (hφ.2 xh x)
        · simp only [E, hxB, if_false]
          exact hxB
      · by_cases hxB : x ∈ B i
        · simp only [E, hxh, if_false] at hx
          exact absurd hxB hx
        · simp only [E, hxB, if_false]
          exact hxB
  choose γi hγi hγi0 using fun i => hSel (E i) (hEdd i)
  let γ : Measure (X × X) := Measure.sum fun i => (γi i).restrict (B i ×ˢ Set.univ)
  have hprodm : ∀ i, MeasurableSet (B i ×ˢ (Set.univ : Set X)) :=
    fun i => (hBm i).prod MeasurableSet.univ
  have hmap : γ.map Prod.fst = Phat := by
    rw [Measure.map_sum measurable_fst.aemeasurable]
    have : ∀ i, ((γi i).restrict (B i ×ˢ Set.univ)).map Prod.fst = Phat.restrict (B i) := by
      intro i
      rw [Set.prod_univ, ← Measure.restrict_map measurable_fst (hBm i), (hγi i).2]
    simp_rw [this]
    rw [← Measure.restrict_iUnion hdisj hBm]
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [hGae] with x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hγprob : IsProbabilityMeasure γ := by
    constructor
    have h1 := congrArg (fun m : Measure X => m Set.univ) hmap
    simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h1
    rw [h1]
    exact measure_univ
  have hγ : γ ∈ ShortWDRODual.Legendre.couplingsFst Phat := ⟨hγprob, hmap⟩
  have hγae : ∀ᵐ q ∂γ, g q.1 ≤ φ q := by
    rw [Measure.ae_sum_iff]
    intro i
    rw [ae_restrict_iff' (hprodm i)]
    have hgr : ∀ᵐ q ∂(γi i), q ∈ graph (E i) := by
      rw [ae_iff]
      exact hγi0 i
    filter_upwards [hgr] with q hq hqB
    have hq1 : q.1 ∈ B i := hqB.1
    rw [hgB i q.1 hq1]
    have : q.2 ∈ E i q.1 := hq
    simp only [E, hq1, if_true, Set.mem_ofPred_eq] at this
    exact this.le
  have hpush : extIntegral Phat g = extIntegral γ (fun q => g q.1) := by
    rw [← hmap]
    unfold extIntegral
    rw [lintegral_map (f := fun x => (g x).toENNReal) (measurable_ereal_toENNReal.comp hgm)
        measurable_fst,
      lintegral_map (f := fun x => (-g x).toENNReal) (measurable_ereal_toENNReal.comp hgm.neg)
        measurable_fst]
  calc extIntegral Phat (fun x => min (Φ' x - (((2 / ((k : ℝ) + 1)) : ℝ) : EReal))
          ((((k : ℝ) + 1 : ℝ)) : EReal))
      ≤ extIntegral Phat g := PSI_extInt_mono (hGae.mono fun x hx => hgh x hx)
    _ = extIntegral γ (fun q => g q.1) := hpush
    _ ≤ extIntegral γ φ := PSI_extInt_mono hγae
    _ ≤ S := le_iSup₂ (f := fun γ (_ : γ ∈ ShortWDRODual.Legendre.couplingsFst Phat) =>
          extIntegral γ φ) γ hγ
