-- Prove2me | solution 1 for OpaquePricing.Dominance.case_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T05:49:53.699074+00:00
-- url     : https://prove2.me/submissions/045608ff-3cfa-4528-8e25-1d088a0fadf8

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OPQSol
open OpaquePricing.Dominance

/-- Collapsing a menu along a map to "types" on which prices are constant. -/
lemma menu_collapse {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (φ : ι → κ) (u price : ι → ℝ) (U c : κ → ℝ)
    (hφ : ∀ o ∈ s, φ o ∈ t) (hprice : ∀ o ∈ s, price o = c (φ o))
    (hle : ∀ o ∈ s, u o ≤ U (φ o))
    (hatt : ∀ k ∈ t, ∃ o ∈ s, φ o = k ∧ u o = U k) :
    menuRevenue s u price = menuRevenue t U c := by
  classical
  unfold menuRevenue
  simp only
  set Ws := s.filter (fun o => 0 ≤ u o ∧ ∀ o' ∈ s, u o' ≤ u o) with hWs
  set Wt := t.filter (fun k => 0 ≤ U k ∧ ∀ k' ∈ t, U k' ≤ U k) with hWt
  have h1 : ∀ o ∈ Ws, φ o ∈ Wt ∧ u o = U (φ o) := by
    intro o ho
    rw [hWs, Finset.mem_filter] at ho
    obtain ⟨hos, h0, hmax⟩ := ho
    obtain ⟨o', ho's, hφo', hu'⟩ := hatt (φ o) (hφ o hos)
    have heq : u o = U (φ o) := le_antisymm (hle o hos) (by rw [← hu']; exact hmax o' ho's)
    refine ⟨?_, heq⟩
    rw [hWt, Finset.mem_filter]
    refine ⟨hφ o hos, heq ▸ h0, ?_⟩
    intro k hk
    obtain ⟨o'', ho''s, _, hu''⟩ := hatt k hk
    rw [← hu'', ← heq]; exact hmax o'' ho''s
  have h2 : ∀ k ∈ Wt, ∃ o ∈ Ws, φ o = k := by
    intro k hk
    rw [hWt, Finset.mem_filter] at hk
    obtain ⟨hkt, h0, hmax⟩ := hk
    obtain ⟨o, hos, hφo, hu⟩ := hatt k hkt
    refine ⟨o, ?_, hφo⟩
    rw [hWs, Finset.mem_filter]
    refine ⟨hos, hu ▸ h0, ?_⟩
    intro o' ho'
    rw [hu]
    exact (hle o' ho').trans (hmax _ (hφ o' ho'))
  by_cases hne : Ws.Nonempty
  · have hne' : Wt.Nonempty := by
      obtain ⟨o, ho⟩ := hne; exact ⟨_, (h1 o ho).1⟩
    rw [dif_pos hne, dif_pos hne']
    apply le_antisymm
    · apply Finset.sup'_le
      intro o ho
      rw [hprice o (Finset.mem_filter.mp ho).1]
      exact Finset.le_sup' c (h1 o ho).1
    · apply Finset.sup'_le
      intro k hk
      obtain ⟨o, ho, rfl⟩ := h2 k hk
      rw [← hprice o (Finset.mem_filter.mp ho).1]
      exact Finset.le_sup' price ho
  · have hne' : ¬ Wt.Nonempty := by
      rintro ⟨k, hk⟩
      obtain ⟨o, ho, _⟩ := h2 k hk
      exact hne ⟨o, ho⟩
    rw [dif_neg hne, dif_neg hne']

lemma menuRevenue_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (u price : ι → ℝ)
    (hp : ∀ o ∈ s, 0 ≤ price o) : 0 ≤ menuRevenue s u price := by
  classical
  unfold menuRevenue
  simp only
  split_ifs with h
  · obtain ⟨o, ho⟩ := h
    exact (hp o (Finset.mem_filter.mp ho).1).trans (Finset.le_sup' price ho)
  · exact le_rfl

noncomputable def winnerRev {ι : Type*} (T : Finset ι) (price : ι → ℝ) : ℝ :=
  if h : T.Nonempty then T.sup' h price else 0

lemma menuRevenue_eq_winnerRev {ι : Type*} [DecidableEq ι] (s : Finset ι) (u price : ι → ℝ) :
    menuRevenue s u price =
      winnerRev (s.filter fun o => 0 ≤ u o ∧ ∀ o' ∈ s, u o' ≤ u o) price := by
  classical
  unfold menuRevenue winnerRev
  rfl

lemma measurable_menuRevenue {α ι : Type*} [MeasurableSpace α] [DecidableEq ι] [Fintype ι]
    (s : Finset ι) (u : α → ι → ℝ) (hu : ∀ o, Measurable fun x => u x o) (price : ι → ℝ) :
    Measurable fun x => menuRevenue s (u x) price := by
  classical
  let G : (ι → Bool) → ℝ := fun b => winnerRev (s.filter (fun o => b o = true)) price
  let W : α → ι → Bool := fun x o => decide (0 ≤ u x o ∧ ∀ o' ∈ s, u x o' ≤ u x o)
  have hfun : (fun x => menuRevenue s (u x) price) = G ∘ W := by
    funext x
    rw [menuRevenue_eq_winnerRev]
    simp only [Function.comp, G, W, decide_eq_true_eq]
    congr 1
    ext; simp
  rw [hfun]
  refine (measurable_of_finite G).comp ?_
  refine measurable_pi_lambda _ (fun o => ?_)
  refine measurable_to_bool ?_
  have : (fun x => W x o) ⁻¹' {true} =
      {x | 0 ≤ u x o} ∩ ⋂ o' ∈ s, {x | u x o' ≤ u x o} := by
    ext x; simp [W]
  rw [this]
  refine MeasurableSet.inter (measurableSet_le measurable_const (hu o)) ?_
  refine MeasurableSet.biInter s.countable_toSet (fun o' _ => measurableSet_le (hu o') (hu o))


lemma exists_antitone_perm {N : ℕ} (v : Fin N → ℝ) :
    ∃ σ : Equiv.Perm (Fin N), Antitone (v ∘ σ) := by
  refine ⟨Tuple.sort (OrderDual.toDual ∘ v), ?_⟩
  have := Tuple.monotone_sort (OrderDual.toDual ∘ v)
  exact this

/-- the menu indexed by ranks -/
noncomputable def rankRev {N : ℕ} (π w : Fin N → ℝ) : ℝ :=
  menuRevenue Finset.univ (fun r => w r - π r) π

lemma dp_perm_eq {N : ℕ} (p v : Fin N → ℝ) (σ ρ : Equiv.Perm (Fin N)) :
    dpRevenue p (v ∘ ρ) = rankRev (p ∘ (ρ.trans σ.symm).symm) (v ∘ σ) := by
  classical
  unfold dpRevenue rankRev
  let e : Equiv.Perm (Fin N) := ρ.trans σ.symm
  apply menu_collapse Finset.univ Finset.univ e
  · intro o _; exact Finset.mem_univ _
  · intro o _; simp [e]
  · intro o _; simp [e]
  · intro k _
    refine ⟨e.symm k, Finset.mem_univ _, by simp, ?_⟩
    simp [e]


def qOf {N : ℕ} (π : Fin N → ℝ) : ℕ → ℝ := fun k => if h : k - 1 < N then π ⟨k - 1, h⟩ else 0

lemma card_sub_one_lt {N : ℕ} (hN : 1 ≤ N) (S : Finset (Fin N)) : S.card - 1 < N := by
  have := S.card_le_univ
  simp only [Fintype.card_fin] at this
  omega

lemma pess_le {N : ℕ} (hN : 1 ≤ N) (v : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : Antitone (v ∘ σ)) (S : Finset (Fin N)) (hS : S.Nonempty) :
    pessValue v S ≤ (v ∘ σ) ⟨S.card - 1, card_sub_one_lt hN S⟩ := by
  classical
  set T := S.map σ.symm.toEmbedding with hT
  have hcard : T.card = S.card := by simp [hT]
  have hpos : 0 < S.card := hS.card_pos
  obtain ⟨j, hjT, hj⟩ : ∃ j ∈ T, S.card - 1 ≤ j.val := by
    by_contra hcon
    push Not at hcon
    have hsub : T ⊆ Finset.Iio ⟨S.card - 1, card_sub_one_lt hN S⟩ := by
      intro j hj
      simp only [Finset.mem_Iio, Fin.lt_def]
      exact hcon j hj
    have := Finset.card_le_card hsub
    simp only [Fin.card_Iio] at this
    omega
  have hσj : σ j ∈ S := by
    simp only [hT, Finset.mem_map, Equiv.coe_toEmbedding] at hjT
    obtain ⟨x, hx, rfl⟩ := hjT
    simpa using hx
  unfold pessValue
  rw [dif_pos hS]
  calc S.inf' hS v ≤ v (σ j) := Finset.inf'_le v hσj
    _ = (v ∘ σ) j := rfl
    _ ≤ (v ∘ σ) ⟨S.card - 1, card_sub_one_lt hN S⟩ := hσ (by rw [Fin.le_def]; exact hj)

lemma pess_attain {N : ℕ} (v : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : Antitone (v ∘ σ)) (m : Fin N) :
    pessValue v ((Finset.Iic m).map σ.toEmbedding) = (v ∘ σ) m ∧
      ((Finset.Iic m).map σ.toEmbedding).card = m.val + 1 := by
  classical
  have hne : ((Finset.Iic m).map σ.toEmbedding).Nonempty := by
    simp only [Finset.map_nonempty]; exact ⟨m, Finset.mem_Iic.mpr le_rfl⟩
  refine ⟨?_, by simp⟩
  unfold pessValue
  rw [dif_pos hne]
  apply le_antisymm
  · exact Finset.inf'_le v (Finset.mem_map_of_mem _ (Finset.mem_Iic.mpr le_rfl))
  · apply Finset.le_inf'
    intro x hx
    simp only [Finset.mem_map, Finset.mem_Iic, Equiv.coe_toEmbedding] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact hσ hj

lemma opq_pess_eq {N : ℕ} (hN : 1 ≤ N) (π v : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : Antitone (v ∘ σ)) :
    opqRevenue pessValue (π ⟨0, hN⟩) (qOf π) v = rankRev π (v ∘ σ) := by
  classical
  unfold opqRevenue rankRev
  have hprice : ∀ S ∈ opqOptions N,
      opqPrice (π ⟨0, hN⟩) (qOf π) S = π ⟨S.card - 1, card_sub_one_lt hN S⟩ := by
    intro S _
    unfold opqPrice qOf
    split_ifs with h1 h2
    · congr 1; ext; simp [h1]
    · rfl
    · exact absurd (card_sub_one_lt hN S) h2
  apply menu_collapse (opqOptions N) Finset.univ
    (fun S => (⟨S.card - 1, card_sub_one_lt hN S⟩ : Fin N))
  · intro o _; exact Finset.mem_univ _
  · exact hprice
  · intro S hS
    have hS' : S.Nonempty := by simpa [opqOptions] using hS
    rw [hprice S hS]
    have := pess_le hN v σ hσ S hS'
    linarith
  · intro m _
    obtain ⟨h1, h2⟩ := pess_attain v σ hσ m
    refine ⟨(Finset.Iic m).map σ.toEmbedding, ?_, ?_, ?_⟩
    · simp only [opqOptions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.map_nonempty]
      exact ⟨m, Finset.mem_Iic.mpr le_rfl⟩
    · ext; simp [h2]
    · have hm : (⟨((Finset.Iic m).map σ.toEmbedding).card - 1,
          card_sub_one_lt hN _⟩ : Fin N) = m := by ext; simp [h2]
      rw [hprice _ (by simp only [opqOptions, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.map_nonempty]; exact ⟨m, Finset.mem_Iic.mpr le_rfl⟩), hm, h1]


lemma measurable_pessValue {N : ℕ} (S : Finset (Fin N)) :
    Measurable fun v : Fin N → ℝ => pessValue v S := by
  unfold pessValue
  by_cases h : S.Nonempty
  · simp only [dif_pos h]
    exact (Continuous.finset_inf'_apply h (fun i _ => continuous_apply i)).measurable
  · simp only [dif_neg h]; exact measurable_const

lemma measurable_opq_pess {N : ℕ} (p : ℝ) (q : ℕ → ℝ) :
    Measurable fun v : Fin N → ℝ => opqRevenue pessValue p q v := by
  unfold opqRevenue
  exact measurable_menuRevenue _ (fun v S => pessValue v S - opqPrice p q S)
    (fun S => (measurable_pessValue S).sub_const _) _

lemma measurable_dp {N : ℕ} (p : Fin N → ℝ) :
    Measurable fun v : Fin N → ℝ => dpRevenue p v := by
  unfold dpRevenue
  exact measurable_menuRevenue _ (fun (v : Fin N → ℝ) i => v i - p i)
    (fun i => (measurable_pi_apply i).sub_const _) _

lemma measurable_comp_perm {N : ℕ} (ρ : Equiv.Perm (Fin N)) :
    Measurable fun v : Fin N → ℝ => v ∘ ρ :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (ρ i))

lemma lintegral_perm {N : ℕ} (μ : Measure (Fin N → ℝ)) (hexch : Exchangeable μ)
    (F : (Fin N → ℝ) → ENNReal) (hF : Measurable F) (ρ : Equiv.Perm (Fin N)) :
    ∫⁻ v, F v ∂μ = ∫⁻ v, F (v ∘ ρ) ∂μ := by
  conv_lhs => rw [← hexch ρ]
  rw [lintegral_map hF (measurable_comp_perm ρ)]

lemma le_optOPQ_one {N : ℕ} (μ : Measure (Fin N → ℝ)) (p : ℝ) (q : ℕ → ℝ)
    (hp : 0 ≤ p) (hq : ∀ k, 0 ≤ q k) :
    ∫⁻ v, ENNReal.ofReal (opqRevenue pessValue p q v) ∂μ ≤ optOPQ μ 1 := by
  have : expOPQ μ 1 p q = ∫⁻ v, ENNReal.ofReal (opqRevenue pessValue p q v) ∂μ := by
    unfold expOPQ; simp
  rw [← this]
  unfold optOPQ
  exact le_iSup_of_le p (le_iSup_of_le q (le_iSup_of_le ⟨hp, hq⟩ le_rfl))

theorem case_i {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ0 : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (hexch : Exchangeable μ) :
    optDP μ ≤ optOPQ μ 1 := by
  classical
  have hN1 : 1 ≤ N := by omega
  unfold optDP
  refine iSup₂_le (fun p hp => ?_)
  let F : (Fin N → ℝ) → ENNReal := fun v => ENNReal.ofReal (dpRevenue p v)
  have hF : Measurable F := ENNReal.measurable_ofReal.comp (measurable_dp p)
  let G : Equiv.Perm (Fin N) → (Fin N → ℝ) → ENNReal := fun τ v =>
    ENNReal.ofReal (opqRevenue pessValue ((p ∘ τ) ⟨0, hN1⟩) (qOf (p ∘ τ)) v)
  have hG : ∀ τ, Measurable (G τ) := fun τ =>
    ENNReal.measurable_ofReal.comp (measurable_opq_pess _ _)
  -- pointwise identity
  have hpt : ∀ v, ∑ ρ : Equiv.Perm (Fin N), F (v ∘ ρ) = ∑ τ : Equiv.Perm (Fin N), G τ v := by
    intro v
    obtain ⟨σ, hσ⟩ := exists_antitone_perm v
    have h1 : ∀ ρ : Equiv.Perm (Fin N), F (v ∘ ρ) =
        ENNReal.ofReal (rankRev (p ∘ (ρ.trans σ.symm).symm) (v ∘ σ)) := by
      intro ρ; simp only [F]; rw [dp_perm_eq p v σ ρ]
    have h2 : ∀ τ : Equiv.Perm (Fin N), G τ v = ENNReal.ofReal (rankRev (p ∘ τ) (v ∘ σ)) := by
      intro τ; simp only [G]; rw [opq_pess_eq hN1 (p ∘ τ) v σ hσ]
    simp only [h1, h2]
    let e : Equiv.Perm (Fin N) ≃ Equiv.Perm (Fin N) :=
      { toFun := fun ρ => (ρ.trans σ.symm).symm
        invFun := fun τ => τ.symm.trans σ
        left_inv := fun ρ => by ext; simp
        right_inv := fun τ => by ext; simp }
    exact Fintype.sum_equiv e _ _ (fun ρ => rfl)
  have hcard : ((Fintype.card (Equiv.Perm (Fin N)) : ℕ) : ENNReal) * expDP μ p ≤
      ((Fintype.card (Equiv.Perm (Fin N)) : ℕ) : ENNReal) * optOPQ μ 1 := by
    calc ((Fintype.card (Equiv.Perm (Fin N)) : ℕ) : ENNReal) * expDP μ p
        = ∑ ρ : Equiv.Perm (Fin N), ∫⁻ v, F v ∂μ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
      _ = ∑ ρ : Equiv.Perm (Fin N), ∫⁻ v, F (v ∘ ρ) ∂μ := by
          refine Finset.sum_congr rfl (fun ρ _ => lintegral_perm μ hexch F hF ρ)
      _ = ∫⁻ v, ∑ ρ : Equiv.Perm (Fin N), F (v ∘ ρ) ∂μ := by
          rw [lintegral_finsetSum]
          intro ρ _; exact hF.comp (measurable_comp_perm ρ)
      _ = ∫⁻ v, ∑ τ : Equiv.Perm (Fin N), G τ v ∂μ := by
          congr 1; funext v; exact hpt v
      _ = ∑ τ : Equiv.Perm (Fin N), ∫⁻ v, G τ v ∂μ := by
          rw [lintegral_finsetSum]
          intro τ _; exact hG τ
      _ ≤ ∑ τ : Equiv.Perm (Fin N), optOPQ μ 1 := by
          refine Finset.sum_le_sum (fun τ _ => ?_)
          refine le_optOPQ_one μ _ _ (hp _) (fun k => ?_)
          unfold qOf; split_ifs
          · exact hp _
          · exact le_rfl
      _ = ((Fintype.card (Equiv.Perm (Fin N)) : ℕ) : ENNReal) * optOPQ μ 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hne : ((Fintype.card (Equiv.Perm (Fin N)) : ℕ) : ENNReal) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  exact (ENNReal.mul_le_mul_iff_right hne (ENNReal.natCast_ne_top _)).mp hcard

end OPQSol

open OpaquePricing.Dominance

theorem solution {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ0 : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (hexch : Exchangeable μ) :
    optDP μ ≤ optOPQ μ 1 :=
  OPQSol.case_i hN μ hμ0 hexch
