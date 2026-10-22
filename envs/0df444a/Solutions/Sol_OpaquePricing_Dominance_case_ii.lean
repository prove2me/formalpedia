-- Prove2me | solution 1 for OpaquePricing.Dominance.case_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T05:56:34.798876+00:00
-- url     : https://prove2.me/submissions/0dd017cf-a33a-4aff-af82-e26c13f4a091

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


/-! ## Case (ii) -/

lemma menuRevenue_ge {ι : Type*} [DecidableEq ι] (s : Finset ι) (u price : ι → ℝ)
    (o : ι) (ho : o ∈ s) (h0 : 0 ≤ u o) (hmax : ∀ o' ∈ s, u o' ≤ u o) :
    price o ≤ menuRevenue s u price := by
  classical
  rw [menuRevenue_eq_winnerRev]
  unfold winnerRev
  have hmem : o ∈ s.filter (fun o => 0 ≤ u o ∧ ∀ o' ∈ s, u o' ≤ u o) :=
    Finset.mem_filter.mpr ⟨ho, h0, hmax⟩
  rw [dif_pos ⟨o, hmem⟩]
  exact Finset.le_sup' price hmem

lemma menuRevenue_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (u price : ι → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ o ∈ s, 0 ≤ u o → (∀ o' ∈ s, u o' ≤ u o) → price o ≤ B) :
    menuRevenue s u price ≤ B := by
  classical
  rw [menuRevenue_eq_winnerRev]
  unfold winnerRev
  split_ifs with hne
  · apply Finset.sup'_le
    intro o ho
    obtain ⟨hos, h0, hmax⟩ := Finset.mem_filter.mp ho
    exact h o hos h0 hmax
  · exact hB

lemma val_le {N : ℕ} (val : (Fin N → ℝ) → Finset (Fin N) → ℝ)
    (hval : val = pessValue ∨ val = rnValue) (v : Fin N → ℝ) (S : Finset (Fin N))
    (hS : S.Nonempty) (c : ℝ) (h : ∀ i ∈ S, v i ≤ c) : val v S ≤ c := by
  rcases hval with rfl | rfl
  · unfold pessValue; rw [dif_pos hS]
    obtain ⟨i, hi⟩ := hS
    exact (Finset.inf'_le v hi).trans (h i hi)
  · unfold rnValue
    have hpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    rw [div_le_iff₀ hpos]
    have := Finset.sum_le_card_nsmul S v c h
    simpa [nsmul_eq_mul, mul_comm] using this

lemma val_ge {N : ℕ} (val : (Fin N → ℝ) → Finset (Fin N) → ℝ)
    (hval : val = pessValue ∨ val = rnValue) (v : Fin N → ℝ) (S : Finset (Fin N))
    (hS : S.Nonempty) (c : ℝ) (h : ∀ i ∈ S, c ≤ v i) : c ≤ val v S := by
  rcases hval with rfl | rfl
  · unfold pessValue; rw [dif_pos hS]
    exact Finset.le_inf' hS v h
  · unfold rnValue
    have hpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    rw [le_div_iff₀ hpos]
    have := Finset.card_nsmul_le_sum S v c h
    simpa [nsmul_eq_mul, mul_comm] using this

lemma rn_ineq (j k i n : ℝ) (hk : 1 ≤ k) (hkN : k ≤ n) (hj0 : 0 ≤ j) (hjk : j ≤ k)
    (hji : j ≤ i) (hiN : i ≤ n) : j / k + k / n - 1 ≤ i / n := by
  have hk0 : 0 < k := by linarith
  have hn0 : 0 < n := by linarith
  rw [div_add_div _ _ hk0.ne' hn0.ne', div_sub_one (by positivity), div_le_div_iff₀ (by positivity) hn0]
  rcases le_total k i with hki | hki
  · nlinarith [mul_le_mul_of_nonneg_right hjk hn0.le, mul_le_mul_of_nonneg_left hki hk0.le]
  · nlinarith [mul_le_mul_of_nonneg_right hji hn0.le, mul_nonneg (sub_nonneg.mpr hki) (sub_nonneg.mpr hkN)]

/-- opaque price of a nonempty set under ladder-type size prices -/
lemma opqPrice_ladder {N : ℕ} (a b : ℝ) (q : ℕ → ℝ)
    (hq : ∀ k, 1 ≤ k → k ≤ N → q k = ladder N a b k) (S : Finset (Fin N)) (hS : S.Nonempty) :
    opqPrice (ladder N a b 1) q S = ladder N a b S.card := by
  unfold opqPrice
  split_ifs with h
  · rw [h]
  · apply hq
    · exact hS.card_pos
    · simpa using S.card_le_univ

lemma ladder_mono {N : ℕ} (hN : 1 ≤ N) (a b : ℝ) (hab : a < b) {k l : ℕ} (hkl : k ≤ l) :
    ladder N a b l ≤ ladder N a b k := by
  unfold ladder
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have : ((N : ℝ) - l) / N ≤ ((N : ℝ) - k) / N := by
    apply div_le_div_of_nonneg_right _ hN0.le
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  nlinarith

lemma ladder_N {N : ℕ} (hN : 1 ≤ N) (a b : ℝ) : ladder N a b N = a := by
  unfold ladder; simp

lemma ladder_le_b {N : ℕ} (hN : 1 ≤ N) (a b : ℝ) (hab : a < b) {k : ℕ} (hk : 0 ≤ k) :
    ladder N a b k ≤ b := by
  unfold ladder
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have : ((N : ℝ) - k) / N ≤ 1 := by
    rw [div_le_one hN0]; have : (0:ℝ) ≤ k := by positivity
    linarith
  nlinarith

/-- The revenue target in case (ii). -/
noncomputable def ladderTarget (N : ℕ) (a b : ℝ) (v : Fin N → ℝ) : ℝ :=
  if highCount b v = 0 then a else a + (((N : ℝ) - highCount b v) / N) * (b - a)

lemma ladder_ge {N : ℕ} (hN : 1 ≤ N) (a b : ℝ) (hab : a < b)
    (v : Fin N → ℝ) (hv : ∀ i, v i = a ∨ v i = b)
    (val : (Fin N → ℝ) → Finset (Fin N) → ℝ) (hval : val = pessValue ∨ val = rnValue)
    (q : ℕ → ℝ) (hq : ∀ k, 1 ≤ k → k ≤ N → q k = ladder N a b k) :
    ladderTarget N a b v ≤ opqRevenue val (ladder N a b 1) q v := by
  classical
  unfold opqRevenue ladderTarget
  have hopt : ∀ S ∈ opqOptions N, S.Nonempty := by
    intro S hS; simpa [opqOptions] using hS
  have hcardle : ∀ S : Finset (Fin N), (S.card : ℝ) ≤ N := by
    intro S; exact_mod_cast (by simpa using S.card_le_univ)
  split_ifs with hU
  · -- all values are `a`
    have hall : ∀ i, v i = a := by
      intro i
      rcases hv i with h | h
      · exact h
      · exfalso
        have : i ∈ Finset.univ.filter (fun i => v i = b) := by simp [h]
        unfold highCount at hU
        rw [Finset.card_eq_zero] at hU
        rw [hU] at this; simp at this
    have hval_eq : ∀ S : Finset (Fin N), S.Nonempty → val v S = a := fun S hS =>
      le_antisymm (val_le val hval v S hS a (fun i _ => (hall i).le))
        (val_ge val hval v S hS a (fun i _ => (hall i).ge))
    have huniv : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    have h := menuRevenue_ge (opqOptions N) (fun S => val v S - opqPrice (ladder N a b 1) q S)
      (opqPrice (ladder N a b 1) q) Finset.univ (by simp [opqOptions, huniv]) ?_ ?_
    · rw [opqPrice_ladder a b q hq _ huniv] at h
      simpa [ladder_N hN] using h
    · beta_reduce
      rw [opqPrice_ladder a b q hq _ huniv, hval_eq _ huniv]
      simp [ladder_N hN]
    · intro S hS
      beta_reduce
      rw [opqPrice_ladder a b q hq _ huniv, hval_eq _ huniv,
        opqPrice_ladder a b q hq _ (hopt S hS), hval_eq _ (hopt S hS)]
      simp only [Finset.card_univ, Fintype.card_fin, ladder_N hN, sub_self]
      have := ladder_mono hN a b hab (by simpa using S.card_le_univ : S.card ≤ N)
      rw [ladder_N hN] at this
      linarith
  · -- some values are `b`
    set B := Finset.univ.filter (fun i => v i = b) with hB
    have hBc : B.card = highCount b v := rfl
    have hBne : B.Nonempty := by
      rw [← Finset.card_pos, hBc]; omega
    have hvB : val v B = b :=
      le_antisymm (val_le val hval v B hBne b (fun i hi => (Finset.mem_filter.mp hi).2.le))
        (val_ge val hval v B hBne b (fun i hi => (Finset.mem_filter.mp hi).2.ge))
    have h := menuRevenue_ge (opqOptions N) (fun S => val v S - opqPrice (ladder N a b 1) q S)
      (opqPrice (ladder N a b 1) q) B (by simp [opqOptions, hBne]) ?_ ?_
    · rw [opqPrice_ladder a b q hq _ hBne, hBc] at h
      exact h
    · beta_reduce
      rw [opqPrice_ladder a b q hq _ hBne, hvB]
      linarith [ladder_le_b hN a b hab (Nat.zero_le B.card)]
    · intro S hS
      have hSne := hopt S hS
      beta_reduce
      rw [opqPrice_ladder a b q hq _ hBne, hvB, opqPrice_ladder a b q hq _ hSne]
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rcases hval with hp | hr
      · -- pessimistic
        by_cases hsub : S ⊆ B
        · have hcard : S.card ≤ B.card := Finset.card_le_card hsub
          have h1 := ladder_mono hN a b hab hcard
          have h2 := val_le val (Or.inl hp) v S hSne b
            (fun i hi => (Finset.mem_filter.mp (hsub hi)).2.le)
          linarith
        · obtain ⟨x, hxS, hxB⟩ := Finset.not_subset.mp hsub
          have hxa : v x = a := by
            rcases hv x with h | h
            · exact h
            · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩ : x ∈ B) hxB
          have h2 : val v S ≤ a := by
            rw [hp]; unfold pessValue; rw [dif_pos hSne]
            exact (Finset.inf'_le v hxS).trans hxa.le
          have h3 := ladder_mono hN a b hab (by simpa using S.card_le_univ : S.card ≤ N)
          rw [ladder_N hN] at h3
          have h4 := ladder_le_b hN a b hab (Nat.zero_le B.card)
          linarith
      · -- risk-neutral
        rw [hr]
        unfold rnValue
        set J := S.filter (fun i => v i = b) with hJ
        have hsum : ∑ i ∈ S, v i = J.card * b + (S.card - J.card) * a := by
          rw [← Finset.sum_filter_add_sum_filter_not S (fun i => v i = b)]
          have e1 : ∑ i ∈ S.filter (fun i => v i = b), v i = J.card * b := by
            rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
            simp [hJ]
          have e2 : ∑ i ∈ S.filter (fun i => ¬ v i = b), v i =
              (S.filter (fun i => ¬ v i = b)).card * a := by
            rw [Finset.sum_congr rfl (fun i hi => (hv i).resolve_right (Finset.mem_filter.mp hi).2)]
            simp
          have e3 : ((S.filter (fun i => ¬ v i = b)).card : ℝ) = S.card - J.card := by
            have := Finset.card_filter_add_card_filter_not (s := S) (fun i => v i = b)
            rw [hJ]; push_cast [← this]; ring
          rw [e1, e2, e3]
        rw [hsum]
        have hJS : J.card ≤ S.card := Finset.card_filter_le _ _
        have hJB : J.card ≤ B.card := by
          apply Finset.card_le_card
          intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
        have hk1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hSne.card_pos
        have hineq := rn_ineq (J.card : ℝ) (S.card : ℝ) (B.card : ℝ) (N : ℝ) hk1 (hcardle S)
          (by positivity) (by exact_mod_cast hJS) (by exact_mod_cast hJB) (hcardle B)
        unfold ladder
        have hk0 : (0 : ℝ) < S.card := by linarith
        have key : (↑J.card * b + (↑S.card - ↑J.card) * a) / ↑S.card =
            a + (J.card / S.card) * (b - a) := by
          field_simp; ring
        rw [key]
        have hd : 0 < b - a := by linarith
        have : (J.card : ℝ) / S.card * (b - a) - ((N : ℝ) - S.card) / N * (b - a) ≤
            (b - a) - ((N : ℝ) - B.card) / N * (b - a) := by
          have e : (J.card : ℝ) / S.card - ((N : ℝ) - S.card) / N =
              J.card / S.card + S.card / N - 1 := by field_simp; ring
          have e' : (1 : ℝ) - ((N : ℝ) - B.card) / N = B.card / N := by field_simp; ring
          nlinarith [mul_le_mul_of_nonneg_right hineq hd.le]
        linarith


lemma dp_le_caseA {N : ℕ} (a b : ℝ) (hab : a < b) (hb : 0 ≤ b) (p v : Fin N → ℝ)
    (hv : ∀ i, v i = a ∨ v i = b) (hA : ∀ i, a < p i) :
    dpRevenue p v ≤ (if ∃ i, v i = b then b else 0) := by
  unfold dpRevenue
  apply menuRevenue_le _ _ _ _ (by split_ifs <;> linarith)
  intro o _ h0 _
  split_ifs with hex
  · rcases hv o with h | h <;> linarith
  · rcases hv o with h | h
    · linarith [hA o]
    · exact absurd ⟨o, h⟩ hex

noncomputable def mixedRev {N : ℕ} (a b : ℝ) (j : Fin N) (v : Fin N → ℝ) : ℝ :=
  if v j = a ∧ ∃ i, v i = b then b else a

lemma dp_le_caseB {N : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (p v : Fin N → ℝ)
    (hv : ∀ i, v i = a ∨ v i = b) (j : Fin N) (hj : p j ≤ a) :
    dpRevenue p v ≤ mixedRev a b j v := by
  unfold dpRevenue mixedRev
  apply menuRevenue_le _ _ _ _ (by split_ifs <;> linarith)
  intro o _ h0 hmax
  have hjo := hmax j (Finset.mem_univ _)
  by_cases hpo : p o ≤ a
  · split_ifs <;> linarith
  · push Not at hpo
    have hvo : v o = b := by rcases hv o with h | h <;> [linarith; exact h]
    have hvj : v j = a := by
      rcases hv j with h | h
      · exact h
      · rw [h, hvo] at hjo; linarith
    rw [if_pos ⟨hvj, o, hvo⟩]
    linarith

lemma singleB_ge {N : ℕ} (a b : ℝ) (hab : a < b) (hb : 0 ≤ b) (v : Fin N → ℝ)
    (hv : ∀ i, v i = a ∨ v i = b)
    (val : (Fin N → ℝ) → Finset (Fin N) → ℝ) (hval : val = pessValue ∨ val = rnValue) :
    (if ∃ i, v i = b then b else 0) ≤ opqRevenue val b (fun _ => b) v := by
  classical
  have hprice : ∀ S, opqPrice (N := N) b (fun _ => b) S = b := by
    intro S; unfold opqPrice; split_ifs <;> rfl
  have hle : ∀ i, v i ≤ b := fun i => by rcases hv i with h | h <;> linarith
  unfold opqRevenue
  split_ifs with hex
  · obtain ⟨i, hi⟩ := hex
    have hne : ({i} : Finset (Fin N)).Nonempty := Finset.singleton_nonempty i
    have hvi : val v {i} = b := le_antisymm (val_le val hval v _ hne b (fun k _ => hle k))
      (val_ge val hval v _ hne b (fun k hk => by rw [Finset.mem_singleton.mp hk, hi]))
    have h := menuRevenue_ge (opqOptions N) (fun S => val v S - opqPrice b (fun _ => b) S)
      (opqPrice b (fun _ => b)) {i} (by simp [opqOptions]) ?_ ?_
    · rwa [hprice] at h
    · rw [hvi, hprice]; simp
    · intro S hS
      have hSne : S.Nonempty := by simpa [opqOptions] using hS
      rw [hvi, hprice, hprice]
      linarith [val_le val hval v S hSne b (fun k _ => hle k)]
  · exact menuRevenue_nonneg _ _ _ (fun S _ => by rw [hprice]; exact hb)

lemma sum_mixedRev {N : ℕ} (a b : ℝ) (hab : a < b) (v : Fin N → ℝ)
    (hv : ∀ i, v i = a ∨ v i = b) (hN : 1 ≤ N) :
    ∑ j, mixedRev a b j v = N * ladderTarget N a b v := by
  classical
  unfold mixedRev ladderTarget
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hiff : highCount b v = 0 ↔ ¬ ∃ i, v i = b := by
    unfold highCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp
  by_cases hex : ∃ i, v i = b
  · have h0 : highCount b v ≠ 0 := fun h => (hiff.mp h) hex
    rw [if_neg h0]
    simp only [hex, and_true]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hc : (Finset.univ.filter (fun j => v j = a)).card +
        (Finset.univ.filter (fun j => ¬ v j = a)).card = N := by
      rw [Finset.card_filter_add_card_filter_not]; simp
    have hc2 : (Finset.univ.filter (fun j => ¬ v j = a)) = Finset.univ.filter (fun j => v j = b) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact (hv j).resolve_left h
      · intro h h'; rw [h'] at h; linarith
    rw [hc2] at hc ⊢
    have hc' : ((Finset.univ.filter (fun j => v j = a)).card : ℝ) = N - highCount b v := by
      unfold highCount
      have : ((Finset.univ.filter (fun j => v j = a)).card : ℝ) +
          (Finset.univ.filter (fun j => v j = b)).card = N := by exact_mod_cast hc
      linarith
    rw [hc']
    unfold highCount
    field_simp
    ring
  · have h0 : highCount b v = 0 := hiff.mpr hex
    rw [if_pos h0]
    simp [hex]

lemma measurable_mixedRev {N : ℕ} (a b : ℝ) (j : Fin N) :
    Measurable fun v : Fin N → ℝ => mixedRev a b j v := by
  unfold mixedRev
  refine Measurable.ite ?_ measurable_const measurable_const
  refine MeasurableSet.inter (measurableSet_eq_fun (measurable_pi_apply j) measurable_const) ?_
  show MeasurableSet {x : Fin N → ℝ | ∃ i, x i = b}
  have e : {x : Fin N → ℝ | ∃ i, x i = b} = ⋃ i, {x | x i = b} := by ext; simp
  rw [e]
  exact MeasurableSet.iUnion (fun i : Fin N =>
    measurableSet_eq_fun (measurable_pi_apply i) measurable_const)

lemma mixedRev_perm {N : ℕ} (a b : ℝ) (j k : Fin N) (v : Fin N → ℝ) :
    mixedRev a b j (v ∘ Equiv.swap j k) = mixedRev a b k v := by
  unfold mixedRev
  simp only [Function.comp, Equiv.swap_apply_left]
  congr 2
  apply propext
  constructor
  · rintro ⟨i, hi⟩; exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨Equiv.swap j k i, by simpa using hi⟩

lemma le_optOPQ {N : ℕ} (μ : Measure (Fin N → ℝ)) (α p : ℝ) (q : ℕ → ℝ)
    (hp : 0 ≤ p) (hq : ∀ k, 0 ≤ q k) : expOPQ μ α p q ≤ optOPQ μ α := by
  unfold optOPQ
  exact le_iSup_of_le p (le_iSup_of_le q (le_iSup_of_le ⟨hp, hq⟩ le_rfl))

lemma expOPQ_ge {N : ℕ} (μ : Measure (Fin N → ℝ)) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (p : ℝ) (q : ℕ → ℝ) (F : (Fin N → ℝ) → ℝ)
    (hpess : ∀ᵐ v ∂μ, F v ≤ opqRevenue pessValue p q v)
    (hrn : ∀ᵐ v ∂μ, F v ≤ opqRevenue rnValue p q v) :
    ∫⁻ v, ENNReal.ofReal (F v) ∂μ ≤ expOPQ μ α p q := by
  have hsum : ENNReal.ofReal α + ENNReal.ofReal (1 - α) = 1 := by
    rw [← ENNReal.ofReal_add hα0 (by linarith)]; simp
  unfold expOPQ
  calc ∫⁻ v, ENNReal.ofReal (F v) ∂μ
      = (ENNReal.ofReal α + ENNReal.ofReal (1 - α)) * ∫⁻ v, ENNReal.ofReal (F v) ∂μ := by
        rw [hsum, one_mul]
    _ = ENNReal.ofReal α * ∫⁻ v, ENNReal.ofReal (F v) ∂μ +
        ENNReal.ofReal (1 - α) * ∫⁻ v, ENNReal.ofReal (F v) ∂μ := add_mul _ _ _
    _ ≤ _ := add_le_add
        (mul_le_mul' le_rfl (lintegral_mono_ae (hpess.mono fun v hv => ENNReal.ofReal_le_ofReal hv)))
        (mul_le_mul' le_rfl (lintegral_mono_ae (hrn.mono fun v hv => ENNReal.ofReal_le_ofReal hv)))

lemma case_ii_ab {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ] (hexch : Exchangeable μ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hsupp : ∀ᵐ v ∂μ, ∀ i, v i = a ∨ v i = b)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    optDP μ ≤ optOPQ μ α := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hb : 0 ≤ b := by linarith
  unfold optDP
  refine iSup₂_le (fun p hp => ?_)
  by_cases hA : ∀ i, a < p i
  · calc expDP μ p ≤ ∫⁻ v, ENNReal.ofReal (if ∃ i, v i = b then b else 0) ∂μ := by
          unfold expDP
          exact lintegral_mono_ae (hsupp.mono fun v hv =>
            ENNReal.ofReal_le_ofReal (dp_le_caseA a b hab hb p v hv hA))
      _ ≤ expOPQ μ α b (fun _ => b) :=
          expOPQ_ge μ α hα0 hα1 _ _ _
            (hsupp.mono fun v hv => singleB_ge a b hab hb v hv _ (Or.inl rfl))
            (hsupp.mono fun v hv => singleB_ge a b hab hb v hv _ (Or.inr rfl))
      _ ≤ optOPQ μ α := le_optOPQ μ α _ _ hb (fun _ => hb)
  · push Not at hA
    obtain ⟨j, hj⟩ := hA
    let q : ℕ → ℝ := fun k => ladder N a b (min k N)
    have hq : ∀ k, 1 ≤ k → k ≤ N → q k = ladder N a b k := by
      intro k _ hk; simp [q, min_eq_left hk]
    have hq0 : ∀ k, 0 ≤ q k := by
      intro k
      have := ladder_mono hN1 a b hab (min_le_right k N)
      rw [ladder_N hN1] at this
      linarith
    have hp0 : 0 ≤ ladder N a b 1 := by
      have := ladder_mono hN1 a b hab hN1
      rw [ladder_N hN1] at this; linarith
    have hM : ∀ k : Fin N, Measurable fun v : Fin N → ℝ => ENNReal.ofReal (mixedRev a b k v) :=
      fun k => ENNReal.measurable_ofReal.comp (measurable_mixedRev a b k)
    have hNe : ((N : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hmix : ∫⁻ v, ENNReal.ofReal (mixedRev a b j v) ∂μ ≤
        ∫⁻ v, ENNReal.ofReal (ladderTarget N a b v) ∂μ := by
      have key : ((N : ℕ) : ENNReal) * ∫⁻ v, ENNReal.ofReal (mixedRev a b j v) ∂μ ≤
          ((N : ℕ) : ENNReal) * ∫⁻ v, ENNReal.ofReal (ladderTarget N a b v) ∂μ := by
        calc ((N : ℕ) : ENNReal) * ∫⁻ v, ENNReal.ofReal (mixedRev a b j v) ∂μ
            = ∑ k : Fin N, ∫⁻ v, ENNReal.ofReal (mixedRev a b j v) ∂μ := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = ∑ k : Fin N, ∫⁻ v, ENNReal.ofReal (mixedRev a b k v) ∂μ := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [lintegral_perm μ hexch _ (hM j) (Equiv.swap j k)]
              simp only [mixedRev_perm]
          _ = ∫⁻ v, ∑ k : Fin N, ENNReal.ofReal (mixedRev a b k v) ∂μ := by
              rw [lintegral_finsetSum]; intro k _; exact hM k
          _ ≤ ∫⁻ v, ((N : ℕ) : ENNReal) * ENNReal.ofReal (ladderTarget N a b v) ∂μ := by
              refine lintegral_mono_ae (hsupp.mono fun v hv => ?_)
              rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by
                unfold mixedRev; split_ifs <;> linarith), sum_mixedRev a b hab v hv hN1,
                ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
          _ = ((N : ℕ) : ENNReal) * ∫⁻ v, ENNReal.ofReal (ladderTarget N a b v) ∂μ := by
              rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
      exact (ENNReal.mul_le_mul_iff_right hNe (ENNReal.natCast_ne_top _)).mp key
    calc expDP μ p ≤ ∫⁻ v, ENNReal.ofReal (mixedRev a b j v) ∂μ := by
          unfold expDP
          exact lintegral_mono_ae (hsupp.mono fun v hv =>
            ENNReal.ofReal_le_ofReal (dp_le_caseB a b ha hab p v hv j hj))
      _ ≤ ∫⁻ v, ENNReal.ofReal (ladderTarget N a b v) ∂μ := hmix
      _ ≤ expOPQ μ α (ladder N a b 1) q :=
          expOPQ_ge μ α hα0 hα1 _ _ _
            (hsupp.mono fun v hv => ladder_ge hN1 a b hab v hv _ (Or.inl rfl) q hq)
            (hsupp.mono fun v hv => ladder_ge hN1 a b hab v hv _ (Or.inr rfl) q hq)
      _ ≤ optOPQ μ α := le_optOPQ μ α _ _ hp0 hq0

theorem case_ii {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ0 : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (hexch : Exchangeable μ)
    (htwo : TwoValued μ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    optDP μ ≤ optOPQ μ α := by
  obtain ⟨a, b, hab, hsupp⟩ := htwo
  by_cases ha : 0 ≤ a
  · exact case_ii_ab hN μ hexch a b ha hab hsupp α hα0 hα1
  · push Not at ha
    let b' : ℝ := if 0 < b then b else 1
    have hb' : 0 < b' := by simp only [b']; split_ifs with h <;> linarith
    refine case_ii_ab hN μ hexch 0 b' le_rfl hb' ?_ α hα0 hα1
    filter_upwards [hsupp, hμ0] with v hv hv0 i
    rcases hv i with h | h
    · linarith [hv0 i]
    · by_cases hb : 0 < b
      · right; simp only [b', if_pos hb]; exact h
      · left; have := hv0 i; linarith

theorem theorem_1 {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ0 : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (hexch : Exchangeable μ)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcase : α = 1 ∨ TwoValued μ) :
    optDP μ ≤ optOPQ μ α := by
  rcases hcase with rfl | htwo
  · exact case_i hN μ hμ0 hexch
  · exact case_ii hN μ hμ0 hexch htwo α hα0 hα1

end OPQSol

open OpaquePricing.Dominance

theorem solution {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ0 : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (hexch : Exchangeable μ)
    (htwo : TwoValued μ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    optDP μ ≤ optOPQ μ α :=
  OPQSol.case_ii hN μ hμ0 hexch htwo α hα0 hα1
