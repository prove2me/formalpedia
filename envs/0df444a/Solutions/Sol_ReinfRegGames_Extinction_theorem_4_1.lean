-- Prove2me | solution 1 for ReinfRegGames.Extinction.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:34:33.766964+00:00
-- url     : https://prove2.me/submissions/b988594c-8b3f-4667-9c94-5374898f5213

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_Extinction_Dominance

namespace RRAux_ReinfRegGames_Extinction_theorem_4_1

open ReinfRegGames.Extinction

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]

lemma prod_update (z : ∀ ℓ, A ℓ → ℝ) (k : ι) (q : A k → ℝ) (s : ∀ ℓ, A ℓ) :
    ∏ i, Function.update z k q i (s i) = q (s k) * ∏ i ∈ Finset.univ.erase k, z i (s i) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

lemma ep_update (u : ι → (∀ k, A k) → ℝ) (z : ∀ ℓ, A ℓ → ℝ) (k j : ι) (q : A k → ℝ) :
    AGT.expectedPayoff u (Function.update z k q) j =
      ∑ s : (∀ ℓ, A ℓ), q (s k) * (∏ i ∈ Finset.univ.erase k, z i (s i)) * u j s := by
  unfold AGT.expectedPayoff AGT.profileProb
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [prod_update]

lemma ep_linear (u : ι → (∀ k, A k) → ℝ) (z : ∀ ℓ, A ℓ → ℝ) (k j : ι) (q : A k → ℝ) :
    AGT.expectedPayoff u (Function.update z k q) j =
      ∑ α, q α * AGT.expectedPayoff u (Function.update z k (Pi.single α 1)) j := by
  simp only [ep_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.single_apply]
  have : ∀ α : A k, q α * ((if s k = α then (1 : ℝ) else 0) *
      (∏ i ∈ Finset.univ.erase k, z i (s i)) * u j s) =
      if s k = α then q (s k) * (∏ i ∈ Finset.univ.erase k, z i (s i)) * u j s else 0 := by
    intro α
    split_ifs with h
    · rw [h]; ring
    · ring
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ep_continuous (u : ι → (∀ k, A k) → ℝ) (k j : ι) (q : A k → ℝ) :
    Continuous fun z : (∀ ℓ, A ℓ → ℝ) => AGT.expectedPayoff u (Function.update z k q) j := by
  simp only [ep_update]
  fun_prop

end

lemma compact_gap {E : Type*} [TopologicalSpace E] {P : Set E} (hP : IsCompact P)
    {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hpos : ∀ z ∈ P, f z = 0 → 0 < g z) (hf0 : ∀ z ∈ P, 0 ≤ f z) :
    ∃ η > 0, ∃ δ > 0, ∀ z ∈ P, f z < η → δ ≤ g z := by
  have hK : IsCompact (P ∩ f ⁻¹' {0}) := hP.inter_right (isClosed_singleton.preimage hf)
  obtain ⟨δ₀, hδ₀, hδK⟩ : ∃ δ₀ > 0, ∀ z ∈ P ∩ f ⁻¹' {0}, δ₀ ≤ g z := by
    rcases (P ∩ f ⁻¹' {0}).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun z hz => by rw [he] at hz; exact absurd hz (by simp)⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne hg.continuousOn
      exact ⟨g z₀, hpos z₀ hz₀.1 hz₀.2, fun z hz => isMinOn_iff.1 hmin z hz⟩
  have hL : IsCompact (P ∩ g ⁻¹' Set.Iic (δ₀ / 2)) :=
    hP.inter_right (isClosed_Iic.preimage hg)
  obtain ⟨η, hη, hηL⟩ : ∃ η > 0, ∀ z ∈ P ∩ g ⁻¹' Set.Iic (δ₀ / 2), η ≤ f z := by
    rcases (P ∩ g ⁻¹' Set.Iic (δ₀ / 2)).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun z hz => by rw [he] at hz; exact absurd hz (by simp)⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hL.exists_isMinOn hne hf.continuousOn
      refine ⟨f z₀, ?_, fun z hz => isMinOn_iff.1 hmin z hz⟩
      rcases (hf0 z₀ hz₀.1).lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 := hδK z₀ ⟨hz₀.1, h.symm⟩
        have h2 : g z₀ ≤ δ₀ / 2 := hz₀.2
        linarith
  refine ⟨η, hη, δ₀ / 2, by linarith, fun z hz hfz => ?_⟩
  by_contra hcon
  push Not at hcon
  have := hηL z ⟨hz, le_of_lt hcon⟩
  linarith

lemma choice_alg {ε yp yp' yx yw hw hx hp' H : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hyw : yw * (1 - ε) = yx - ε * yp)
    (opt1 : yw - hw ≤ yx - hx) (opt2 : yp' - hp' ≤ yx - hx)
    (hbw : |hw| ≤ H) (hbx : |hx| ≤ H) (hbp' : |hp'| ≤ H) :
    ε * (yp' - yp) ≤ 4 * H := by
  have h1ε : 0 < 1 - ε := by linarith
  rw [abs_le] at hbw hbx hbp'
  have hH : 0 ≤ H := by linarith [hbw.1, hbw.2]
  have e1 := mul_le_mul_of_nonneg_left opt1 h1ε.le
  have e2 : ε * (yx - yp) ≤ (1 - ε) * (hw - hx) := by nlinarith
  have e3 : (1 - ε) * (hw - hx) ≤ 2 * H := by nlinarith
  have e4 := mul_le_mul_of_nonneg_left opt2 hε0.le
  have e5 : ε * (hp' - hx) ≤ 2 * H := by nlinarith
  nlinarith

lemma choice_gap {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (H : ℝ)
    (hH : ∀ q ∈ stdSimplex ℝ B, |h q| ≤ H) (y x p p' : B → ℝ) (hx : IsChoice h y x)
    (hp : AGT.IsLottery p) (hp' : AGT.IsLottery p') (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hge : ∀ α, 0 < p α → ε ≤ x α) :
    ε * (y ⬝ᵥ p' - y ⬝ᵥ p) ≤ 4 * H := by
  have hp'S : p' ∈ stdSimplex ℝ B := ⟨hp'.1, hp'.2⟩
  have hxS := hx.1
  have h1ε : 0 < 1 - ε := by linarith
  have hp1 : ∀ α, p α ≤ 1 := fun α => by
    have := Finset.single_le_sum (fun a _ => hp.1 a) (Finset.mem_univ α)
    rw [hp.2] at this
    exact this
  let w : B → ℝ := fun α => (x α - ε * p α) / (1 - ε)
  have hwS : w ∈ stdSimplex ℝ B := by
    refine ⟨fun α => div_nonneg ?_ h1ε.le, ?_⟩
    · rcases (hp.1 α).lt_or_eq with h | h
      · have h1 := hge α h
        have h2 := hp1 α
        have h3 := mul_le_mul_of_nonneg_left h2 hε0.le
        linarith
      · rw [← h, mul_zero, sub_zero]; exact hxS.1 α
    · simp only [w, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hxS.2, hp.2]
      field_simp
  have hyw : y ⬝ᵥ w * (1 - ε) = y ⬝ᵥ x - ε * y ⬝ᵥ p := by
    simp only [dotProduct, w, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    field_simp
  exact choice_alg hε0 hε1 hyw (hx.2 w hwS) (hx.2 p' hp'S) (hH w hwS) (hH x hxS) (hH p' hp'S)

lemma growth (D D' : ℝ → ℝ) (T₀ δ : ℝ) (hT₀ : 0 ≤ T₀)
    (hD : ∀ t, 0 ≤ t → HasDerivWithinAt D (D' t) (Set.Ici 0) t)
    (hD' : ∀ t, T₀ ≤ t → δ ≤ D' t) :
    ∀ t, T₀ ≤ t → D T₀ + δ * (t - T₀) ≤ D t := by
  have hmono : MonotoneOn (fun t => D t - δ * t) (Set.Ici T₀) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => D' t - δ) (convex_Ici T₀)
    · intro t ht
      have ht' : T₀ ≤ t := ht
      have h1 : ContinuousWithinAt D (Set.Ici T₀) t :=
        (hD t (le_trans hT₀ ht')).continuousWithinAt.mono (Set.Ici_subset_Ici.2 hT₀)
      exact h1.sub (continuousWithinAt_const.mul continuousWithinAt_id)
    · intro t ht
      rw [interior_Ici] at ht ⊢
      have ht' : T₀ < t := ht
      have h1 : HasDerivAt D (D' t) t :=
        (hD t (by linarith)).hasDerivAt (Ici_mem_nhds (by linarith))
      have h2 := h1.sub ((hasDerivAt_id t).const_mul δ)
      simp only [mul_one] at h2
      exact h2.hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : T₀ < t := ht
      linarith [hD' t ht'.le]
  intro t ht
  have := hmono (Set.mem_Ici.2 le_rfl) ht ht
  simp only at this
  linarith

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]

lemma elim_round (u : ι → (∀ k, A k) → ℝ) (ℓ : ι) (β : A ℓ) :
    ∀ r, β ∉ survivors u r ℓ →
      ∃ r' < r, β ∈ survivors u r' ℓ ∧ β ∉ survivors u (r' + 1) ℓ := by
  intro r
  induction r with
  | zero => intro h; exact absurd (by simp [survivors]) h
  | succ n ih =>
    intro h
    by_cases hn : β ∈ survivors u n ℓ
    · exact ⟨n, Nat.lt_succ_self n, hn, h⟩
    · obtain ⟨r', hr', h1, h2⟩ := ih hn
      exact ⟨r', Nat.lt_succ_of_lt hr', h1, h2⟩

lemma single_lottery {B : Type*} [Fintype B] [DecidableEq B] (β : B) :
    AGT.IsLottery (Pi.single β (1 : ℝ) : B → ℝ) := by
  refine ⟨fun a => ?_, by simp⟩
  rw [Pi.single_apply]
  split_ifs <;> norm_num

lemma single_eq {B : Type*} [DecidableEq B] {β α : B}
    (h : (Pi.single β (1 : ℝ) : B → ℝ) α ≠ 0) : α = β := by
  by_contra hne
  exact h (by simp [Pi.single_apply, hne])

lemma main_ind (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (K : ι → ℝ)
    (hpen : ∀ k, IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : IsRLOrbit u h y x) :
    ∀ (r : ℕ) (k : ι) (p p' : A k → ℝ), AGT.IsLottery p → AGT.IsLottery p' →
    (∀ α, p α ≠ 0 → α ∈ survivors u r k) → (∀ α, p' α ≠ 0 → α ∈ survivors u r k) →
    (∀ z : ∀ ℓ, A ℓ → ℝ, AGT.IsMixedProfile z →
      (∀ ℓ β, z ℓ β ≠ 0 → β ∈ survivors u r ℓ) →
      AGT.expectedPayoff u (Function.update z k p) k <
        AGT.expectedPayoff u (Function.update z k p') k) →
    ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T, ∃ α, 0 < p α ∧ x t k α < ε := by
  classical
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro k p p' hp hp' hpS hp'S hdom ε hε
  -- Step 1: strategies eliminated before round r die out
  have hsmall : ∀ ℓ (β : A ℓ), β ∉ survivors u r ℓ → ∀ η > 0,
      ∀ᶠ t in Filter.atTop, x t ℓ β < η := by
    intro ℓ β hβ η hη
    obtain ⟨r', hr', hin, hout⟩ := elim_round u ℓ β r hβ
    simp only [survivors, Set.mem_setOf_eq, not_and, not_not] at hout
    obtain ⟨q, hq, hqS, hqdom⟩ := hout hin
    obtain ⟨T, hT⟩ := ih r' hr' ℓ (Pi.single β 1) q (single_lottery β) hq
      (fun α hα => by rw [single_eq hα]; exact hin) hqS (fun z hz hzS => hqdom z hz hzS) η hη
    rw [Filter.eventually_atTop]
    refine ⟨T, fun t ht => ?_⟩
    obtain ⟨α, hα, hxα⟩ := hT t ht
    rw [← single_eq hα.ne']
    exact hxα
  -- Step 2: uniform gap near the survivor face
  let P : Set (∀ ℓ, A ℓ → ℝ) := Set.pi Set.univ (fun ℓ => stdSimplex ℝ (A ℓ))
  have hP : IsCompact P := isCompact_univ_pi (fun ℓ => isCompact_stdSimplex ℝ (A ℓ))
  let f : (∀ ℓ, A ℓ → ℝ) → ℝ := fun z =>
    ∑ ℓ, ∑ β : A ℓ, (if β ∈ survivors u r ℓ then 0 else z ℓ β)
  let g : (∀ ℓ, A ℓ → ℝ) → ℝ := fun z =>
    AGT.expectedPayoff u (Function.update z k p') k - AGT.expectedPayoff u (Function.update z k p) k
  have hf : Continuous f := by
    refine continuous_finset_sum _ fun ℓ _ => continuous_finset_sum _ fun β _ => ?_
    split_ifs
    · exact continuous_const
    · exact (continuous_apply β).comp (continuous_apply ℓ)
  have hg : Continuous g := (ep_continuous u k k p').sub (ep_continuous u k k p)
  have hf0 : ∀ z ∈ P, 0 ≤ f z := by
    intro z hz
    refine Finset.sum_nonneg fun ℓ _ => Finset.sum_nonneg fun β _ => ?_
    split_ifs
    · exact le_rfl
    · exact (hz ℓ (Set.mem_univ ℓ)).1 β
  have hpos : ∀ z ∈ P, f z = 0 → 0 < g z := by
    intro z hz hfz
    have hterm : ∀ ℓ (β : A ℓ), (if β ∈ survivors u r ℓ then 0 else z ℓ β) = 0 := by
      intro ℓ β
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun ℓ _ => Finset.sum_nonneg fun β _ => by
        split_ifs
        · exact le_rfl
        · exact (hz ℓ (Set.mem_univ ℓ)).1 β)).1 hfz ℓ (Finset.mem_univ ℓ)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun β _ => by
        split_ifs
        · exact le_rfl
        · exact (hz ℓ (Set.mem_univ ℓ)).1 β)).1 h1 β (Finset.mem_univ β)
    have hzS : ∀ ℓ β, z ℓ β ≠ 0 → β ∈ survivors u r ℓ := by
      intro ℓ β hne
      by_contra hβ
      have := hterm ℓ β
      rw [if_neg hβ] at this
      exact hne this
    have hzM : AGT.IsMixedProfile z := fun ℓ =>
      ⟨(hz ℓ (Set.mem_univ ℓ)).1, (hz ℓ (Set.mem_univ ℓ)).2⟩
    exact sub_pos.2 (hdom z hzM hzS)
  obtain ⟨η, hη, δ, hδ, hgap⟩ := compact_gap hP hf hg hpos hf0
  -- Step 3: eventually the orbit is close to the survivor face
  let N : ℝ := (∑ ℓ, (Fintype.card (A ℓ) : ℝ)) + 1
  have hN0 : (0 : ℝ) ≤ ∑ ℓ, (Fintype.card (A ℓ) : ℝ) :=
    Finset.sum_nonneg fun ℓ _ => Nat.cast_nonneg _
  have hN : 0 < N := by simp only [N]; linarith
  have hηN : 0 < η / N := div_pos hη hN
  have hev : ∀ᶠ t in Filter.atTop,
      (∀ ℓ, ∀ β : A ℓ, (if β ∈ survivors u r ℓ then 0 else x t ℓ β) ≤ η / N) ∧ 0 ≤ t := by
    refine Filter.Eventually.and (Filter.eventually_all.2 fun ℓ =>
      Filter.eventually_all.2 fun β => ?_) (Filter.eventually_ge_atTop 0)
    by_cases hβ : β ∈ survivors u r ℓ
    · exact Filter.Eventually.of_forall fun t => by rw [if_pos hβ]; exact hηN.le
    · exact (hsmall ℓ β hβ (η / N) hηN).mono fun t ht => by rw [if_neg hβ]; exact ht.le
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 hev
  let T₀ : ℝ := max T₁ 0
  have hxP : ∀ t, 0 ≤ t → x t ∈ P := fun t ht ℓ _ => (horb t ht ℓ).1.1
  have hfx : ∀ t, T₀ ≤ t → f (x t) < η := by
    intro t ht
    have ht1 := (hT₁ t (le_trans (le_max_left _ _) ht)).1
    have hle : f (x t) ≤ ∑ ℓ, ∑ β : A ℓ, η / N :=
      Finset.sum_le_sum fun ℓ _ => Finset.sum_le_sum fun β _ => ht1 ℓ β
    have hcomp : ∑ ℓ, ∑ β : A ℓ, η / N = (∑ ℓ, (Fintype.card (A ℓ) : ℝ)) * (η / N) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_mul]
    have hlt : (∑ ℓ, (Fintype.card (A ℓ) : ℝ)) * (η / N) < η := by
      rw [mul_div_assoc', div_lt_iff₀ hN]
      simp only [N]
      nlinarith
    linarith
  -- Step 4: the score difference grows linearly
  let D : ℝ → ℝ := fun t => y t k ⬝ᵥ p' - y t k ⬝ᵥ p
  have hDer : ∀ t, 0 ≤ t → HasDerivWithinAt D (g (x t)) (Set.Ici 0) t := by
    intro t ht
    have hy : ∀ α, HasDerivWithinAt (fun s => y s k α) (payoffVec u (x t) k α) (Set.Ici 0) t := by
      intro α
      have := (horb t ht k).2 α
      simpa only [one_mul] using this
    have h1 : HasDerivWithinAt (fun s => y s k ⬝ᵥ p')
        (∑ α, payoffVec u (x t) k α * p' α) (Set.Ici 0) t :=
      HasDerivWithinAt.fun_sum fun α _ => (hy α).mul_const (p' α)
    have h2 : HasDerivWithinAt (fun s => y s k ⬝ᵥ p)
        (∑ α, payoffVec u (x t) k α * p α) (Set.Ici 0) t :=
      HasDerivWithinAt.fun_sum fun α _ => (hy α).mul_const (p α)
    have heq : g (x t) = ∑ α, payoffVec u (x t) k α * p' α - ∑ α, payoffVec u (x t) k α * p α := by
      simp only [g, payoffVec]
      rw [ep_linear u (x t) k k p', ep_linear u (x t) k k p]
      congr 1 <;> exact Finset.sum_congr rfl fun α _ => mul_comm _ _
    rw [heq]
    exact h1.sub h2
  have hgrow := growth D (fun t => g (x t)) T₀ δ (le_max_right _ _) hDer
    (fun t ht => hgap (x t) (hxP t (le_trans (le_max_right _ _) ht)) (hfx t ht))
  -- Step 5: bounded penalty, and the choice-map bound
  obtain ⟨H, hH⟩ := (isCompact_stdSimplex ℝ (A k)).exists_bound_of_continuousOn (hpen k).1
  have hH' : ∀ q ∈ stdSimplex ℝ (A k), |h k q| ≤ H := fun q hq => by
    rw [← Real.norm_eq_abs]; exact hH q hq
  let ε' : ℝ := min ε (1 / 2)
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨max T₀ (T₀ + (4 * H / ε' - D T₀ + 1) / δ), fun t ht => ?_⟩
  have htT₀ : T₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : T₀ + (4 * H / ε' - D T₀ + 1) / δ ≤ t := le_trans (le_max_right _ _) ht
  have hDt := hgrow t htT₀
  have hlow : 4 * H / ε' + 1 ≤ D t := by
    have h3 : (4 * H / ε' - D T₀ + 1) / δ ≤ t - T₀ := by linarith
    have h4 : 4 * H / ε' - D T₀ + 1 ≤ δ * (t - T₀) := by
      rw [div_le_iff₀ hδ] at h3; linarith
    linarith
  by_contra hcon
  push Not at hcon
  have hge : ∀ α, 0 < p α → ε' ≤ x t k α := fun α hα =>
    le_trans (min_le_left _ _) (hcon α hα)
  have ht0 : 0 ≤ t := le_trans (le_max_right _ _) htT₀
  have hb := choice_gap (h k) H hH' (y t k) (x t k) p p' (horb t ht0 k).1 hp hp' ε' hε'0 hε'1 hge
  have : D t ≤ 4 * H / ε' := by
    rw [le_div_iff₀ hε'0]
    simp only [D]
    linarith
  linarith

end

end RRAux_ReinfRegGames_Extinction_theorem_4_1

open RRAux_ReinfRegGames_Extinction_theorem_4_1 in
open ReinfRegGames.Extinction in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (K : ι → ℝ)
    (hpen : ∀ k, IsPenalty (h k) (K k))
    (y x : ℝ → ∀ k, A k → ℝ) (horb : IsRLOrbit u h y x)
    (r : ℕ) (k : ι) (p p' : A k → ℝ) (hp : AGT.IsLottery p) (hp' : AGT.IsLottery p')
    (hpS : ∀ α, p α ≠ 0 → α ∈ survivors u r k) (hp'S : ∀ α, p' α ≠ 0 → α ∈ survivors u r k)
    (hdom : ∀ z : ∀ ℓ, A ℓ → ℝ, AGT.IsMixedProfile z →
      (∀ ℓ β, z ℓ β ≠ 0 → β ∈ survivors u r ℓ) →
      AGT.expectedPayoff u (Function.update z k p) k <
        AGT.expectedPayoff u (Function.update z k p') k) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t ≥ T, ∃ α, 0 < p α ∧ x t k α < ε :=
  main_ind u h K hpen y x horb r k p p' hp hp' hpS hp'S hdom

#print axioms solution
