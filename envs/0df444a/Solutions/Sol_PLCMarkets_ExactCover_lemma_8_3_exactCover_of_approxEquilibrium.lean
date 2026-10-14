-- Prove2me | solution 1 for PLCMarkets.ExactCover.lemma_8_3_exactCover_of_approxEquilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:56:49.868551+00:00
-- url     : https://prove2.me/submissions/deeb655f-d4ff-435c-ab3e-f927b2f2f5ce

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD

set_option autoImplicit false

namespace C9e55ab3

open PLCMarkets.ExactCover

noncomputable def G (A x : ℝ) : ℝ := 2 * min (max x 0) A + max (x - A) 0

lemma reg_eval (n : ℕ) (x : ℝ) : (regulatorUtil n).eval x = G ((n : ℝ) ^ 3) x := by
  simp [PLUtility.eval, regulatorUtil, PLUtility.oneSeg, segEval, PLUtility.length, G]

lemma G_up (A u s : ℝ) (hA : 0 ≤ A) (hu : 0 ≤ u) (hs : 0 ≤ s) :
    s ≤ G A (u + s) - G A u := by
  unfold G
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma G_down (A u s : ℝ) (hA : 0 ≤ A) (_hu : 0 ≤ u) (hs : 0 ≤ s) :
    G A (u + s) - G A u ≤ 2 * s := by
  unfold G
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma util_reg {n : ℕ} (C : Fin n → Finset (Fin n)) (l : Good n) :
    (marketD C).util Agent.regulator l = regulatorUtil n := rfl

lemma nonreg_bound {n : ℕ} (C : Fin n → Finset (Fin n)) (i : Agent n)
    (hi : i ≠ Agent.regulator) (j : Good n) :
    ((marketD C).util i j).tail = 0 ∧ ((((marketD C).util i j).length : ℚ) : ℝ) ≤ 3 / 4 := by
  cases i with
  | regulator => exact absurd rfl hi
  | setAgent a =>
    cases j with
    | zero => simp [marketD, utilD, PLUtility.oneSeg, PLUtility.length]; norm_num
    | set b =>
      simp only [marketD, utilD]
      split_ifs <;> simp [PLUtility.oneSeg, PLUtility.flat, PLUtility.length] <;> norm_num
    | elem b =>
      simp only [marketD, utilD]
      split_ifs <;> simp [PLUtility.oneSeg, PLUtility.flat, PLUtility.length] <;> norm_num
  | elemAgent a =>
    cases j <;> simp [marketD, utilD, PLUtility.oneSeg, PLUtility.flat, PLUtility.length] <;> norm_num
  | extra =>
    cases j <;> simp [marketD, utilD, PLUtility.oneSeg, PLUtility.flat, PLUtility.length] <;> norm_num

lemma card_agent (n : ℕ) : Fintype.card (Agent n) ≤ 2 * n + 2 := by
  let f : Agent n → Option (Option (Fin n ⊕ Fin n)) := fun a => match a with
    | .regulator => none
    | .extra => some none
    | .setAgent i => some (some (Sum.inl i))
    | .elemAgent i => some (some (Sum.inr i))
  have hf : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp_all [f]
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin] at this
  omega

end C9e55ab3

open PLCMarkets.ExactCover in
theorem C9e55ab3.l72 (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (p : Good n → ℝ)
    (hp : (marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p) :
    (∀ j, 0 < p j) ∧ ∀ j k, p j ≤ 2 * p k := by
  obtain ⟨⟨hp0, _hpsum⟩, x, hopt, hclear⟩ := hp
  obtain ⟨hy0, hycost, hymax, -⟩ := hopt Agent.regulator
  set y := x Agent.regulator with hy
  have hA : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hU : ∀ z : Good n → ℝ,
      (marketD C).utility Agent.regulator z = ∑ l, C9e55ab3.G ((n : ℝ) ^ 3) (z l) := by
    intro z; simp only [ADMarket.utility, C9e55ab3.util_reg, C9e55ab3.reg_eval]
  have hpos : ∀ j, 0 < p j := by
    intro j
    rcases (hp0 j).lt_or_eq with h | h
    · exact h
    exfalso
    let z : Good n → ℝ := fun l => y l + if l = j then 1 else 0
    have hz0 : ∀ l, 0 ≤ z l := by
      intro l; have := hy0 l; simp only [z]; split_ifs <;> linarith
    have hzc : ∑ l, p l * z l ≤ (marketD C).income p Agent.regulator := by
      have : ∑ l, p l * z l = ∑ l, p l * y l := by
        simp only [z, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, ← h, add_zero]
      rw [this]; exact hycost
    have h1 := hymax z hz0 hzc
    rw [hU, hU] at h1
    have h2 : ∀ l, (if l = j then (1 : ℝ) else 0) ≤ C9e55ab3.G ((n : ℝ) ^ 3) (z l) - C9e55ab3.G ((n : ℝ) ^ 3) (y l) := by
      intro l
      simp only [z]
      split_ifs
      · exact C9e55ab3.G_up _ _ _ hA (hy0 l) zero_le_one
      · simp
    have h3 := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => h2 l)
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq'] at h3
    simp only [Finset.mem_univ, if_true] at h3
    linarith
  refine ⟨hpos, ?_⟩
  intro j k
  by_contra hjk
  push Not at hjk
  have hjk' : j ≠ k := by rintro rfl; linarith [hpos j]
  have hyj : y j = 0 := by
    by_contra hne
    have hyjpos : 0 < y j := lt_of_le_of_ne (hy0 j) (Ne.symm hne)
    have hpk := hpos k
    set δ := y j with hδ
    set t := δ * p j / p k with ht
    have htpos : 0 ≤ t := div_nonneg (mul_nonneg hyjpos.le (hp0 j)) hpk.le
    have hpt : p k * t = δ * p j := by rw [ht]; field_simp
    have htd : 0 < t - 2 * δ := by
      have : t - 2 * δ = δ * (p j - 2 * p k) / p k := by rw [ht]; field_simp
      rw [this]; apply div_pos _ hpk; apply mul_pos hyjpos; linarith
    let z : Good n → ℝ := fun l => y l + ((if l = k then t else 0) - (if l = j then δ else 0))
    have hz0 : ∀ l, 0 ≤ z l := by
      intro l; have := hy0 l; simp only [z]
      split_ifs with h1 h2 h2
      · exact absurd (h2.symm.trans h1) hjk'
      · linarith
      · subst h2; linarith
      · linarith
    have hzc : ∑ l, p l * z l ≤ (marketD C).income p Agent.regulator := by
      have : ∑ l, p l * z l = ∑ l, p l * y l := by
        simp only [z, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [hpt]; ring
      rw [this]; exact hycost
    have h1 := hymax z hz0 hzc
    rw [hU, hU] at h1
    have h2 : ∀ l, (if l = k then t else 0) - 2 * (if l = j then δ else 0) ≤
        C9e55ab3.G ((n : ℝ) ^ 3) (z l) - C9e55ab3.G ((n : ℝ) ^ 3) (y l) := by
      intro l
      simp only [z]
      split_ifs with h1 h2 h2
      · exact absurd (h2.symm.trans h1) hjk'
      · have := C9e55ab3.G_up _ _ _ hA (hy0 l) htpos
        simp only [sub_zero, mul_zero]
        linarith
      · subst h2
        have := C9e55ab3.G_down ((n : ℝ) ^ 3) 0 δ hA le_rfl hyjpos.le
        simp only [zero_add] at this
        have e : y l + (0 - δ) = 0 := by rw [← hδ]; ring
        rw [e]; linarith
      · simp
    have h3 := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => h2 l)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.sum_ite_eq'] at h3
    simp only [Finset.mem_univ, if_true] at h3
    linarith
  -- demand bound
  have hb : ∀ i, x i j ≤ 3 / 4 := by
    intro i
    by_cases hi : i = Agent.regulator
    · subst hi; rw [← hy, hyj]; norm_num
    · obtain ⟨htail, hlen⟩ := C9e55ab3.nonreg_bound C i hi j
      have := (hopt i).2.2.2 j htail
      linarith
  have hsum : ∑ i, x i j ≤ (Fintype.card (Agent n) : ℝ) * (3 / 4) := by
    calc ∑ i, x i j ≤ ∑ _i : Agent n, (3 / 4 : ℝ) := Finset.sum_le_sum (fun i _ => hb i)
      _ = _ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcardA : (Fintype.card (Agent n) : ℝ) ≤ 2 * n + 2 := by
    exact_mod_cast C9e55ab3.card_agent n
  -- supply bound
  have hS : (n : ℝ) ^ 3 ≤ (marketD C).supply j := by
    unfold ADMarket.supply
    have := Finset.single_le_sum (f := fun i => (((marketD C).endow i j : ℚ) : ℝ))
      (fun i _ => by exact_mod_cast (marketD C).endow_nonneg i j) (Finset.mem_univ Agent.regulator)
    simpa [marketD, endowD] using this
  have hn' : (36 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : (2 : ℝ) ≤ (n : ℝ) ^ 5 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 36) hn' 5]
  have hε : ((n : ℝ) ^ 5)⁻¹ ≤ 1 / 2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) h5
  have hc := hclear j
  have hc' := (abs_le.mp hc).1
  have hSnn : 0 ≤ (marketD C).supply j := le_trans hA hS
  have : ((n : ℝ) ^ 5)⁻¹ * (marketD C).supply j ≤ 1 / 2 * (marketD C).supply j :=
    mul_le_mul_of_nonneg_right hε hSnn
  have hn3 : (n : ℝ) ^ 3 = n * n * n := by ring
  nlinarith

namespace Cadc30cb

open PLCMarkets.ExactCover

/-! ## Generic exchange arguments for optimal bundles -/

lemma exch {A G : Type} [Fintype A] [Fintype G] [DecidableEq G] (M : ADMarket A G) (p : G → ℝ)
    (i : A) (y : G → ℝ) (hy : M.IsOptimalBundle p i y) (g h : G) (hgh : g ≠ h)
    (δ η : ℝ) (hδ : 0 ≤ δ) (hηy : η ≤ y h) (hbal : p g * δ = p h * η) :
    (M.util i g).eval (y g + δ) - (M.util i g).eval (y g) ≤
      (M.util i h).eval (y h) - (M.util i h).eval (y h - η) := by
  obtain ⟨hy0, hyc, hymax, -⟩ := hy
  let z : G → ℝ := fun l => y l + (if l = g then δ else 0) - (if l = h then η else 0)
  have hzg : z g = y g + δ := by simp [z, hgh]
  have hzh : z h = y h - η := by simp [z, hgh.symm]
  have hz0 : ∀ l, 0 ≤ z l := by
    intro l
    rcases eq_or_ne l h with rfl | h2
    · rw [hzh]; linarith
    · have := hy0 l
      simp only [z, if_neg h2]
      split_ifs <;> linarith
  have hzc : ∑ l, p l * z l ≤ M.income p i := by
    have : ∑ l, p l * z l = ∑ l, p l * y l := by
      simp only [z, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hbal]; ring
    rw [this]; exact hyc
  have h1 := hymax z hz0 hzc
  unfold ADMarket.utility at h1
  have h2 : ∑ l, ((M.util i l).eval (z l) - (M.util i l).eval (y l)) =
      ((M.util i g).eval (z g) - (M.util i g).eval (y g)) +
        ((M.util i h).eval (z h) - (M.util i h).eval (y h)) := by
    apply Fintype.sum_eq_add g h hgh
    intro l ⟨hl1, hl2⟩
    simp [z, hl1, hl2]
  rw [Finset.sum_sub_distrib, hzg, hzh] at h2
  linarith

lemma unsp {A G : Type} [Fintype A] [Fintype G] [DecidableEq G] (M : ADMarket A G) (p : G → ℝ)
    (i : A) (y : G → ℝ) (hy : M.IsOptimalBundle p i y) (g : G)
    (δ : ℝ) (hδ : 0 ≤ δ) (hc : ∑ l, p l * y l + p g * δ ≤ M.income p i) :
    (M.util i g).eval (y g + δ) ≤ (M.util i g).eval (y g) := by
  obtain ⟨hy0, hyc, hymax, -⟩ := hy
  let z : G → ℝ := fun l => y l + (if l = g then δ else 0)
  have hzg : z g = y g + δ := by simp [z]
  have hz0 : ∀ l, 0 ≤ z l := by
    intro l; have := hy0 l; simp only [z]; split_ifs <;> linarith
  have hzc : ∑ l, p l * z l ≤ M.income p i := by
    have : ∑ l, p l * z l = ∑ l, p l * y l + p g * δ := by
      simp only [z, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [this]; exact hc
  have h1 := hymax z hz0 hzc
  unfold ADMarket.utility at h1
  have h2 : ∑ l, ((M.util i l).eval (z l) - (M.util i l).eval (y l)) =
      (M.util i g).eval (z g) - (M.util i g).eval (y g) := by
    apply Fintype.sum_eq_single g
    intro l hl
    simp [z, hl]
  rw [Finset.sum_sub_distrib, hzg] at h2
  linarith

/-- Exchange contradiction: moving money from `h` to `g` would strictly gain. -/
lemma exch_contra {A G : Type} [Fintype A] [Fintype G] [DecidableEq G] (M : ADMarket A G)
    (p : G → ℝ) (i : A) (y : G → ℝ) (hy : M.IsOptimalBundle p i y) (g h : G) (hgh : g ≠ h)
    (hpg : 0 < p g) (hph : 0 < p h) (cg ch cap room : ℝ)
    (hcap : y g < cap) (hroom : 0 < room) (hroomle : room ≤ y h)
    (hgain : ∀ δ, 0 ≤ δ → y g + δ ≤ cap →
      cg * δ ≤ (M.util i g).eval (y g + δ) - (M.util i g).eval (y g))
    (hloss : ∀ η, 0 ≤ η → η ≤ room →
      (M.util i h).eval (y h) - (M.util i h).eval (y h - η) ≤ ch * η)
    (hbang : ch * p g < cg * p h) : False := by
  set δ := min (cap - y g) (room * p h / p g) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (div_pos (mul_pos hroom hph) hpg)
  set η := δ * p g / p h with hη
  have hηnn : 0 ≤ η := div_nonneg (mul_nonneg hδpos.le hpg.le) hph.le
  have hηroom : η ≤ room := by
    rw [hη, div_le_iff₀ hph]
    have : δ ≤ room * p h / p g := min_le_right _ _
    rw [le_div_iff₀ hpg] at this; linarith
  have hbal : p g * δ = p h * η := by rw [hη]; field_simp
  have e := exch M p i y hy g h hgh δ η hδpos.le (le_trans hηroom hroomle) hbal
  have g1 := hgain δ hδpos.le (by have := min_le_left (cap - y g) (room * p h / p g); linarith)
  have l1 := hloss η hηnn hηroom
  have key : cg * δ ≤ ch * η := by linarith
  have key2 : cg * δ * p h ≤ ch * δ * p g := by
    have := mul_le_mul_of_nonneg_right key hph.le
    rw [hη] at this
    have e2 : ch * (δ * p g / p h) * p h = ch * δ * p g := by field_simp
    linarith
  have : δ * (ch * p g) < δ * (cg * p h) := mul_lt_mul_of_pos_left hbang hδpos
  nlinarith

/-- Unspent-money contradiction. -/
lemma unsp_contra {A G : Type} [Fintype A] [Fintype G] [DecidableEq G] (M : ADMarket A G)
    (p : G → ℝ) (i : A) (y : G → ℝ) (hy : M.IsOptimalBundle p i y) (g : G)
    (hpg : 0 < p g) (cg cap : ℝ) (hcg : 0 < cg) (hcap : y g < cap)
    (hgap : ∑ l, p l * y l < M.income p i)
    (hgain : ∀ δ, 0 ≤ δ → y g + δ ≤ cap →
      cg * δ ≤ (M.util i g).eval (y g + δ) - (M.util i g).eval (y g)) : False := by
  set δ := min (cap - y g) ((M.income p i - ∑ l, p l * y l) / p g) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (div_pos (by linarith) hpg)
  have hc : ∑ l, p l * y l + p g * δ ≤ M.income p i := by
    have : δ ≤ (M.income p i - ∑ l, p l * y l) / p g := min_le_right _ _
    rw [le_div_iff₀ hpg] at this; linarith
  have u := unsp M p i y hy g δ hδpos.le hc
  have g1 := hgain δ hδpos.le (by have := min_le_left (cap - y g) ((M.income p i - ∑ l, p l * y l) / p g); linarith)
  nlinarith

/-- Total unspent money is at most `ε · Σ p s`. -/
lemma money {A G : Type} [Fintype A] [Fintype G] (M : ADMarket A G) (ε : ℝ) (p : G → ℝ)
    (hp : ∀ g, 0 ≤ p g) (x : A → G → ℝ)
    (hclear : ∀ j, |∑ i, x i j - M.supply j| ≤ ε * M.supply j) :
    ∑ i, (M.income p i - ∑ g, p g * x i g) ≤ ε * ∑ g, p g * M.supply g := by
  have h1 : ∑ i, M.income p i = ∑ g, p g * M.supply g := by
    simp only [ADMarket.income, ADMarket.supply, Finset.mul_sum]; exact Finset.sum_comm
  have h2 : ∑ i, ∑ g, p g * x i g = ∑ g, p g * ∑ i, x i g := by
    simp only [Finset.mul_sum]; exact Finset.sum_comm
  rw [Finset.sum_sub_distrib, h1, h2, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum; intro g _
  have := (abs_le.mp (hclear g)).1
  have h3 := mul_le_mul_of_nonneg_left (show M.supply g - ∑ i, x i g ≤ ε * M.supply g by linarith) (hp g)
  linarith [show p g * (ε * M.supply g) = ε * (p g * M.supply g) by ring,
    show p g * (M.supply g - ∑ i, x i g) = p g * M.supply g - p g * ∑ i, x i g by ring]

/-! ## Piecewise-linear pieces -/

lemma mm_up (c t δ : ℝ) (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hc : t + δ ≤ c) :
    min (max (t + δ) 0) c - min (max t 0) c = δ := by
  simp only [max_def, min_def]; split_ifs <;> linarith

lemma mm_lip (c t η : ℝ) (hc : 0 ≤ c) (hη : 0 ≤ η) :
    min (max t 0) c - min (max (t - η) 0) c ≤ η := by
  simp only [max_def, min_def]; split_ifs <;> linarith

noncomputable def G (A x : ℝ) : ℝ := 2 * min (max x 0) A + max (x - A) 0

lemma G_up2 (A u s : ℝ) (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ A) :
    G A (u + s) - G A u = 2 * s := by
  unfold G; simp only [max_def, min_def]; split_ifs <;> linarith

lemma G_tail (A u s : ℝ) (hA : 0 ≤ A) (hs : 0 ≤ s) (hus : A ≤ u - s) :
    G A u - G A (u - s) = s := by
  unfold G; simp only [max_def, min_def]; split_ifs <;> linarith

lemma eval_oneSeg (c a t : ℚ) (hc : 0 < c) (ha : 0 ≤ a) (ht : 0 ≤ t) (htc : t ≤ c) (x : ℝ) :
    (PLUtility.oneSeg c a t hc ha ht htc).eval x =
      (c : ℝ) * min (max x 0) (a : ℝ) + (t : ℝ) * max (x - (a : ℝ)) 0 := by
  simp [PLUtility.eval, PLUtility.oneSeg, segEval, PLUtility.length]

lemma eval_flat (x : ℝ) : PLUtility.flat.eval x = 0 := by
  simp [PLUtility.eval, PLUtility.flat, segEval, PLUtility.length]

lemma reg_eval (n : ℕ) (x : ℝ) : (regulatorUtil n).eval x = G ((n : ℝ) ^ 3) x := by
  simp [PLUtility.eval, regulatorUtil, PLUtility.oneSeg, segEval, PLUtility.length, G]

section evals
variable {n : ℕ} (C : Fin n → Finset (Fin n)) (t : ℝ)

lemma ev_r (g : Good n) : ((marketD C).util .regulator g).eval t = G ((n : ℝ) ^ 3) t :=
  reg_eval n t
lemma ev_s0 (i : Fin n) : ((marketD C).util (.setAgent i) .zero).eval t = min (max t 0) (1 / 2) := by
  simp [marketD, utilD, eval_oneSeg]
lemma ev_se (i j : Fin n) (hj : j ∈ C i) : ((marketD C).util (.setAgent i) (.elem j)).eval t =
    1 / 3 * min (max t 0) (1 / 6) := by
  simp only [marketD, utilD, if_pos hj]; simp [eval_oneSeg]
lemma ev_ss (i : Fin n) : ((marketD C).util (.setAgent i) (.set i)).eval t =
    1 / 9 * min (max t 0) (1 / 4) := by
  simp only [marketD, utilD, if_pos rfl]; simp [eval_oneSeg]
lemma ev_e0 (j : Fin n) : ((marketD C).util (.elemAgent j) .zero).eval t = min (max t 0) (1 / 12) := by
  simp [marketD, utilD, eval_oneSeg]

end evals

/-! ## Sums over goods and agents -/

def goodEquiv (n : ℕ) : Good n ≃ Unit ⊕ (Fin n ⊕ Fin n) where
  toFun g := match g with
    | .zero => Sum.inl ()
    | .set i => Sum.inr (Sum.inl i)
    | .elem j => Sum.inr (Sum.inr j)
  invFun s := match s with
    | Sum.inl _ => .zero
    | Sum.inr (Sum.inl i) => .set i
    | Sum.inr (Sum.inr j) => .elem j
  left_inv g := by cases g <;> rfl
  right_inv s := by rcases s with _ | i | j <;> rfl

lemma sum_good {n : ℕ} (f : Good n → ℝ) :
    ∑ g, f g = f .zero + ∑ i, f (.set i) + ∑ j, f (.elem j) := by
  rw [← (goodEquiv n).symm.sum_comp f]
  simp [Fintype.sum_sum_type, goodEquiv, add_assoc]

def agentEquiv (n : ℕ) : Agent n ≃ Unit ⊕ (Fin n ⊕ (Fin n ⊕ Unit)) where
  toFun g := match g with
    | .regulator => Sum.inl ()
    | .setAgent i => Sum.inr (Sum.inl i)
    | .elemAgent j => Sum.inr (Sum.inr (Sum.inl j))
    | .extra => Sum.inr (Sum.inr (Sum.inr ()))
  invFun s := match s with
    | Sum.inl _ => .regulator
    | Sum.inr (Sum.inl i) => .setAgent i
    | Sum.inr (Sum.inr (Sum.inl j)) => .elemAgent j
    | Sum.inr (Sum.inr (Sum.inr _)) => .extra
  left_inv g := by cases g <;> rfl
  right_inv s := by rcases s with _ | i | j | _ <;> rfl

lemma sum_agent {n : ℕ} (f : Agent n → ℝ) :
    ∑ g, f g = f .regulator + ∑ i, f (.setAgent i) + ∑ j, f (.elemAgent j) + f .extra := by
  rw [← (agentEquiv n).symm.sum_comp f]
  simp [Fintype.sum_sum_type, agentEquiv, add_assoc]

lemma sum_ite_S {n : ℕ} (S : Finset (Fin n)) (a b : ℝ) :
    ∑ i, (if i ∈ S then a else b) = (S.card : ℝ) * a + ((n : ℝ) - S.card) * b := by
  have h : ∀ i : Fin n, (if i ∈ S then a else b) = b + (a - b) * (if i ∈ S then 1 else 0) := by
    intro i; split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp [Finset.filter_mem_eq_inter]
  ring

/-! ## Incomes and supplies -/

section market
variable {n : ℕ} (C : Fin n → Finset (Fin n)) (p : Good n → ℝ)

lemma inc_set (i : Fin n) : (marketD C).income p (.setAgent i) = p (.set i) := by
  unfold ADMarket.income
  rw [sum_good]
  simp [marketD, endowD, apply_ite (Rat.cast : ℚ → ℝ), mul_ite]

lemma inc_elem (j : Fin n) : (marketD C).income p (.elemAgent j) = p (.elem j) / 6 := by
  unfold ADMarket.income
  rw [sum_good]
  simp [marketD, endowD, apply_ite (Rat.cast : ℚ → ℝ), mul_ite]; ring

lemma inc_reg : (marketD C).income p .regulator = ∑ g, p g * (n : ℝ) ^ 3 := by
  unfold ADMarket.income
  simp [marketD, endowD]

lemma sup_zero : (marketD C).supply (Good.zero : Good n) = (n : ℝ) ^ 3 + n / 2 := by
  unfold ADMarket.supply
  rw [sum_agent]
  simp [marketD, endowD]

lemma sup_set (i : Fin n) : (marketD C).supply (Good.set i) = (n : ℝ) ^ 3 + 1 := by
  unfold ADMarket.supply
  rw [sum_agent]
  simp [marketD, endowD, apply_ite (Rat.cast : ℚ → ℝ)]

lemma sup_elem (j : Fin n) : (marketD C).supply (Good.elem j) = (n : ℝ) ^ 3 + 1 / 6 := by
  unfold ADMarket.supply
  rw [sum_agent]
  simp [marketD, endowD, apply_ite (Rat.cast : ℚ → ℝ)]

end market


/-! ## Hypotheses bundle and flatness facts -/

structure Hyp (n : ℕ) (C : Fin n → Finset (Fin n)) (p : Good n → ℝ)
    (x : Agent n → Good n → ℝ) : Prop where
  hn : 35 < n
  hopt : ∀ a, (marketD C).IsOptimalBundle p a (x a)
  hclear : ∀ j, |∑ i, x i j - (marketD C).supply j| ≤ ((n : ℝ) ^ 5)⁻¹ * (marketD C).supply j
  hsum : ∑ g, p g = 1
  hpos : ∀ g, 0 < p g
  h2 : ∀ g k, p g ≤ 2 * p k

section flat
variable {n : ℕ} {C : Fin n → Finset (Fin n)} {p : Good n → ℝ} {x : Agent n → Good n → ℝ}

lemma nn (H : Hyp n C p x) (a : Agent n) (g : Good n) : 0 ≤ x a g := (H.hopt a).1 g

lemma fl_s0 (H : Hyp n C p x) (i : Fin n) : x (.setAgent i) .zero ≤ 1 / 2 := by
  have h := (H.hopt (.setAgent i)).2.2.2 .zero (by simp [marketD, utilD, PLUtility.oneSeg])
  norm_num [marketD, utilD, PLUtility.oneSeg, PLUtility.length] at h
  linarith

lemma fl_se (H : Hyp n C p x) (i j : Fin n) (hj : j ∈ C i) : x (.setAgent i) (.elem j) ≤ 1 / 6 := by
  have h := (H.hopt (.setAgent i)).2.2.2 (.elem j) (by simp [marketD, utilD, hj, PLUtility.oneSeg])
  norm_num [marketD, utilD, hj, PLUtility.oneSeg, PLUtility.length] at h
  linarith

lemma fl_se0 (H : Hyp n C p x) (i j : Fin n) (hj : j ∉ C i) : x (.setAgent i) (.elem j) = 0 := by
  have h := (H.hopt (.setAgent i)).2.2.2 (.elem j) (by simp [marketD, utilD, hj, PLUtility.flat])
  norm_num [marketD, utilD, hj, PLUtility.flat, PLUtility.length] at h
  linarith [nn H (.setAgent i) (.elem j)]

lemma fl_ss (H : Hyp n C p x) (i : Fin n) : x (.setAgent i) (.set i) ≤ 1 / 4 := by
  have h := (H.hopt (.setAgent i)).2.2.2 (.set i) (by simp [marketD, utilD, PLUtility.oneSeg])
  norm_num [marketD, utilD, PLUtility.oneSeg, PLUtility.length] at h
  linarith

lemma fl_ss0 (H : Hyp n C p x) (i k : Fin n) (hk : k ≠ i) : x (.setAgent i) (.set k) = 0 := by
  have h := (H.hopt (.setAgent i)).2.2.2 (.set k) (by simp [marketD, utilD, hk, PLUtility.flat])
  norm_num [marketD, utilD, hk, PLUtility.flat, PLUtility.length] at h
  linarith [nn H (.setAgent i) (.set k)]

lemma fl_e0 (H : Hyp n C p x) (j : Fin n) : x (.elemAgent j) .zero ≤ 1 / 12 := by
  have h := (H.hopt (.elemAgent j)).2.2.2 .zero (by simp [marketD, utilD, PLUtility.oneSeg])
  norm_num [marketD, utilD, PLUtility.oneSeg, PLUtility.length] at h
  linarith

lemma fl_es (H : Hyp n C p x) (j k : Fin n) : x (.elemAgent j) (.set k) = 0 := by
  have h := (H.hopt (.elemAgent j)).2.2.2 (.set k) (by simp [marketD, utilD, PLUtility.flat])
  norm_num [marketD, utilD, PLUtility.flat, PLUtility.length] at h
  linarith [nn H (.elemAgent j) (.set k)]

lemma fl_ee (H : Hyp n C p x) (j k : Fin n) : x (.elemAgent j) (.elem k) = 0 := by
  have h := (H.hopt (.elemAgent j)).2.2.2 (.elem k) (by simp [marketD, utilD, PLUtility.flat])
  norm_num [marketD, utilD, PLUtility.flat, PLUtility.length] at h
  linarith [nn H (.elemAgent j) (.elem k)]

lemma fl_xs (H : Hyp n C p x) (k : Fin n) : x .extra (.set k) ≤ 3 / 4 := by
  have h := (H.hopt .extra).2.2.2 (.set k) (by simp [marketD, utilD, PLUtility.oneSeg])
  norm_num [marketD, utilD, PLUtility.oneSeg, PLUtility.length] at h
  linarith

lemma fl_x0 (H : Hyp n C p x) : x .extra .zero = 0 := by
  have h := (H.hopt .extra).2.2.2 .zero (by simp [marketD, utilD, PLUtility.flat])
  norm_num [marketD, utilD, PLUtility.flat, PLUtility.length] at h
  linarith [nn H .extra .zero]

lemma fl_xe (H : Hyp n C p x) (k : Fin n) : x .extra (.elem k) = 0 := by
  have h := (H.hopt .extra).2.2.2 (.elem k) (by simp [marketD, utilD, PLUtility.flat])
  norm_num [marketD, utilD, PLUtility.flat, PLUtility.length] at h
  linarith [nn H .extra (.elem k)]

/-! ## Spending and demand decompositions -/

lemma spend_set (H : Hyp n C p x) (i : Fin n) :
    ∑ g, p g * x (.setAgent i) g = p .zero * x (.setAgent i) .zero +
      ∑ j ∈ C i, p (.elem j) * x (.setAgent i) (.elem j) + p (.set i) * x (.setAgent i) (.set i) := by
  rw [sum_good]
  have hs : ∑ k, p (.set k) * x (.setAgent i) (.set k) = p (.set i) * x (.setAgent i) (.set i) :=
    Fintype.sum_eq_single i (fun k hk => by rw [fl_ss0 H i k hk, mul_zero])
  have he : ∑ j, p (.elem j) * x (.setAgent i) (.elem j) =
      ∑ j ∈ C i, p (.elem j) * x (.setAgent i) (.elem j) :=
    (Finset.sum_subset (Finset.subset_univ _)
      (fun j _ hj => by rw [fl_se0 H i j hj, mul_zero])).symm
  rw [hs, he]; ring

lemma spend_elem (H : Hyp n C p x) (j : Fin n) :
    ∑ g, p g * x (.elemAgent j) g = p .zero * x (.elemAgent j) .zero := by
  rw [sum_good]
  simp [fl_es H, fl_ee H]

lemma dem_zero (H : Hyp n C p x) :
    ∑ a, x a .zero = x .regulator .zero + ∑ i, x (.setAgent i) .zero +
      ∑ j, x (.elemAgent j) .zero := by
  rw [sum_agent, fl_x0 H, add_zero]

lemma dem_set (H : Hyp n C p x) (i : Fin n) :
    ∑ a, x a (.set i) = x .regulator (.set i) + x (.setAgent i) (.set i) + x .extra (.set i) := by
  rw [sum_agent]
  have hs : ∑ k, x (.setAgent k) (.set i) = x (.setAgent i) (.set i) :=
    Fintype.sum_eq_single i (fun k hk => fl_ss0 H k i (Ne.symm hk))
  have he : ∑ j, x (.elemAgent j) (.set i) = 0 := by simp [fl_es H]
  rw [hs, he]; ring

lemma dem_elem (H : Hyp n C p x) (j : Fin n) (i k : Fin n) (hik : i ≠ k) :
    x .regulator (.elem j) + x (.setAgent i) (.elem j) + x (.setAgent k) (.elem j) ≤
      ∑ a, x a (.elem j) := by
  rw [sum_agent]
  have h1 : x (.setAgent i) (.elem j) + x (.setAgent k) (.elem j) ≤
      ∑ l, x (.setAgent l) (.elem j) := by
    rw [← Finset.sum_pair (f := fun l => x (.setAgent l) (.elem j)) hik]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun l _ _ => nn H _ _)
  have h2 : 0 ≤ ∑ l, x (.elemAgent l) (.elem j) := Finset.sum_nonneg (fun l _ => nn H _ _)
  linarith [nn H .extra (.elem j)]

end flat

/-! ## Price facts and the steps of Lemma 8.3 -/

section steps
variable {n : ℕ} {C : Fin n → Finset (Fin n)} {p : Good n → ℝ} {x : Agent n → Good n → ℝ}

lemma m_le (p : Good n → ℝ) (g : Good n) : minPrice p ≤ p g :=
  Finset.inf'_le _ (Finset.mem_univ g)

lemma le_2m (H : Hyp n C p x) (g : Good n) : p g ≤ 2 * minPrice p := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Good n)) p
  have : minPrice p = p k := hk
  rw [this]; exact H.h2 g k

lemma m_pos (H : Hyp n C p x) : 0 < minPrice p := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Good n)) p
  have : minPrice p = p k := hk
  rw [this]; exact H.hpos k

/-- The error scale `e = n⁻⁵ (n³ + n/2)`. -/
lemma e_bound (n : ℕ) (hn : 35 < n) :
    0 ≤ ((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2) ∧
      (n : ℝ) * (((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2)) ≤ 1 / 30 ∧
      ((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2) ≤ 1 / 1000 := by
  have hn' : (36 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) < n := by linarith
  have h5 : (0 : ℝ) < (n : ℝ) ^ 5 := by positivity
  have he0 : 0 ≤ ((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2) := by positivity
  have h4 : (36 : ℝ) * (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
    have : (n : ℝ) ^ 5 = (n : ℝ) * (n : ℝ) ^ 4 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hn' (by positivity)
  have h22 : (15 : ℝ) * (n : ℝ) ^ 2 ≤ 6 * (n : ℝ) ^ 4 := by
    have hsq : (3 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have : (n : ℝ) ^ 4 = (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := by ring
    rw [this]; nlinarith
  have key : (n : ℝ) * (((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2)) ≤ 1 / 30 := by
    rw [show (n : ℝ) * (((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2)) =
      ((n : ℝ) ^ 4 + (n : ℝ) ^ 2 / 2) / (n : ℝ) ^ 5 by field_simp]
    rw [div_le_iff₀ h5]; nlinarith
  refine ⟨he0, key, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hn' he0]

lemma eps_sup (n : ℕ) (hn : 35 < n) (C : Fin n → Finset (Fin n)) (g : Good n) :
    0 ≤ (marketD C).supply g ∧ (marketD C).supply g ≤ (n : ℝ) ^ 3 + n / 2 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  cases g with
  | zero => rw [sup_zero]; exact ⟨by positivity, le_rfl⟩
  | set i => rw [sup_set]; exact ⟨by positivity, by linarith⟩
  | elem j => rw [sup_elem]; exact ⟨by positivity, by linarith⟩

/-- Each clearing error is at most `e`. -/
lemma clr (H : Hyp n C p x) (g : Good n) :
    (marketD C).supply g - ((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2) ≤ ∑ a, x a g ∧
      ∑ a, x a g ≤ (marketD C).supply g + ((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2) := by
  have h := abs_le.mp (H.hclear g)
  obtain ⟨hs0, hs1⟩ := eps_sup n H.hn C g
  have : ((n : ℝ) ^ 5)⁻¹ * (marketD C).supply g ≤ ((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2) :=
    mul_le_mul_of_nonneg_left hs1 (by positivity)
  constructor <;> linarith [h.1, h.2]

/-- Set agents always buy their half unit of good `0`. -/
lemma A0 (H : Hyp n C p x) (i : Fin n) : 1 / 2 ≤ x (.setAgent i) .zero := by
  by_contra hlt
  push Not at hlt
  have hy := H.hopt (.setAgent i)
  have hsp := spend_set H i
  have hinc := inc_set C p i
  have hgain : ∀ δ, 0 ≤ δ → x (.setAgent i) .zero + δ ≤ 1 / 2 →
      1 * δ ≤ ((marketD C).util (.setAgent i) .zero).eval (x (.setAgent i) .zero + δ) -
        ((marketD C).util (.setAgent i) .zero).eval (x (.setAgent i) .zero) := by
    intro δ hδ hc
    rw [ev_s0, ev_s0, mm_up _ _ _ (nn H _ _) hδ hc]; linarith
  rcases lt_or_ge (∑ g, p g * x (.setAgent i) g) ((marketD C).income p (.setAgent i)) with hgap | hge
  · exact unsp_contra _ p _ _ hy .zero (H.hpos _) 1 (1 / 2) one_pos hlt hgap hgain
  · have h02 := H.h2 .zero (.set i)
    have hlt2 : p .zero * x (.setAgent i) .zero < p .zero * (1 / 2) :=
      mul_lt_mul_of_pos_left hlt (H.hpos _)
    by_cases hs : 0 < x (.setAgent i) (.set i)
    · refine exch_contra _ p _ _ hy .zero (.set i) (by simp) (H.hpos _) (H.hpos _) 1 (1 / 9)
        (1 / 2) (x (.setAgent i) (.set i)) hlt hs le_rfl hgain ?_ ?_
      · intro η hη _
        rw [ev_ss, ev_ss]
        have := mm_lip (1 / 4) (x (.setAgent i) (.set i)) η (by norm_num) hη
        linarith
      · linarith [H.hpos (.set i), H.hpos .zero]
    · have hs0 : x (.setAgent i) (.set i) = 0 := le_antisymm (not_lt.mp hs) (nn H _ _)
      have hpos : 0 < ∑ j ∈ C i, p (.elem j) * x (.setAgent i) (.elem j) := by
        rw [hs0] at hsp; linarith
      obtain ⟨j, hj, hjpos⟩ := Finset.exists_lt_of_sum_lt
        (s := C i) (f := fun _ => (0 : ℝ)) (by simpa using hpos)
      have hxj : 0 < x (.setAgent i) (.elem j) := by
        by_contra hc; push Not at hc
        have := mul_nonpos_of_nonneg_of_nonpos (H.hpos (.elem j)).le hc
        have hj' : 0 < p (.elem j) * x (.setAgent i) (.elem j) := hjpos
        linarith
      have h0j := H.h2 .zero (.elem j)
      refine exch_contra _ p _ _ hy .zero (.elem j) (by simp) (H.hpos _) (H.hpos _) 1 (1 / 3)
        (1 / 2) (x (.setAgent i) (.elem j)) hlt hxj le_rfl hgain ?_ ?_
      · intro η hη _
        rw [ev_se C _ i j hj, ev_se C _ i j hj]
        have := mm_lip (1 / 6) (x (.setAgent i) (.elem j)) η (by norm_num) hη
        linarith
      · linarith [H.hpos (.elem j), H.hpos .zero]

/-- Element agents always buy their `1/12` unit of good `0`. -/
lemma B0 (H : Hyp n C p x) (j : Fin n) : 1 / 12 ≤ x (.elemAgent j) .zero := by
  by_contra hlt
  push Not at hlt
  have hy := H.hopt (.elemAgent j)
  have hgap : ∑ g, p g * x (.elemAgent j) g < (marketD C).income p (.elemAgent j) := by
    rw [spend_elem H j, inc_elem]
    have := mul_lt_mul_of_pos_left hlt (H.hpos .zero)
    linarith [H.h2 .zero (.elem j)]
  refine unsp_contra _ p _ _ hy .zero (H.hpos _) 1 (1 / 12) one_pos hlt hgap ?_
  intro δ hδ hc
  rw [ev_e0, ev_e0, mm_up _ _ _ (nn H _ _) hδ hc]; linarith

/-- The regulator buys at least `n³` of every good priced below `2 p_m`. -/
lemma Rge (H : Hyp n C p x) (g : Good n) (hg : p g < 2 * minPrice p) :
    (n : ℝ) ^ 3 ≤ x .regulator g := by
  by_contra hlt
  push Not at hlt
  have hy := H.hopt .regulator
  have hA : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hgain : ∀ δ, 0 ≤ δ → x .regulator g + δ ≤ (n : ℝ) ^ 3 →
      2 * δ ≤ ((marketD C).util .regulator g).eval (x .regulator g + δ) -
        ((marketD C).util .regulator g).eval (x .regulator g) := by
    intro δ hδ hc
    rw [ev_r, ev_r, G_up2 _ _ _ (nn H _ _) hδ hc]
  rcases lt_or_ge (∑ l, p l * x .regulator l) ((marketD C).income p .regulator) with hgap | hge
  · exact unsp_contra _ p _ _ hy g (H.hpos _) 2 ((n : ℝ) ^ 3) two_pos hlt hgap hgain
  · rw [inc_reg] at hge
    have hex : ∃ h, (n : ℝ) ^ 3 < x .regulator h := by
      by_contra hall
      push Not at hall
      have : ∑ l, p l * x .regulator l < ∑ l, p l * (n : ℝ) ^ 3 := by
        apply Finset.sum_lt_sum
        · intro l _; exact mul_le_mul_of_nonneg_left (hall l) (H.hpos l).le
        · exact ⟨g, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt (H.hpos g)⟩
      linarith
    obtain ⟨h, hh⟩ := hex
    have hgh : g ≠ h := by rintro rfl; linarith
    refine exch_contra _ p _ _ hy g h hgh (H.hpos _) (H.hpos _) 2 1 ((n : ℝ) ^ 3)
      (x .regulator h - (n : ℝ) ^ 3) hlt (by linarith) (by linarith) hgain ?_ ?_
    · intro η hη hηr
      rw [ev_r, ev_r, G_tail _ _ _ hA hη (by linarith)]; linarith
    · linarith [m_le p h]

/-- Claim 8.4: `p(0) = 2 p_m`. -/
lemma p0_eq (H : Hyp n C p x) : p .zero = 2 * minPrice p := by
  rcases (le_2m H .zero).lt_or_eq with hlt | heq
  · exfalso
    have hR := Rge H .zero hlt
    have hA : (n : ℝ) * (1 / 2) ≤ ∑ i, x (.setAgent i) .zero := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => A0 H i)
      simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
    have hB : (n : ℝ) * (1 / 12) ≤ ∑ j, x (.elemAgent j) .zero := by
      have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => B0 H j)
      simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
    have hc := (clr H .zero).2
    rw [dem_zero H, sup_zero] at hc
    obtain ⟨-, -, he⟩ := e_bound n H.hn
    have hn' : (36 : ℝ) ≤ n := by exact_mod_cast H.hn
    linarith
  · exact heq

/-- Claim 8.5: every element good is priced below `2 p_m`. -/
lemma elem_lt (H : Hyp n C p x) (j : Fin n) : p (.elem j) < 2 * minPrice p := by
  by_contra hge
  push Not at hge
  have hm := money (marketD C) (((n : ℝ) ^ 5)⁻¹) p (fun g => (H.hpos g).le) x H.hclear
  have hnn : ∀ a, 0 ≤ (marketD C).income p a - ∑ g, p g * x a g :=
    fun a => by linarith [(H.hopt a).2.1]
  have hsingle := Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => hnn a)
    (Finset.mem_univ (Agent.elemAgent j))
  rw [inc_elem, spend_elem H j] at hsingle
  have hps : ∑ g, p g * (marketD C).supply g ≤ (n : ℝ) ^ 3 + n / 2 := by
    calc ∑ g, p g * (marketD C).supply g ≤ ∑ g, p g * ((n : ℝ) ^ 3 + n / 2) :=
          Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (eps_sup n H.hn C g).2 (H.hpos g).le)
      _ = (n : ℝ) ^ 3 + n / 2 := by rw [← Finset.sum_mul, H.hsum, one_mul]
  have hE : ((n : ℝ) ^ 5)⁻¹ * ∑ g, p g * (marketD C).supply g ≤
      ((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2) := mul_le_mul_of_nonneg_left hps (by positivity)
  obtain ⟨he0, hne, -⟩ := e_bound n H.hn
  have hB := fl_e0 H j
  have hp0 := p0_eq H
  have hBp : p .zero * x (.elemAgent j) .zero ≤ p .zero * (1 / 12) :=
    mul_le_mul_of_nonneg_left hB (H.hpos _).le
  -- lower bound on the minimum price
  have hmlow : 1 ≤ 2 * minPrice p * (2 * n + 1) := by
    have hs := H.hsum
    rw [sum_good] at hs
    have h1 : ∑ i, p (.set i) ≤ ∑ _i : Fin n, 2 * minPrice p :=
      Finset.sum_le_sum (fun i _ => le_2m H _)
    have h2 : ∑ j, p (.elem j) ≤ ∑ _j : Fin n, 2 * minPrice p :=
      Finset.sum_le_sum (fun j _ => le_2m H _)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
    have h3 := le_2m H .zero
    nlinarith
  have hmpos := m_pos H
  have hn' : (36 : ℝ) ≤ n := by exact_mod_cast H.hn
  -- unspent money of agent x_j is at least m/6
  have hunsp : minPrice p / 6 ≤ ((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2) := by
    linarith
  -- so 5 n m ≤ 1 < m (4n+2): contradiction
  have h5 : 5 * (n : ℝ) * minPrice p ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hunsp (show (0 : ℝ) ≤ 30 * n by positivity)
    nlinarith
  nlinarith

/-- An agent `C_i` that buys its own good has bought all of its elements. -/
lemma Cp (H : Hyp n C p x) (i : Fin n) (hs : 0 < x (.setAgent i) (.set i)) (j : Fin n)
    (hj : j ∈ C i) : 1 / 6 ≤ x (.setAgent i) (.elem j) := by
  by_contra hlt
  push Not at hlt
  have hy := H.hopt (.setAgent i)
  refine exch_contra _ p _ _ hy (.elem j) (.set i) (by simp) (H.hpos _) (H.hpos _) (1 / 3) (1 / 9)
    (1 / 6) (x (.setAgent i) (.set i)) hlt hs le_rfl ?_ ?_ ?_
  · intro δ hδ hc
    rw [ev_se C _ i j hj, ev_se C _ i j hj]
    have := mm_up (1 / 6) _ _ (nn H _ _) hδ hc
    linarith
  · intro η hη _
    rw [ev_ss, ev_ss]
    have := mm_lip (1 / 4) (x (.setAgent i) (.set i)) η (by norm_num) hη
    linarith
  · linarith [H.h2 (.elem j) (.set i), H.hpos (.elem j)]

lemma mem_cover (i : Fin n) :
    i ∈ coverSet C p ↔ minPrice p + 1 / 6 * ∑ j ∈ C i, p (.elem j) ≤ p (.set i) := by
  simp [coverSet]

/-- An agent `C_i` with `i ∈ S` buys all of its elements. -/
lemma Cpp (H : Hyp n C p x) (i : Fin n) (hi : i ∈ coverSet C p) (j : Fin n) (hj : j ∈ C i) :
    1 / 6 ≤ x (.setAgent i) (.elem j) := by
  by_contra hlt
  push Not at hlt
  have hy := H.hopt (.setAgent i)
  rcases lt_or_ge (∑ g, p g * x (.setAgent i) g) ((marketD C).income p (.setAgent i)) with hgap | hge
  · refine unsp_contra _ p _ _ hy (.elem j) (H.hpos _) (1 / 3) (1 / 6) (by norm_num) hlt hgap ?_
    intro δ hδ hc
    rw [ev_se C _ i j hj, ev_se C _ i j hj]
    have := mm_up (1 / 6) _ _ (nn H _ _) hδ hc
    linarith
  · rw [spend_set H i, inc_set] at hge
    rw [mem_cover] at hi
    have h0 : p .zero * x (.setAgent i) .zero ≤ minPrice p := by
      have := mul_le_mul_of_nonneg_left (fl_s0 H i) (H.hpos .zero).le
      linarith [p0_eq H]
    have hlt2 : ∑ k ∈ C i, p (.elem k) * x (.setAgent i) (.elem k) <
        ∑ k ∈ C i, p (.elem k) * (1 / 6) := by
      apply Finset.sum_lt_sum
      · intro k hk; exact mul_le_mul_of_nonneg_left (fl_se H i k hk) (H.hpos _).le
      · exact ⟨j, hj, mul_lt_mul_of_pos_left hlt (H.hpos _)⟩
    rw [← Finset.sum_mul] at hlt2
    have hpos : 0 < p (.set i) * x (.setAgent i) (.set i) := by linarith
    have hs : 0 < x (.setAgent i) (.set i) := by
      by_contra hc; push Not at hc
      have := mul_nonpos_of_nonneg_of_nonpos (H.hpos (.set i)).le hc
      linarith
    linarith [Cp H i hs j hj]

/-- Claim 8.6 (in the form used): an agent `C_i` with `i ∉ S` does not buy its own good. -/
lemma Cnot (H : Hyp n C p x) (i : Fin n) (hi : i ∉ coverSet C p) :
    x (.setAgent i) (.set i) = 0 := by
  by_contra hne
  have hs : 0 < x (.setAgent i) (.set i) := lt_of_le_of_ne (nn H _ _) (Ne.symm hne)
  apply hi
  rw [mem_cover]
  have hc := (H.hopt (.setAgent i)).2.1
  rw [spend_set H i, inc_set] at hc
  have h0 : minPrice p ≤ p .zero * x (.setAgent i) .zero := by
    have := mul_le_mul_of_nonneg_left (A0 H i) (H.hpos .zero).le
    linarith [p0_eq H]
  have he : ∑ k ∈ C i, p (.elem k) * (1 / 6) ≤ ∑ k ∈ C i, p (.elem k) * x (.setAgent i) (.elem k) :=
    Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (Cp H i hs k hk) (H.hpos _).le)
  rw [← Finset.sum_mul] at he
  have hpos : 0 < p (.set i) * x (.setAgent i) (.set i) := mul_pos (H.hpos _) hs
  linarith

/-- Claim 8.7: the sets of `S` are pairwise disjoint. -/
lemma disj (H : Hyp n C p x) (i : Fin n) (hi : i ∈ coverSet C p) (k : Fin n)
    (hk : k ∈ coverSet C p) (hik : i ≠ k) : Disjoint (C i) (C k) := by
  rw [Finset.disjoint_left]
  intro j hji hjk
  have hR := Rge H (.elem j) (elem_lt H j)
  have h1 := Cpp H i hi j hji
  have h2 := Cpp H k hk j hjk
  have hd := dem_elem H j i k hik
  have hc := (clr H (.elem j)).2
  rw [sup_elem] at hc
  obtain ⟨-, -, he⟩ := e_bound n H.hn
  linarith

/-- Counting: `3 |S| ≥ n`. -/
lemma count (H : Hyp n C p x) (hdiv : 3 ∣ n) : n ≤ 3 * (coverSet C p).card := by
  set S := coverSet C p with hS
  set e := ((n : ℝ) ^ 5)⁻¹ * ((n : ℝ) ^ 3 + n / 2) with he_def
  obtain ⟨he0, hne, he⟩ := e_bound n H.hn
  rw [← he_def] at he0 hne he
  have hn' : (36 : ℝ) ≤ n := by exact_mod_cast H.hn
  have hm := m_pos H
  have hp0 := p0_eq H
  -- regulator budget
  have hbud := (H.hopt .regulator).2.1
  rw [inc_reg, sum_good, sum_good] at hbud
  -- good 0
  have hR0 : (n : ℝ) ^ 3 - n / 12 - e ≤ x .regulator .zero := by
    have hc := (clr H .zero).1
    rw [dem_zero H, sup_zero] at hc
    have hA : ∑ i, x (.setAgent i) .zero ≤ (n : ℝ) * (1 / 2) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => fl_s0 H i)
      simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
    have hB : ∑ j, x (.elemAgent j) .zero ≤ (n : ℝ) * (1 / 12) := by
      have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => fl_e0 H j)
      simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
    linarith
  have hT0 : -(2 * minPrice p) * (n / 12 + e) ≤
      p .zero * x .regulator .zero - p .zero * (n : ℝ) ^ 3 := by
    rw [hp0]
    have := mul_le_mul_of_nonneg_left (show -(n / 12 + e) ≤ x .regulator .zero - (n : ℝ) ^ 3 by linarith)
      (show (0 : ℝ) ≤ 2 * minPrice p by linarith)
    linarith
  -- set goods
  have hTi : ∀ i, (if i ∈ S then -(2 * minPrice p * e) else minPrice p * (1 / 4 - e)) ≤
      p (.set i) * x .regulator (.set i) - p (.set i) * (n : ℝ) ^ 3 := by
    intro i
    have hc := (clr H (.set i)).1
    rw [dem_set H i, sup_set] at hc
    have hX := fl_xs H i
    have hpm := m_le p (.set i)
    have hp2 := le_2m H (.set i)
    split_ifs with hiS
    · have hA := fl_ss H i
      have hr : -e ≤ x .regulator (.set i) - (n : ℝ) ^ 3 := by linarith
      have := mul_le_mul_of_nonneg_left hr (H.hpos (.set i)).le
      have h3 : p (.set i) * e ≤ 2 * minPrice p * e := mul_le_mul_of_nonneg_right hp2 he0
      linarith
    · have hA := Cnot H i hiS
      have hr : 1 / 4 - e ≤ x .regulator (.set i) - (n : ℝ) ^ 3 := by linarith
      have := mul_le_mul hpm hr (by linarith) (H.hpos _).le
      linarith
  have hTj : ∀ j, (0 : ℝ) ≤ p (.elem j) * x .regulator (.elem j) - p (.elem j) * (n : ℝ) ^ 3 := by
    intro j
    have := mul_le_mul_of_nonneg_left (Rge H (.elem j) (elem_lt H j)) (H.hpos (.elem j)).le
    linarith
  have hsumi := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hTi i)
  have hsumj := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hTj j)
  rw [sum_ite_S, Finset.sum_sub_distrib] at hsumi
  rw [Finset.sum_sub_distrib] at hsumj
  simp only [Finset.sum_const_zero] at hsumj
  set s : ℝ := (S.card : ℝ) with hs
  have hsn : s ≤ n := by
    rw [hs]; exact_mod_cast (Finset.card_le_univ S).trans (by simp)
  have hs0 : 0 ≤ s := by positivity
  -- combine: m * [ (n - s)(1/4 - e) - n/6 - 2e - 2 s e ] ≤ 0
  have hcomb : minPrice p * ((n - s) * (1 / 4 - e) - n / 6 - 2 * e - 2 * s * e) ≤ 0 := by
    nlinarith
  have hbr : (n - s) * (1 / 4 - e) - n / 6 - 2 * e - 2 * s * e ≤ 0 := by
    by_contra hpos; push Not at hpos
    have := mul_pos hm hpos; linarith
  have h1 : e * (n + s + 2) ≤ e * (2 * n + 2) := mul_le_mul_of_nonneg_left (by linarith) he0
  have h2 : (n : ℝ) < 3 * s + 3 := by nlinarith
  have h3 : n < 3 * S.card + 3 := by
    have : (n : ℝ) < ((3 * S.card + 3 : ℕ) : ℝ) := by push_cast; rw [← hs]; linarith
    exact_mod_cast this
  omega

end steps

lemma main {n : ℕ} (C : Fin n → Finset (Fin n)) (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n)
    (p : Good n → ℝ) (x : Agent n → Good n → ℝ) (H : Hyp n C p x) : HasExactCover C := by
  classical
  set S := coverSet C p with hS
  refine ⟨S, ?_⟩
  have hcnt := count H hdiv
  have hpd : (S : Set (Fin n)).PairwiseDisjoint C := by
    intro i hi k hk hik
    exact disj H i hi k hk hik
  have hc3 : (S.biUnion C).card = 3 * S.card := by
    rw [Finset.card_biUnion hpd, Finset.sum_congr rfl (fun i _ => hcard i)]
    simp [mul_comm]
  have huniv : S.biUnion C = Finset.univ := by
    apply Finset.eq_univ_of_card
    apply le_antisymm (Finset.card_le_univ _)
    rw [hc3, Fintype.card_fin]; exact hcnt
  intro y
  have hy : y ∈ S.biUnion C := by rw [huniv]; exact Finset.mem_univ y
  obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hy
  refine ⟨i, ⟨hi, hyi⟩, ?_⟩
  rintro k ⟨hk, hyk⟩
  by_contra hne
  exact Finset.disjoint_left.mp (disj H k hk i hi hne) hyk hyi

end Cadc30cb

open PLCMarkets.ExactCover in
theorem solution (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (h : (∃ p : Good n → ℝ, (marketD C).IsEquilibrium p) ∨
      (∃ p : Good n → ℝ, (marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p)) :
    HasExactCover C := by
  have happ : ∃ p : Good n → ℝ, (marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p := by
    rcases h with ⟨p, hs, x, hopt, hclr⟩ | h
    · refine ⟨p, hs, x, hopt, fun j => ?_⟩
      rw [hclr j, sub_self, abs_zero]
      exact mul_nonneg (by positivity) (Cadc30cb.eps_sup n hn C j).1
    · exact h
  obtain ⟨p, hp⟩ := happ
  have h72 := C9e55ab3.l72 n C hcard hdiv hn hcover p hp
  obtain ⟨⟨_, hsum⟩, x, hopt, hclear⟩ := hp
  exact Cadc30cb.main C hcard hdiv p x ⟨hn, hopt, hclear, hsum, h72.1, h72.2⟩
