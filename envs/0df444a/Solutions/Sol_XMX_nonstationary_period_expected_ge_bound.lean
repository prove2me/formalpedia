-- Prove2me | solution 1 for XMX.nonstationary_period_expected_ge_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:32:21.717483+00:00
-- url     : https://prove2.me/submissions/793fef1e-e013-46d0-b62b-18659b9aba03

import Definitions.Def_XMX_NonstationaryInventory
import Theorems.Thm_UnderstandingML_representativeness_le_rademacher
import Theorems.Thm_UnderstandingML_contraction_lemma
import Theorems.Thm_UnderstandingML_dudley_chaining
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

/-! ### Elementary order, metric, and Lipschitz helper lemmas -/

private lemma abs_sup'_sub_sup'_le {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f g : α → ℝ) :
    |s.sup' hs f - s.sup' hs g| ≤ s.sup' hs (fun a => |f a - g a|) := by
  rw [abs_le]
  constructor
  · have h1 : s.sup' hs g ≤ s.sup' hs f + s.sup' hs (fun a => |f a - g a|) := by
      refine Finset.sup'_le hs _ fun a ha => ?_
      have hfg : g a - f a ≤ |f a - g a| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      have hf : f a ≤ s.sup' hs f := Finset.le_sup' f ha
      have hd : |f a - g a| ≤ s.sup' hs (fun b => |f b - g b|) :=
        Finset.le_sup' (fun b => |f b - g b|) ha
      linarith
    linarith
  · have h2 : s.sup' hs f ≤ s.sup' hs g + s.sup' hs (fun a => |f a - g a|) := by
      refine Finset.sup'_le hs _ fun a ha => ?_
      have hfg : f a - g a ≤ |f a - g a| := le_abs_self _
      have hg : g a ≤ s.sup' hs g := Finset.le_sup' g ha
      have hd : |f a - g a| ≤ s.sup' hs (fun b => |f b - g b|) :=
        Finset.le_sup' (fun b => |f b - g b|) ha
      linarith
    linarith

private lemma sup'_le_sum_of_nonneg {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℝ) (hf : ∀ a ∈ s, 0 ≤ f a) :
    s.sup' hs f ≤ ∑ a ∈ s, f a :=
  Finset.sup'_le hs _ fun _a ha => Finset.single_le_sum hf ha

private lemma eucNorm_eq_euclideanSpace_norm {N : ℕ} (v : Fin N → ℝ) :
    UnderstandingML.eucNorm v = ‖(WithLp.equiv 2 (Fin N → ℝ)).symm v‖ := by
  rw [UnderstandingML.eucNorm, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  change (v i) ^ 2 = ‖v i‖ ^ 2
  rw [Real.norm_eq_abs, sq_abs]

private lemma eucNorm_sub_le {N : ℕ} (a b c : Fin N → ℝ) :
    UnderstandingML.eucNorm (a - c) ≤
      UnderstandingML.eucNorm (a - b) + UnderstandingML.eucNorm (b - c) := by
  rw [eucNorm_eq_euclideanSpace_norm, eucNorm_eq_euclideanSpace_norm,
    eucNorm_eq_euclideanSpace_norm]
  have h : (WithLp.equiv 2 (Fin N → ℝ)).symm (a - c) =
      (WithLp.equiv 2 (Fin N → ℝ)).symm (a - b) +
      (WithLp.equiv 2 (Fin N → ℝ)).symm (b - c) := by
    ext i
    change a i - c i = (a i - b i) + (b i - c i)
    ring
  rw [h]
  exact norm_add_le _ _

private lemma cost_lipschitz (h b : ℝ) (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    LipschitzWith 1 (XMX.cost h b) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
  unfold XMX.cost
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · rw [max_eq_right hx, max_eq_right hy,
      max_eq_left (neg_nonneg.mpr hx), max_eq_left (neg_nonneg.mpr hy)]
    have : h * 0 + b * -x - (h * 0 + b * -y) = b * (y - x) := by ring
    rw [this, abs_mul, abs_of_nonneg hb.1, abs_sub_comm]
    exact mul_le_of_le_one_left (abs_nonneg _) hb.2
  · rw [max_eq_right hx, max_eq_left hy,
      max_eq_left (neg_nonneg.mpr hx), max_eq_right (neg_nonpos.mpr hy)]
    rw [abs_of_nonpos (by linarith : x - y ≤ 0), abs_le]
    have h1 : 0 ≤ b * (-x) := mul_nonneg hb.1 (neg_nonneg.mpr hx)
    have h2 : b * (-x) ≤ -x := mul_le_of_le_one_left (neg_nonneg.mpr hx) hb.2
    have h3 : 0 ≤ h * y := mul_nonneg hh.1 hy
    have h4 : h * y ≤ y := mul_le_of_le_one_left hy hh.2
    constructor <;> linarith
  · rw [max_eq_left hx, max_eq_right hy,
      max_eq_right (neg_nonpos.mpr hx), max_eq_left (neg_nonneg.mpr hy)]
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y), abs_le]
    have h1 : 0 ≤ h * x := mul_nonneg hh.1 hx
    have h2 : h * x ≤ x := mul_le_of_le_one_left hx hh.2
    have h3 : 0 ≤ b * (-y) := mul_nonneg hb.1 (neg_nonneg.mpr hy)
    have h4 : b * (-y) ≤ -y := mul_le_of_le_one_left (neg_nonneg.mpr hy) hb.2
    constructor <;> linarith
  · rw [max_eq_left hx, max_eq_left hy,
      max_eq_right (neg_nonpos.mpr hx), max_eq_right (neg_nonpos.mpr hy)]
    have : h * x + b * 0 - (h * y + b * 0) = h * (x - y) := by ring
    rw [this, abs_mul, abs_of_nonneg hh.1]
    exact mul_le_of_le_one_left (abs_nonneg _) hh.2

private lemma phi_lipschitz (h b M c : ℝ) (hM : 0 ≤ M)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    LipschitzWith ⟨M, hM⟩ (fun y => XMX.cost h b (M * y - c)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hlip := (cost_lipschitz h b hh hb).dist_le_mul (M * x - c) (M * y - c)
  rw [NNReal.coe_one, one_mul] at hlip
  calc
    dist (XMX.cost h b (M * x - c)) (XMX.cost h b (M * y - c))
        ≤ dist (M * x - c) (M * y - c) := hlip
    _ = |M * (x - y)| := by
        rw [Real.dist_eq]
        congr 1
        ring
    _ = (⟨M, hM⟩ : NNReal) * dist x y := by
        rw [abs_mul, abs_of_nonneg hM, Real.dist_eq]

/-! ### Continuity and boundedness of inventory and single-period cost -/

private lemma inventory_continuous (T L k : ℕ) (U : ℝ) :
    Continuous (fun z : XMX.Levels T L U × XMX.Demand T L U =>
      XMX.inventory T L U z.1 z.2 k) := by
  dsimp only [XMX.inventory]
  apply Continuous.finset_sup'_apply
  intro j _
  apply Continuous.sub
  · split_ifs with h
    · exact ((continuous_apply (⟨j, h⟩ : Fin (T + L))).comp continuous_fst).subtype_val
    · exact continuous_const
  · apply continuous_finsetSum
    intro r _
    split_ifs with h
    · exact ((continuous_apply (⟨r, h⟩ : Fin (T + L))).comp continuous_snd).subtype_val
    · exact continuous_const

private lemma period_cost_continuous (T L : ℕ) (U h b : ℝ) (k : Fin T) :
    Continuous (fun z : XMX.Levels T L U × XMX.Demand T L U =>
      XMX.cost h b (XMX.inventory T L U z.1 z.2 k - (z.2 ⟨L + k, by omega⟩ : ℝ))) := by
  have hc := (inventory_continuous T L k U).sub
    (((continuous_apply (⟨L + k, by omega⟩ : Fin (T + L))).comp continuous_snd).subtype_val)
  unfold XMX.cost
  exact (continuous_const.mul (hc.max continuous_const)).add
    (continuous_const.mul (hc.neg.max continuous_const))

/-- Normalized cumulative demand from period `j` through `k + L - 1`. -/
private noncomputable def cumDemand (T L : ℕ) (U : ℝ) (k : Fin T)
    (d : XMX.Demand T L U) (j : Fin (k.1 + 1)) : ℝ :=
  (∑ r ∈ Finset.Ico (j : ℕ) (k.1 + L),
    if hr : r < T + L then (d ⟨r, hr⟩ : ℝ) else 0) / (((L : ℝ) + 1) * U)

private lemma cumDemand_nonneg (T L : ℕ) (U : ℝ) (hU : 0 < U) (k : Fin T)
    (d : XMX.Demand T L U) (j : Fin (k.1 + 1)) :
    0 ≤ cumDemand T L U k d j := by
  unfold cumDemand
  apply div_nonneg
  · refine Finset.sum_nonneg fun r _ => ?_
    split_ifs with hr
    · exact (d ⟨r, hr⟩).2.1
    · exact le_rfl
  · positivity

private lemma cumDemand_antitone (T L : ℕ) (U : ℝ) (hU : 0 < U) (k : Fin T)
    (d : XMX.Demand T L U) {j₁ j₂ : Fin (k.1 + 1)} (h : j₁ ≤ j₂) :
    cumDemand T L U k d j₂ ≤ cumDemand T L U k d j₁ := by
  unfold cumDemand
  have hM : 0 < ((L : ℝ) + 1) * U := by positivity
  refine div_le_div_of_nonneg_right ?_ hM.le
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro r hr
    rw [Finset.mem_Ico] at hr ⊢
    exact ⟨le_trans h hr.1, hr.2⟩
  · intro r _ _
    split_ifs with hr
    · exact (d ⟨r, hr⟩).2.1
    · exact le_rfl

private lemma cumDemand_last_le_one (T L : ℕ) (U : ℝ) (hU : 0 < U) (k : Fin T)
    (d : XMX.Demand T L U) :
    cumDemand T L U k d ⟨k.1, Nat.lt_succ_self _⟩ ≤ 1 := by
  unfold cumDemand
  have hM : 0 < ((L : ℝ) + 1) * U := by positivity
  rw [div_le_one hM]
  calc
    ∑ r ∈ Finset.Ico k.1 (k.1 + L),
        (if hr : r < T + L then (d ⟨r, hr⟩ : ℝ) else 0)
        ≤ ∑ _r ∈ Finset.Ico k.1 (k.1 + L), U := by
      refine Finset.sum_le_sum fun r _ => ?_
      split_ifs with hr
      · exact (d ⟨r, hr⟩).2.2
      · exact hU.le
    _ = (L : ℝ) * U := by
      rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]
    _ ≤ ((L : ℝ) + 1) * U := by nlinarith

private lemma normalizedInventory_eq_sup' (T L : ℕ) (U : ℝ) (hU : 0 < U) (k : Fin T)
    (S : XMX.Levels T L U) (d : XMX.Demand T L U) :
    XMX.normalizedInventory T L U k.1 S d =
      (Finset.univ : Finset (Fin (k.1 + 1))).sup' Finset.univ_nonempty
        (fun j => (S ⟨j.1, by omega⟩ : ℝ) / (((L : ℝ) + 1) * U) - cumDemand T L U k d j) := by
  have hM : 0 < ((L : ℝ) + 1) * U := by positivity
  unfold XMX.normalizedInventory XMX.inventory cumDemand
  apply le_antisymm
  · rw [div_le_iff₀ hM]
    refine Finset.sup'_le Finset.univ_nonempty _ fun j hj => ?_
    rw [← div_le_iff₀ hM]
    have hjlt : (j : ℕ) < T + L := by omega
    simp only [dif_pos hjlt]
    rw [sub_div]
    exact Finset.le_sup' (f := fun j : Fin (k.1 + 1) =>
      (S ⟨j.1, by omega⟩ : ℝ) / (((L : ℝ) + 1) * U) -
        (∑ r ∈ Finset.Ico (j : ℕ) (k.1 + L),
          if hr : r < T + L then (d ⟨r, hr⟩ : ℝ) else 0) / (((L : ℝ) + 1) * U)) hj
  · refine Finset.sup'_le Finset.univ_nonempty _ fun j hj => ?_
    rw [le_div_iff₀ hM]
    have hjlt : (j : ℕ) < T + L := by omega
    have hle := Finset.le_sup' (f := fun j : Fin (k.1 + 1) =>
      (if hj' : (j : ℕ) < T + L then (S ⟨j, hj'⟩ : ℝ) else 0) -
        ∑ r ∈ Finset.Ico (j : ℕ) (k.1 + L),
          if hr : r < T + L then (d ⟨r, hr⟩ : ℝ) else 0) hj
    simp only [dif_pos hjlt] at hle
    calc
      ((S ⟨j.1, by omega⟩ : ℝ) / (((L : ℝ) + 1) * U) -
          (∑ r ∈ Finset.Ico (j : ℕ) (k.1 + L),
            if hr : r < T + L then (d ⟨r, hr⟩ : ℝ) else 0) / (((L : ℝ) + 1) * U)) *
          (((L : ℝ) + 1) * U)
          = (S ⟨j.1, by omega⟩ : ℝ) -
              ∑ r ∈ Finset.Ico (j : ℕ) (k.1 + L),
                if hr : r < T + L then (d ⟨r, hr⟩ : ℝ) else 0 := by
        rw [sub_mul, div_mul_cancel₀ _ hM.ne', div_mul_cancel₀ _ hM.ne']
      _ ≤ _ := hle

private lemma normalizedInventory_mem_Icc (T L : ℕ) (U : ℝ) (hU : 0 < U) (k : Fin T)
    (S : XMX.Levels T L U) (d : XMX.Demand T L U) :
    XMX.normalizedInventory T L U k.1 S d ∈ Set.Icc (-1 : ℝ) 1 := by
  have hM : 0 < ((L : ℝ) + 1) * U := by positivity
  rw [normalizedInventory_eq_sup' T L U hU k S d]
  constructor
  · have hlast := Finset.le_sup'
      (f := fun j : Fin (k.1 + 1) =>
        (S ⟨j.1, by omega⟩ : ℝ) / (((L : ℝ) + 1) * U) - cumDemand T L U k d j)
      (Finset.mem_univ (⟨k.1, Nat.lt_succ_self _⟩ : Fin (k.1 + 1)))
    have hs0 : 0 ≤ (S ⟨k.1, by omega⟩ : ℝ) / (((L : ℝ) + 1) * U) :=
      div_nonneg (S ⟨k.1, by omega⟩).2.1 hM.le
    have hd1 := cumDemand_last_le_one T L U hU k d
    linarith
  · refine Finset.sup'_le Finset.univ_nonempty _ fun j _ => ?_
    have hs1 : (S ⟨j.1, by omega⟩ : ℝ) / (((L : ℝ) + 1) * U) ≤ 1 :=
      (div_le_one hM).mpr (S ⟨j.1, by omega⟩).2.2
    have hd0 := cumDemand_nonneg T L U hU k d j
    linarith

private lemma abs_period_cost_le (T L : ℕ) (U h b : ℝ) (hU : 0 < U)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (k : Fin T) (S : XMX.Levels T L U) (d : XMX.Demand T L U) :
    |XMX.cost h b (XMX.inventory T L U S d k.1 - (d ⟨L + k.1, by omega⟩ : ℝ))| ≤
      2 * (((L : ℝ) + 1) * U) := by
  have hM : 0 < ((L : ℝ) + 1) * U := by positivity
  have hni := normalizedInventory_mem_Icc T L U hU k S d
  have hinv_eq : XMX.inventory T L U S d k.1 =
      (((L : ℝ) + 1) * U) * XMX.normalizedInventory T L U k.1 S d := by
    unfold XMX.normalizedInventory
    field_simp [hM.ne']
  have hinv_lo : -(((L : ℝ) + 1) * U) ≤ XMX.inventory T L U S d k.1 := by
    rw [hinv_eq]; nlinarith [hni.1]
  have hinv_hi : XMX.inventory T L U S d k.1 ≤ ((L : ℝ) + 1) * U := by
    rw [hinv_eq]; nlinarith [hni.2]
  have hd0 : 0 ≤ (d ⟨L + k.1, by omega⟩ : ℝ) := (d ⟨L + k.1, by omega⟩).2.1
  have hdU : (d ⟨L + k.1, by omega⟩ : ℝ) ≤ U := (d ⟨L + k.1, by omega⟩).2.2
  have hdM : (d ⟨L + k.1, by omega⟩ : ℝ) ≤ ((L : ℝ) + 1) * U := by nlinarith
  set x := XMX.inventory T L U S d k.1 - (d ⟨L + k.1, by omega⟩ : ℝ)
  have hx_lo : -(2 * (((L : ℝ) + 1) * U)) ≤ x := by linarith
  have hx_hi : x ≤ 2 * (((L : ℝ) + 1) * U) := by linarith
  unfold XMX.cost
  have hc0 : 0 ≤ h * max x 0 + b * max (-x) 0 := by
    apply add_nonneg
    · exact mul_nonneg hh.1 (le_max_right _ _)
    · exact mul_nonneg hb.1 (le_max_right _ _)
  rw [abs_of_nonneg hc0]
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    nlinarith [hb.1, hb.2]
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    nlinarith [hh.1, hh.2]

/-! ### Monotone chain L¹ bucketing and covering-number bound for normalized inventory -/

/-- Any coordinatewise monotone chain in `[-1, 1]^N` admits an empirical `L¹` net of
size at most `B + 1` with radius `2 / B`. -/
private lemma monotone_chain_l1_bucket {N n B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (u : Fin (n + 1) → Fin N → ℝ)
    (hu_range : ∀ q i, u q i ∈ Set.Icc (-1 : ℝ) 1)
    (hu_mono : ∀ q₁ q₂, q₁ ≤ q₂ → ∀ i, u q₁ i ≤ u q₂ i) :
    ∃ (rep : Fin (B + 1) → Fin (n + 1)) (bkt : Fin (n + 1) → Fin (B + 1)),
      ∀ q : Fin (n + 1),
        (∑ i : Fin N, |u q i - u (rep (bkt q)) i|) / (N : ℝ) ≤ 2 / (B : ℝ) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  let Φ : Fin (n + 1) → ℝ := fun q => (∑ i : Fin N, u q i) / (N : ℝ)
  have hΦ_range : ∀ q, Φ q ∈ Set.Icc (-1 : ℝ) 1 := fun q => by
    constructor
    · rw [le_div_iff₀ hNpos]
      calc
        (-1 : ℝ) * N = ∑ _i : Fin N, (-1 : ℝ) := by simp
        _ ≤ ∑ i : Fin N, u q i := Finset.sum_le_sum fun i _ => (hu_range q i).1
    · rw [div_le_iff₀ hNpos]
      calc
        ∑ i : Fin N, u q i ≤ ∑ _i : Fin N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (hu_range q i).2
        _ = 1 * N := by simp
  let scaled : Fin (n + 1) → ℝ := fun q => (B : ℝ) * ((Φ q + 1) / 2)
  have hscaled_nonneg : ∀ q, 0 ≤ scaled q := fun q => by
    dsimp only [scaled]
    have h1 : 0 ≤ Φ q + 1 := by linarith [(hΦ_range q).1]
    positivity
  have hscaled_le : ∀ q, scaled q ≤ (B : ℝ) := fun q => by
    dsimp only [scaled]
    have := (hΦ_range q).2
    nlinarith
  let bkt : Fin (n + 1) → Fin (B + 1) := fun q =>
    ⟨Nat.floor (scaled q), Nat.lt_succ_of_le (Nat.floor_le_of_le (hscaled_le q))⟩
  let rep : Fin (B + 1) → Fin (n + 1) := fun b =>
    if h : ∃ q : Fin (n + 1), bkt q = b then Classical.choose h else ⟨0, Nat.succ_pos _⟩
  refine ⟨rep, bkt, fun q => ?_⟩
  set q' : Fin (n + 1) := rep (bkt q)
  have hq'_bkt : bkt q' = bkt q := by
    have hex : ∃ q₀ : Fin (n + 1), bkt q₀ = bkt q := ⟨q, rfl⟩
    change bkt (if h : ∃ q₀ : Fin (n + 1), bkt q₀ = bkt q then Classical.choose h else _) = bkt q
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have hfloor_eq : Nat.floor (scaled q') = Nat.floor (scaled q) :=
    congrArg Fin.val hq'_bkt
  have hq_lo : (Nat.floor (scaled q) : ℝ) ≤ scaled q :=
    Nat.floor_le (hscaled_nonneg q)
  have hq_hi : scaled q < (Nat.floor (scaled q) : ℝ) + 1 :=
    Nat.lt_floor_add_one (scaled q)
  have hq'_lo : (Nat.floor (scaled q) : ℝ) ≤ scaled q' := by
    rw [← hfloor_eq]; exact Nat.floor_le (hscaled_nonneg q')
  have hq'_hi : scaled q' < (Nat.floor (scaled q) : ℝ) + 1 := by
    rw [← hfloor_eq]; exact Nat.lt_floor_add_one (scaled q')
  have hΦ_diff : |Φ q - Φ q'| ≤ 2 / (B : ℝ) := by
    have hsd : |scaled q - scaled q'| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hmul : scaled q - scaled q' = ((B : ℝ) / 2) * (Φ q - Φ q') := by
      dsimp only [scaled]; ring
    rw [hmul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (B : ℝ) / 2)] at hsd
    rw [le_div_iff₀ hBpos]
    linarith
  rcases le_total q q' with hle | hle
  · have hsum : (∑ i : Fin N, |u q i - u q' i|) / (N : ℝ) = Φ q' - Φ q := by
      have heq : ∀ i : Fin N, |u q i - u q' i| = u q' i - u q i := fun i => by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hu_mono q q' hle i))]
      simp_rw [heq, Finset.sum_sub_distrib, sub_div]
      rfl
    rw [hsum]
    rw [abs_sub_comm] at hΦ_diff
    exact (le_abs_self _).trans hΦ_diff
  · have hsum : (∑ i : Fin N, |u q i - u q' i|) / (N : ℝ) = Φ q - Φ q' := by
      have heq : ∀ i : Fin N, |u q i - u q' i| = u q i - u q' i := fun i =>
        abs_of_nonneg (sub_nonneg.mpr (hu_mono q' q hle i))
      simp_rw [heq, Finset.sum_sub_distrib, sub_div]
      rfl
    rw [hsum]
    exact (le_abs_self _).trans hΦ_diff

/-- Explicit Euclidean covering-number bound for the normalized single-period inventory
evaluation set at scale `√N · 2^{-j}` (`j ≥ 1`). -/
private lemma normalizedInventory_coveringNumber_le
    (T L N : ℕ) (hN : 0 < N) (U : ℝ) (hU : 0 < U)
    (k : Fin T) (data : Fin N → XMX.Demand T L U) (j : ℕ) :
    let A : Set (Fin N → ℝ) :=
      {v | ∃ S : XMX.Levels T L U,
        v = fun i => XMX.normalizedInventory T L U k.1 S (data i)}
    (UnderstandingML.coveringNumber (Real.sqrt N * (2 : ℝ)⁻¹ ^ j) A).toNat ≤
      (64 * 8 ^ j + 1) ^ (2 ^ (j + 1) + 1) := by
  classical
  intro A
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMpos : 0 < ((L : ℝ) + 1) * U := by positivity
  set m : ℕ := 2 ^ (j + 1)
  set B : ℕ := 64 * 8 ^ j
  have hm_pos : 0 < m := by positivity
  have hB_pos : 0 < B := by positivity
  have hm_rpos : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hB_rpos : (0 : ℝ) < B := by exact_mod_cast hB_pos
  set r : ℝ := Real.sqrt N * (2 : ℝ)⁻¹ ^ j
  -- For each quantized level `ℓ ∈ {0, ..., m}` and index `q ∈ {0, ..., k + 1}`
  -- (`q = 0` represents the floor `-1`, `q = t + 1` represents `max(-1, ℓ/m - D_t)`):
  let v : Fin (m + 1) → Fin (k.1 + 2) → Fin N → ℝ := fun ℓ q i =>
    if hq : q.1 = 0 then -1
    else max (-1 : ℝ) ((ℓ.1 : ℝ) / (m : ℝ) - cumDemand T L U k (data i) ⟨q.1 - 1, by omega⟩)
  have hv_range : ∀ ℓ q i, v ℓ q i ∈ Set.Icc (-1 : ℝ) 1 := fun ℓ q i => by
    dsimp only [v]
    split_ifs with hq
    · constructor <;> norm_num
    · constructor
      · exact le_max_left _ _
      · refine max_le (by norm_num) ?_
        have hℓm : (ℓ.1 : ℝ) / (m : ℝ) ≤ 1 := by
          rw [div_le_one hm_rpos]
          exact_mod_cast Nat.lt_succ_iff.mp ℓ.2
        have hd0 := cumDemand_nonneg T L U hU k (data i) ⟨q.1 - 1, by omega⟩
        linarith
  have hv_mono : ∀ ℓ q₁ q₂, q₁ ≤ q₂ → ∀ i, v ℓ q₁ i ≤ v ℓ q₂ i := fun ℓ q₁ q₂ hle i => by
    dsimp only [v]
    split_ifs with h1 h2
    · exact le_rfl
    · exact le_max_left _ _
    · exfalso; omega
    · refine max_le_max_left (-1) ?_
      have hsub : (⟨q₁.1 - 1, by omega⟩ : Fin (k.1 + 1)) ≤ ⟨q₂.1 - 1, by omega⟩ := by
        change q₁.1 - 1 ≤ q₂.1 - 1
        omega
      have hcd := cumDemand_antitone T L U hU k (data i) hsub
      linarith
  -- Apply L¹ bucketing to each level `ℓ`:
  have hbucket : ∀ ℓ : Fin (m + 1),
      ∃ (rep : Fin (B + 1) → Fin (k.1 + 2)) (bkt : Fin (k.1 + 2) → Fin (B + 1)),
        ∀ q : Fin (k.1 + 2),
          (∑ i : Fin N, |v ℓ q i - v ℓ (rep (bkt q)) i|) / (N : ℝ) ≤ 2 / (B : ℝ) := fun ℓ =>
    monotone_chain_l1_bucket hN hB_pos (v ℓ) (hv_range ℓ) (hv_mono ℓ)
  choose rep bkt hbkt using hbucket
  -- Build the finite cover `A'` of size `≤ (B + 1)^(m + 1)`:
  let Ψ : (Fin (m + 1) → Fin (B + 1)) → (Fin N → ℝ) := fun c i =>
    (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty
      (fun ℓ => v ℓ (rep ℓ (c ℓ)) i)
  let A' : Finset (Fin N → ℝ) := Finset.univ.image Ψ
  have hcard : A'.card ≤ (B + 1) ^ (m + 1) := by
    calc
      A'.card ≤ (Finset.univ : Finset (Fin (m + 1) → Fin (B + 1))).card :=
        Finset.card_image_le
      _ = (B + 1) ^ (m + 1) := by
        simp [Finset.card_univ, Fintype.card_fin]
  have hcover : UnderstandingML.IsCover r A A' := by
    rintro a ⟨S, rfl⟩
    let s : Fin (k.1 + 1) → ℝ := fun t =>
      (S ⟨t.1, by omega⟩ : ℝ) / (((L : ℝ) + 1) * U)
    have hs_range : ∀ t, s t ∈ Set.Icc (0 : ℝ) 1 := fun t => by
      dsimp only [s]
      exact ⟨div_nonneg (S ⟨t.1, by omega⟩).2.1 hMpos.le,
        (div_le_one hMpos).mpr (S ⟨t.1, by omega⟩).2.2⟩
    let lvl : Fin (k.1 + 1) → Fin (m + 1) := fun t =>
      ⟨Nat.floor ((m : ℝ) * s t),
        Nat.lt_succ_of_le (Nat.floor_le_of_le (by nlinarith [(hs_range t).2]))⟩
    let sHat : Fin (k.1 + 1) → ℝ := fun t => ((lvl t).1 : ℝ) / (m : ℝ)
    have hs_approx : ∀ t, |s t - sHat t| ≤ 1 / (m : ℝ) := fun t => by
      dsimp only [sHat, lvl]
      have h0 : 0 ≤ (m : ℝ) * s t := mul_nonneg hm_rpos.le (hs_range t).1
      have hlo : (Nat.floor ((m : ℝ) * s t) : ℝ) ≤ (m : ℝ) * s t := Nat.floor_le h0
      have hhi : (m : ℝ) * s t < (Nat.floor ((m : ℝ) * s t) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hlo' : (Nat.floor ((m : ℝ) * s t) : ℝ) / (m : ℝ) ≤ s t :=
        (div_le_iff₀ hm_rpos).mpr (by linarith)
      have hhi' : s t ≤ (Nat.floor ((m : ℝ) * s t) : ℝ) / (m : ℝ) + 1 / (m : ℝ) := by
        rw [← add_div, le_div_iff₀ hm_rpos]
        linarith
      have hinv_pos : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
      rw [abs_le]
      constructor <;> linarith
    let aHat : Fin N → ℝ := fun i =>
      (Finset.univ : Finset (Fin (k.1 + 1))).sup' Finset.univ_nonempty
        (fun t => sHat t - cumDemand T L U k (data i) t)
    -- Step 1: `eucNorm (a - aHat) ≤ r / 2`
    have hnorm1 : UnderstandingML.eucNorm
        ((fun i => XMX.normalizedInventory T L U k.1 S (data i)) - aHat) ≤ r / 2 := by
      have hcoord : ∀ i : Fin N,
          |XMX.normalizedInventory T L U k.1 S (data i) - aHat i| ≤ 1 / (m : ℝ) := fun i => by
        rw [normalizedInventory_eq_sup' T L U hU k S (data i)]
        calc
          |(Finset.univ.sup' Finset.univ_nonempty
              (fun t : Fin (k.1 + 1) => s t - cumDemand T L U k (data i) t)) -
              (Finset.univ.sup' Finset.univ_nonempty
                (fun t : Fin (k.1 + 1) => sHat t - cumDemand T L U k (data i) t))|
              ≤ Finset.univ.sup' Finset.univ_nonempty
                (fun t : Fin (k.1 + 1) =>
                  |(s t - cumDemand T L U k (data i) t) -
                    (sHat t - cumDemand T L U k (data i) t)|) :=
            abs_sup'_sub_sup'_le _ _ _ _
          _ ≤ 1 / (m : ℝ) := by
            refine Finset.sup'_le Finset.univ_nonempty _ fun t _ => ?_
            have : (s t - cumDemand T L U k (data i) t) -
                (sHat t - cumDemand T L U k (data i) t) = s t - sHat t := by ring
            rw [this]
            exact hs_approx t
      rw [UnderstandingML.eucNorm]
      have hr2_nonneg : 0 ≤ r / 2 := by dsimp only [r]; positivity
      have hsq : ∑ i : Fin N,
          (XMX.normalizedInventory T L U k.1 S (data i) - aHat i) ^ 2 ≤ (r / 2) ^ 2 := by
        calc
          ∑ i : Fin N, (XMX.normalizedInventory T L U k.1 S (data i) - aHat i) ^ 2
              ≤ ∑ _i : Fin N, (1 / (m : ℝ)) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [← sq_abs]
            exact sq_le_sq' (by linarith [abs_nonneg (XMX.normalizedInventory T L U k.1 S (data i) - aHat i), hcoord i]) (hcoord i)
          _ = (N : ℝ) * (1 / (m : ℝ)) ^ 2 := by simp
          _ = (r / 2) ^ 2 := by
            dsimp only [r, m]
            rw [mul_div_assoc, mul_pow, Real.sq_sqrt hNpos.le]
            push_cast
            rw [pow_succ, inv_pow, one_div]
            ring
      calc
        Real.sqrt (∑ i : Fin N,
            (XMX.normalizedInventory T L U k.1 S (data i) - aHat i) ^ 2)
            ≤ Real.sqrt ((r / 2) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = r / 2 := Real.sqrt_sq hr2_nonneg
    -- Step 2: Collapse `aHat` to one index `qOpt ℓ` per level `ℓ ∈ {0, ..., m}`
    let E : Fin (m + 1) → Finset (Fin (k.1 + 1)) := fun ℓ =>
      Finset.univ.filter (fun t => lvl t = ℓ)
    let qOpt : Fin (m + 1) → Fin (k.1 + 2) := fun ℓ =>
      if hE : (E ℓ).Nonempty then ⟨((E ℓ).max' hE).1 + 1, by omega⟩ else ⟨0, Nat.succ_pos _⟩
    have haHat_eq : ∀ i : Fin N,
        aHat i = (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty
          (fun ℓ => v ℓ (qOpt ℓ) i) := fun i => by
      have haHat_ge : -1 ≤ aHat i := by
        have hlast := Finset.le_sup'
          (f := fun t : Fin (k.1 + 1) => sHat t - cumDemand T L U k (data i) t)
          (Finset.mem_univ (⟨k.1, Nat.lt_succ_self _⟩ : Fin (k.1 + 1)))
        have hs0 : 0 ≤ sHat ⟨k.1, Nat.lt_succ_self _⟩ := by
          dsimp only [sHat]; positivity
        have hd1 := cumDemand_last_le_one T L U hU k (data i)
        linarith
      apply le_antisymm
      · refine Finset.sup'_le Finset.univ_nonempty _ fun t _ => ?_
        set ℓ := lvl t
        have htE : t ∈ E ℓ := Finset.mem_filter.mpr ⟨Finset.mem_univ t, rfl⟩
        have hE : (E ℓ).Nonempty := ⟨t, htE⟩
        set tMax := (E ℓ).max' hE
        have ht_le : t ≤ tMax := Finset.le_max' (E ℓ) t htE
        have hcd := cumDemand_antitone T L U hU k (data i) ht_le
        have hv_eq : v ℓ (qOpt ℓ) i =
            max (-1 : ℝ) ((ℓ.1 : ℝ) / (m : ℝ) - cumDemand T L U k (data i) tMax) := by
          dsimp only [v, qOpt]
          rw [dif_pos hE]
          have hne : tMax.1 + 1 ≠ 0 := Nat.succ_ne_zero _
          rw [dif_neg hne]
          congr 2
        have hsup := Finset.le_sup' (f := fun ℓ' : Fin (m + 1) => v ℓ' (qOpt ℓ') i)
          (Finset.mem_univ ℓ)
        calc
          sHat t - cumDemand T L U k (data i) t
              = (ℓ.1 : ℝ) / (m : ℝ) - cumDemand T L U k (data i) t := rfl
          _ ≤ (ℓ.1 : ℝ) / (m : ℝ) - cumDemand T L U k (data i) tMax := by linarith
          _ ≤ max (-1 : ℝ) ((ℓ.1 : ℝ) / (m : ℝ) - cumDemand T L U k (data i) tMax) :=
            le_max_right _ _
          _ = v ℓ (qOpt ℓ) i := hv_eq.symm
          _ ≤ _ := hsup
      · refine Finset.sup'_le Finset.univ_nonempty _ fun ℓ _ => ?_
        by_cases hE : (E ℓ).Nonempty
        · dsimp only [v, qOpt]
          rw [dif_pos hE, dif_neg (Nat.succ_ne_zero _)]
          set tMax := (E ℓ).max' hE
          have htMax_mem : tMax ∈ E ℓ := Finset.max'_mem (E ℓ) hE
          have hlvl_tMax : lvl tMax = ℓ := (Finset.mem_filter.mp htMax_mem).2
          have ht_eq : (⟨tMax.1 + 1 - 1, by omega⟩ : Fin (k.1 + 1)) = tMax := by
            ext; simp
          rw [ht_eq]
          refine max_le haHat_ge ?_
          have hsup := Finset.le_sup'
            (f := fun t : Fin (k.1 + 1) => sHat t - cumDemand T L U k (data i) t)
            (Finset.mem_univ tMax)
          have hs_eq : (ℓ.1 : ℝ) / (m : ℝ) = sHat tMax := by
            dsimp only [sHat]; rw [hlvl_tMax]
          rw [hs_eq]
          exact hsup
        · dsimp only [v, qOpt]
          rw [dif_neg hE, dif_pos rfl]
          exact haHat_ge
    -- Step 3: Approximate each `qOpt ℓ` by its bucket representative `c ℓ = bkt ℓ (qOpt ℓ)`
    let c : Fin (m + 1) → Fin (B + 1) := fun ℓ => bkt ℓ (qOpt ℓ)
    refine ⟨Ψ c, Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩, ?_⟩
    have hnorm2 : UnderstandingML.eucNorm (aHat - Ψ c) ≤ r / 2 := by
      have haHat_range : ∀ i, aHat i ∈ Set.Icc (-1 : ℝ) 1 := fun i => by
        rw [haHat_eq i]
        exact ⟨le_trans (hv_range ⟨0, Nat.succ_pos _⟩ _ i).1
            (Finset.le_sup' (f := fun ℓ => v ℓ (qOpt ℓ) i) (Finset.mem_univ _)),
          Finset.sup'_le Finset.univ_nonempty _ fun ℓ _ => (hv_range ℓ (qOpt ℓ) i).2⟩
      have hΨ_range : ∀ i, Ψ c i ∈ Set.Icc (-1 : ℝ) 1 := fun i => by
        dsimp only [Ψ]
        exact ⟨le_trans (hv_range ⟨0, Nat.succ_pos _⟩ _ i).1
            (Finset.le_sup' (f := fun ℓ => v ℓ (rep ℓ (c ℓ)) i) (Finset.mem_univ _)),
          Finset.sup'_le Finset.univ_nonempty _ fun ℓ _ => (hv_range ℓ (rep ℓ (c ℓ)) i).2⟩
      have hsq_sum : ∑ i : Fin N, (aHat i - Ψ c i) ^ 2 ≤ (r / 2) ^ 2 := by
        have hstep1 : ∑ i : Fin N, (aHat i - Ψ c i) ^ 2 ≤
            2 * ∑ ℓ : Fin (m + 1), ∑ i : Fin N,
              |v ℓ (qOpt ℓ) i - v ℓ (rep ℓ (c ℓ)) i| := by
          calc
            ∑ i : Fin N, (aHat i - Ψ c i) ^ 2
                ≤ ∑ i : Fin N, 2 * |aHat i - Ψ c i| := by
              refine Finset.sum_le_sum fun i _ => ?_
              have habs : |aHat i - Ψ c i| ≤ 2 := by
                rw [abs_le]
                constructor <;> linarith [(haHat_range i).1, (haHat_range i).2,
                  (hΨ_range i).1, (hΨ_range i).2]
              rw [← sq_abs]
              nlinarith [abs_nonneg (aHat i - Ψ c i)]
            _ ≤ ∑ i : Fin N, 2 * ∑ ℓ : Fin (m + 1),
                  |v ℓ (qOpt ℓ) i - v ℓ (rep ℓ (c ℓ)) i| := by
              refine Finset.sum_le_sum fun i _ => ?_
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              rw [haHat_eq i]
              dsimp only [Ψ]
              exact (abs_sup'_sub_sup'_le Finset.univ Finset.univ_nonempty _ _).trans
                (sup'_le_sum_of_nonneg Finset.univ Finset.univ_nonempty _
                  (fun ℓ _ => abs_nonneg _))
            _ = 2 * ∑ i : Fin N, ∑ ℓ : Fin (m + 1),
                  |v ℓ (qOpt ℓ) i - v ℓ (rep ℓ (c ℓ)) i| := by
              rw [← Finset.mul_sum]
            _ = 2 * ∑ ℓ : Fin (m + 1), ∑ i : Fin N,
                  |v ℓ (qOpt ℓ) i - v ℓ (rep ℓ (c ℓ)) i| := by
              rw [Finset.sum_comm]
        have hstep2 : ∑ ℓ : Fin (m + 1), ∑ i : Fin N,
            |v ℓ (qOpt ℓ) i - v ℓ (rep ℓ (c ℓ)) i| ≤
            ((m + 1 : ℕ) : ℝ) * ((N : ℝ) * (2 / (B : ℝ))) := by
          calc
            ∑ ℓ : Fin (m + 1), ∑ i : Fin N,
                |v ℓ (qOpt ℓ) i - v ℓ (rep ℓ (c ℓ)) i|
                ≤ ∑ _ℓ : Fin (m + 1), (N : ℝ) * (2 / (B : ℝ)) := by
              refine Finset.sum_le_sum fun ℓ _ => ?_
              have h := hbkt ℓ (qOpt ℓ)
              rw [div_le_iff₀ hNpos] at h
              linarith
            _ = ((m + 1 : ℕ) : ℝ) * ((N : ℝ) * (2 / (B : ℝ))) := by
              simp [nsmul_eq_mul]
        have hstep3 : 2 * (((m + 1 : ℕ) : ℝ) * ((N : ℝ) * (2 / (B : ℝ)))) ≤ (r / 2) ^ 2 := by
          dsimp only [r, m, B]
          rw [mul_div_assoc, mul_pow, Real.sq_sqrt hNpos.le]
          push_cast
          have h1 : (2 : ℝ) ^ (j + 1) + 1 ≤ 4 * (2 : ℝ) ^ j := by
            have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
            rw [pow_succ]
            linarith
          have h2 : (8 : ℝ) ^ j = (2 : ℝ) ^ j * (4 : ℝ) ^ j := by
            rw [← mul_pow]; norm_num
          have h4pos : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
          have h2pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
          have h8pos : (0 : ℝ) < 64 * (8 : ℝ) ^ j := by positivity
          have hsimp : ((2 : ℝ)⁻¹ ^ j / 2) ^ 2 = 1 / (4 * (4 : ℝ) ^ j) := by
            rw [div_pow, inv_pow, one_div, inv_pow, ← pow_mul, mul_comm j 2, pow_mul]
            norm_num
            ring
          rw [hsimp]
          have hkey : 2 * (((2 : ℝ) ^ (j + 1) + 1) * ((N : ℝ) * (2 / (64 * (8 : ℝ) ^ j)))) ≤
              (N : ℝ) * (1 / (4 * (4 : ℝ) ^ j)) := by
            rw [h2]
            have hfrac : 2 * ((4 * (2 : ℝ) ^ j) * ((N : ℝ) * (2 / (64 * ((2 : ℝ) ^ j * (4 : ℝ) ^ j))))) =
                (N : ℝ) * (1 / (4 * (4 : ℝ) ^ j)) := by
              field_simp [h2pos.ne', h4pos.ne']
              ring
            calc
              2 * (((2 : ℝ) ^ (j + 1) + 1) * ((N : ℝ) * (2 / (64 * ((2 : ℝ) ^ j * (4 : ℝ) ^ j)))))
                  ≤ 2 * ((4 * (2 : ℝ) ^ j) * ((N : ℝ) * (2 / (64 * ((2 : ℝ) ^ j * (4 : ℝ) ^ j))))) := by
                gcongr
              _ = (N : ℝ) * (1 / (4 * (4 : ℝ) ^ j)) := hfrac
          exact hkey
        exact hstep1.trans ((mul_le_mul_of_nonneg_left hstep2 (by norm_num)).trans hstep3)
      rw [UnderstandingML.eucNorm]
      have hr2_nonneg : 0 ≤ r / 2 := by dsimp only [r]; positivity
      calc
        Real.sqrt (∑ i : Fin N, (aHat i - Ψ c i) ^ 2)
            ≤ Real.sqrt ((r / 2) ^ 2) := Real.sqrt_le_sqrt hsq_sum
        _ = r / 2 := Real.sqrt_sq hr2_nonneg
    calc
      UnderstandingML.eucNorm
          ((fun i => XMX.normalizedInventory T L U k.1 S (data i)) - Ψ c)
          ≤ UnderstandingML.eucNorm
              ((fun i => XMX.normalizedInventory T L U k.1 S (data i)) - aHat) +
            UnderstandingML.eucNorm (aHat - Ψ c) := eucNorm_sub_le _ _ _
      _ ≤ r / 2 + r / 2 := add_le_add hnorm1 hnorm2
      _ = r := by ring
  have hcov_le : UnderstandingML.coveringNumber r A ≤ (((B + 1) ^ (m + 1) : ℕ) : ENat) := by
    unfold UnderstandingML.coveringNumber
    refine le_trans (iInf₂_le A' hcover) ?_
    exact_mod_cast hcard
  exact ENat.toNat_le_of_le_natCast hcov_le

/-! ### Dudley chaining bound for the normalized inventory class -/

private lemma rademacher_normalizedInventory_le
    (T L N : ℕ) (hN : 0 < N) (U : ℝ) (hU : 0 < U)
    (k : Fin T) (data : Fin N → XMX.Demand T L U) :
    let A : Set (Fin N → ℝ) :=
      {v | ∃ S : XMX.Levels T L U,
        v = fun i => XMX.normalizedInventory T L U k.1 S (data i)}
    UnderstandingML.rademacher A ≤ 361 / Real.sqrt N := by
  intro A
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hMpos : 0 < ((L : ℝ) + 1) * U := by positivity
  let S0 : XMX.Levels T L U := fun _ => ⟨0, le_rfl, hMpos.le⟩
  have hA_nonempty : A.Nonempty := ⟨fun i => XMX.normalizedInventory T L U k.1 S0 (data i), S0, rfl⟩
  have hc : ∀ a ∈ A, UnderstandingML.eucNorm (a - 0) ≤ Real.sqrt N := by
    rintro a ⟨S, rfl⟩
    rw [sub_zero, UnderstandingML.eucNorm]
    refine Real.sqrt_le_sqrt ?_
    calc
      ∑ i : Fin N, (XMX.normalizedInventory T L U k.1 S (data i)) ^ 2
          ≤ ∑ _i : Fin N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := normalizedInventory_mem_Icc T L U hU k S (data i)
        nlinarith [h.1, h.2]
      _ = (N : ℝ) := by simp
  have hdudley := UnderstandingML.dudley_chaining hN A hA_nonempty (Real.sqrt N) 0 hc N hN
  -- Bound the tail term `√N · 2^{-N} / √N ≤ 1 / √N`:
  have htail : Real.sqrt N * (2 : ℝ)⁻¹ ^ N / Real.sqrt N ≤ 1 / Real.sqrt N := by
    rw [mul_div_cancel_left₀ _ hsqrt_pos.ne', inv_pow, one_div]
    refine inv_anti₀ hsqrt_pos ?_
    have h1 : Real.sqrt N ≤ (N : ℝ) := by
      rw [Real.sqrt_le_iff]
      exact ⟨hNpos.le, by nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast hN]⟩
    have h2 : (N : ℝ) ≤ (2 : ℝ) ^ N := by
      exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
    exact h1.trans h2
  -- Bound each summand in Dudley's chaining sum:
  have hterm : ∀ j ∈ Finset.Icc 1 N,
      (2 : ℝ)⁻¹ ^ j *
        Real.sqrt (Real.log ((UnderstandingML.coveringNumber
          (Real.sqrt N * (2 : ℝ)⁻¹ ^ j) A).toNat : ℝ)) ≤
        12 * (4 / 5 : ℝ) ^ j := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hcov := normalizedInventory_coveringNumber_le T L N hN U hU k data j
    set n := (UnderstandingML.coveringNumber (Real.sqrt N * (2 : ℝ)⁻¹ ^ j) A).toNat
    have hlog_le : Real.log (n : ℝ) ≤ 30 * (j : ℝ) * (2 : ℝ) ^ j := by
      have hcard_nat : n ≤ (64 * 8 ^ j + 1) ^ (2 ^ (j + 1) + 1) := hcov
      have hbase_nat : 64 * 8 ^ j + 1 ≤ 2 ^ (10 * j) := by
        have h64 : 64 * 8 ^ j = 2 ^ (3 * j + 6) := by
          have : (64 : ℕ) = 2 ^ 6 := by norm_num
          have h8 : (8 : ℕ) ^ j = 2 ^ (3 * j) := by
            rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
          rw [this, h8, ← pow_add, add_comm]
        have hstep : 2 ^ (3 * j + 6) + 1 ≤ 2 ^ (3 * j + 7) := by
          have hpow7 : 2 ^ (3 * j + 7) = 2 ^ (3 * j + 6) * 2 := by
            rw [show 3 * j + 7 = (3 * j + 6) + 1 by omega, pow_succ]
          have hge1 : 1 ≤ 2 ^ (3 * j + 6) := Nat.one_le_two_pow
          omega
        have hexp : 3 * j + 7 ≤ 10 * j := by omega
        calc
          64 * 8 ^ j + 1 = 2 ^ (3 * j + 6) + 1 := by rw [h64]
          _ ≤ 2 ^ (3 * j + 7) := hstep
          _ ≤ 2 ^ (10 * j) := Nat.pow_le_pow_right (by norm_num) hexp
      have hexp_nat : 2 ^ (j + 1) + 1 ≤ 3 * 2 ^ j := by
        rw [pow_succ]
        have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        omega
      have hn_le : n ≤ (2 ^ (10 * j)) ^ (3 * 2 ^ j) :=
        hcard_nat.trans
          ((Nat.pow_le_pow_left hbase_nat _).trans
            (Nat.pow_le_pow_right (Nat.one_le_two_pow) hexp_nat))
      by_cases hn0 : n = 0
      · rw [hn0, Nat.cast_zero, Real.log_zero]
        positivity
      · have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have hle_real : (n : ℝ) ≤ ((2 : ℝ) ^ (10 * j)) ^ (3 * 2 ^ j) := by
          exact_mod_cast hn_le
        calc
          Real.log (n : ℝ) ≤ Real.log (((2 : ℝ) ^ (10 * j)) ^ (3 * 2 ^ j)) :=
            Real.log_le_log hn_pos hle_real
          _ = ((3 * 2 ^ j : ℕ) : ℝ) * (((10 * j : ℕ) : ℝ) * Real.log 2) := by
            rw [Real.log_pow, Real.log_pow]
          _ ≤ ((3 * 2 ^ j : ℕ) : ℝ) * (((10 * j : ℕ) : ℝ) * 1) := by
            have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
              have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
              linarith
            gcongr
          _ = 30 * (j : ℝ) * (2 : ℝ) ^ j := by
            push_cast
            ring
    have hbern : (j : ℝ) ≤ 4 * (32 / 25 : ℝ) ^ j := by
      have h1 : (1 : ℝ) + (j : ℝ) * (7 / 25 : ℝ) ≤ (1 + 7 / 25 : ℝ) ^ j :=
        one_add_mul_le_pow (by norm_num) j
      have h2 : (1 + 7 / 25 : ℝ) = 32 / 25 := by norm_num
      rw [h2] at h1
      linarith
    have hsq_bound : 30 * (j : ℝ) * (2 : ℝ) ^ j ≤ (12 * (8 / 5 : ℝ) ^ j) ^ 2 := by
      have h1 : 30 * (j : ℝ) * (2 : ℝ) ^ j ≤ 30 * (4 * (32 / 25 : ℝ) ^ j) * (2 : ℝ) ^ j := by
        gcongr
      have h2 : 30 * (4 * (32 / 25 : ℝ) ^ j) * (2 : ℝ) ^ j = 120 * ((8 / 5 : ℝ) ^ j) ^ 2 := by
        rw [← pow_mul, mul_comm j 2, pow_mul]
        have hpow : (32 / 25 : ℝ) ^ j * (2 : ℝ) ^ j = ((8 / 5 : ℝ) ^ 2) ^ j := by
          rw [← mul_pow]; norm_num
        linarith
      have h3 : 120 * ((8 / 5 : ℝ) ^ j) ^ 2 ≤ 144 * ((8 / 5 : ℝ) ^ j) ^ 2 := by
        have : (0 : ℝ) ≤ ((8 / 5 : ℝ) ^ j) ^ 2 := sq_nonneg _
        linarith
      have h4 : 144 * ((8 / 5 : ℝ) ^ j) ^ 2 = (12 * (8 / 5 : ℝ) ^ j) ^ 2 := by ring
      linarith
    have hsqrt_le : Real.sqrt (Real.log (n : ℝ)) ≤ 12 * (8 / 5 : ℝ) ^ j := by
      calc
        Real.sqrt (Real.log (n : ℝ))
            ≤ Real.sqrt ((12 * (8 / 5 : ℝ) ^ j) ^ 2) :=
          Real.sqrt_le_sqrt (hlog_le.trans hsq_bound)
        _ = 12 * (8 / 5 : ℝ) ^ j := Real.sqrt_sq (by positivity)
    calc
      (2 : ℝ)⁻¹ ^ j * Real.sqrt (Real.log (n : ℝ))
          ≤ (2 : ℝ)⁻¹ ^ j * (12 * (8 / 5 : ℝ) ^ j) := by
        exact mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
      _ = 12 * (4 / 5 : ℝ) ^ j := by
        have : (2 : ℝ)⁻¹ ^ j * (8 / 5 : ℝ) ^ j = (4 / 5 : ℝ) ^ j := by
          rw [← mul_pow]; norm_num
        linarith
  -- Sum the geometric series `∑_{j=1}^N 12 · (4/5)^j ≤ 60`:
  have hsum_le : ∑ j ∈ Finset.Icc 1 N,
      (2 : ℝ)⁻¹ ^ j *
        Real.sqrt (Real.log ((UnderstandingML.coveringNumber
          (Real.sqrt N * (2 : ℝ)⁻¹ ^ j) A).toNat : ℝ)) ≤ 60 := by
    calc
      ∑ j ∈ Finset.Icc 1 N,
          (2 : ℝ)⁻¹ ^ j *
            Real.sqrt (Real.log ((UnderstandingML.coveringNumber
              (Real.sqrt N * (2 : ℝ)⁻¹ ^ j) A).toNat : ℝ))
          ≤ ∑ j ∈ Finset.Icc 1 N, 12 * (4 / 5 : ℝ) ^ j := Finset.sum_le_sum hterm
      _ ≤ ∑ j ∈ Finset.range (N + 1), 12 * (4 / 5 : ℝ) ^ j := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro j hj
        rw [Finset.mem_Icc] at hj
        rw [Finset.mem_range]
        omega
      _ = 12 * ∑ j ∈ Finset.range (N + 1), (4 / 5 : ℝ) ^ j := by rw [← Finset.mul_sum]
      _ = 12 * (((4 / 5 : ℝ) ^ (N + 1) - 1) / ((4 / 5 : ℝ) - 1)) := by
        rw [geom_sum_eq (by norm_num)]
      _ ≤ 60 := by
        have hpos : (0 : ℝ) ≤ (4 / 5 : ℝ) ^ (N + 1) := by positivity
        have heq : 12 * (((4 / 5 : ℝ) ^ (N + 1) - 1) / ((4 / 5 : ℝ) - 1)) =
            60 * (1 - (4 / 5 : ℝ) ^ (N + 1)) := by ring
        rw [heq]
        linarith
  have h6 : 6 * Real.sqrt N / (N : ℝ) * 60 = 360 / Real.sqrt N := by
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hNpos.le
    field_simp [hsqrt_pos.ne', hNpos.ne']
    linarith [hsq]
  calc
    UnderstandingML.rademacher A
        ≤ Real.sqrt N * (2 : ℝ)⁻¹ ^ N / Real.sqrt N +
          6 * Real.sqrt N / (N : ℝ) *
            ∑ j ∈ Finset.Icc 1 N,
              (2 : ℝ)⁻¹ ^ j *
                Real.sqrt (Real.log ((UnderstandingML.coveringNumber
                  (Real.sqrt N * (2 : ℝ)⁻¹ ^ j) A).toNat : ℝ)) := hdudley
    _ ≤ 1 / Real.sqrt N + 6 * Real.sqrt N / (N : ℝ) * 60 := by
      gcongr
    _ = 361 / Real.sqrt N := by
      rw [h6]
      ring

/-! ### Single-period cost, measurability, contraction, and main theorem -/

private noncomputable def periodCost (T L : ℕ) (U h b : ℝ) (k : Fin T)
    (S : XMX.Levels T L U) (d : XMX.Demand T L U) : ℝ :=
  XMX.cost h b (XMX.inventory T L U S d k.1 - (d ⟨L + k.1, by omega⟩ : ℝ))

private lemma periodCost_rademacher_pointwise
    (T L N : ℕ) (hN : 0 < N)
    (U h b : ℝ) (hU : 0 < U) (hh : h ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (k : Fin T) (data : Fin N → XMX.Demand T L U) :
    UnderstandingML.rademacher
        (UnderstandingML.evalSet
          (UnderstandingML.lossClass (periodCost T L U h b k) Set.univ) data) ≤
      (((L : ℝ) + 1) * U) * (361 / Real.sqrt N) := by
  have hMpos : 0 < ((L : ℝ) + 1) * U := by positivity
  set M : ℝ := ((L : ℝ) + 1) * U
  let S0 : XMX.Levels T L U := fun _ => ⟨0, le_rfl, hMpos.le⟩
  let A : Set (Fin N → ℝ) :=
    {v | ∃ S : XMX.Levels T L U,
      v = fun i => XMX.normalizedInventory T L U k.1 S (data i)}
  let φ : Fin N → ℝ → ℝ := fun i y =>
    XMX.cost h b (M * y - (data i ⟨L + k.1, by omega⟩ : ℝ))
  have hA_nonempty : A.Nonempty :=
    ⟨fun i => XMX.normalizedInventory T L U k.1 S0 (data i), S0, rfl⟩
  have hA_bdd : Bornology.IsBounded A := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, ?_⟩
    rintro v ⟨S, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    rw [Real.norm_eq_abs, abs_le]
    exact normalizedInventory_mem_Icc T L U hU k S (data i)
  have hφ_lip : ∀ i : Fin N, LipschitzWith ⟨M, hMpos.le⟩ (φ i) := fun i =>
    phi_lipschitz h b M _ hMpos.le hh hb
  have himg : UnderstandingML.evalSet
      (UnderstandingML.lossClass (periodCost T L U h b k) Set.univ) data =
      (fun a i => φ i (a i)) '' A := by
    ext v
    simp only [UnderstandingML.evalSet, UnderstandingML.lossClass, Set.mem_ofPred_eq,
      Set.mem_image, A, Set.mem_univ, true_and]
    constructor
    · rintro ⟨f, ⟨S, rfl⟩, rfl⟩
      refine ⟨fun i => XMX.normalizedInventory T L U k.1 S (data i), ⟨S, rfl⟩, ?_⟩
      ext i
      dsimp only [φ, periodCost, XMX.normalizedInventory]
      rw [mul_div_cancel₀ _ hMpos.ne']
    · rintro ⟨a, ⟨S, rfl⟩, rfl⟩
      refine ⟨periodCost T L U h b k S, ⟨S, rfl⟩, ?_⟩
      ext i
      dsimp only [φ, periodCost, XMX.normalizedInventory]
      rw [mul_div_cancel₀ _ hMpos.ne']
  rw [himg]
  have hcontr := UnderstandingML.contraction_lemma A hA_nonempty hA_bdd ⟨M, hMpos.le⟩ φ hφ_lip
  have hdud := rademacher_normalizedInventory_le T L N hN U hU k data
  calc
    UnderstandingML.rademacher ((fun a i => φ i (a i)) '' A)
        ≤ (⟨M, hMpos.le⟩ : NNReal) * UnderstandingML.rademacher A := hcontr
    _ ≤ M * (361 / Real.sqrt N) := mul_le_mul_of_nonneg_left hdud hMpos.le

private lemma rademacher_sup_eq_levels
    {P X : Type*} [Nonempty P] {N : ℕ} (ℓ : P → X → ℝ) (B : ℝ)
    (hB : ∀ p x, |ℓ p x| ≤ B) (data : Fin N → X) (σ : Fin N → Bool) :
    (⨆ a : UnderstandingML.evalSet (UnderstandingML.lossClass ℓ Set.univ) data,
        ∑ i : Fin N, UnderstandingML.signVec σ i * (a : Fin N → ℝ) i) =
    (⨆ p : P, ∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)) := by
  have hsum_abs : ∀ p : P,
      |∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)| ≤ (N : ℝ) * B := fun p => by
    calc
      |∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)|
          ≤ ∑ i : Fin N, |UnderstandingML.signVec σ i * ℓ p (data i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, B := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        have hs : |UnderstandingML.signVec σ i| = 1 := by
          unfold UnderstandingML.signVec; split_ifs <;> norm_num
        rw [hs, one_mul]
        exact hB p (data i)
      _ = (N : ℝ) * B := by simp
  have hbdd_P : BddAbove (Set.range fun p : P =>
      ∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)) :=
    ⟨(N : ℝ) * B, by rintro _ ⟨p, rfl⟩; exact (abs_le.mp (hsum_abs p)).2⟩
  have hbdd_a : BddAbove (Set.range fun a :
      UnderstandingML.evalSet (UnderstandingML.lossClass ℓ Set.univ) data =>
      ∑ i : Fin N, UnderstandingML.signVec σ i * (a : Fin N → ℝ) i) :=
    ⟨(N : ℝ) * B, by
      rintro _ ⟨⟨a, f, ⟨p, _, rfl⟩, rfl⟩, rfl⟩
      exact (abs_le.mp (hsum_abs p)).2⟩
  obtain ⟨p0⟩ := ‹Nonempty P›
  have : Nonempty (UnderstandingML.evalSet (UnderstandingML.lossClass ℓ Set.univ) data) :=
    ⟨⟨fun i => ℓ p0 (data i), ℓ p0, ⟨p0, Set.mem_univ _, rfl⟩, rfl⟩⟩
  apply le_antisymm
  · refine ciSup_le fun a => ?_
    rcases a.2 with ⟨f, ⟨p, _, rfl⟩, ha⟩
    simp_rw [ha]
    exact le_ciSup hbdd_P p
  · refine ciSup_le fun p => ?_
    let a : UnderstandingML.evalSet (UnderstandingML.lossClass ℓ Set.univ) data :=
      ⟨fun i => ℓ p (data i), ℓ p, ⟨p, Set.mem_univ _, rfl⟩, rfl⟩
    exact le_ciSup hbdd_a a

private lemma expectedGE_le_of_rademacher_bound
    {P X : Type*} [Nonempty P] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (N : ℕ) (hN : 0 < N) (μ : Measure X) [IsProbabilityMeasure μ]
    (ℓ : P → X → ℝ) (hcont : ∀ p, Continuous (ℓ p))
    (B R : ℝ) (hB : ∀ p x, |ℓ p x| ≤ B)
    (hrad_pt : ∀ data : Fin N → X,
      UnderstandingML.rademacher
        (UnderstandingML.evalSet (UnderstandingML.lossClass ℓ Set.univ) data) ≤ R) :
    XMX.expectedGE N μ ℓ ≤ 2 * R := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨p0⟩ := ‹Nonempty P›
  have hH : (Set.univ : Set P).Nonempty := ⟨p0, Set.mem_univ _⟩
  have hc : ∀ p ∈ (Set.univ : Set P), ∀ x, |ℓ p x| ≤ B := fun p _ x => hB p x
  have hmeas : ∀ p ∈ (Set.univ : Set P), Measurable (ℓ p) := fun p _ => (hcont p).measurable
  have hemp_cont : ∀ p : P, Continuous (fun data : Fin N → X => UnderstandingML.empRisk ℓ data p) :=
    fun p => by
      unfold UnderstandingML.empRisk
      exact (continuous_finsetSum _ fun i _ => (hcont p).comp (continuous_apply i)).div_const _
  have hemp_abs : ∀ data (p : P), |UnderstandingML.empRisk ℓ data p| ≤ B := fun data p => by
    unfold UnderstandingML.empRisk
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    calc
      |∑ i : Fin N, ℓ p (data i)| ≤ ∑ i : Fin N, |ℓ p (data i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hB p (data i)
      _ = B * (N : ℝ) := by simp [mul_comm]
  have hrisk_abs : ∀ p : P, |UnderstandingML.risk ℓ μ p| ≤ B := fun p => by
    unfold UnderstandingML.risk
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const (μ := μ) (f := ℓ p)
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB p x))
  have hrep_meas : Measurable (fun data : Fin N → X =>
      UnderstandingML.representativeness ℓ Set.univ μ data) := by
    apply LowerSemicontinuous.measurable
    refine lowerSemicontinuous_ciSup ?_ fun p => ?_
    · intro data
      refine ⟨2 * B, ?_⟩
      rintro _ ⟨p, rfl⟩
      have h1 := (abs_le.mp (hrisk_abs p.1)).2
      have h2 := (abs_le.mp (hemp_abs data p.1)).1
      linarith
    · exact (continuous_const.sub (hemp_cont p.1)).lowerSemicontinuous
  have hdbl_meas : Measurable (fun p : (Fin N → X) × (Fin N → X) =>
      ⨆ h : (Set.univ : Set P), (UnderstandingML.empRisk ℓ p.2 h.1 - UnderstandingML.empRisk ℓ p.1 h.1)) := by
    apply LowerSemicontinuous.measurable
    refine lowerSemicontinuous_ciSup ?_ fun h => ?_
    · intro p
      refine ⟨2 * B, ?_⟩
      rintro _ ⟨h, rfl⟩
      have h1 := (abs_le.mp (hemp_abs p.2 h.1)).2
      have h2 := (abs_le.mp (hemp_abs p.1 h.1)).1
      linarith
    · exact (((hemp_cont h.1).comp continuous_snd).sub
        ((hemp_cont h.1).comp continuous_fst)).lowerSemicontinuous
  have hsum_abs : ∀ (data : Fin N → X) (σ : Fin N → Bool) (p : P),
      |∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)| ≤ (N : ℝ) * B := fun data σ p => by
    calc
      |∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)|
          ≤ ∑ i : Fin N, |UnderstandingML.signVec σ i * ℓ p (data i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, B := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        have hs : |UnderstandingML.signVec σ i| = 1 := by
          unfold UnderstandingML.signVec; split_ifs <;> norm_num
        rw [hs, one_mul]
        exact hB p (data i)
      _ = (N : ℝ) * B := by simp
  have hrad_meas : Measurable (fun data : Fin N → X =>
      UnderstandingML.rademacher
        (UnderstandingML.evalSet (UnderstandingML.lossClass ℓ Set.univ) data)) := by
    have hfun : (fun data : Fin N → X =>
        UnderstandingML.rademacher
          (UnderstandingML.evalSet (UnderstandingML.lossClass ℓ Set.univ) data)) =
      fun data => (1 / (N : ℝ)) * ((1 / (2 : ℝ) ^ N) *
        ∑ σ : Fin N → Bool, ⨆ p : P,
          ∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)) := by
      ext data
      unfold UnderstandingML.rademacher
      simp_rw [rademacher_sup_eq_levels ℓ B hB data]
    rw [hfun]
    refine Measurable.const_mul (Measurable.const_mul ?_ _) _
    refine Finset.measurable_sum Finset.univ fun σ _ => ?_
    apply LowerSemicontinuous.measurable
    refine lowerSemicontinuous_ciSup ?_ fun p => ?_
    · intro data
      refine ⟨(N : ℝ) * B, ?_⟩
      rintro _ ⟨p, rfl⟩
      exact (abs_le.mp (hsum_abs data σ p)).2
    · exact (continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((hcont p).comp (continuous_apply i))).lowerSemicontinuous
  have hsym := UnderstandingML.representativeness_le_rademacher
    ℓ Set.univ hH B hc hmeas μ N hN hrep_meas hrad_meas hdbl_meas
  have : IsProbabilityMeasure (UnderstandingML.iidLaw μ N) := by
    unfold UnderstandingML.iidLaw; infer_instance
  have hrad_int : Integrable (fun data : Fin N → X =>
      UnderstandingML.rademacher
        (UnderstandingML.evalSet (UnderstandingML.lossClass ℓ Set.univ) data))
      (UnderstandingML.iidLaw μ N) := by
    refine Integrable.of_bound hrad_meas.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun data => ?_)
    rw [Real.norm_eq_abs]
    unfold UnderstandingML.rademacher
    simp_rw [rademacher_sup_eq_levels ℓ B hB data]
    have hterm : ∀ σ : Fin N → Bool,
        |⨆ p : P, ∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)| ≤ (N : ℝ) * B := by
      intro σ
      have hbdd : BddAbove (Set.range fun p : P =>
          ∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)) :=
        ⟨(N : ℝ) * B, by rintro _ ⟨p, rfl⟩; exact (abs_le.mp (hsum_abs data σ p)).2⟩
      rw [abs_le]
      exact ⟨(abs_le.mp (hsum_abs data σ p0)).1.trans (le_ciSup hbdd p0),
        ciSup_le fun p => (abs_le.mp (hsum_abs data σ p)).2⟩
    have hsum_bd :
        |∑ σ : Fin N → Bool, ⨆ p : P,
            ∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)| ≤
          (2 : ℝ) ^ N * ((N : ℝ) * B) := by
      calc
        |∑ σ : Fin N → Bool, ⨆ p : P,
            ∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)|
            ≤ ∑ σ : Fin N → Bool,
                |⨆ p : P, ∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _σ : Fin N → Bool, (N : ℝ) * B := Finset.sum_le_sum fun σ _ => hterm σ
        _ = (2 : ℝ) ^ N * ((N : ℝ) * B) := by
          simp [Finset.card_univ, Fintype.card_fin]
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ)),
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ N)]
    calc
      1 / (N : ℝ) * (1 / (2 : ℝ) ^ N *
          |∑ σ : Fin N → Bool, ⨆ p : P,
            ∑ i : Fin N, UnderstandingML.signVec σ i * ℓ p (data i)|)
          ≤ 1 / (N : ℝ) * (1 / (2 : ℝ) ^ N * ((2 : ℝ) ^ N * ((N : ℝ) * B))) := by
        gcongr
      _ = B := by
        field_simp [hNpos.ne', (pow_pos (by norm_num : (0 : ℝ) < 2) N).ne']
  have hge_eq : XMX.expectedGE N μ ℓ =
      ∫ data, UnderstandingML.representativeness ℓ Set.univ μ data
        ∂(UnderstandingML.iidLaw μ N) := by
    unfold XMX.expectedGE UnderstandingML.iidLaw
    congr 1
    ext data
    unfold XMX.generalizationError UnderstandingML.representativeness
    exact (Equiv.iSup_comp
      (g := fun p : P => XMX.risk μ ℓ p - XMX.empiricalRisk N ℓ data p)
      (Equiv.Set.univ P)).symm
  have hint_le : ∫ data, UnderstandingML.rademacher
      (UnderstandingML.evalSet (UnderstandingML.lossClass ℓ Set.univ) data)
      ∂(UnderstandingML.iidLaw μ N) ≤ R := by
    calc
      ∫ data, UnderstandingML.rademacher
          (UnderstandingML.evalSet (UnderstandingML.lossClass ℓ Set.univ) data)
          ∂(UnderstandingML.iidLaw μ N)
          ≤ ∫ _data, R ∂(UnderstandingML.iidLaw μ N) :=
        integral_mono hrad_int (integrable_const _) hrad_pt
      _ = R := by simp
  calc
    XMX.expectedGE N μ ℓ
        = ∫ data, UnderstandingML.representativeness ℓ Set.univ μ data
            ∂(UnderstandingML.iidLaw μ N) := hge_eq
    _ ≤ 2 * ∫ data, UnderstandingML.rademacher
          (UnderstandingML.evalSet (UnderstandingML.lossClass ℓ Set.univ) data)
          ∂(UnderstandingML.iidLaw μ N) := hsym
    _ ≤ 2 * R := by linarith

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (T L N : ℕ), 0 < T → 0 < N →
      ∀ (U h b : ℝ), 0 < U → h ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (μ : Measure (XMX.Demand T L U)) [IsProbabilityMeasure μ], ∀ k : Fin T,
      XMX.expectedGE N μ (fun (S : XMX.Levels T L U) (d : XMX.Demand T L U) =>
        XMX.cost h b (XMX.inventory T L U S d k - (d ⟨L + k, by omega⟩ : ℝ))) ≤
        C * (((L : ℝ) + 1) * U) / Real.sqrt N := by
  refine Exists.intro (722 : ℝ) ?_
  constructor
  · norm_num
  · intro T L N _hT hN U h b hU hh hb μ hμ k
    have hMpos : 0 < ((L : ℝ) + 1) * U := by positivity
    have : Nonempty (XMX.Levels T L U) := ⟨fun _ => ⟨0, le_rfl, hMpos.le⟩⟩
    have hcont : ∀ S : XMX.Levels T L U, Continuous (periodCost T L U h b k S) := fun S => by
      have hpair : Continuous (fun d : XMX.Demand T L U => (S, d)) :=
        continuous_const.prodMk continuous_id
      unfold periodCost
      simpa only [Function.comp_def] using
        (period_cost_continuous T L U h b k).comp hpair
    have hB : ∀ S d, |periodCost T L U h b k S d| ≤ 2 * (((L : ℝ) + 1) * U) := fun S d =>
      abs_period_cost_le T L U h b hU hh hb k S d
    have hge := expectedGE_le_of_rademacher_bound N hN μ (periodCost T L U h b k) hcont
      (2 * (((L : ℝ) + 1) * U)) ((((L : ℝ) + 1) * U) * (361 / Real.sqrt N)) hB
      (periodCost_rademacher_pointwise T L N hN U h b hU hh hb k)
    have hfun : (fun (S : XMX.Levels T L U) (d : XMX.Demand T L U) =>
        XMX.cost h b (XMX.inventory T L U S d k - (d ⟨L + k, by omega⟩ : ℝ))) =
        periodCost T L U h b k := rfl
    rw [hfun]
    calc
      XMX.expectedGE N μ (periodCost T L U h b k)
          ≤ 2 * ((((L : ℝ) + 1) * U) * (361 / Real.sqrt N)) := hge
      _ = 722 * (((L : ℝ) + 1) * U) / Real.sqrt N := by ring
