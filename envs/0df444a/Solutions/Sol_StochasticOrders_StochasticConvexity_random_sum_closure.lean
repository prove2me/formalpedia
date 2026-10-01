-- Prove2me | solution 1 for StochasticOrders.StochasticConvexity.random_sum_closure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T13:03:23.970277+00:00
-- url     : https://prove2.me/submissions/c2350a29-5148-4e35-986a-ed33cccf06eb

import Mathlib
import Definitions.Def_StochasticOrders_StochasticConvexity_ConvexOrder
import Definitions.Def_StochasticOrders_StochasticConvexity_IcxOrder
import Definitions.Def_StochasticOrders_StochasticConvexity_IcvOrder

set_option autoImplicit false

open Set MeasureTheory ProbabilityTheory

namespace P58884109

/-- pointwise four-point convexity inequality -/
lemma cvx4 {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) (u v w : ℝ) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    φ (u + v) + φ (u + w) ≤ φ u + φ (u + v + w) := by
  rcases eq_or_lt_of_le (add_nonneg hv hw) with h | h
  · have hv0 : v = 0 := by linarith
    have hw0 : w = 0 := by linarith
    subst hv0; subst hw0; simp
  · have h1 := hφ.2 (mem_univ u) (mem_univ (u + v + w))
      (div_nonneg hw h.le) (div_nonneg hv h.le)
      (by rw [← add_div, add_comm w v, div_self h.ne'])
    have h2 := hφ.2 (mem_univ u) (mem_univ (u + v + w))
      (div_nonneg hv h.le) (div_nonneg hw h.le)
      (by rw [← add_div, div_self h.ne'])
    have e1 : (w / (v + w)) • u + (v / (v + w)) • (u + v + w) = u + v := by
      simp only [smul_eq_mul]; field_simp; ring
    have e2 : (v / (v + w)) • u + (w / (v + w)) • (u + v + w) = u + w := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [e1] at h1; rw [e2] at h2
    simp only [smul_eq_mul] at h1 h2
    have hs : w / (v + w) + v / (v + w) = 1 := by
      rw [← add_div, add_comm w v, div_self h.ne']
    have key : w / (v + w) * φ u + v / (v + w) * φ (u + v + w)
        + (v / (v + w) * φ u + w / (v + w) * φ (u + v + w)) = φ u + φ (u + v + w) := by
      linear_combination (φ u + φ (u + v + w)) * hs
    linarith

/-- lower bound for a convex function on `[0, ∞)` -/
lemma cvx_lb {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) :
    ∃ B : ℝ, ∀ s t : ℝ, 0 ≤ s → s ≤ t → min B (φ t) ≤ φ s := by
  by_cases hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → φ t ≤ φ s
  · exact ⟨0, fun s t hs hst => min_le_of_right_le (hmono s t hs hst)⟩
  · push_neg at hmono
    obtain ⟨a, b, ha, hab, hlt⟩ := hmono
    have hab' : a < b := by
      rcases eq_or_lt_of_le hab with h | h
      · subst h; exact absurd hlt (lt_irrefl _)
      · exact h
    refine ⟨min (φ b) (φ 0 - |φ 0 - φ (-1)| * b), fun s t hs hst => ?_⟩
    apply min_le_of_left_le
    rcases le_or_gt b s with hbs | hsb
    · apply min_le_of_left_le
      rcases eq_or_lt_of_le hbs with h | h
      · rw [h]
      · have := hφ.slope_mono_adjacent (mem_univ a) (mem_univ s) hab' h
        have h1 : 0 < (φ b - φ a) / (b - a) := div_pos (by linarith) (by linarith)
        have h2 : 0 < (φ s - φ b) / (s - b) := lt_of_lt_of_le h1 this
        have h3 : 0 < φ s - φ b := by
          rcases (div_pos_iff.mp h2) with ⟨p, _⟩ | ⟨_, q⟩
          · exact p
          · exact absurd q (by linarith)
        linarith
    · apply min_le_of_right_le
      rcases eq_or_lt_of_le hs with h | h
      · rw [← h]; have := abs_nonneg (φ 0 - φ (-1)); nlinarith
      · have := hφ.slope_mono_adjacent (mem_univ (-1)) (mem_univ s) (by norm_num : (-1:ℝ) < 0) h
        simp only [sub_neg_eq_add, zero_add, div_one, sub_zero] at this
        rw [le_div_iff₀ h] at this
        have hab2 := neg_abs_le (φ 0 - φ (-1))
        have : -|φ 0 - φ (-1)| * s ≤ (φ 0 - φ (-1)) * s := mul_le_mul_of_nonneg_right hab2 h.le
        have : |φ 0 - φ (-1)| * s ≤ |φ 0 - φ (-1)| * b :=
          mul_le_mul_of_nonneg_left hsb.le (abs_nonneg _)
        linarith

/-- steps of a convex sequence are monotone -/
lemma dmono (a : ℕ → ℝ) (I : Set ℕ) (hdown : ∀ n, n + 1 ∈ I → n ∈ I)
    (hconv : ∀ n, n + 2 ∈ I → a (n + 1) - a n ≤ a (n + 2) - a (n + 1)) :
    ∀ k n, k ≤ n → n + 1 ∈ I → a (k + 1) - a k ≤ a (n + 1) - a n := by
  intro k n hkn
  induction n, hkn using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ n hkn ih =>
    intro hn
    exact (ih (hdown _ hn)).trans (hconv n hn)

lemma down_le (I : Set ℕ) (hdown : ∀ n, n + 1 ∈ I → n ∈ I) :
    ∀ n, n ∈ I → ∀ m, m ≤ n → m ∈ I := by
  intro n hn m hmn
  induction n, hmn using Nat.le_induction with
  | base => exact hn
  | succ n _ ih => exact ih (hdown _ hn)

lemma chord_le (a : ℕ → ℝ) (I : Set ℕ) (hdown : ∀ n, n + 1 ∈ I → n ∈ I)
    (hconv : ∀ n, n + 2 ∈ I → a (n + 1) - a n ≤ a (n + 2) - a (n + 1))
    (m j : ℕ) (hn : m + j + 1 ∈ I) :
    a (m + j) - (a (m + j + 1) - a (m + j)) * (j : ℝ) ≤ a m := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : m + j + 1 ∈ I := hdown _ (by simpa [Nat.add_assoc] using hn)
    have := ih h1
    have hd := dmono a I hdown hconv (m + j) (m + j + 1) (by omega) (by simpa [Nat.add_assoc] using hn)
    have e1 : m + (j + 1) = m + j + 1 := by ring
    rw [e1]
    push_cast
    have hj : (0:ℝ) ≤ (j:ℝ) + 1 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hj]

lemma chord_ge (a : ℕ → ℝ) (I : Set ℕ) (hdown : ∀ n, n + 1 ∈ I → n ∈ I)
    (hconv : ∀ n, n + 2 ∈ I → a (n + 1) - a n ≤ a (n + 2) - a (n + 1))
    (n j : ℕ) (hm : n + 1 + j ∈ I) :
    a n + (a (n + 1) - a n) * (1 + (j : ℝ)) ≤ a (n + 1 + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : n + 1 + j ∈ I := hdown _ (by simpa [Nat.add_assoc] using hm)
    have := ih h1
    have hd := dmono a I hdown hconv n (n + 1 + j) (by omega) (by simpa [Nat.add_assoc] using hm)
    have e1 : n + 1 + (j + 1) = n + 1 + j + 1 := by ring
    rw [e1]
    push_cast
    linarith

/-- chord inequality -/
lemma chord (a : ℕ → ℝ) (I : Set ℕ) (hdown : ∀ n, n + 1 ∈ I → n ∈ I)
    (hconv : ∀ n, n + 2 ∈ I → a (n + 1) - a n ≤ a (n + 2) - a (n + 1))
    (n : ℕ) (hn : n + 1 ∈ I) (m : ℕ) (hm : m ∈ I) :
    a n + (a (n + 1) - a n) * ((m : ℝ) - n) ≤ a m := by
  rcases le_or_gt m n with hmn | hnm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have := chord_le a I hdown hconv m j hn
    push_cast
    linarith
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hnm
    have := chord_ge a I hdown hconv n j (by simpa [Nat.add_right_comm] using hm)
    have e : n + j + 1 = n + 1 + j := by ring
    rw [e]
    push_cast
    linarith


lemma extend (a : ℕ → ℝ) (I : Set ℕ) (h0 : 0 ∈ I) (hdown : ∀ n, n + 1 ∈ I → n ∈ I)
    (hconv : ∀ n, n + 2 ∈ I → a (n + 1) - a n ≤ a (n + 2) - a (n + 1)) :
    ∃ g : ℝ → ℝ, ConvexOn ℝ univ g ∧ (∀ n ∈ I, g n = a n) ∧
      ((∀ n, n + 1 ∈ I → a n ≤ a (n + 1)) → Monotone g) ∧
      ((∀ n, n + 1 ∈ I → a (n + 1) ≤ a n) → Antitone g) := by
  by_cases h1 : 1 ∈ I
  swap
  · refine ⟨fun _ => a 0, convexOn_const _ convex_univ, ?_, fun _ => monotone_const,
      fun _ => antitone_const⟩
    intro n hn
    have : n = 0 := by
      by_contra hne
      exact h1 (down_le I hdown n hn 1 (by omega))
    subst this; simp
  · let ℓ : ℕ → ℝ → ℝ := fun n x => a n + (a (n + 1) - a n) * (x - n)
    let T := {n : ℕ // n + 1 ∈ I}
    have : Nonempty T := ⟨⟨0, h1⟩⟩
    have hbdd : ∀ x : ℝ, BddAbove (range fun n : T => ℓ n.1 x) := by
      intro x
      refine ⟨∑ j ∈ Finset.range (⌈x⌉₊ + 1), |ℓ j x|, ?_⟩
      rintro _ ⟨⟨n, hn⟩, rfl⟩
      show ℓ n x ≤ _
      by_cases hnj : n ≤ ⌈x⌉₊
      · exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |ℓ j x|)
          (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (by omega)))
      · push_neg at hnj
        have hj1 : ⌈x⌉₊ + 1 ∈ I := down_le I hdown (n + 1) hn (⌈x⌉₊ + 1) (by omega)
        have hjI : ⌈x⌉₊ ∈ I := hdown _ hj1
        have hc := chord a I hdown hconv n hn ⌈x⌉₊ hjI
        have hd := dmono a I hdown hconv ⌈x⌉₊ n hnj.le hn
        have hx : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
        have : ℓ n x ≤ ℓ ⌈x⌉₊ x := by
          simp only [ℓ]
          nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hx)]
        exact this.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun j => |ℓ j x|)
          (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))))
    refine ⟨fun x => ⨆ n : T, ℓ n.1 x, ?_, ?_, ?_, ?_⟩
    · refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
      simp only [smul_eq_mul]
      apply ciSup_le
      intro n
      have e : ℓ n.1 (p * x + q * y) = p * ℓ n.1 x + q * ℓ n.1 y := by
        simp only [ℓ]
        linear_combination (-(a n.1 - (a (n.1 + 1) - a n.1) * (n.1 : ℝ))) * hpq
      rw [e]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_ciSup (hbdd x) n) hp)
        (mul_le_mul_of_nonneg_left (le_ciSup (hbdd y) n) hq)
    · intro m hm
      apply le_antisymm
      · exact ciSup_le fun n => chord a I hdown hconv n.1 n.2 m hm
      · by_cases hm1 : m + 1 ∈ I
        · exact le_ciSup_of_le (hbdd m) ⟨m, hm1⟩ (le_of_eq (by simp [ℓ]))
        · have hm0 : m ≠ 0 := by rintro rfl; exact hm1 h1
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
          exact le_ciSup_of_le (hbdd _) ⟨k, hm⟩ (le_of_eq (by simp only [ℓ]; push_cast; ring))
    · intro hstep x y hxy
      exact ciSup_le fun n => le_ciSup_of_le (hbdd y) n (by
        simp only [ℓ]
        nlinarith [mul_nonneg (sub_nonneg.mpr (hstep n.1 n.2)) (sub_nonneg.mpr hxy)])
    · intro hstep x y hxy
      exact ciSup_le fun n => le_ciSup_of_le (hbdd x) n (by
        simp only [ℓ]
        nlinarith [mul_nonneg (sub_nonneg.mpr (hstep n.1 n.2)) (sub_nonneg.mpr hxy)])

lemma disint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k)) (X : Ω → ℕ) (hX : Measurable X)
    (hind : IndepFun X (fun ω k => Y k ω) μ) (h : ℝ → ℝ) (hh : Measurable h)
    (hint : Integrable (fun ω => h (∑ k ∈ Finset.range (X ω), Y k ω)) μ) :
    (∫ ω, h (∑ k ∈ Finset.range (X ω), Y k ω) ∂μ
        = ∫ ω, (∫ ω', h (∑ k ∈ Finset.range (X ω), Y k ω') ∂μ) ∂μ) ∧
    Integrable (fun ω => ∫ ω', h (∑ k ∈ Finset.range (X ω), Y k ω') ∂μ) μ ∧
    ∀ᵐ ω ∂μ, Integrable (fun ω' => h (∑ k ∈ Finset.range (X ω), Y k ω')) μ := by
  set Yv : Ω → (ℕ → ℝ) := fun ω k => Y k ω with hYv
  have hYvm : Measurable Yv := measurable_pi_lambda _ hY
  have hmap : μ.map (fun ω => (X ω, Yv ω)) = (μ.map X).prod (μ.map Yv) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hYvm.aemeasurable).mp hind
  let F : ℕ × (ℕ → ℝ) → ℝ := fun z => h (∑ k ∈ Finset.range z.1, z.2 k)
  have hFm : Measurable F := by
    apply measurable_from_prod_countable_right
    intro m
    show Measurable fun y : ℕ → ℝ => h (∑ k ∈ Finset.range m, y k)
    exact hh.comp (Finset.measurable_sum (Finset.range m) (fun k _ => measurable_pi_apply k))
  have hpm : Measurable (fun ω => (X ω, Yv ω)) := hX.prodMk hYvm
  have hFint : Integrable F ((μ.map X).prod (μ.map Yv)) := by
    rw [← hmap, integrable_map_measure hFm.aestronglyMeasurable hpm.aemeasurable]
    exact hint
  have hFm' : ∀ m : ℕ, Measurable (fun y : ℕ → ℝ => F (m, y)) := fun m =>
    hFm.comp (measurable_const.prodMk measurable_id)
  have hinner : ∀ m : ℕ, ∫ y, F (m, y) ∂(μ.map Yv)
      = ∫ ω', h (∑ k ∈ Finset.range m, Y k ω') ∂μ := by
    intro m
    rw [integral_map hYvm.aemeasurable (hFm' m).aestronglyMeasurable]
  refine ⟨?_, ?_, ?_⟩
  · have e1 : ∫ ω, h (∑ k ∈ Finset.range (X ω), Y k ω) ∂μ
        = ∫ z, F z ∂((μ.map X).prod (μ.map Yv)) := by
      rw [← hmap, integral_map hpm.aemeasurable hFm.aestronglyMeasurable]
    rw [e1, integral_prod F hFint]
    simp_rw [hinner]
    rw [integral_map hX.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
  · have := hFint.integral_prod_left
    simp_rw [hinner] at this
    exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      hX.aemeasurable).mp this
  · have := hFint.prod_right_ae
    have h2 : ∀ᵐ m ∂(μ.map X), Integrable (fun ω' => h (∑ k ∈ Finset.range m, Y k ω')) μ := by
      filter_upwards [this] with m hm
      exact (integrable_map_measure (hFm' m).aestronglyMeasurable hYvm.aemeasurable).mp hm
    exact ae_of_ae_map hX.aemeasurable h2

lemma pair_map {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k)) (hYindep : iIndepFun Y μ)
    (hYiid : ∀ j k : ℕ, IdentDistrib (Y j) (Y k) μ μ) (n i j : ℕ) (hi : n ≤ i) (hj : n ≤ j) :
    μ.map (fun ω => (∑ k ∈ Finset.range n, Y k ω, Y i ω))
      = μ.map (fun ω => (∑ k ∈ Finset.range n, Y k ω, Y j ω)) := by
  have hSm : Measurable (fun ω => ∑ k ∈ Finset.range n, Y k ω) :=
    Finset.measurable_sum _ (fun k _ => hY k)
  have hind : ∀ i, n ≤ i → IndepFun (fun ω => ∑ k ∈ Finset.range n, Y k ω) (Y i) μ := by
    intro i hi
    have := hYindep.indepFun_finsetSum_of_notMem hY (s := Finset.range n) (i := i)
      (by simp; omega)
    convert this using 1
    ext ω; simp [Finset.sum_apply]
  rw [(indepFun_iff_map_prod_eq_prod_map_map hSm.aemeasurable (hY i).aemeasurable).mp (hind i hi),
    (indepFun_iff_map_prod_eq_prod_map_map hSm.aemeasurable (hY j).aemeasurable).mp (hind j hj),
    (hYiid i j).map_eq]

lemma transfer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k)) (hYindep : iIndepFun Y μ)
    (hYiid : ∀ j k : ℕ, IdentDistrib (Y j) (Y k) μ μ) (f : ℝ → ℝ) (hf : Measurable f)
    (n i j : ℕ) (hi : n ≤ i) (hj : n ≤ j) :
    (∫ ω, f (∑ k ∈ Finset.range n, Y k ω + Y i ω) ∂μ
        = ∫ ω, f (∑ k ∈ Finset.range n, Y k ω + Y j ω) ∂μ) ∧
    (Integrable (fun ω => f (∑ k ∈ Finset.range n, Y k ω + Y i ω)) μ ↔
        Integrable (fun ω => f (∑ k ∈ Finset.range n, Y k ω + Y j ω)) μ) := by
  have hSm : Measurable (fun ω => ∑ k ∈ Finset.range n, Y k ω) :=
    Finset.measurable_sum _ (fun k _ => hY k)
  let G : ℝ × ℝ → ℝ := fun z => f (z.1 + z.2)
  have hG : Measurable G := hf.comp (measurable_fst.add measurable_snd)
  have hp := pair_map μ Y hY hYindep hYiid n i j hi hj
  have hpi : Measurable (fun ω => (∑ k ∈ Finset.range n, Y k ω, Y i ω)) := hSm.prodMk (hY i)
  have hpj : Measurable (fun ω => (∑ k ∈ Finset.range n, Y k ω, Y j ω)) := hSm.prodMk (hY j)
  constructor
  · have e1 := integral_map hpi.aemeasurable (hG.aestronglyMeasurable (μ := μ.map _))
    have e2 := integral_map hpj.aemeasurable (hG.aestronglyMeasurable (μ := μ.map _))
    rw [hp] at e1
    exact e1.symm.trans e2
  · have e1 : Integrable (fun ω => f (∑ k ∈ Finset.range n, Y k ω + Y i ω)) μ ↔
        Integrable G (μ.map (fun ω => (∑ k ∈ Finset.range n, Y k ω, Y i ω))) :=
      (integrable_map_measure hG.aestronglyMeasurable hpi.aemeasurable).symm
    have e2 : Integrable (fun ω => f (∑ k ∈ Finset.range n, Y k ω + Y j ω)) μ ↔
        Integrable G (μ.map (fun ω => (∑ k ∈ Finset.range n, Y k ω, Y j ω))) :=
      (integrable_map_measure hG.aestronglyMeasurable hpj.aemeasurable).symm
    rw [e1, e2, hp]


lemma nn_all {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hYnn : ∀ k, 0 ≤ᵐ[μ] Y k) : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ Y k ω :=
  ae_all_iff.2 fun k => by filter_upwards [hYnn k] with ω h; simpa using h

lemma seq_down {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k)) (hYnn : ∀ k, 0 ≤ᵐ[μ] Y k)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) (n : ℕ)
    (hn : Integrable (fun ω => φ (∑ k ∈ Finset.range (n + 1), Y k ω)) μ) :
    Integrable (fun ω => φ (∑ k ∈ Finset.range n, Y k ω)) μ := by
  have hφc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  obtain ⟨B, hB⟩ := cvx_lb hφ
  refine Integrable.mono' ((integrable_const (|φ 0| + |B|)).add hn.abs) ?_ ?_
  · exact (hφc.measurable.comp (Finset.measurable_sum _ fun k _ => hY k)).aestronglyMeasurable
  · filter_upwards [nn_all μ Y hYnn] with ω hω
    have ht : ∑ k ∈ Finset.range (n + 1), Y k ω = ∑ k ∈ Finset.range n, Y k ω + Y n ω :=
      Finset.sum_range_succ _ _
    simp only [Pi.add_apply, Real.norm_eq_abs, ht]
    set s := ∑ k ∈ Finset.range n, Y k ω
    have hs : 0 ≤ s := Finset.sum_nonneg fun k _ => hω k
    have hst : s ≤ s + Y n ω := by linarith [hω n]
    have up := hφ.le_max_of_mem_Icc (mem_univ 0) (mem_univ (s + Y n ω)) ⟨hs, hst⟩
    have lo := hB s (s + Y n ω) hs hst
    rw [abs_le]
    constructor
    · rcases le_total B (φ (s + Y n ω)) with h | h
      · rw [min_eq_left h] at lo
        linarith [neg_abs_le B, abs_nonneg (φ 0), abs_nonneg (φ (s + Y n ω))]
      · rw [min_eq_right h] at lo
        linarith [neg_abs_le (φ (s + Y n ω)), abs_nonneg (φ 0), abs_nonneg B]
    · rcases le_total (φ 0) (φ (s + Y n ω)) with h | h
      · rw [max_eq_right h] at up
        linarith [le_abs_self (φ (s + Y n ω)), abs_nonneg (φ 0), abs_nonneg B]
      · rw [max_eq_left h] at up
        linarith [le_abs_self (φ 0), abs_nonneg (φ (s + Y n ω)), abs_nonneg B]

lemma seq_conv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k)) (hYindep : iIndepFun Y μ)
    (hYiid : ∀ j k : ℕ, IdentDistrib (Y j) (Y k) μ μ) (hYnn : ∀ k, 0 ≤ᵐ[μ] Y k)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) (n : ℕ)
    (h2 : Integrable (fun ω => φ (∑ k ∈ Finset.range (n + 2), Y k ω)) μ) :
    (∫ ω, φ (∑ k ∈ Finset.range (n + 1), Y k ω) ∂μ) - ∫ ω, φ (∑ k ∈ Finset.range n, Y k ω) ∂μ
      ≤ (∫ ω, φ (∑ k ∈ Finset.range (n + 2), Y k ω) ∂μ)
        - ∫ ω, φ (∑ k ∈ Finset.range (n + 1), Y k ω) ∂μ := by
  have hφc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  have h1 := seq_down μ Y hY hYnn φ hφ (n + 1) h2
  have h0 := seq_down μ Y hY hYnn φ hφ n h1
  obtain ⟨eT, iT⟩ := transfer μ Y hY hYindep hYiid φ hφc.measurable n n (n + 1) le_rfl (by omega)
  rw [show n + 2 = n + 1 + 1 from rfl] at h2 ⊢
  simp only [Finset.sum_range_succ] at h1 h2 ⊢
  have iW := iT.mp h1
  have key : ∫ ω, (φ (∑ k ∈ Finset.range n, Y k ω + Y n ω)
        + φ (∑ k ∈ Finset.range n, Y k ω + Y (n + 1) ω)) ∂μ
      ≤ ∫ ω, (φ (∑ k ∈ Finset.range n, Y k ω)
        + φ (∑ k ∈ Finset.range n, Y k ω + Y n ω + Y (n + 1) ω)) ∂μ := by
    apply integral_mono_ae (h1.add iW) (h0.add h2)
    filter_upwards [nn_all μ Y hYnn] with ω hω
    exact cvx4 hφ _ _ _ (hω n) (hω (n + 1))
  rw [integral_add h1 iW, integral_add h0 h2] at key
  linarith [eT]

lemma seq_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k)) (hYnn : ∀ k, 0 ≤ᵐ[μ] Y k)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) (hm : Monotone φ) (n : ℕ)
    (h1 : Integrable (fun ω => φ (∑ k ∈ Finset.range (n + 1), Y k ω)) μ) :
    ∫ ω, φ (∑ k ∈ Finset.range n, Y k ω) ∂μ ≤ ∫ ω, φ (∑ k ∈ Finset.range (n + 1), Y k ω) ∂μ := by
  have h0 := seq_down μ Y hY hYnn φ hφ n h1
  apply integral_mono_ae h0 h1
  filter_upwards [nn_all μ Y hYnn] with ω hω
  rw [Finset.sum_range_succ]
  exact hm (by linarith [hω n])

lemma seq_anti {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k)) (hYnn : ∀ k, 0 ≤ᵐ[μ] Y k)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) (hm : Antitone φ) (n : ℕ)
    (h1 : Integrable (fun ω => φ (∑ k ∈ Finset.range (n + 1), Y k ω)) μ) :
    ∫ ω, φ (∑ k ∈ Finset.range (n + 1), Y k ω) ∂μ ≤ ∫ ω, φ (∑ k ∈ Finset.range n, Y k ω) ∂μ := by
  have h0 := seq_down μ Y hY hYnn φ hφ n h1
  apply integral_mono_ae h1 h0
  filter_upwards [nn_all μ Y hYnn] with ω hω
  rw [Finset.sum_range_succ]
  exact hm (by linarith [hω n])

lemma core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k)) (hYindep : iIndepFun Y μ)
    (hYiid : ∀ j k : ℕ, IdentDistrib (Y j) (Y k) μ μ) (hYnn : ∀ k, 0 ≤ᵐ[μ] Y k)
    (M N : Ω → ℕ) (hM : Measurable M) (hN : Measurable N)
    (hindM : IndepFun M (fun ω k => Y k ω) μ) (hindN : IndepFun N (fun ω k => Y k ω) μ)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ)
    (hiM : Integrable (fun ω => φ (∑ k ∈ Finset.range (M ω), Y k ω)) μ)
    (hiN : Integrable (fun ω => φ (∑ k ∈ Finset.range (N ω), Y k ω)) μ)
    (Ord : ∀ g : ℝ → ℝ, ConvexOn ℝ univ g → (Monotone φ → Monotone g) →
      (Antitone φ → Antitone g) → Integrable (fun ω => g (M ω : ℝ)) μ →
      Integrable (fun ω => g (N ω : ℝ)) μ → ∫ ω, g (M ω : ℝ) ∂μ ≤ ∫ ω, g (N ω : ℝ) ∂μ) :
    ∫ ω, φ (∑ k ∈ Finset.range (M ω), Y k ω) ∂μ ≤ ∫ ω, φ (∑ k ∈ Finset.range (N ω), Y k ω) ∂μ := by
  have hφc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  obtain ⟨eM, iM, aeM⟩ := disint μ Y hY M hM hindM φ hφc.measurable hiM
  obtain ⟨eN, iN, aeN⟩ := disint μ Y hY N hN hindN φ hφc.measurable hiN
  obtain ⟨g, hgc, hgv, hgm, hga⟩ := extend (fun n => ∫ ω, φ (∑ k ∈ Finset.range n, Y k ω) ∂μ)
    {n | Integrable (fun ω => φ (∑ k ∈ Finset.range n, Y k ω)) μ}
    (by
      show Integrable (fun ω => φ (∑ k ∈ Finset.range 0, Y k ω)) μ
      simp only [Finset.range_zero, Finset.sum_empty]
      exact integrable_const _)
    (fun n hn => seq_down μ Y hY hYnn φ hφ n hn)
    (fun n hn => seq_conv μ Y hY hYindep hYiid hYnn φ hφ n hn)
  have gM : ∀ᵐ ω ∂μ, g (M ω) = ∫ ω', φ (∑ k ∈ Finset.range (M ω), Y k ω') ∂μ :=
    aeM.mono fun ω h => hgv (M ω) h
  have gN : ∀ᵐ ω ∂μ, g (N ω) = ∫ ω', φ (∑ k ∈ Finset.range (N ω), Y k ω') ∂μ :=
    aeN.mono fun ω h => hgv (N ω) h
  have igM : Integrable (fun ω => g (M ω : ℝ)) μ := iM.congr (gM.mono fun ω h => h.symm)
  have igN : Integrable (fun ω => g (N ω : ℝ)) μ := iN.congr (gN.mono fun ω h => h.symm)
  have key := Ord g hgc (fun h => hgm (fun n hn => seq_mono μ Y hY hYnn φ hφ h n hn))
    (fun h => hga (fun n hn => seq_anti μ Y hY hYnn φ hφ h n hn)) igM igN
  rw [eM, eN]
  calc _ = ∫ ω, g (M ω : ℝ) ∂μ := integral_congr_ae (gM.mono fun ω h => h.symm)
    _ ≤ ∫ ω, g (N ω : ℝ) ∂μ := key
    _ = _ := integral_congr_ae gN

end P58884109

open MeasureTheory ProbabilityTheory StochasticOrders.StochasticConvexity in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (M N : Ω → ℕ)
    (hYmeas : ∀ k, Measurable (Y k)) (hMmeas : Measurable M) (hNmeas : Measurable N)
    (hYindep : iIndepFun Y μ) (hYiid : ∀ j k : ℕ, IdentDistrib (Y j) (Y k) μ μ)
    (hYnn : ∀ k, 0 ≤ᵐ[μ] Y k)
    (hIndepMN_Y : IndepFun (fun ω => (M ω, N ω)) (fun ω k => Y k ω) μ) :
    (IcxOrder μ μ (fun ω => (M ω : ℝ)) (fun ω => (N ω : ℝ)) →
      IcxOrder μ μ (fun ω => ∑ k ∈ Finset.range (M ω), Y k ω)
        (fun ω => ∑ k ∈ Finset.range (N ω), Y k ω)) ∧
    (IcvOrder μ μ (fun ω => (M ω : ℝ)) (fun ω => (N ω : ℝ)) →
      IcvOrder μ μ (fun ω => ∑ k ∈ Finset.range (M ω), Y k ω)
        (fun ω => ∑ k ∈ Finset.range (N ω), Y k ω)) ∧
    (ConvexOrder μ μ (fun ω => (M ω : ℝ)) (fun ω => (N ω : ℝ)) →
      ConvexOrder μ μ (fun ω => ∑ k ∈ Finset.range (M ω), Y k ω)
        (fun ω => ∑ k ∈ Finset.range (N ω), Y k ω)) := by
  have hindM : IndepFun M (fun ω k => Y k ω) μ := hIndepMN_Y.comp measurable_fst measurable_id
  have hindN : IndepFun N (fun ω k => Y k ω) μ := hIndepMN_Y.comp measurable_snd measurable_id
  refine ⟨?_, ?_, ?_⟩
  · intro hMN φ hφm hφc hiM hiN
    exact P58884109.core μ Y hYmeas hYindep hYiid hYnn M N hMmeas hNmeas hindM hindN φ hφc hiM hiN
      (fun g hg hgm _ igM igN => hMN g (hgm hφm) hg igM igN)
  · intro hMN φ hφm hφcv hiM hiN
    have key := P58884109.core μ Y hYmeas hYindep hYiid hYnn N M hNmeas hMmeas hindN hindM
      (fun x => -φ x) hφcv.neg hiN.neg hiM.neg (fun g hg _ hga igN igM => by
        have := hMN (fun x => -g x) (fun x y h => neg_le_neg (hga (fun x y h => neg_le_neg (hφm h)) h))
          hg.neg igM.neg igN.neg
        simp only [integral_neg] at this
        linarith)
    simp only [integral_neg] at key
    linarith
  · intro hMN φ hφc hiM hiN
    exact P58884109.core μ Y hYmeas hYindep hYiid hYnn M N hMmeas hNmeas hindM hindN φ hφc hiM hiN
      (fun g hg _ _ igM igN => hMN g hg igM igN)
