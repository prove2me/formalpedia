-- Prove2me | solution 1 for TsallisINF.Half.theorem_1_rv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T23:03:17.630178+00:00
-- url     : https://prove2.me/submissions/6feafc26-d96f-4f43-baa0-493561cb921c

import Mathlib
import Definitions.Def_TsallisINF_AdvAlpha_Setting
import Definitions.Def_TsallisINF_Half_Setting

set_option autoImplicit false
set_option linter.all false
set_option linter.unusedVariables false

namespace TsallisINF.AdvAlpha.P64936

section SArgmax

open Finset Filter Topology

/-- The OMD objective of `IsOMDBandit` for the α-Tsallis regularizer with `ξ = 1`. -/
noncomputable def obj {K : ℕ} (α e : ℝ) (L w : Fin K → ℝ) : ℝ :=
  e * (∑ i, w i * -L i) - tsallisPsi α (fun _ => 1) w

/-- coordinate summand of the objective -/
noncomputable def gc (α e c y : ℝ) : ℝ :=
  e * (y * -c) + (y ^ α - α * y) / (α * (1 - α))

lemma obj_eq {K : ℕ} (α e : ℝ) (L w : Fin K → ℝ) :
    obj α e L w = ∑ i, gc α e (L i) (w i) := by
  simp only [obj, tsallisPsi, gc, mul_one, Finset.mul_sum, sub_neg_eq_add,
    Finset.sum_add_distrib]

lemma mid_rpow_le (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a ^ α + b ^ α) / 2 ≤ ((a + b) / 2) ^ α := by
  have h := (Real.strictConcaveOn_rpow hα.1 hα.2).concaveOn.2 (Set.mem_Ici.2 ha)
    (Set.mem_Ici.2 hb) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at h
  calc (a ^ α + b ^ α) / 2 = 1 / 2 * a ^ α + 1 / 2 * b ^ α := by ring
    _ ≤ (1 / 2 * a + 1 / 2 * b) ^ α := h
    _ = ((a + b) / 2) ^ α := by ring_nf

lemma mid_rpow_lt (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≠ b) : (a ^ α + b ^ α) / 2 < ((a + b) / 2) ^ α := by
  have h := (Real.strictConcaveOn_rpow hα.1 hα.2).2 (Set.mem_Ici.2 ha)
    (Set.mem_Ici.2 hb) hab (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at h
  calc (a ^ α + b ^ α) / 2 = 1 / 2 * a ^ α + 1 / 2 * b ^ α := by ring
    _ < (1 / 2 * a + 1 / 2 * b) ^ α := h
    _ = ((a + b) / 2) ^ α := by ring_nf

lemma gc_mid_le (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (e c a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (gc α e c a + gc α e c b) / 2 ≤ gc α e c ((a + b) / 2) := by
  have hd : 0 < α * (1 - α) := mul_pos hα.1 (by linarith [hα.2])
  have h := mid_rpow_le α hα a b ha hb
  unfold gc
  have : (a ^ α + b ^ α) / 2 / (α * (1 - α)) ≤ ((a + b) / 2) ^ α / (α * (1 - α)) :=
    div_le_div_of_nonneg_right h hd.le
  have e1 : (e * (a * -c) + (a ^ α - α * a) / (α * (1 - α)) +
      (e * (b * -c) + (b ^ α - α * b) / (α * (1 - α)))) / 2 =
      e * ((a + b) / 2 * -c) - α * ((a + b) / 2) / (α * (1 - α)) +
        (a ^ α + b ^ α) / 2 / (α * (1 - α)) := by
    field_simp; ring
  have e2 : e * ((a + b) / 2 * -c) + (((a + b) / 2) ^ α - α * ((a + b) / 2)) / (α * (1 - α)) =
      e * ((a + b) / 2 * -c) - α * ((a + b) / 2) / (α * (1 - α)) +
        ((a + b) / 2) ^ α / (α * (1 - α)) := by
    field_simp; ring
  rw [e1, e2]; linarith

lemma gc_mid_lt (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (e c a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≠ b) : (gc α e c a + gc α e c b) / 2 < gc α e c ((a + b) / 2) := by
  have hd : 0 < α * (1 - α) := mul_pos hα.1 (by linarith [hα.2])
  have h := mid_rpow_lt α hα a b ha hb hab
  unfold gc
  have : (a ^ α + b ^ α) / 2 / (α * (1 - α)) < ((a + b) / 2) ^ α / (α * (1 - α)) :=
    div_lt_div_of_pos_right h hd
  have e1 : (e * (a * -c) + (a ^ α - α * a) / (α * (1 - α)) +
      (e * (b * -c) + (b ^ α - α * b) / (α * (1 - α)))) / 2 =
      e * ((a + b) / 2 * -c) - α * ((a + b) / 2) / (α * (1 - α)) +
        (a ^ α + b ^ α) / 2 / (α * (1 - α)) := by
    field_simp; ring
  have e2 : e * ((a + b) / 2 * -c) + (((a + b) / 2) ^ α - α * ((a + b) / 2)) / (α * (1 - α)) =
      e * ((a + b) / 2 * -c) - α * ((a + b) / 2) / (α * (1 - α)) +
        ((a + b) / 2) ^ α / (α * (1 - α)) := by
    field_simp; ring
  rw [e1, e2]; linarith

/-- `x` maximizes the OMD objective over the simplex. -/
def IsArgmax {K : ℕ} (α e : ℝ) (L x : Fin K → ℝ) : Prop :=
  x ∈ stdSimplex ℝ (Fin K) ∧ ∀ v ∈ stdSimplex ℝ (Fin K), obj α e L v ≤ obj α e L x

lemma argmax_unique {K : ℕ} (α e : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (L x y : Fin K → ℝ)
    (hx : IsArgmax α e L x) (hy : IsArgmax α e L y) : x = y := by
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  set m : Fin K → ℝ := fun k => (x k + y k) / 2 with hm
  have hmS : m ∈ stdSimplex ℝ (Fin K) := by
    have := (convex_stdSimplex ℝ (Fin K)) hx.1 hy.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert this using 1
    funext k; simp [hm]; ring
  have hlt : (obj α e L x + obj α e L y) / 2 < obj α e L m := by
    rw [obj_eq, obj_eq, obj_eq, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_lt_sum
    · intro k _
      exact gc_mid_le α hα e (L k) (x k) (y k) (hx.1.1 k) (hy.1.1 k)
    · exact ⟨i, Finset.mem_univ _, gc_mid_lt α hα e (L i) (x i) (y i) (hx.1.1 i) (hy.1.1 i) hi⟩
  have h1 := hx.2 m hmS
  have h2 := hy.2 x hx.1
  have h3 := hx.2 y hy.1
  linarith

lemma continuous_obj {K : ℕ} (α e : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    Continuous (fun p : (Fin K → ℝ) × (Fin K → ℝ) => obj α e p.1 p.2) := by
  simp only [obj_eq, gc]
  refine continuous_finsetSum _ (fun i _ => ?_)
  have h1 : Continuous (fun p : (Fin K → ℝ) × (Fin K → ℝ) => p.2 i) :=
    (continuous_apply i).comp continuous_snd
  have h2 : Continuous (fun p : (Fin K → ℝ) × (Fin K → ℝ) => p.1 i) :=
    (continuous_apply i).comp continuous_fst
  have h3 : Continuous (fun p : (Fin K → ℝ) × (Fin K → ℝ) => p.2 i ^ α) :=
    h1.rpow_const (fun _ => Or.inr hα.1.le)
  fun_prop

lemma exists_argmax {K : ℕ} (hK : 0 < K) (α e : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (L : Fin K → ℝ) : ∃ x, IsArgmax α e L x := by
  have hc : ContinuousOn (fun w => obj α e L w) (stdSimplex ℝ (Fin K)) := by
    have := (continuous_obj (K := K) α e hα).comp (Continuous.prodMk continuous_const continuous_id
      : Continuous (fun w : Fin K → ℝ => (L, w)))
    exact this.continuousOn
  obtain ⟨x, hx, hmax⟩ := (isCompact_stdSimplex ℝ (Fin K)).exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ (⟨0, hK⟩ : Fin K)⟩ hc
  exact ⟨x, hx, fun v hv => hmax hv⟩

open Classical in
/-- The (unique) OMD argmax map. -/
noncomputable def G {K : ℕ} (α e : ℝ) (L : Fin K → ℝ) : Fin K → ℝ :=
  if h : ∃ x, IsArgmax α e L x then h.choose else 0

lemma G_spec {K : ℕ} (hK : 0 < K) (α e : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (L : Fin K → ℝ) :
    IsArgmax α e L (G α e L) := by
  have h := exists_argmax hK α e hα L
  unfold G; rw [dif_pos h]; exact h.choose_spec

lemma eq_G {K : ℕ} (hK : 0 < K) (α e : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (L x : Fin K → ℝ)
    (hx : IsArgmax α e L x) : x = G α e L :=
  argmax_unique α e hα L x _ hx (G_spec hK α e hα L)

lemma G_continuous {K : ℕ} (hK : 0 < K) (α e : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    Continuous (G (K := K) α e) := by
  rw [continuous_iff_seqContinuous]
  intro u L hu
  have hmem : ∀ᶠ n in atTop, (G α e ∘ u) n ∈ stdSimplex ℝ (Fin K) :=
    Eventually.of_forall fun n => (G_spec hK α e hα (u n)).1
  refine (isCompact_stdSimplex ℝ (Fin K)).tendsto_nhds_of_unique_mapClusterPt hmem ?_
  intro y hy hclus
  obtain ⟨ψ, hψ, hlim⟩ := MapClusterPt.tendsto_subseq hclus
  have hlim' : Tendsto (fun n => G α e (u (ψ n))) atTop (𝓝 y) := hlim
  refine eq_G hK α e hα L y ⟨hy, fun v hv => ?_⟩
  have huψ : Tendsto (fun n => u (ψ n)) atTop (𝓝 L) := hu.comp hψ.tendsto_atTop
  have hc := continuous_obj (K := K) α e hα
  have h1 : Tendsto (fun n => obj α e (u (ψ n)) v) atTop (𝓝 (obj α e L v)) := by
    have := (hc.tendsto (L, v)).comp (huψ.prodMk_nhds (tendsto_const_nhds (x := v)))
    exact this
  have h2 : Tendsto (fun n => obj α e (u (ψ n)) (G α e (u (ψ n)))) atTop
      (𝓝 (obj α e L y)) := by
    have := (hc.tendsto (L, y)).comp (huψ.prodMk_nhds hlim')
    exact this
  have h3 : ∀ n, obj α e (u (ψ n)) v ≤ obj α e (u (ψ n)) (G α e (u (ψ n))) :=
    fun n => (G_spec hK α e hα (u (ψ n))).2 v hv
  exact le_of_tendsto_of_tendsto' h1 h2 h3

lemma rpow_le_tangent' (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X Y : ℝ) (hY : 0 < Y) (hX : 0 ≤ X) :
    X ^ p ≤ Y ^ p + p * Y ^ (p - 1) * (X - Y) := by
  have hs : -1 ≤ (X - Y) / Y := by
    rw [le_div_iff₀ hY]; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hp0 hp1
  have hXe : X = Y * (1 + (X - Y) / Y) := by field_simp; ring
  have h1 : 0 ≤ 1 + (X - Y) / Y := by linarith
  calc X ^ p = Y ^ p * (1 + (X - Y) / Y) ^ p := by
        rw [hXe, Real.mul_rpow hY.le h1]; congr 1; congr 1; field_simp; ring
    _ ≤ Y ^ p * (1 + p * ((X - Y) / Y)) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le p)
    _ = Y ^ p + p * Y ^ (p - 1) * (X - Y) := by
        rw [Real.rpow_sub_one hY.ne']; field_simp

lemma sum_two {K : ℕ} (f : Fin K → ℝ) (i j : Fin K) (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → f k = 0) : ∑ k, f k = f i + f j :=
  Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij
    (fun c _ hc => h c hc.1 hc.2)

/-- Every maximizer lies in the open simplex (the slope of `w^α` is infinite at `0`). -/
lemma argmax_pos {K : ℕ} (α e : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (L x : Fin K → ℝ)
    (hx : IsArgmax α e L x) (i : Fin K) : 0 < x i := by
  obtain ⟨⟨hx0, hx1⟩, hmax⟩ := hx
  rcases (hx0 i).lt_or_eq with h | h
  · exact h
  exfalso
  have hxi : x i = 0 := h.symm
  obtain ⟨j, hj⟩ : ∃ j, 0 < x j := by
    by_contra hne
    push Not at hne
    have : ∑ k, x k = 0 := Finset.sum_eq_zero (fun k _ => le_antisymm (hne k) (hx0 k))
    linarith
  have hij : i ≠ j := by intro h'; rw [h'] at hxi; linarith
  have hα0 := hα.1
  have hα1 := hα.2
  set a := α * (1 - α) with ha_def
  have ha : 0 < a := mul_pos hα0 (by linarith)
  set M := (x j / 2) ^ (α - 1) with hM
  have hM0 : 0 ≤ M := Real.rpow_nonneg (by linarith) _
  set C := |e * (L j - L i)| + M / (1 - α) with hC
  have hC0 : 0 ≤ C := add_nonneg (abs_nonneg _) (div_nonneg hM0 (by linarith))
  set D := a * C with hD
  have hD0 : 0 ≤ D := mul_nonneg ha.le hC0
  set t := (D + 1) ^ (-(1 - α)⁻¹) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos (by linarith) _
  set s := min (x j / 2) t with hs
  have hs0 : 0 < s := lt_min (by linarith) ht0
  have hsj : s ≤ x j / 2 := min_le_left _ _
  have hst : s ≤ t := min_le_right _ _
  -- s^(α-1) ≥ D + 1
  have hpow : D + 1 ≤ s ^ (α - 1) := by
    have h1 : t ^ (α - 1) ≤ s ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos hs0 hst (by linarith)
    have h2 : t ^ (α - 1) = D + 1 := by
      rw [ht, ← Real.rpow_mul (by linarith)]
      have : -(1 - α)⁻¹ * (α - 1) = 1 := by
        have : (1 - α) ≠ 0 := by linarith
        field_simp; ring
      rw [this, Real.rpow_one]
    linarith
  have hsa : s ^ α = s ^ (α - 1) * s := by
    rw [← Real.rpow_add_one hs0.ne']; ring_nf
  have hkey : a * C * s < s ^ α := by
    rw [hsa]
    have h := mul_lt_mul_of_pos_right (show a * C < s ^ (α - 1) by linarith [hD]) hs0
    linarith
  -- the competitor
  set v : Fin K → ℝ := fun k => if k = i then s else if k = j then x j - s else x k with hv
  have hvi : v i = s := by simp [hv]
  have hvj : v j = x j - s := by simp [hv, Ne.symm hij]
  have hvk : ∀ k, k ≠ i → k ≠ j → v k = x k := by
    intro k hki hkj; simp [hv, hki, hkj]
  have hvS : v ∈ stdSimplex ℝ (Fin K) := by
    refine ⟨fun k => ?_, ?_⟩
    · by_cases hki : k = i
      · rw [hki, hvi]; exact hs0.le
      by_cases hkj : k = j
      · rw [hkj, hvj]; linarith
      rw [hvk k hki hkj]; exact hx0 k
    · have hd : ∑ k, (v k - x k) = (v i - x i) + (v j - x j) :=
        sum_two _ i j hij (fun k hki hkj => by rw [hvk k hki hkj]; ring)
      rw [Finset.sum_sub_distrib, hvi, hvj, hxi, hx1] at hd
      linarith
  have hdiff : obj α e L v - obj α e L x =
      (gc α e (L i) s - gc α e (L i) 0) + (gc α e (L j) (x j - s) - gc α e (L j) (x j)) := by
    rw [obj_eq, obj_eq, ← Finset.sum_sub_distrib,
      sum_two _ i j hij (fun k hki hkj => by rw [hvk k hki hkj]; ring), hvi, hvj, hxi]
  have htan : x j ^ α ≤ (x j - s) ^ α + α * (x j - s) ^ (α - 1) * (x j - (x j - s)) :=
    rpow_le_tangent' α hα0.le hα1.le (x j) (x j - s) (by linarith) (hx0 j)
  have hMb : (x j - s) ^ (α - 1) ≤ M :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have habs : -(|e * (L j - L i)|) * s ≤ e * s * (L j - L i) := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le (e * (L j - L i))) hs0.le
    linarith
  have hgc : 0 < (gc α e (L i) s - gc α e (L i) 0) +
      (gc α e (L j) (x j - s) - gc α e (L j) (x j)) := by
    simp only [gc]
    rw [Real.zero_rpow hα0.ne']
    have e1 : e * (s * -L i) + (s ^ α - α * s) / a - (e * (0 * -L i) + (0 - α * 0) / a) +
        (e * ((x j - s) * -L j) + ((x j - s) ^ α - α * (x j - s)) / a -
          (e * (x j * -L j) + (x j ^ α - α * x j) / a)) =
        e * s * (L j - L i) + (s ^ α + (x j - s) ^ α - x j ^ α) / a := by
      field_simp; ring
    rw [e1]
    have h3 : α * (x j - s) ^ (α - 1) * s ≤ α * M * s := by
      have := mul_le_mul_of_nonneg_left hMb hα0.le
      exact mul_le_mul_of_nonneg_right this hs0.le
    have h4 : (s ^ α - α * M * s) / a ≤ (s ^ α + (x j - s) ^ α - x j ^ α) / a := by
      apply div_le_div_of_nonneg_right _ ha.le
      have : x j - (x j - s) = s := by ring
      rw [this] at htan
      linarith
    have h5 : (s ^ α - α * M * s) / a = s ^ α / a - M / (1 - α) * s := by
      have : (1 - α) ≠ 0 := by linarith
      rw [ha_def]; field_simp
    have h6 : C * s < s ^ α / a := by
      rw [lt_div_iff₀ ha]; linarith
    have h7 : C * s = |e * (L j - L i)| * s + M / (1 - α) * s := by rw [hC]; ring
    linarith
  have := hmax v hvS
  linarith

lemma hasDerivAt_gc (α e c y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun z => gc α e c z) (e * -c + (α * y ^ (α - 1) - α) / (α * (1 - α))) y := by
  have h1 : HasDerivAt (fun z : ℝ => z ^ α) (α * y ^ (α - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  have h2 : HasDerivAt (fun z : ℝ => e * (z * -c)) (e * (1 * -c)) y :=
    ((hasDerivAt_id' y).mul_const (-c)).const_mul e
  have h3 : HasDerivAt (fun z : ℝ => (z ^ α - α * z) / (α * (1 - α)))
      ((α * y ^ (α - 1) - α * 1) / (α * (1 - α))) y :=
    (h1.sub ((hasDerivAt_id' y).const_mul α)).div_const (α * (1 - α))
  have h4 := h2.add h3
  have h5 : e * (1 * -c) + (α * y ^ (α - 1) - α * 1) / (α * (1 - α)) =
      e * -c + (α * y ^ (α - 1) - α) / (α * (1 - α)) := by ring
  rw [h5] at h4
  exact h4

/-- First-order optimality condition at the (interior) maximizer. -/
lemma first_order {K : ℕ} (α e : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (L x w : Fin K → ℝ)
    (hx : IsArgmax α e L x) (hw : w ∈ stdSimplex ℝ (Fin K)) :
    ∑ i, (w i - x i) * (e * -L i + (α * x i ^ (α - 1) - α) / (α * (1 - α))) ≤ 0 := by
  have hpos := argmax_pos α e hα L x hx
  set g : ℝ → ℝ := fun s => ∑ i, gc α e (L i) (x i + s * (w i - x i)) with hg
  have hder : HasDerivAt g
      (∑ i, (w i - x i) * (e * -L i + (α * x i ^ (α - 1) - α) / (α * (1 - α)))) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have hin : HasDerivAt (fun s : ℝ => x i + s * (w i - x i)) (1 * (w i - x i)) 0 :=
      ((hasDerivAt_id' (0 : ℝ)).mul_const (w i - x i)).const_add (x i)
    have hgc' : HasDerivAt (fun z => gc α e (L i) z)
        (e * -L i + (α * x i ^ (α - 1) - α) / (α * (1 - α))) (x i + 0 * (w i - x i)) := by
      rw [zero_mul, add_zero]; exact hasDerivAt_gc α e (L i) (x i) (hpos i)
    have hc := hgc'.comp (0 : ℝ) hin
    have h5 : (e * -L i + (α * x i ^ (α - 1) - α) / (α * (1 - α))) * (1 * (w i - x i)) =
        (w i - x i) * (e * -L i + (α * x i ^ (α - 1) - α) / (α * (1 - α))) := by ring
    rw [h5] at hc
    exact hc
  have hmax : IsMaxOn g (Set.Icc 0 1) 0 := by
    intro s hs
    show g s ≤ g 0
    have hmem : (fun i => x i + s * (w i - x i)) ∈ stdSimplex ℝ (Fin K) := by
      have := (convex_stdSimplex ℝ (Fin K)) hx.1 hw (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)
        hs.1 (by ring)
      convert this using 1
      funext i; simp; ring
    have h1 := hx.2 _ hmem
    rw [obj_eq, obj_eq] at h1
    simp only [hg, zero_mul, add_zero]
    exact h1
  have hseg : segment ℝ (0 : ℝ) (0 + 1) ⊆ Set.Icc 0 1 := by
    rw [zero_add, segment_eq_Icc zero_le_one]
  have := hmax.localize.hasFDerivWithinAt_nonpos hder.hasDerivWithinAt.hasFDerivWithinAt
    (mem_posTangentConeAt_of_segment_subset hseg)
  simpa using this

/-- `x^(α-1) ≥ 1 + (1-α)(1-x)` on `(0,1]`. -/
lemma rpow_neg_lower (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    1 + (1 - α) * (1 - x) ≤ x ^ (α - 1) := by
  have hα0 := hα.1
  have hα1 := hα.2
  have hb := rpow_one_add_le_one_add_mul_self (by linarith : (-1 : ℝ) ≤ x - 1)
    (by linarith : (0 : ℝ) ≤ 1 - α) (by linarith : 1 - α ≤ 1)
  rw [add_sub_cancel] at hb
  have hprod : x ^ (α - 1) * x ^ (1 - α) = 1 := by
    rw [← Real.rpow_add hx0]; norm_num
  have hp1 : 0 < x ^ (α - 1) := Real.rpow_pos_of_pos hx0 _
  have hp2 : 0 < x ^ (1 - α) := Real.rpow_pos_of_pos hx0 _
  set z := (1 - α) * (1 - x) with hz
  have hz0 : 0 ≤ z := mul_nonneg (by linarith) (by linarith)
  have hle : (1 + z) * x ^ (1 - α) ≤ 1 := by
    have : x ^ (1 - α) ≤ 1 - z := by rw [hz]; linarith
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hle hp1.le]

/-- Second-order (Bregman) bound for the concave power on `[0,1]`. -/
lemma breg_r (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r ^ α ≤ 1 + α * (r - 1) - α * (1 - α) / 2 * (1 - r) ^ 2 := by
  have hα0 := hα.1
  set φ : ℝ → ℝ := fun y => 1 + α * (y - 1) - α * (1 - α) / 2 * (1 - y) ^ 2 - y ^ α with hφ
  have hcont : ContinuousOn φ (Set.Icc 0 1) := by
    have : Continuous (fun y : ℝ => y ^ α) := Real.continuous_rpow_const hα0.le
    exact (by fun_prop : Continuous φ).continuousOn
  have hderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt φ (α - α * (1 - α) / 2 * (2 * (1 - y) * (-1)) - α * y ^ (α - 1)) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => z ^ α) (α * y ^ (α - 1)) y :=
      Real.hasDerivAt_rpow_const (Or.inl hy.1.ne')
    have h2 : HasDerivAt (fun z : ℝ => (1 - z) ^ 2) (2 * (1 - y) * (-1)) y := by
      have := ((hasDerivAt_id' y).const_sub 1).fun_pow' 2
      exact this.congr_deriv (by simp [Finset.sum_range_succ]; ring)
    have h3 : HasDerivAt (fun z : ℝ => 1 + α * (z - 1)) α y := by
      have := (((hasDerivAt_id' y).sub_const 1).const_mul α).const_add 1
      simpa using this
    exact (h3.sub (h2.const_mul (α * (1 - α) / 2))).sub h1
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hcont
    · intro y hy
      rw [interior_Icc] at hy
      exact (hderiv y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hderiv y hy).deriv]
      have := rpow_neg_lower α hα y hy.1 hy.2.le
      nlinarith
  have h := hanti ⟨hr0, hr1⟩ ⟨zero_le_one, le_refl 1⟩ hr1
  simp only [hφ, Real.one_rpow] at h
  nlinarith

/-- Bregman lower bound: `x^α + α x^(α-1)(w-x) - w^α ≥ α(1-α)/2 · (x-w)² x^(α-2)` for `0 ≤ w ≤ x`. -/
lemma breg_bound (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (x w : ℝ) (hx : 0 < x) (hw0 : 0 ≤ w)
    (hwx : w ≤ x) :
    α * (1 - α) / 2 * (x - w) ^ 2 * x ^ (α - 2) ≤ x ^ α + α * x ^ (α - 1) * (w - x) - w ^ α := by
  have h := breg_r α hα (w / x) (div_nonneg hw0 hx.le) ((div_le_one hx).2 hwx)
  rw [Real.div_rpow hw0 hx.le] at h
  have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx _
  have e1 : x ^ (α - 1) = x ^ α / x := Real.rpow_sub_one hx.ne' α
  have e2 : x ^ (α - 2) = x ^ α / x ^ 2 := by
    rw [Real.rpow_sub hx, Real.rpow_two]
  rw [e1, e2]
  have h' := mul_le_mul_of_nonneg_left h hxa.le
  have e3 : x ^ α * (w ^ α / x ^ α) = w ^ α := by field_simp
  rw [e3] at h'
  have e4 : x ^ α * (1 + α * (w / x - 1) - α * (1 - α) / 2 * (1 - w / x) ^ 2) =
      x ^ α + α * (x ^ α / x) * (w - x) - α * (1 - α) / 2 * (x - w) ^ 2 * (x ^ α / x ^ 2) := by
    field_simp
  rw [e4] at h'
  linarith

/-- Per-coordinate stability bound. -/
lemma coord_stab (α e : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (he : 0 < e) (x w l : ℝ) (hx : 0 < x)
    (hw : 0 ≤ w) (hl : 0 ≤ l) :
    e * (x - w) * l - (x ^ α + α * x ^ (α - 1) * (w - x) - w ^ α) / (α * (1 - α)) ≤
      e ^ 2 / 2 * x ^ (2 - α) * l ^ 2 := by
  have hα0 := hα.1
  have hα1 := hα.2
  have ha : 0 < α * (1 - α) := mul_pos hα0 (by linarith)
  have hP : 0 < x ^ (2 - α) := Real.rpow_pos_of_pos hx _
  have hc : 0 < x ^ (α - 2) := Real.rpow_pos_of_pos hx _
  have hPc : x ^ (2 - α) * x ^ (α - 2) = 1 := by
    rw [← Real.rpow_add hx]; norm_num
  rcases le_or_gt x w with hxw | hwx
  · have ht := rpow_le_tangent' α hα0.le hα1.le w x hx hw
    have hD : 0 ≤ (x ^ α + α * x ^ (α - 1) * (w - x) - w ^ α) / (α * (1 - α)) :=
      div_nonneg (by linarith) ha.le
    have h1 : e * (x - w) * l ≤ 0 := by
      have : 0 ≤ e * (w - x) * l := mul_nonneg (mul_nonneg he.le (by linarith)) hl
      nlinarith
    have h2 : 0 ≤ e ^ 2 / 2 * x ^ (2 - α) * l ^ 2 := by positivity
    linarith
  · have hb := breg_bound α hα x w hx hw hwx.le
    have hD : (x - w) ^ 2 * x ^ (α - 2) / 2 ≤
        (x ^ α + α * x ^ (α - 1) * (w - x) - w ^ α) / (α * (1 - α)) := by
      rw [le_div_iff₀ ha]; nlinarith
    set s := x - w
    set c := x ^ (α - 2)
    set P := x ^ (2 - α)
    have hsq : 0 ≤ P * (e * l - s * c) ^ 2 := mul_nonneg hP.le (sq_nonneg _)
    have : e * s * l - s ^ 2 * c / 2 ≤ e ^ 2 / 2 * P * l ^ 2 := by
      have hexp : P * (e * l - s * c) ^ 2 =
          P * e ^ 2 * l ^ 2 - 2 * (P * c) * e * l * s + (P * c) * s ^ 2 * c := by ring
      rw [hPc] at hexp
      nlinarith
    linarith

/-- KEY per-round stability inequality (paper Lemma 11 in pathwise form). -/
lemma key_round {K : ℕ} (α e : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (he : 0 < e)
    (L x l w : Fin K → ℝ) (hx : IsArgmax α e L x) (hl : ∀ i, 0 ≤ l i)
    (hw : w ∈ stdSimplex ℝ (Fin K)) :
    e * (∑ i, x i * l i) + obj α e (fun i => L i + l i) w - obj α e L x ≤
      e ^ 2 / 2 * ∑ i, x i ^ (2 - α) * l i ^ 2 := by
  have fo := first_order α e hα L x w hx hw
  have hpos := argmax_pos α e hα L x hx
  rw [obj_eq, obj_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  have hterm : ∀ i, e * (x i * l i) + gc α e (L i + l i) (w i) - gc α e (L i) (x i) ≤
      (w i - x i) * (e * -L i + (α * x i ^ (α - 1) - α) / (α * (1 - α))) +
        e ^ 2 / 2 * (x i ^ (2 - α) * l i ^ 2) := by
    intro i
    have hcs := coord_stab α e hα he (x i) (w i) (l i) (hpos i) (hw.1 i) (hl i)
    have hid : e * (x i * l i) + gc α e (L i + l i) (w i) - gc α e (L i) (x i) =
        (w i - x i) * (e * -L i + (α * x i ^ (α - 1) - α) / (α * (1 - α))) +
          (e * (x i - w i) * l i -
            (x i ^ α + α * x i ^ (α - 1) * (w i - x i) - w i ^ α) / (α * (1 - α))) := by
      have : α * (1 - α) ≠ 0 := (mul_pos hα.1 (by linarith [hα.2])).ne'
      unfold gc; field_simp; ring
    rw [hid]
    have : e ^ 2 / 2 * (x i ^ (2 - α) * l i ^ 2) = e ^ 2 / 2 * x i ^ (2 - α) * l i ^ 2 := by ring
    linarith
  calc ∑ i, (e * (x i * l i) + gc α e (L i + l i) (w i) - gc α e (L i) (x i))
      ≤ ∑ i, ((w i - x i) * (e * -L i + (α * x i ^ (α - 1) - α) / (α * (1 - α))) +
          e ^ 2 / 2 * (x i ^ (2 - α) * l i ^ 2)) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, (w i - x i) * (e * -L i + (α * x i ^ (α - 1) - α) / (α * (1 - α)))) +
          ∑ i, e ^ 2 / 2 * (x i ^ (2 - α) * l i ^ 2) := Finset.sum_add_distrib
    _ ≤ ∑ i, e ^ 2 / 2 * (x i ^ (2 - α) * l i ^ 2) := by linarith

/-- `key_round` divided by the learning rate. -/
lemma key_div {K : ℕ} (α e : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (he : 0 < e)
    (L x l w : Fin K → ℝ) (hx : IsArgmax α e L x) (hl : ∀ i, 0 ≤ l i)
    (hw : w ∈ stdSimplex ℝ (Fin K)) :
    (∑ i, x i * l i) + ((∑ i, w i * -(L i + l i)) - tsallisPsi α (fun _ => 1) w / e) -
      ((∑ i, x i * -L i) - tsallisPsi α (fun _ => 1) x / e) ≤
      e / 2 * ∑ i, x i ^ (2 - α) * l i ^ 2 := by
  have h := key_round α e hα he L x l w hx hl hw
  unfold obj at h
  set A := ∑ i, x i * l i
  set B := ∑ i, w i * -(L i + l i)
  set C := ∑ i, x i * -L i
  set S := ∑ i, x i ^ (2 - α) * l i ^ 2
  set Pw := tsallisPsi α (fun _ => 1) w
  set Px := tsallisPsi α (fun _ => 1) x
  have h1 : e * (A + (B - Pw / e) - (C - Px / e)) ≤ e * (e / 2 * S) := by
    have : e * (A + (B - Pw / e) - (C - Px / e)) = e * A + (e * B - Pw) - (e * C - Px) := by
      field_simp
    rw [this]; nlinarith
  exact le_of_mul_le_mul_left h1 he

/-- Pathwise FTRL telescoping (the stability + penalty decomposition). -/
lemma telescope {K : ℕ} (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (e : ℕ → ℝ)
    (x l Lh : ℕ → Fin K → ℝ) (hL1 : ∀ i, Lh 1 i = 0) (hLs : ∀ t i, Lh (t + 1) i = Lh t i + l t i)
    (he : ∀ t, 1 ≤ t → 0 < e t) (hx : ∀ t, 1 ≤ t → IsArgmax α (e t) (Lh t) (x t))
    (hl : ∀ t i, 0 ≤ l t i) :
    ∀ T, 1 ≤ T → ∀ w ∈ stdSimplex ℝ (Fin K),
      (∑ t ∈ Icc 1 T, ∑ i, x t i * l t i) +
        ((∑ i, w i * -Lh (T + 1) i) - tsallisPsi α (fun _ => 1) w / e T) +
        tsallisPsi α (fun _ => 1) (x 1) / e 1 +
        ∑ t ∈ Icc 2 T, (1 / e t - 1 / e (t - 1)) * tsallisPsi α (fun _ => 1) (x t) ≤
      ∑ t ∈ Icc 1 T, e t / 2 * ∑ i, x t i ^ (2 - α) * l t i ^ 2 := by
  intro T hT
  induction T, hT using Nat.le_induction with
  | base =>
    intro w hw
    have h := key_div α (e 1) hα (he 1 le_rfl) (Lh 1) (x 1) (l 1) w (hx 1 le_rfl) (hl 1) hw
    have hL2 : ∀ i, Lh (1 + 1) i = Lh 1 i + l 1 i := hLs 1
    simp only [Finset.Icc_self, Finset.sum_singleton, hL2]
    have hC : (∑ i, x 1 i * -Lh 1 i) = 0 := by simp [hL1]
    rw [hC] at h
    have h2 : Finset.Icc 2 1 = ∅ := by decide
    rw [h2, Finset.sum_empty]
    linarith
  | succ T hT ih =>
    intro w hw
    have hIH := ih (x (T + 1)) (hx (T + 1) (by omega)).1
    have h := key_div α (e (T + 1)) hα (he (T + 1) (by omega)) (Lh (T + 1)) (x (T + 1))
      (l (T + 1)) w (hx (T + 1) (by omega)) (hl (T + 1)) hw
    have hL2 : ∀ i, Lh (T + 1 + 1) i = Lh (T + 1) i + l (T + 1) i := hLs (T + 1)
    simp only [hL2]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T + 1), Finset.sum_Icc_succ_top (by omega : 2 ≤ T + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ T + 1)]
    have hsub : T + 1 - 1 = T := by omega
    rw [hsub]
    have heT : 0 < e T := he T hT
    have heT1 : 0 < e (T + 1) := he (T + 1) (by omega)
    have hid : (1 / e (T + 1) - 1 / e T) * tsallisPsi α (fun _ => 1) (x (T + 1)) =
        tsallisPsi α (fun _ => 1) (x (T + 1)) / e (T + 1) -
          tsallisPsi α (fun _ => 1) (x (T + 1)) / e T := by
      field_simp
    rw [hid]
    linarith

section B
open TsallisINF.Half RegretBandits.Adversarial MeasureTheory

lemma tsallisPsi_half {K : ℕ} (v : Fin K → ℝ) :
    tsallisPsi (1 / 2) (fun _ => 1) v = -4 * ∑ i, (Real.sqrt (v i) - v i / 2) := by
  unfold tsallisPsi
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.sqrt_eq_rpow]
  ring

lemma obj_half {K : ℕ} (e : ℝ) (he : e ≠ 0) (L v : Fin K → ℝ) :
    obj (1 / 2) e L v = e * ((∑ i, v i * -L i) - psiHalf e v) := by
  unfold obj psiHalf
  rw [tsallisPsi_half]
  field_simp
  ring_nf

lemma isArgmax_of {K : ℕ} (e : ℝ) (he : 0 < e) (L x : Fin K → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin K))
    (hmax : ∀ v ∈ stdSimplex ℝ (Fin K),
      (∑ i, v i * -L i) - psiHalf e v ≤ (∑ i, x i * -L i) - psiHalf e x) :
    IsArgmax (1 / 2) e L x := by
  refine ⟨hx, fun v hv => ?_⟩
  rw [obj_half e he.ne', obj_half e he.ne']
  exact mul_le_mul_of_nonneg_left (hmax v hv) he.le

lemma half_mem : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num

lemma W_eq_G {K : ℕ} {Ω : Type*} (hK : 0 < K) (η : ℕ → ℝ) (hη : ∀ s, 1 ≤ s → 0 < η s)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsTsallisINF η est W) (t : ℕ) (ht : 1 ≤ t) (ω : Ω)
    (h : ℕ → Fin K) : W t ω h = G (1 / 2) (η t) (fun i => Lhat est t ω h i) :=
  eq_G hK (1 / 2) (η t) half_mem _ _
    (isArgmax_of (η t) (hη t ht) _ _ (hW t ht ω h).1 (hW t ht ω h).2)

lemma W_causal {K : ℕ} {Ω : Type*} (hK : 0 < K) (η : ℕ → ℝ) (hη : ∀ s, 1 ≤ s → 0 < η s)
    (adv : Ω → Adversary K) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsTsallisINF η (estRV η adv W) W) :
    ∀ t, 1 ≤ t → ∀ ω h h', AgreeBefore t h h' → W t ω h = W t ω h' := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht ω h h' hag
  rw [W_eq_G hK η hη _ W hW t ht ω h, W_eq_G hK η hη _ W hW t ht ω h']
  congr 1
  funext i
  unfold Lhat
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_Ico] at hs
  have hs' : h s = h' s := hag s hs.1 hs.2
  have hag' : AgreeBefore s h h' := fun r hr1 hr2 => hag r hr1 (lt_trans hr2 hs.2)
  have hadv : (adv ω).val s h = (adv ω).val s h' := (adv ω).nonanticipating s h h' hag'
  have hWs : W s ω h = W s ω h' := ih s hs.2 hs.1 ω h h' hag'
  simp only [estRV, hs', hadv, hWs]

lemma W_measurable {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (hK : 0 < K) (η : ℕ → ℝ)
    (hη : ∀ s, 1 ≤ s → 0 < η s) (adv : Ω → Adversary K)
    (hadv : ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsTsallisINF η (estRV η adv W) W) :
    ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => W t ω h i) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht h i
  have hL : Measurable (fun ω => (fun j => Lhat (estRV η adv W) t ω h j)) := by
    apply measurable_pi_lambda
    intro j
    unfold Lhat
    apply Finset.measurable_fun_sum
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hWm := ih s hs.2 hs.1 h j
    have hB : Measurable (fun ω => if η s ^ 2 ≤ W s ω h j then (1 / 2 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_const hWm) measurable_const measurable_const
    by_cases hj : h s = j
    · simp only [estRV, hj, if_true]
      exact (((hadv s hs.1 h j).sub hB).div hWm).add hB
    · simp only [estRV, hj, if_false, zero_add]
      exact hB
  have hG : Measurable (fun ω => G (1 / 2) (η t) (fun j => Lhat (estRV η adv W) t ω h j)) :=
    (G_continuous hK (1 / 2) (η t) half_mem).measurable.comp hL
  have : (fun ω => W t ω h i) =
      fun ω => G (1 / 2) (η t) (fun j => Lhat (estRV η adv W) t ω h j) i := by
    funext ω; rw [W_eq_G hK η hη _ W hW t ht ω h]
  rw [this]
  exact (measurable_pi_apply i).comp hG

end B

end SArgmax

section STree

open Finset TsallisINF.Half RegretBandits.Adversarial

/-- Expectation over the action tree for a fixed seed (the integrand of `expect`). -/
noncomputable def E {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ)
    (F : (ℕ → Fin K) → ℝ) : ℝ :=
  ∑ a : Fin T → Fin K,
    (∏ t ∈ Finset.Icc 1 T, p t (extend i₀ T a) (extend i₀ T a t)) * F (extend i₀ T a)

lemma extend_snoc {K : ℕ} (i₀ : Fin K) (T : ℕ) (a : Fin T → Fin K) (j : Fin K) :
    extend i₀ (T + 1) (Fin.snoc a j) = Function.update (extend i₀ T a) (T + 1) j := by
  funext s
  by_cases hs : s = T + 1
  · subst hs
    simp [extend, Fin.snoc]
  · rw [Function.update_of_ne hs]
    by_cases h1 : 1 ≤ s ∧ s ≤ T
    · have h2 : 1 ≤ s ∧ s ≤ T + 1 := ⟨h1.1, by omega⟩
      simp only [extend, dif_pos h1, dif_pos h2, Fin.snoc]
      have h3 : s - 1 < T := by omega
      simp [h3]
    · have h2 : ¬ (1 ≤ s ∧ s ≤ T + 1) := by omega
      simp only [extend, dif_neg h1, dif_neg h2]

lemma sum_snoc {K T : ℕ} (g : (Fin (T + 1) → Fin K) → ℝ) :
    ∑ b, g b = ∑ a : Fin T → Fin K, ∑ j, g (Fin.snoc a j) := by
  rw [← (Fin.snocEquiv (fun _ => Fin K)).sum_comp, Fintype.sum_prod_type_right]
  rfl

/-- Causality of the weights: round `s` weights depend only on rounds `< s`. -/
def Causal {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) : Prop :=
  ∀ s, 1 ≤ s → ∀ h h', AgreeBefore s h h' → p s h = p s h'

lemma E_succ {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hc : Causal p) (i₀ : Fin K) (T : ℕ)
    (F : (ℕ → Fin K) → ℝ) :
    E p i₀ (T + 1) F =
      E p i₀ T (fun h => ∑ j, p (T + 1) h j * F (Function.update h (T + 1) j)) := by
  unfold E
  rw [sum_snoc]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [extend_snoc, Finset.prod_Icc_succ_top (by omega : 1 ≤ T + 1)]
  have hprod : ∏ t ∈ Icc 1 T, p t (Function.update (extend i₀ T a) (T + 1) j)
      (Function.update (extend i₀ T a) (T + 1) j t) =
      ∏ t ∈ Icc 1 T, p t (extend i₀ T a) (extend i₀ T a t) := by
    apply Finset.prod_congr rfl
    intro t ht
    rw [Finset.mem_Icc] at ht
    have hne : t ≠ T + 1 := by omega
    rw [Function.update_of_ne hne,
      hc t ht.1 (Function.update (extend i₀ T a) (T + 1) j) (extend i₀ T a)
        (fun s _ hs2 => Function.update_of_ne (by omega) _ _)]
  rw [hprod, Function.update_self,
    hc (T + 1) (by omega) _ (extend i₀ T a) (fun s _ hs => Function.update_of_ne (by omega) _ _)]
  ring

lemma E_zero {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K)
    (F : (ℕ → Fin K) → ℝ) : E p i₀ 0 F = F (fun _ => i₀) := by
  unfold E
  rw [Fintype.sum_unique]
  have : extend i₀ 0 default = fun _ => i₀ := by
    funext s; unfold extend; rw [dif_neg (by omega)]
  rw [this]
  simp

lemma E_congr {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ)
    (F G : (ℕ → Fin K) → ℝ) (h : ∀ h, F h = G h) : E p i₀ T F = E p i₀ T G := by
  have : F = G := funext h
  rw [this]

lemma E_const {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hc : Causal p)
    (hsum : ∀ s, 1 ≤ s → ∀ h, ∑ j, p s h j = 1) (i₀ : Fin K) (T : ℕ) (c : ℝ) :
    E p i₀ T (fun _ => c) = c := by
  induction T with
  | zero => exact E_zero p i₀ _
  | succ T ih =>
    rw [E_succ p hc]
    rw [E_congr p i₀ T _ (fun _ => c) (fun h => by rw [← Finset.sum_mul, hsum _ (by omega), one_mul])]
    exact ih

lemma E_sum {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ) {ι : Type*}
    (S : Finset ι) (g : ι → (ℕ → Fin K) → ℝ) :
    E p i₀ T (fun h => ∑ x ∈ S, g x h) = ∑ x ∈ S, E p i₀ T (g x) := by
  unfold E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma E_add {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ)
    (F G : (ℕ → Fin K) → ℝ) : E p i₀ T (fun h => F h + G h) = E p i₀ T F + E p i₀ T G := by
  unfold E
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

lemma E_sub {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ)
    (F G : (ℕ → Fin K) → ℝ) : E p i₀ T (fun h => F h - G h) = E p i₀ T F - E p i₀ T G := by
  unfold E
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

lemma E_mul {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ) (c : ℝ)
    (F : (ℕ → Fin K) → ℝ) : E p i₀ T (fun h => c * F h) = c * E p i₀ T F := by
  unfold E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; ring

lemma E_mono {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hp : ∀ s, 1 ≤ s → ∀ h j, 0 ≤ p s h j)
    (i₀ : Fin K) (T : ℕ) (F G : (ℕ → Fin K) → ℝ) (hFG : ∀ h, F h ≤ G h) :
    E p i₀ T F ≤ E p i₀ T G := by
  unfold E
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left (hFG _)
  exact Finset.prod_nonneg (fun t ht => hp _ (Finset.mem_Icc.mp ht).1 _ _)

/-- `F` depends only on the rounds `1, …, t`. -/
def DepUpTo {K : ℕ} (t : ℕ) (F : (ℕ → Fin K) → ℝ) : Prop :=
  ∀ h h', (∀ s, 1 ≤ s → s ≤ t → h s = h' s) → F h = F h'

lemma E_marg_succ {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hc : Causal p)
    (hsum : ∀ s, 1 ≤ s → ∀ h, ∑ j, p s h j = 1) (i₀ : Fin K) (T : ℕ)
    (F : (ℕ → Fin K) → ℝ) (hF : DepUpTo T F) : E p i₀ (T + 1) F = E p i₀ T F := by
  rw [E_succ p hc]
  apply E_congr
  intro h
  have : ∀ j, F (Function.update h (T + 1) j) = F h := fun j =>
    hF _ _ (fun s _ hs => Function.update_of_ne (by omega) _ _)
  simp_rw [this]
  rw [← Finset.sum_mul, hsum _ (by omega), one_mul]

lemma DepUpTo.mono {K : ℕ} {t t' : ℕ} (htt : t ≤ t') {F : (ℕ → Fin K) → ℝ} (hF : DepUpTo t F) :
    DepUpTo t' F :=
  fun h h' hh => hF h h' (fun s h1 h2 => hh s h1 (le_trans h2 htt))

lemma E_marg {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hc : Causal p)
    (hsum : ∀ s, 1 ≤ s → ∀ h, ∑ j, p s h j = 1) (i₀ : Fin K) (t T : ℕ) (htT : t ≤ T)
    (F : (ℕ → Fin K) → ℝ) (hF : DepUpTo t F) : E p i₀ T F = E p i₀ t F := by
  induction T, htT using Nat.le_induction with
  | base => rfl
  | succ T hT ih =>
    rw [E_marg_succ p hc hsum i₀ T F (hF.mono hT), ih]

/-- Conditioning on the past at round `t ≥ 1`. -/
lemma E_cond {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hc : Causal p)
    (hsum : ∀ s, 1 ≤ s → ∀ h, ∑ j, p s h j = 1) (i₀ : Fin K) (t T : ℕ) (ht : 1 ≤ t)
    (htT : t ≤ T) (F : (ℕ → Fin K) → ℝ) (hF : DepUpTo t F) :
    E p i₀ T F = E p i₀ (t - 1) (fun h => ∑ j, p t h j * F (Function.update h t j)) := by
  rw [E_marg p hc hsum i₀ t T htT F hF]
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [E_succ p hc]
  rfl

end STree

section SRV

open Finset


/-- Lemma 19 coordinate inequality in square-root variables (`s = √x`, `u = √w`). -/
lemma coord_sq (e s u c : ℝ) (he : 0 < e) (hs : 0 < s) 
    (hd : e * max (-c) 0 * s ≤ 1) :
    e * (s ^ 2 - u ^ 2) * c - 2 * (u - s) ^ 2 / s ≤
      e ^ 2 / 2 * s ^ 3 * c ^ 2 + e ^ 3 / 2 * s ^ 4 * (max (-c) 0) ^ 3 := by
  have hsplit : e * (s ^ 2 - u ^ 2) * c - 2 * (u - s) ^ 2 / s =
      (e * (s ^ 2 - u ^ 2) * c * s - 2 * (u - s) ^ 2) / s := by
    field_simp
  rw [hsplit, div_le_iff₀ hs]
  rcases le_or_gt 0 c with hc | hc
  · rw [max_eq_right (by linarith : -c ≤ 0)]
    have h1 : 0 ≤ e * c * s * (u - s) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg he.le hc) hs.le) (sq_nonneg _)
    nlinarith [sq_nonneg (u - s + e * c * s ^ 2 / 2)]
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ -c)] at hd ⊢
    set d := -c with hdd
    have hd0 : 0 < d := by linarith
    have hc' : c = -d := by linarith
    rw [hc']
    set y := e * d * s with hy
    set m := e * d * s ^ 2 with hm
    have hy0 : 0 < y := by positivity
    have hy1 : y ≤ 1 := hd
    have key : (2 - y) * ((e ^ 2 / 2 * s ^ 3 * (-d) ^ 2 + e ^ 3 / 2 * s ^ 4 * d ^ 3) * s -
        (e * (s ^ 2 - u ^ 2) * (-d) * s - 2 * (u - s) ^ 2)) =
        ((2 - y) * (u - s) - m) ^ 2 + m ^ 2 * y * (1 - y) / 2 := by
      rw [hy, hm]; ring
    have hpos : 0 ≤ ((2 - y) * (u - s) - m) ^ 2 + m ^ 2 * y * (1 - y) / 2 := by
      have : 0 ≤ m ^ 2 * y * (1 - y) / 2 :=
        div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hy0.le) (by linarith)) (by norm_num)
      positivity
    have h2y : 0 < 2 - y := by linarith
    have : 0 ≤ (e ^ 2 / 2 * s ^ 3 * (-d) ^ 2 + e ^ 3 / 2 * s ^ 4 * d ^ 3) * s -
        (e * (s ^ 2 - u ^ 2) * (-d) * s - 2 * (u - s) ^ 2) := by
      by_contra hneg
      have := mul_neg_of_pos_of_neg h2y (lt_of_not_ge hneg)
      linarith
    linarith


lemma coord_rpow (e x w c : ℝ) (he : 0 < e) (hx : 0 < x) (hw : 0 ≤ w)
    (hd : e * max (-c) 0 * Real.sqrt x ≤ 1) :
    e * (x - w) * c -
        (x ^ (1 / 2 : ℝ) + 1 / 2 * x ^ ((1 / 2 : ℝ) - 1) * (w - x) - w ^ (1 / 2 : ℝ)) /
          (1 / 2 * (1 - 1 / 2)) ≤
      e ^ 2 / 2 * Real.sqrt x ^ 3 * c ^ 2 + e ^ 3 / 2 * Real.sqrt x ^ 4 * (max (-c) 0) ^ 3 := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ x = s ^ 2 :=
    ⟨Real.sqrt x, Real.sqrt_pos.2 hx, (Real.sq_sqrt hx.le).symm⟩
  obtain ⟨u, hu0, rfl⟩ : ∃ u, 0 ≤ u ∧ w = u ^ 2 :=
    ⟨Real.sqrt w, Real.sqrt_nonneg w, (Real.sq_sqrt hw).symm⟩
  have hss : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hs0.le
  have h1 : (s ^ 2) ^ (1 / 2 : ℝ) = s := by rw [← Real.sqrt_eq_rpow, hss]
  have h3 : (u ^ 2) ^ (1 / 2 : ℝ) = u := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hu0]
  have h2 : (s ^ 2) ^ ((1 / 2 : ℝ) - 1) = s / s ^ 2 := by
    rw [Real.rpow_sub_one (by positivity), h1]
  rw [hss] at hd ⊢
  rw [h1, h2, h3]
  have heq : e * (s ^ 2 - u ^ 2) * c - (s + 1 / 2 * (s / s ^ 2) * (u ^ 2 - s ^ 2) - u) /
      (1 / 2 * (1 - 1 / 2)) = e * (s ^ 2 - u ^ 2) * c - 2 * (u - s) ^ 2 / s := by
    field_simp; ring
  rw [heq]
  exact coord_sq e s u c he hs0 hd

/-- Pathwise Lemma 19 (alpha = 1/2) with the shift `z`, objective form. -/
lemma key_round_RV {K : ℕ} (e : ℝ) (he : 0 < e) (L x l w : Fin K → ℝ) (z : ℝ)
    (hx : IsArgmax (1 / 2) e L x)
    (hz : ∀ i, e * max (-(l i - z)) 0 * Real.sqrt (x i) ≤ 1)
    (hw : w ∈ stdSimplex ℝ (Fin K)) :
    e * (∑ i, x i * l i) + obj (1 / 2) e (fun i => L i + l i) w - obj (1 / 2) e L x ≤
      ∑ i, (e ^ 2 / 2 * Real.sqrt (x i) ^ 3 * (l i - z) ^ 2 +
        e ^ 3 / 2 * Real.sqrt (x i) ^ 4 * (max (-(l i - z)) 0) ^ 3) := by
  have hα := half_mem
  have fo := first_order (1 / 2) e hα L x w hx hw
  have hpos := argmax_pos (1 / 2) e hα L x hx
  have hx1 : ∑ i, x i = 1 := hx.1.2
  have hw1 : ∑ i, w i = 1 := hw.2
  set c : Fin K → ℝ := fun i => l i - z with hc
  have hshift : e * (∑ i, x i * l i) + obj (1 / 2) e (fun i => L i + l i) w =
      e * (∑ i, x i * c i) + obj (1 / 2) e (fun i => L i + c i) w := by
    unfold obj
    have a1 : ∑ i, x i * l i = ∑ i, x i * c i + z := by
      simp only [hc, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hx1]; ring
    have a2 : ∑ i, w i * -(L i + l i) = ∑ i, w i * -(L i + c i) - z := by
      have : ∀ i, w i * -(L i + l i) = w i * -(L i + c i) - w i * z := by
        intro i; simp only [hc]; ring
      simp only [this, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1]; ring
    rw [a1, a2]; ring
  rw [hshift, obj_eq, obj_eq, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  have hterm : ∀ i, e * (x i * c i) + gc (1 / 2) e (L i + c i) (w i) - gc (1 / 2) e (L i) (x i) ≤
      (w i - x i) * (e * -L i + (1 / 2 * x i ^ ((1 / 2 : ℝ) - 1) - 1 / 2) /
        (1 / 2 * (1 - 1 / 2))) +
        (e ^ 2 / 2 * Real.sqrt (x i) ^ 3 * (l i - z) ^ 2 +
          e ^ 3 / 2 * Real.sqrt (x i) ^ 4 * (max (-(l i - z)) 0) ^ 3) := by
    intro i
    have hcs := coord_rpow e (x i) (w i) (c i) he (hpos i) (hw.1 i) (hz i)
    have hid : e * (x i * c i) + gc (1 / 2) e (L i + c i) (w i) - gc (1 / 2) e (L i) (x i) =
        (w i - x i) * (e * -L i + (1 / 2 * x i ^ ((1 / 2 : ℝ) - 1) - 1 / 2) /
          (1 / 2 * (1 - 1 / 2))) +
          (e * (x i - w i) * c i -
            (x i ^ (1 / 2 : ℝ) + 1 / 2 * x i ^ ((1 / 2 : ℝ) - 1) * (w i - x i) -
              w i ^ (1 / 2 : ℝ)) / (1 / 2 * (1 - 1 / 2))) := by
      unfold gc; field_simp; ring
    rw [hid]
    simp only [hc] at hcs ⊢
    linarith
  calc ∑ i, (e * (x i * c i) + gc (1 / 2) e (L i + c i) (w i) - gc (1 / 2) e (L i) (x i))
      ≤ ∑ i, ((w i - x i) * (e * -L i + (1 / 2 * x i ^ ((1 / 2 : ℝ) - 1) - 1 / 2) /
          (1 / 2 * (1 - 1 / 2))) +
          (e ^ 2 / 2 * Real.sqrt (x i) ^ 3 * (l i - z) ^ 2 +
            e ^ 3 / 2 * Real.sqrt (x i) ^ 4 * (max (-(l i - z)) 0) ^ 3)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, (w i - x i) * (e * -L i + (1 / 2 * x i ^ ((1 / 2 : ℝ) - 1) - 1 / 2) /
          (1 / 2 * (1 - 1 / 2)))) +
          ∑ i, (e ^ 2 / 2 * Real.sqrt (x i) ^ 3 * (l i - z) ^ 2 +
            e ^ 3 / 2 * Real.sqrt (x i) ^ 4 * (max (-(l i - z)) 0) ^ 3) := Finset.sum_add_distrib
    _ ≤ _ := by linarith

end SRV

section STel

open Finset

/-- Divided form of `key_round_RV`. -/
lemma key_div_RV {K : ℕ} (e : ℝ) (he : 0 < e) (L x l w : Fin K → ℝ) (z : ℝ)
    (hx : IsArgmax (1 / 2) e L x)
    (hz : ∀ i, e * max (-(l i - z)) 0 * Real.sqrt (x i) ≤ 1)
    (hw : w ∈ stdSimplex ℝ (Fin K)) :
    (∑ i, x i * l i) + ((∑ i, w i * -(L i + l i)) - tsallisPsi (1 / 2) (fun _ => 1) w / e) -
      ((∑ i, x i * -L i) - tsallisPsi (1 / 2) (fun _ => 1) x / e) ≤
      ∑ i, (e / 2 * Real.sqrt (x i) ^ 3 * (l i - z) ^ 2 +
        e ^ 2 / 2 * Real.sqrt (x i) ^ 4 * (max (-(l i - z)) 0) ^ 3) := by
  have h := key_round_RV e he L x l w z hx hz hw
  unfold obj at h
  set A := ∑ i, x i * l i
  set B := ∑ i, w i * -(L i + l i)
  set C := ∑ i, x i * -L i
  set Pw := tsallisPsi (1 / 2) (fun _ => 1) w
  set Px := tsallisPsi (1 / 2) (fun _ => 1) x
  have hS : ∑ i, (e ^ 2 / 2 * Real.sqrt (x i) ^ 3 * (l i - z) ^ 2 +
        e ^ 3 / 2 * Real.sqrt (x i) ^ 4 * (max (-(l i - z)) 0) ^ 3) =
      e * ∑ i, (e / 2 * Real.sqrt (x i) ^ 3 * (l i - z) ^ 2 +
        e ^ 2 / 2 * Real.sqrt (x i) ^ 4 * (max (-(l i - z)) 0) ^ 3) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hS] at h
  set S := ∑ i, (e / 2 * Real.sqrt (x i) ^ 3 * (l i - z) ^ 2 +
        e ^ 2 / 2 * Real.sqrt (x i) ^ 4 * (max (-(l i - z)) 0) ^ 3)
  have h1 : e * (A + (B - Pw / e) - (C - Px / e)) ≤ e * S := by
    have : e * (A + (B - Pw / e) - (C - Px / e)) = e * A + (e * B - Pw) - (e * C - Px) := by
      field_simp
    rw [this]; linarith
  exact le_of_mul_le_mul_left h1 he

/-- For nonnegative estimates the round term is at most the played loss estimate. -/
lemma round_nonneg {K : ℕ} (e : ℝ) (he : 0 < e) (L x l w : Fin K → ℝ)
    (hx : IsArgmax (1 / 2) e L x) (hl : ∀ i, 0 ≤ l i) (hw : w ∈ stdSimplex ℝ (Fin K)) :
    (∑ i, x i * l i) + ((∑ i, w i * -(L i + l i)) - tsallisPsi (1 / 2) (fun _ => 1) w / e) -
      ((∑ i, x i * -L i) - tsallisPsi (1 / 2) (fun _ => 1) x / e) ≤ ∑ i, x i * l i := by
  have h := hx.2 w hw
  unfold obj at h
  have hmono : (∑ i, w i * -(L i + l i)) ≤ ∑ i, w i * -L i := by
    apply Finset.sum_le_sum; intro i _
    have := mul_nonneg (hw.1 i) (hl i)
    nlinarith
  have h2 : (∑ i, w i * -L i) - tsallisPsi (1 / 2) (fun _ => 1) w / e ≤
      (∑ i, x i * -L i) - tsallisPsi (1 / 2) (fun _ => 1) x / e := by
    have : e * ((∑ i, w i * -L i) - tsallisPsi (1 / 2) (fun _ => 1) w / e) ≤
        e * ((∑ i, x i * -L i) - tsallisPsi (1 / 2) (fun _ => 1) x / e) := by
      rw [mul_sub, mul_sub, mul_div_cancel₀ _ he.ne', mul_div_cancel₀ _ he.ne']; exact h
    exact le_of_mul_le_mul_left this he
  linarith

/-- Pathwise FTRL telescoping with an abstract per-round bound `r`. -/
lemma telescope_gen {K : ℕ} (e : ℕ → ℝ) (x l Lh : ℕ → Fin K → ℝ) (r : ℕ → ℝ)
    (hL1 : ∀ i, Lh 1 i = 0) (hLs : ∀ t i, Lh (t + 1) i = Lh t i + l t i)
    (he : ∀ t, 1 ≤ t → 0 < e t)
    (hr : ∀ t, 1 ≤ t → ∀ w ∈ stdSimplex ℝ (Fin K),
      (∑ i, x t i * l t i) + ((∑ i, w i * -(Lh t i + l t i)) -
        tsallisPsi (1 / 2) (fun _ => 1) w / e t) -
      ((∑ i, x t i * -Lh t i) - tsallisPsi (1 / 2) (fun _ => 1) (x t) / e t) ≤ r t)
    (hxs : ∀ t, 1 ≤ t → x t ∈ stdSimplex ℝ (Fin K)) :
    ∀ T, 1 ≤ T → ∀ w ∈ stdSimplex ℝ (Fin K),
      (∑ t ∈ Icc 1 T, ∑ i, x t i * l t i) +
        ((∑ i, w i * -Lh (T + 1) i) - tsallisPsi (1 / 2) (fun _ => 1) w / e T) +
        tsallisPsi (1 / 2) (fun _ => 1) (x 1) / e 1 +
        ∑ t ∈ Icc 2 T, (1 / e t - 1 / e (t - 1)) * tsallisPsi (1 / 2) (fun _ => 1) (x t) ≤
      ∑ t ∈ Icc 1 T, r t := by
  intro T hT
  induction T, hT using Nat.le_induction with
  | base =>
    intro w hw
    have h := hr 1 le_rfl w hw
    have hL2 : ∀ i, Lh (1 + 1) i = Lh 1 i + l 1 i := hLs 1
    simp only [Finset.Icc_self, Finset.sum_singleton, hL2]
    have hC : (∑ i, x 1 i * -Lh 1 i) = 0 := by simp [hL1]
    rw [hC] at h
    have h2 : Finset.Icc 2 1 = ∅ := by decide
    rw [h2, Finset.sum_empty]
    linarith
  | succ T hT ih =>
    intro w hw
    have hIH := ih (x (T + 1)) (hxs (T + 1) (by omega))
    have h := hr (T + 1) (by omega) w hw
    have hL2 : ∀ i, Lh (T + 1 + 1) i = Lh (T + 1) i + l (T + 1) i := hLs (T + 1)
    simp only [hL2]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T + 1),
      Finset.sum_Icc_succ_top (by omega : 2 ≤ T + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ T + 1)]
    have hsub : T + 1 - 1 = T := by omega
    rw [hsub]
    have heT : 0 < e T := he T hT
    have heT1 : 0 < e (T + 1) := he (T + 1) (by omega)
    have hid : (1 / e (T + 1) - 1 / e T) * tsallisPsi (1 / 2) (fun _ => 1) (x (T + 1)) =
        tsallisPsi (1 / 2) (fun _ => 1) (x (T + 1)) / e (T + 1) -
          tsallisPsi (1 / 2) (fun _ => 1) (x (T + 1)) / e T := by
      field_simp
    rw [hid]
    linarith

end STel

section SRVArm

lemma F_le (e s c m : ℝ) (he : 0 < e) (hs : 0 ≤ s) (hc2 : c ^ 2 ≤ m ^ 2)
    (hm : max (-c) 0 ≤ m) :
    e / 2 * s ^ 3 * c ^ 2 + e ^ 2 / 2 * s ^ 4 * (max (-c) 0) ^ 3 ≤
      e / 2 * s ^ 3 * m ^ 2 + e ^ 2 / 2 * s ^ 4 * m ^ 3 := by
  have h1 := mul_le_mul_of_nonneg_left hc2 (by positivity : (0:ℝ) ≤ e / 2 * s ^ 3)
  have h2 : (max (-c) 0) ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ (le_max_right _ _) hm 3
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ e ^ 2 / 2 * s ^ 4)
  linarith

lemma rv_comb_half (e s w q mq S : ℝ) (he : 0 < e) (hs : 0 < s) (hw : s ^ 2 = w)
    (hw1 : w ≤ 1) (hq : q ^ 2 ≤ (1 - w) ^ 2 / 4) (hmq0 : 0 ≤ mq) (hmq : mq ≤ (1 - w) / 2)
    (hS : S ≤ (1 - w) * (e / 2 * s ^ 3 * (1 - 1 / 2) ^ 2 + e ^ 2 / 2 * s ^ 4 * (1 - 1 / 2) ^ 3)) :
    e / 2 * s * q ^ 2 + e ^ 2 / 2 * mq ^ 3 + S ≤ 7 * e ^ 2 / 8 + e / 8 * s * (1 - w) := by
  have hw0 : 0 ≤ w := by rw [← hw]; positivity
  have h1 := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ e / 2 * s)
  have h2 : mq ^ 3 ≤ ((1 - w) / 2) ^ 3 := pow_le_pow_left₀ hmq0 hmq 3
  have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ e ^ 2 / 2)
  have hs3 : s ^ 3 = s * w := by rw [← hw]; ring
  have hs4 : s ^ 4 = w ^ 2 := by rw [← hw]; ring
  rw [hs3, hs4] at hS
  have hX : (1 - w) ^ 3 + (1 - w) * w ^ 2 ≤ 2 := by
    have a : (1 - w) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have b : (1 - w) * w ^ 2 ≤ 1 := by
      have : w ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
      nlinarith
    linarith
  have hX' := mul_le_mul_of_nonneg_left hX (sq_nonneg e)
  nlinarith

lemma rv_comb_zero (e s w q S : ℝ) (he : 0 < e) (hs : 0 < s) (hw : s ^ 2 = w)
    (hw1 : w ≤ 1) (hse : s < e) (hq : q ^ 2 ≤ (1 - w) ^ 2)
    (hS : S ≤ (1 - w) * (e / 2 * s ^ 3 * (1 - 0) ^ 2 + e ^ 2 / 2 * s ^ 4 * (1 - 0) ^ 3)) :
    e / 2 * s * q ^ 2 + e ^ 2 / 2 * 0 ^ 3 + S ≤ 7 * e ^ 2 / 8 + e / 8 * s * (1 - w) := by
  have hw0 : 0 ≤ w := by rw [← hw]; positivity
  have h1 := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ e / 2 * s)
  have hs3 : s ^ 3 = s * w := by rw [← hw]; ring
  have hs4 : s ^ 4 = w ^ 2 := by rw [← hw]; ring
  rw [hs3, hs4] at hS
  have hA : s * (1 - w) ≤ e := by nlinarith
  have hA' := mul_le_mul_of_nonneg_left hA he.le
  have hB : (1 - w) * w ^ 2 ≤ 1 := by
    have : w ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
    nlinarith
  have hB' := mul_le_mul_of_nonneg_left hB (sq_nonneg e)
  nlinarith

/-- Conditional expectation (over the played arm `j`) of the RV round bound for arm `i`. -/
lemma rv_arm {K : ℕ} (e : ℝ) (he0 : 0 < e) (he1 : e ≤ 1) (w l : Fin K → ℝ)
    (hw : w ∈ stdSimplex ℝ (Fin K)) (hwpos : ∀ j, 0 < w j)
    (hl : ∀ j, 0 ≤ l j ∧ l j ≤ 1) (i : Fin K) (B : ℝ)
    (hB : B = if e ^ 2 ≤ w i then 1 / 2 else 0) :
    (∀ j, e * max (-(((if j = i then (l i - B) / w i else 0) + B) - l j)) 0 *
        Real.sqrt (w i) ≤ 1) ∧
    ∑ j, w j * (e / 2 * Real.sqrt (w i) ^ 3 *
          (((if j = i then (l i - B) / w i else 0) + B) - l j) ^ 2 +
        e ^ 2 / 2 * Real.sqrt (w i) ^ 4 *
          (max (-(((if j = i then (l i - B) / w i else 0) + B) - l j)) 0) ^ 3) ≤
      7 * e ^ 2 / 8 + e / 8 * Real.sqrt (w i) * (1 - w i) := by
  set s := Real.sqrt (w i) with hsdef
  have hwi := hwpos i
  have hs : 0 < s := Real.sqrt_pos.2 hwi
  have hs2 : s ^ 2 = w i := Real.sq_sqrt hwi.le
  have hsum : ∑ j, w j = 1 := hw.2
  have hwi1 : w i ≤ 1 := by
    have := Finset.single_le_sum (fun j _ => (hwpos j).le) (Finset.mem_univ i) (f := w)
    linarith
  have hs1 : s ≤ 1 := by rw [hsdef]; exact Real.sqrt_le_one.mpr hwi1
  have hB01 : 0 ≤ B ∧ B ≤ 1 / 2 := by rw [hB]; split_ifs <;> norm_num
  have hci : ((if i = i then (l i - B) / w i else 0) + B) - l i =
      (l i - B) * (1 - w i) / w i := by
    rw [if_pos rfl]; field_simp; ring
  have hcj : ∀ j, j ≠ i → ((if j = i then (l i - B) / w i else 0) + B) - l j = B - l j := by
    intro j hj; rw [if_neg hj]; ring
  have hmj : ∀ j, (B - l j) ^ 2 ≤ (1 - B) ^ 2 ∧ max (-(B - l j)) 0 ≤ 1 - B := by
    intro j
    obtain ⟨hl0, hl1⟩ := hl j
    refine ⟨sq_le_sq' (by linarith) (by linarith), max_le (by linarith) (by linarith)⟩
  have hmaxi : max (-((l i - B) * (1 - w i) / w i)) 0 = max (-((l i - B) * (1 - w i))) 0 / w i := by
    rw [← max_div_div_right hwi.le, zero_div, neg_div]
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst hj
      rw [hci, hmaxi]
      rcases le_or_gt (e ^ 2) (w j) with h | h
      · have hB' : B = 1 / 2 := by rw [hB, if_pos h]
        have hes : e ≤ s := by
          rw [hsdef]; exact Real.le_sqrt_of_sq_le h
        have hm : max (-((l j - B) * (1 - w j))) 0 ≤ 1 / 2 := by
          obtain ⟨hl0, hl1⟩ := hl j
          rw [hB']; apply max_le _ (by norm_num)
          have := mul_le_mul_of_nonneg_right (show 1 / 2 - l j ≤ 1 / 2 by linarith)
            (show 0 ≤ 1 - w j by linarith)
          linarith
        have hm0 : 0 ≤ max (-((l j - B) * (1 - w j))) 0 := le_max_right _ _
        have hre : e * (max (-((l j - B) * (1 - w j))) 0 / w j) * s =
            (e * max (-((l j - B) * (1 - w j))) 0 * s) / w j := by ring
        rw [hre, div_le_one hwi]
        calc e * max (-((l j - B) * (1 - w j))) 0 * s ≤ s * 1 * s :=
              mul_le_mul (mul_le_mul hes (hm.trans (by norm_num)) hm0 hs.le) le_rfl hs.le
                (by positivity)
          _ = w j := by rw [← hs2]; ring
      · have hB' : B = 0 := by rw [hB, if_neg (not_le.2 h)]
        have hm : max (-((l j - B) * (1 - w j))) 0 = 0 := by
          obtain ⟨hl0, hl1⟩ := hl j
          rw [hB']; apply max_eq_right
          have := mul_nonneg hl0 (show 0 ≤ 1 - w j by linarith)
          linarith
        rw [hm]; simp
    · rw [hcj j hj]
      have h1 := (hmj j).2
      have h0 : 0 ≤ max (-(B - l j)) 0 := le_max_right _ _
      have : max (-(B - l j)) 0 ≤ 1 := by linarith [hB01.1]
      calc e * max (-(B - l j)) 0 * s ≤ 1 * 1 * 1 := by
            apply mul_le_mul (mul_le_mul he1 this h0 zero_le_one) hs1 hs.le (by norm_num)
        _ = 1 := by norm_num
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hS : ∑ j ∈ Finset.univ.erase i, w j * (e / 2 * s ^ 3 *
          (((if j = i then (l i - B) / w i else 0) + B) - l j) ^ 2 +
        e ^ 2 / 2 * s ^ 4 *
          (max (-(((if j = i then (l i - B) / w i else 0) + B) - l j)) 0) ^ 3) ≤
        (1 - w i) * (e / 2 * s ^ 3 * (1 - B) ^ 2 + e ^ 2 / 2 * s ^ 4 * (1 - B) ^ 3) := by
      calc _ ≤ ∑ j ∈ Finset.univ.erase i, w j *
              (e / 2 * s ^ 3 * (1 - B) ^ 2 + e ^ 2 / 2 * s ^ 4 * (1 - B) ^ 3) := by
            apply Finset.sum_le_sum
            intro j hj
            rw [hcj j (Finset.ne_of_mem_erase hj)]
            exact mul_le_mul_of_nonneg_left
              (F_le e s _ _ he0 hs.le (hmj j).1 (hmj j).2) (hwpos j).le
        _ = (1 - w i) * (e / 2 * s ^ 3 * (1 - B) ^ 2 + e ^ 2 / 2 * s ^ 4 * (1 - B) ^ 3) := by
            rw [← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ i), hsum]
    have hq2 : ((l i - B) * (1 - w i)) ^ 2 ≤ (1 - B) ^ 2 * (1 - w i) ^ 2 := by
      have h1 := (hmj i).1
      have e2 : (l i - B) ^ 2 = (B - l i) ^ 2 := by ring
      rw [mul_pow, e2]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    have hterm : w i * (e / 2 * s ^ 3 *
          (((if i = i then (l i - B) / w i else 0) + B) - l i) ^ 2 +
        e ^ 2 / 2 * s ^ 4 *
          (max (-(((if i = i then (l i - B) / w i else 0) + B) - l i)) 0) ^ 3) =
        e / 2 * s * ((l i - B) * (1 - w i)) ^ 2 +
          e ^ 2 / 2 * (max (-((l i - B) * (1 - w i))) 0) ^ 3 := by
      rw [hci, hmaxi]
      have hs3 : s ^ 3 = s * w i := by rw [← hs2]; ring
      have hs4 : s ^ 4 = w i ^ 2 := by rw [← hs2]; ring
      rw [hs3, hs4]
      field_simp
    rw [hterm]
    rcases le_or_gt (e ^ 2) (w i) with h | h
    · have hB' : B = 1 / 2 := by rw [hB, if_pos h]
      rw [hB'] at hS hq2 ⊢
      obtain ⟨hl0, hl1⟩ := hl i
      refine rv_comb_half e s (w i) ((l i - 1 / 2) * (1 - w i))
        (max (-((l i - 1 / 2) * (1 - w i))) 0) _ he0 hs hs2 hwi1
        (by linarith [hq2, show (1 - 1 / 2 : ℝ) ^ 2 * (1 - w i) ^ 2 = (1 - w i) ^ 2 / 4 by ring])
        (le_max_right _ _) ?_ hS
      apply max_le _ (by linarith)
      have := mul_le_mul_of_nonneg_right (show 1 / 2 - l i ≤ 1 / 2 by linarith)
        (show 0 ≤ 1 - w i by linarith)
      linarith
    · have hB' : B = 0 := by rw [hB, if_neg (not_le.2 h)]
      have hse : s < e := by
        rw [hsdef]
        exact (Real.sqrt_lt' he0).2 h
      rw [hB'] at hS hq2 ⊢
      have hm : max (-((l i - 0) * (1 - w i))) 0 = 0 := by
        obtain ⟨hl0, hl1⟩ := hl i
        apply max_eq_right
        have := mul_nonneg hl0 (show 0 ≤ 1 - w i by linarith)
        linarith
      rw [hm]
      exact rv_comb_zero e s (w i) _ _ he0 hs hs2 hwi1 hse
        (by linarith [hq2, show (1 - 0 : ℝ) ^ 2 * (1 - w i) ^ 2 = (1 - w i) ^ 2 by ring]) hS

end SRVArm

section SPerSeed

open Finset TsallisINF.Half RegretBandits.Adversarial

lemma etaRV_eq (t : ℕ) : etaRV t = 4 / Real.sqrt (t : ℝ) := by
  unfold etaRV
  rw [one_div, Real.sqrt_inv, div_eq_mul_inv]

lemma sqrt_t_pos (t : ℕ) (ht : 1 ≤ t) : 0 < Real.sqrt (t : ℝ) :=
  Real.sqrt_pos.2 (by exact_mod_cast (show 0 < t by omega))

lemma etaRV_pos (t : ℕ) (ht : 1 ≤ t) : 0 < etaRV t := by
  rw [etaRV_eq]; have := sqrt_t_pos t ht; positivity

lemma inv_etaRV (t : ℕ) (ht : 1 ≤ t) : 1 / etaRV t = Real.sqrt (t : ℝ) / 4 := by
  rw [etaRV_eq]; have := (sqrt_t_pos t ht).ne'; field_simp

lemma etaRV_le_one (t : ℕ) (ht : 16 ≤ t) : etaRV t ≤ 1 := by
  rw [etaRV_eq, div_le_one (sqrt_t_pos t (by omega))]
  have h16 : (16 : ℝ) ≤ t := by exact_mod_cast ht
  calc (4 : ℝ) = Real.sqrt 16 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    _ ≤ Real.sqrt t := Real.sqrt_le_sqrt h16

lemma etaRV_sq (t : ℕ) (ht : 1 ≤ t) : etaRV t ^ 2 = 16 / (t : ℝ) := by
  rw [etaRV_eq, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; norm_num

lemma one_lt_etaRV_sq (t : ℕ) (ht : 1 ≤ t) (ht16 : t < 16) : 1 < etaRV t ^ 2 := by
  rw [etaRV_sq t ht, one_lt_div (by exact_mod_cast (show 0 < t by omega))]
  exact_mod_cast ht16

/-- Threshold baseline of the RV estimator. -/
noncomputable def Bb {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (t : ℕ) (h : ℕ → Fin K)
    (k : Fin K) : ℝ :=
  if etaRV t ^ 2 ≤ p t h k then 1 / 2 else 0

/-- The RV estimate for a fixed seed. -/
noncomputable def lhR {K : ℕ} (ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (t : ℕ) (h : ℕ → Fin K)
    (k : Fin K) : ℝ :=
  (if h t = k then (ℓ t h k - Bb p t h k) / p t h k else 0) + Bb p t h k

structure HypR {K : ℕ} (ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ) : Prop where
  l0 : ∀ t h k, 0 ≤ ℓ t h k
  l1 : ∀ t h k, ℓ t h k ≤ 1
  lc : ∀ t h h', AgreeBefore t h h' → ℓ t h = ℓ t h'
  pc : Causal p
  smp : ∀ t, 1 ≤ t → ∀ h, p t h ∈ stdSimplex ℝ (Fin K)
  pos : ∀ t, 1 ≤ t → ∀ h k, 0 < p t h k
  arg : ∀ t, 1 ≤ t → ∀ h,
    IsArgmax (1 / 2) (etaRV t) (fun k => ∑ s ∈ Ico 1 t, lhR ℓ p s h k) (p t h)

variable {K : ℕ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ}

lemma HypR.sum1 (H : HypR ℓ p) : ∀ s, 1 ≤ s → ∀ h, ∑ j, p s h j = 1 :=
  fun s hs h => (H.smp s hs h).2

lemma HypR.p0 (H : HypR ℓ p) : ∀ s, 1 ≤ s → ∀ h j, 0 ≤ p s h j :=
  fun s hs h j => (H.pos s hs h j).le

lemma HypR.p1 (H : HypR ℓ p) (t : ℕ) (ht : 1 ≤ t) (h : ℕ → Fin K) (k : Fin K) :
    p t h k ≤ 1 := by
  have := Finset.single_le_sum (fun j _ => H.p0 t ht h j) (Finset.mem_univ k) (f := p t h)
  rw [H.sum1 t ht h] at this
  exact this

lemma agree_of_uptoR {h h' : ℕ → Fin K} {t : ℕ}
    (hh : ∀ s, 1 ≤ s → s ≤ t → h s = h' s) : AgreeBefore t h h' :=
  fun s h1 h2 => hh s h1 h2.le

lemma upd_agreeR (h : ℕ → Fin K) (t : ℕ) (j : Fin K) :
    AgreeBefore t (Function.update h t j) h :=
  fun s _ hs => Function.update_of_ne (ne_of_lt hs) _ _

lemma lhR_congr (H : HypR ℓ p) (t : ℕ) (ht : 1 ≤ t) (h h' : ℕ → Fin K)
    (hh : ∀ s, 1 ≤ s → s ≤ t → h s = h' s) : lhR ℓ p t h = lhR ℓ p t h' := by
  funext k
  unfold lhR Bb
  rw [hh t ht le_rfl, H.lc t h h' (agree_of_uptoR hh), H.pc t ht h h' (agree_of_uptoR hh)]

lemma lhR_update (H : HypR ℓ p) (t : ℕ) (ht : 1 ≤ t) (h : ℕ → Fin K) (j k : Fin K) :
    lhR ℓ p t (Function.update h t j) k =
      (if j = k then (ℓ t h k - Bb p t h k) / p t h k else 0) + Bb p t h k := by
  unfold lhR Bb
  rw [Function.update_self, H.lc t _ h (upd_agreeR h t j), H.pc t ht _ h (upd_agreeR h t j)]

lemma cond_armR (H : HypR ℓ p) (t : ℕ) (ht : 1 ≤ t) (h : ℕ → Fin K) (k : Fin K) :
    ∑ j, p t h j * lhR ℓ p t (Function.update h t j) k = ℓ t h k := by
  simp only [lhR_update H t ht h, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul, H.sum1 t ht h, one_mul]
  have := (H.pos t ht h k).ne'
  field_simp
  ring

lemma cond_unbiasedR (H : HypR ℓ p) (t : ℕ) (ht : 1 ≤ t) (h : ℕ → Fin K) (v : Fin K → ℝ) :
    ∑ j, p t h j * ∑ k, v k * lhR ℓ p t (Function.update h t j) k = ∑ k, v k * ℓ t h k := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← cond_armR H t ht h k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma E_le_of_condR (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hc : Causal p)
    (hsum : ∀ s, 1 ≤ s → ∀ h, ∑ j, p s h j = 1) (hp : ∀ s, 1 ≤ s → ∀ h j, 0 ≤ p s h j)
    (i₀ : Fin K) (t T : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (F G : (ℕ → Fin K) → ℝ)
    (hF : DepUpTo t F) (hG : DepUpTo t G)
    (hFG : ∀ h, ∑ j, p t h j * F (Function.update h t j) ≤
      ∑ j, p t h j * G (Function.update h t j)) :
    E p i₀ T F ≤ E p i₀ T G := by
  rw [E_cond p hc hsum i₀ t T ht htT F hF, E_cond p hc hsum i₀ t T ht htT G hG]
  exact E_mono p hp i₀ (t - 1) _ _ hFG

lemma E_playR (H : HypR ℓ p) (i₀ : Fin K) (t T : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) :
    E p i₀ T (fun h => ℓ t h (h t)) = E p i₀ T (fun h => ∑ i, p t h i * lhR ℓ p t h i) := by
  have hF : DepUpTo t (fun h => ℓ t h (h t)) := by
    intro h h' hh
    simp only
    rw [H.lc t h h' (agree_of_uptoR hh), hh t ht le_rfl]
  have hG : DepUpTo t (fun h => ∑ i, p t h i * lhR ℓ p t h i) := by
    intro h h' hh
    simp only
    rw [H.pc t ht h h' (agree_of_uptoR hh), lhR_congr H t ht h h' hh]
  have hc : ∀ h, ∑ j, p t h j * (fun h => ℓ t h (h t)) (Function.update h t j) =
      ∑ j, p t h j * (fun h => ∑ i, p t h i * lhR ℓ p t h i) (Function.update h t j) := by
    intro h
    have e1 : ∀ j, ℓ t (Function.update h t j) = ℓ t h :=
      fun j => H.lc t _ h (upd_agreeR h t j)
    have e2 : ∀ j, p t (Function.update h t j) = p t h :=
      fun j => H.pc t ht _ h (upd_agreeR h t j)
    simp only [e1, e2, Function.update_self]
    rw [cond_unbiasedR H t ht h (p t h)]
  exact le_antisymm
    (E_le_of_condR p H.pc H.sum1 H.p0 i₀ t T ht htT _ _ hF hG (fun h => (hc h).le))
    (E_le_of_condR p H.pc H.sum1 H.p0 i₀ t T ht htT _ _ hG hF (fun h => (hc h).ge))

lemma E_armR (H : HypR ℓ p) (i₀ : Fin K) (t T : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (k : Fin K) :
    E p i₀ T (fun h => ℓ t h k) = E p i₀ T (fun h => lhR ℓ p t h k) := by
  have hF : DepUpTo t (fun h => ℓ t h k) := by
    intro h h' hh
    simp only
    rw [H.lc t h h' (agree_of_uptoR hh)]
  have hG : DepUpTo t (fun h => lhR ℓ p t h k) := by
    intro h h' hh
    simp only
    rw [lhR_congr H t ht h h' hh]
  have hc : ∀ h, ∑ j, p t h j * (fun h => ℓ t h k) (Function.update h t j) =
      ∑ j, p t h j * (fun h => lhR ℓ p t h k) (Function.update h t j) := by
    intro h
    have e1 : ∀ j, ℓ t (Function.update h t j) = ℓ t h :=
      fun j => H.lc t _ h (upd_agreeR h t j)
    simp only [e1]
    rw [cond_armR H t ht h k, ← Finset.sum_mul, H.sum1 t ht h, one_mul]
  exact le_antisymm
    (E_le_of_condR p H.pc H.sum1 H.p0 i₀ t T ht htT _ _ hF hG (fun h => (hc h).le))
    (E_le_of_condR p H.pc H.sum1 H.p0 i₀ t T ht htT _ _ hG hF (fun h => (hc h).ge))

/-- Lemma 19 per-round bound for the RV estimate (shift by the played loss). -/
noncomputable def FR (ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (t : ℕ) (h : ℕ → Fin K) : ℝ :=
  ∑ i, (etaRV t / 2 * Real.sqrt (p t h i) ^ 3 * (lhR ℓ p t h i - ℓ t h (h t)) ^ 2 +
    etaRV t ^ 2 / 2 * Real.sqrt (p t h i) ^ 4 * (max (-(lhR ℓ p t h i - ℓ t h (h t))) 0) ^ 3)

noncomputable def rR (ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (t : ℕ) (h : ℕ → Fin K) : ℝ :=
  if t < 16 then ∑ i, p t h i * lhR ℓ p t h i else FR ℓ p t h

noncomputable def bR (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (t : ℕ) (h : ℕ → Fin K) : ℝ :=
  if t < 16 then 1 else
    ∑ i, (7 * etaRV t ^ 2 / 8 + etaRV t / 8 * Real.sqrt (p t h i) * (1 - p t h i))

lemma E_rR (H : HypR ℓ p) (i₀ : Fin K) (t T : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) :
    E p i₀ T (rR ℓ p t) ≤ E p i₀ T (bR p t) := by
  apply E_le_of_condR p H.pc H.sum1 H.p0 i₀ t T ht htT
  · intro h h' hh
    unfold rR FR
    rw [H.pc t ht h h' (agree_of_uptoR hh), lhR_congr H t ht h h' hh,
      H.lc t h h' (agree_of_uptoR hh), hh t ht le_rfl]
  · intro h h' hh
    unfold bR
    rw [H.pc t ht h h' (agree_of_uptoR hh)]
  · intro h
    have e1 : ∀ j, ℓ t (Function.update h t j) = ℓ t h :=
      fun j => H.lc t _ h (upd_agreeR h t j)
    have e2 : ∀ j, p t (Function.update h t j) = p t h :=
      fun j => H.pc t ht _ h (upd_agreeR h t j)
    have hb : ∀ j, bR p t (Function.update h t j) = bR p t h := by
      intro j; unfold bR; rw [e2]
    simp only [hb]
    rw [← Finset.sum_mul, H.sum1 t ht h, one_mul]
    unfold rR
    by_cases h16 : t < 16
    · simp only [if_pos h16, e2]
      rw [cond_unbiasedR H t ht h (p t h), bR, if_pos h16]
      calc ∑ k, p t h k * ℓ t h k ≤ ∑ k, p t h k :=
            Finset.sum_le_sum (fun k _ => mul_le_of_le_one_right (H.p0 t ht h k) (H.l1 t h k))
        _ = 1 := H.sum1 t ht h
    · simp only [if_neg h16]
      rw [bR, if_neg h16]
      unfold FR
      simp only [e1, e2, Function.update_self, lhR_update H t ht h]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro i _
      have := (rv_arm (etaRV t) (etaRV_pos t ht) (etaRV_le_one t (by omega)) (p t h) (ℓ t h)
        (H.smp t ht h) (H.pos t ht h) (fun j => ⟨H.l0 t h j, H.l1 t h j⟩) i (Bb p t h i) rfl).2
      exact this

lemma lhR_nonneg_small (H : HypR ℓ p) (t : ℕ) (ht : 1 ≤ t) (ht16 : t < 16) (h : ℕ → Fin K)
    (k : Fin K) : 0 ≤ lhR ℓ p t h k := by
  have hB : Bb p t h k = 0 := by
    unfold Bb
    rw [if_neg]
    have := one_lt_etaRV_sq t ht ht16
    have := H.p1 t ht h k
    linarith
  unfold lhR
  rw [hB]
  split_ifs
  · rw [sub_zero, add_zero]; exact div_nonneg (H.l0 t h k) (H.p0 t ht h k)
  · simp

lemma sum_single_mul {K : ℕ} (j : Fin K) (a : Fin K → ℝ) :
    ∑ i, (if i = j then (1 : ℝ) else 0) * a i = a j := by
  simp

lemma single_simplex {K : ℕ} (j : Fin K) :
    (fun i => if i = j then (1 : ℝ) else 0) ∈ stdSimplex ℝ (Fin K) := by
  refine ⟨fun i => by simp only []; split_ifs <;> norm_num, ?_⟩
  simp

lemma psi_single {K : ℕ} (j : Fin K) :
    tsallisPsi (1 / 2) (fun _ => 1) (fun i => if i = j then (1 : ℝ) else 0) = -2 := by
  rw [tsallisPsi_half]
  have : ∀ i : Fin K, Real.sqrt (if i = j then (1 : ℝ) else 0) - (if i = j then (1 : ℝ) else 0) / 2 =
      if i = j then 1 / 2 else 0 := by
    intro i; split_ifs <;> norm_num
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

lemma Ico_one_succR (T : ℕ) : Finset.Ico 1 (T + 1) = Finset.Icc 1 T := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

/-- Pathwise FTRL bound for a fixed seed and path, comparator arm `j`. -/
lemma pathR (H : HypR ℓ p) (h : ℕ → Fin K) (T : ℕ) (hT : 1 ≤ T) (j : Fin K) :
    (∑ t ∈ Icc 1 T, ∑ i, p t h i * lhR ℓ p t h i) - ∑ t ∈ Icc 1 T, lhR ℓ p t h j ≤
      (∑ t ∈ Icc 1 T, rR ℓ p t h) +
        ((∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) *
          ∑ i, (Real.sqrt (p t h i) - p t h i / 2)) - Real.sqrt (T : ℝ) / 2) := by
  set l : ℕ → Fin K → ℝ := fun t i => if t = 0 then 0 else lhR ℓ p t h i with hl
  set Lh : ℕ → Fin K → ℝ := fun t i => ∑ s ∈ Ico 1 t, lhR ℓ p s h i with hLh
  have hL1 : ∀ i, Lh 1 i = 0 := fun i => by simp [hLh]
  have hLs : ∀ t i, Lh (t + 1) i = Lh t i + l t i := by
    intro t i
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; simp [hLh, hl]
    · simp only [hLh, hl, if_neg (Nat.pos_iff_ne_zero.1 h0)]
      rw [Finset.sum_Ico_succ_top h0]
  have hr : ∀ t, 1 ≤ t → ∀ w ∈ stdSimplex ℝ (Fin K),
      (∑ i, p t h i * l t i) + ((∑ i, w i * -(Lh t i + l t i)) -
        tsallisPsi (1 / 2) (fun _ => 1) w / etaRV t) -
      ((∑ i, p t h i * -Lh t i) - tsallisPsi (1 / 2) (fun _ => 1) (p t h) / etaRV t) ≤
        rR ℓ p t h := by
    intro t ht w hw
    simp only [hl, if_neg (show t ≠ 0 by omega)]
    unfold rR
    by_cases h16 : t < 16
    · rw [if_pos h16]
      exact round_nonneg (etaRV t) (etaRV_pos t ht) (Lh t) (p t h) (lhR ℓ p t h) w
        (H.arg t ht h) (fun k => lhR_nonneg_small H t ht h16 h k) hw
    · rw [if_neg h16]
      have hz : ∀ i, etaRV t * max (-(lhR ℓ p t h i - ℓ t h (h t))) 0 *
          Real.sqrt (p t h i) ≤ 1 := by
        intro i
        unfold lhR
        exact (rv_arm (etaRV t) (etaRV_pos t ht) (etaRV_le_one t (by omega)) (p t h) (ℓ t h)
          (H.smp t ht h) (H.pos t ht h) (fun j => ⟨H.l0 t h j, H.l1 t h j⟩) i (Bb p t h i)
          rfl).1 (h t)
      exact key_div_RV (etaRV t) (etaRV_pos t ht) (Lh t) (p t h) (lhR ℓ p t h) w (ℓ t h (h t))
        (H.arg t ht h) hz hw
  have tel := telescope_gen (fun t => etaRV t) (fun t => p t h) l Lh (fun t => rR ℓ p t h)
    hL1 hLs (fun t ht => etaRV_pos t ht) hr (fun t ht => H.smp t ht h) T hT
    (fun i => if i = j then (1 : ℝ) else 0) (single_simplex j)
  simp only at tel
  have e1 : ∑ t ∈ Icc 1 T, ∑ i, p t h i * l t i = ∑ t ∈ Icc 1 T, ∑ i, p t h i * lhR ℓ p t h i := by
    apply Finset.sum_congr rfl
    intro t ht
    simp only [hl, if_neg (show t ≠ 0 by have := (Finset.mem_Icc.1 ht).1; omega)]
  have e2 : ∑ i, (if i = j then (1 : ℝ) else 0) * -Lh (T + 1) i = -∑ t ∈ Icc 1 T, lhR ℓ p t h j := by
    rw [sum_single_mul]
    simp only [hLh, Ico_one_succR]
  have e3 : tsallisPsi (1 / 2) (fun _ => 1) (fun i => if i = j then (1 : ℝ) else 0) / etaRV T =
      -(Real.sqrt (T : ℝ) / 2) := by
    rw [psi_single, div_eq_mul_one_div, inv_etaRV T hT]; ring
  have e4 : tsallisPsi (1 / 2) (fun _ => 1) (p 1 h) / etaRV 1 =
      -((Real.sqrt ((1 : ℕ) : ℝ) - Real.sqrt ((1 - 1 : ℕ) : ℝ)) *
        ∑ i, (Real.sqrt (p 1 h i) - p 1 h i / 2)) := by
    rw [tsallisPsi_half, div_eq_mul_one_div, inv_etaRV 1 le_rfl]
    simp
    ring
  have e5 : ∑ t ∈ Icc 2 T, (1 / etaRV t - 1 / etaRV (t - 1)) *
      tsallisPsi (1 / 2) (fun _ => 1) (p t h) =
      -∑ t ∈ Icc 2 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) *
          ∑ i, (Real.sqrt (p t h i) - p t h i / 2) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have h2 := (Finset.mem_Icc.1 ht).1
    rw [inv_etaRV t (by omega), inv_etaRV (t - 1) (by omega), tsallisPsi_half]
    ring
  have e6 : ∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) *
      ∑ i, (Real.sqrt (p t h i) - p t h i / 2) =
      (Real.sqrt ((1 : ℕ) : ℝ) - Real.sqrt ((1 - 1 : ℕ) : ℝ)) *
        ∑ i, (Real.sqrt (p 1 h i) - p 1 h i / 2) +
      ∑ t ∈ Icc 2 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) *
          ∑ i, (Real.sqrt (p t h i) - p t h i / 2) := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hT, Finset.sum_insert (by simp)]
    rfl
  rw [e1, e2, e3, e4, e5] at tel
  rw [e6]
  linarith

/-- Per-seed bound (expectation over the action tree). -/
lemma perSeedR (H : HypR ℓ p) (i₀ : Fin K) (T : ℕ) (hT : 1 ≤ T) (j : Fin K) :
    E p i₀ T (fun h => ∑ t ∈ Icc 1 T, ℓ t h (h t)) -
        E p i₀ T (fun h => ∑ t ∈ Icc 1 T, ℓ t h j) ≤
      E p i₀ T (fun h => (∑ t ∈ Icc 1 T, bR p t h) +
        ((∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) *
          ∑ i, (Real.sqrt (p t h i) - p t h i / 2)) - Real.sqrt (T : ℝ) / 2)) := by
  set Q : (ℕ → Fin K) → ℝ := fun h =>
    (∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) *
          ∑ i, (Real.sqrt (p t h i) - p t h i / 2)) - Real.sqrt (T : ℝ) / 2 with hQ
  have a1 : E p i₀ T (fun h => ∑ t ∈ Icc 1 T, ℓ t h (h t)) =
      E p i₀ T (fun h => ∑ t ∈ Icc 1 T, ∑ i, p t h i * lhR ℓ p t h i) := by
    rw [E_sum p i₀ T (Icc 1 T) (fun t h => ℓ t h (h t)),
      E_sum p i₀ T (Icc 1 T) (fun t h => ∑ i, p t h i * lhR ℓ p t h i)]
    apply Finset.sum_congr rfl
    intro t ht
    exact E_playR H i₀ t T (Finset.mem_Icc.1 ht).1 (Finset.mem_Icc.1 ht).2
  have a2 : E p i₀ T (fun h => ∑ t ∈ Icc 1 T, ℓ t h j) =
      E p i₀ T (fun h => ∑ t ∈ Icc 1 T, lhR ℓ p t h j) := by
    rw [E_sum p i₀ T (Icc 1 T) (fun t h => ℓ t h j),
      E_sum p i₀ T (Icc 1 T) (fun t h => lhR ℓ p t h j)]
    apply Finset.sum_congr rfl
    intro t ht
    exact E_armR H i₀ t T (Finset.mem_Icc.1 ht).1 (Finset.mem_Icc.1 ht).2 j
  rw [a1, a2, ← E_sub]
  calc _ ≤ E p i₀ T (fun h => (∑ t ∈ Icc 1 T, rR ℓ p t h) + Q h) :=
        E_mono p H.p0 i₀ T _ _ (fun h => pathR H h T hT j)
    _ = (∑ t ∈ Icc 1 T, E p i₀ T (rR ℓ p t)) + E p i₀ T Q := by
        rw [E_add, E_sum p i₀ T (Icc 1 T) (fun t h => rR ℓ p t h)]
    _ ≤ (∑ t ∈ Icc 1 T, E p i₀ T (bR p t)) + E p i₀ T Q := by
        gcongr with t ht
        exact E_rR H i₀ t T (Finset.mem_Icc.1 ht).1 (Finset.mem_Icc.1 ht).2
    _ = _ := by
        rw [E_add, E_sum p i₀ T (Icc 1 T) (fun t h => bR p t h)]

end SPerSeed

section SReal

open Finset

lemma harm_le_log (T : ℕ) (hT : 1 ≤ T) : ∑ t ∈ Icc 2 T, (1 / (t : ℝ)) ≤ Real.log T := by
  induction T, hT using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have key : Real.log ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ (n : ℝ) / ((n + 1 : ℕ) : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hn0 hn1)
    rw [Real.log_div hn0.ne' hn1.ne'] at key
    have e : (n : ℝ) / ((n + 1 : ℕ) : ℝ) - 1 = -(1 / ((n + 1 : ℕ) : ℝ)) := by
      push_cast; field_simp; ring
    linarith

lemma inv_sqrt_sum_le (T : ℕ) : ∑ t ∈ Icc 1 T, (1 / Real.sqrt (t : ℝ)) ≤ 2 * Real.sqrt T := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ha := Real.sqrt_nonneg (n : ℝ)
    have hb : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have ha2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hb2 := Real.sq_sqrt (Nat.cast_nonneg (n + 1) : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have key : 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
        2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n) := by
      rw [div_le_iff₀ hb]
      nlinarith [sq_nonneg (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n)]
    linarith

lemma sum_at_eq (T : ℕ) :
    ∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) = Real.sqrt T := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel]
    ring

lemma at_nonneg (t : ℕ) : 0 ≤ Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ) := by
  have : ((t - 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast Nat.sub_le t 1
  linarith [Real.sqrt_le_sqrt this]

lemma sum_sqrt_le {K : ℕ} (x : Fin K → ℝ) (hx : x ∈ stdSimplex ℝ (Fin K)) :
    ∑ i, Real.sqrt (x i) ≤ Real.sqrt K := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ))
    (fun i => Real.sqrt (x i))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at cs
  have e : ∑ i, Real.sqrt (x i) ^ 2 = 1 := by
    rw [← hx.2]
    exact Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hx.1 i))
  rw [e, mul_one] at cs
  exact Real.le_sqrt_of_sq_le cs

lemma sqrt_le_one_of {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.sqrt x ≤ 1 :=
  Real.sqrt_le_one.mpr h1

end SReal

section SAdvPath

open Finset TsallisINF.Half RegretBandits.Adversarial

variable {K : ℕ}

/-- The per-seed pathwise bound function. -/
noncomputable def BP (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (T : ℕ) (h : ℕ → Fin K) : ℝ :=
  (∑ t ∈ Icc 1 T, bR p t h) +
    ((∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) *
      ∑ i, (Real.sqrt (p t h i) - p t h i / 2)) - Real.sqrt (T : ℝ) / 2)

lemma bR_le_adv (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (t : ℕ) (ht : 1 ≤ t) (h : ℕ → Fin K)
    (hs : p t h ∈ stdSimplex ℝ (Fin K)) :
    bR p t h ≤ (if t < 16 then 1 else 0) + 14 * K * (if 2 ≤ t then 1 / (t : ℝ) else 0) +
      Real.sqrt K / 2 * (1 / Real.sqrt (t : ℝ)) := by
  have hst := sqrt_t_pos t ht
  have hK0 : 0 ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
  unfold bR
  by_cases h16 : t < 16
  · rw [if_pos h16, if_pos h16]
    have : 0 ≤ 14 * (K : ℝ) * (if 2 ≤ t then 1 / (t : ℝ) else 0) := by
      have : 0 ≤ (if 2 ≤ t then 1 / (t : ℝ) else 0) := by split_ifs <;> positivity
      positivity
    have : 0 ≤ Real.sqrt K / 2 * (1 / Real.sqrt (t : ℝ)) := by positivity
    linarith
  · rw [if_neg h16, if_neg h16, if_pos (by omega)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, etaRV_sq t ht]
    have h1 : ∑ i, Real.sqrt (p t h i) * (1 - p t h i) ≤ ∑ i, Real.sqrt (p t h i) :=
      Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (Real.sqrt_nonneg _)
        (by linarith [hs.1 i]))
    have h2 := sum_sqrt_le (p t h) hs
    have hS : ∑ i, etaRV t / 8 * Real.sqrt (p t h i) * (1 - p t h i) =
        etaRV t / 8 * ∑ i, Real.sqrt (p t h i) * (1 - p t h i) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hS, etaRV_eq]
    have he : 0 ≤ 4 / Real.sqrt (t : ℝ) / 8 := by positivity
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) he
    have e1 : 4 / Real.sqrt (t : ℝ) / 8 * Real.sqrt K = Real.sqrt K / 2 * (1 / Real.sqrt t) := by
      field_simp; ring
    have e2 : (K : ℝ) * (7 * (16 / (t : ℝ)) / 8) = 14 * K * (1 / (t : ℝ)) := by ring
    linarith

lemma sum_lt16 (T : ℕ) : ∑ t ∈ Icc 1 T, (if t < 16 then (1 : ℝ) else 0) ≤ 15 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (Finset.filter (fun t => t < 16) (Icc 1 T)) ⊆ Icc 1 15 := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at ht ⊢
    omega
  have h := Finset.card_le_card this
  simp only [Nat.card_Icc] at h
  exact_mod_cast h

lemma sum_harm_ite (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Icc 1 T, (if 2 ≤ t then 1 / (t : ℝ) else 0) ≤ Real.log T := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hT, Finset.sum_insert (by simp), if_neg (by omega),
    zero_add]
  calc _ = ∑ t ∈ Icc 2 T, (1 / (t : ℝ)) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [if_pos (show 2 ≤ t from (Finset.mem_Icc.1 ht).1)]
    _ ≤ _ := harm_le_log T hT

/-- Adversarial pathwise bound (paper p. 21). -/
lemma BP_le_adv (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (T : ℕ) (hT : 1 ≤ T) (h : ℕ → Fin K)
    (hs : ∀ t, 1 ≤ t → p t h ∈ stdSimplex ℝ (Fin K)) :
    BP p T h ≤ 2 * Real.sqrt ((K : ℝ) * (T : ℝ)) + 14 * (K : ℝ) * Real.log (T : ℝ) + 16 := by
  unfold BP
  have hb : ∑ t ∈ Icc 1 T, bR p t h ≤ ∑ t ∈ Icc 1 T, ((if t < 16 then 1 else 0) +
      14 * K * (if 2 ≤ t then 1 / (t : ℝ) else 0) + Real.sqrt K / 2 * (1 / Real.sqrt (t : ℝ))) :=
    Finset.sum_le_sum (fun t ht => bR_le_adv p t (Finset.mem_Icc.1 ht).1 h
      (hs t (Finset.mem_Icc.1 ht).1))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hb
  have h1 := sum_lt16 T
  have h2 := mul_le_mul_of_nonneg_left (sum_harm_ite T hT)
    (by positivity : (0 : ℝ) ≤ 14 * K)
  have h3 := mul_le_mul_of_nonneg_left (inv_sqrt_sum_le T)
    (by positivity : (0 : ℝ) ≤ Real.sqrt K / 2)
  have hg : ∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) *
      ∑ i, (Real.sqrt (p t h i) - p t h i / 2) ≤
      ∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) * (Real.sqrt K - 1 / 2) := by
    apply Finset.sum_le_sum
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (at_nonneg t)
    have hst := hs t (Finset.mem_Icc.1 ht).1
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hst.2]
    linarith [sum_sqrt_le (p t h) hst]
  rw [← Finset.sum_mul, sum_at_eq] at hg
  have hKT : Real.sqrt ((K : ℝ) * (T : ℝ)) = Real.sqrt K * Real.sqrt T :=
    Real.sqrt_mul (Nat.cast_nonneg K) _
  have hT0 : 0 ≤ Real.sqrt (T : ℝ) := Real.sqrt_nonneg _
  rw [hKT]
  nlinarith

end SAdvPath

section SC5

open Finset

lemma amgm1 (r c b : ℝ) (hb : 0 < b) : 2 * r * c - b * r ^ 2 ≤ c ^ 2 / b := by
  rw [le_div_iff₀ hb]
  nlinarith [sq_nonneg (b * r - c)]

lemma amgm2 (r c b : ℝ) (hc : 0 < c) (hb : 0 < b) (hcb : 2 * c ≤ b) :
    2 * r * c + r ^ 2 * c - b * r ^ 2 ≤ c ^ 2 / b + 2 * c ^ 3 / b ^ 2 := by
  have h1 : 0 < b - c := by linarith
  have h2 : 0 ≤ b - 2 * c := by linarith
  have hS : 0 ≤ b ^ 3 * ((b - c) * r - c) ^ 2 + b * c ^ 3 * (b - 2 * c) :=
    add_nonneg (mul_nonneg (pow_nonneg hb.le 3) (sq_nonneg _))
      (mul_nonneg (mul_nonneg hb.le (pow_nonneg hc.le 3)) h2)
  have hb0 : b ≠ 0 := hb.ne'
  have h10 : b - c ≠ 0 := h1.ne'
  have key : c ^ 2 / b + 2 * c ^ 3 / b ^ 2 - (2 * r * c + r ^ 2 * c - b * r ^ 2) =
      (b ^ 3 * ((b - c) * r - c) ^ 2 + b * c ^ 3 * (b - 2 * c)) / ((b - c) * b ^ 3) := by
    field_simp
    ring
  have : 0 ≤ (b ^ 3 * ((b - c) * r - c) ^ 2 + b * c ^ 3 * (b - 2 * c)) / ((b - c) * b ^ 3) :=
    div_nonneg hS (mul_pos h1 (pow_pos hb 3)).le
  linarith

lemma sqrt_mul_one_sub_le (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    Real.sqrt y * (1 - y) ≤ 1 / 2 := by
  have hr := Real.sqrt_nonneg y
  have hr2 := Real.sq_sqrt h0
  have hr1 : Real.sqrt y ≤ 1 := Real.sqrt_le_one.mpr h1
  rw [show (1 - y) = 1 - Real.sqrt y ^ 2 by rw [hr2]]
  nlinarith [mul_nonneg (sq_nonneg (Real.sqrt y - 1 / 2)) (by linarith : (0 : ℝ) ≤ Real.sqrt y + 1)]

lemma sqrt_sub_nat (t : ℕ) (ht : 1 ≤ t) :
    Real.sqrt (t : ℝ) ^ 2 - Real.sqrt ((t - 1 : ℕ) : ℝ) ^ 2 = 1 := by
  rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_sub ht]
  push_cast; ring

lemma at_ge (t : ℕ) (ht : 1 ≤ t) :
    1 / (2 * Real.sqrt (t : ℝ)) ≤ Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ) := by
  have hu : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast ht)
  have h1 := sqrt_sub_nat t ht
  set u := Real.sqrt (t : ℝ)
  set v := Real.sqrt ((t - 1 : ℕ) : ℝ)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (u - v)]

/-- `∑ 1/√t ≥ 2√T - 3/2 + 1/(2√T)` -/
lemma sum_inv_sqrt_ge (T : ℕ) (hT : 1 ≤ T) :
    2 * Real.sqrt T - 3 / 2 + 1 / (2 * Real.sqrt T) ≤ ∑ t ∈ Icc 1 T, (1 / Real.sqrt (t : ℝ)) := by
  induction T, hT using Nat.le_induction with
  | base => norm_num [Finset.Icc_self]
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := sqrt_sub_nat (n + 1) (by omega)
    rw [Nat.add_sub_cancel] at h1
    have hv : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hu : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    set u := Real.sqrt ((n + 1 : ℕ) : ℝ)
    set v := Real.sqrt (n : ℝ)
    have huv : v ≤ u := by nlinarith
    have hnum : 0 ≤ u + v - 4 * u * v * (u - v) := by
      have e : (u + v) * (u + v - 4 * u * v * (u - v)) = (u - v) ^ 2 := by
        linear_combination (-4 * u * v) * h1
      nlinarith [sq_nonneg (u - v)]
    have key : 1 / (2 * v) + 1 / u - 1 / (2 * u) - 2 * (u - v) =
        (u + v - 4 * u * v * (u - v)) / (2 * u * v) := by
      field_simp
      ring
    have : 0 ≤ (u + v - 4 * u * v * (u - v)) / (2 * u * v) := div_nonneg hnum (by positivity)
    linarith

lemma tail_term (n : ℕ) (hn : 1 ≤ n) :
    1 / (((n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)) ≤
      2 / Real.sqrt (n : ℝ) - 2 / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  have h1 := sqrt_sub_nat (n + 1) (by omega)
  rw [Nat.add_sub_cancel] at h1
  have hv : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hu : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hu2 : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  set u := Real.sqrt ((n + 1 : ℕ) : ℝ)
  set v := Real.sqrt (n : ℝ)
  rw [← hu2]
  have huv : v ≤ u := by nlinarith
  have hnum : 0 ≤ 2 * u ^ 2 * (u - v) - v := by
    have e : (u + v) * (2 * u ^ 2 * (u - v) - v) = (u - v) * (2 * u + v) := by
      linear_combination (2 * u ^ 2) * h1
    nlinarith [mul_nonneg (sub_nonneg.2 huv) (by linarith : (0 : ℝ) ≤ 2 * u + v)]
  have key : 2 / v - 2 / u - 1 / (u ^ 2 * u) = (2 * u ^ 2 * (u - v) - v) / (v * u ^ 3) := by
    field_simp
  have : 0 ≤ (2 * u ^ 2 * (u - v) - v) / (v * u ^ 3) := div_nonneg hnum (by positivity)
  linarith

lemma tail_sum (T0 : ℕ) (h0 : 1 ≤ T0) (T : ℕ) :
    ∑ t ∈ Icc 1 T, (if T0 < t then 1 / ((t : ℝ) * Real.sqrt t) else 0) ≤
      2 / Real.sqrt (T0 : ℝ) - 2 / Real.sqrt ((max T0 T : ℕ) : ℝ) := by
  induction T with
  | zero => rw [show max T0 0 = T0 from max_eq_left (Nat.zero_le _)]; simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    by_cases h : T0 < n + 1
    · rw [if_pos h]
      have hm1 : max T0 (n + 1) = n + 1 := max_eq_right h.le
      have hm0 : max T0 n = n := max_eq_right (by omega)
      rw [hm0] at ih
      rw [hm1]
      have := tail_term n (by omega)
      linarith
    · rw [if_neg h]
      have hm1 : max T0 (n + 1) = T0 := max_eq_left (by omega)
      have hm0 : max T0 n = T0 := max_eq_left (by omega)
      rw [hm0] at ih
      rw [hm1]
      linarith

lemma tail_sum' (T0 : ℕ) (h0 : 1 ≤ T0) (T : ℕ) :
    ∑ t ∈ Icc 1 T, (if T0 < t then 1 / ((t : ℝ) * Real.sqrt t) else 0) ≤
      2 / Real.sqrt (T0 : ℝ) := by
  have := tail_sum T0 h0 T
  have : 0 ≤ 2 / Real.sqrt ((max T0 T : ℕ) : ℝ) := by positivity
  linarith

lemma harm_full (T : ℕ) (hT : 1 ≤ T) : ∑ t ∈ Icc 1 T, (1 / (t : ℝ)) ≤ 1 + Real.log T := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hT, Finset.sum_insert (by simp)]
  have := harm_le_log T hT
  have e : ∑ t ∈ Icc (1 + 1) T, (1 / (t : ℝ)) = ∑ t ∈ Icc 2 T, (1 / (t : ℝ)) := rfl
  simp only [Nat.cast_one, div_one]
  linarith

lemma head_sum (T0 T : ℕ) :
    ∑ t ∈ Icc 1 T, (if T0 < t then 0 else 1 / (2 * Real.sqrt (t : ℝ))) ≤ Real.sqrt T0 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  have hsub : Finset.filter (fun t => ¬ T0 < t) (Icc 1 T) ⊆ Icc 1 T0 := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at ht ⊢
    omega
  calc _ ≤ ∑ t ∈ Icc 1 T0, 1 / (2 * Real.sqrt (t : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 1 / 2 * ∑ t ∈ Icc 1 T0, 1 / Real.sqrt (t : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        rw [one_div_mul_one_div]
    _ ≤ 1 / 2 * (2 * Real.sqrt T0) := mul_le_mul_of_nonneg_left (inv_sqrt_sum_le T0) (by norm_num)
    _ = _ := by ring

lemma d_sum (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Icc 1 T, ((Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) -
      1 / (2 * Real.sqrt (t : ℝ))) ≤ 3 / 4 := by
  rw [Finset.sum_sub_distrib, sum_at_eq]
  have e : ∑ t ∈ Icc 1 T, 1 / (2 * Real.sqrt (t : ℝ)) =
      1 / 2 * ∑ t ∈ Icc 1 T, 1 / Real.sqrt (t : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [one_div_mul_one_div]
  rw [e]
  have := sum_inv_sqrt_ge T hT
  have : 0 ≤ 1 / (2 * Real.sqrt (T : ℝ)) := by positivity
  linarith

/-! the round bound -/

noncomputable def bRx {K : ℕ} (t : ℕ) (x : Fin K → ℝ) : ℝ :=
  if t < 16 then 1 else
    ∑ i, (7 * (4 / Real.sqrt (t : ℝ)) ^ 2 / 8 + 4 / Real.sqrt (t : ℝ) / 8 * Real.sqrt (x i) * (1 - x i))

noncomputable def Gx {K : ℕ} (x : Fin K → ℝ) : ℝ := ∑ i, (Real.sqrt (x i) - x i / 2)

noncomputable def stb (lam s : ℝ) (t : ℕ) (y : ℝ) : ℝ :=
  if t < 16 then 0 else (1 + lam) * (Real.sqrt y * (1 - y) / (2 * s))

noncomputable def U (K : ℕ) (Δ : Fin K → ℝ) (istar : Fin K) (lam : ℝ) (T0 t : ℕ) : ℝ :=
  2 * (if t < 16 then 1 else 0) + 28 * (K : ℝ) * (if 2 ≤ t then 1 / (t : ℝ) else 0) +
    2 * Real.sqrt K * ((Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) - 1 / (2 * Real.sqrt (t : ℝ))) +
    (if T0 < t then 0 else 1 / (2 * Real.sqrt (t : ℝ))) +
    ∑ i ∈ univ.erase istar, (1 / (lam * Δ i) * (1 / (t : ℝ)) +
      (if T0 < t then 2 / (lam * Δ i) ^ 2 * (1 / ((t : ℝ) * Real.sqrt t)) else 0))

lemma stb_le (lam s : ℝ) (t : ℕ) (y : ℝ) (hl : 0 ≤ lam) (hs : 0 < s) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    stb lam s t y ≤ (1 + lam) * (Real.sqrt y * (1 - y) / (2 * s)) := by
  unfold stb
  split_ifs
  · have := Real.sqrt_nonneg y
    have : 0 ≤ 1 - y := by linarith
    exact mul_nonneg (by linarith) (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) this) (by linarith))
  · exact le_rfl

lemma stbA {K : ℕ} (x : Fin K → ℝ) (t : ℕ) (ht : 1 ≤ t) (lam : ℝ) (hl1 : lam ≤ 1) :
    (1 + lam) * bRx t x ≤ 2 * (if t < 16 then 1 else 0) +
      28 * (K : ℝ) * (if 2 ≤ t then 1 / (t : ℝ) else 0) +
      ∑ i, stb lam (Real.sqrt (t : ℝ)) t (x i) := by
  unfold bRx
  by_cases h16 : t < 16
  · rw [if_pos h16, if_pos h16]
    have hz : ∑ i, stb lam (Real.sqrt (t : ℝ)) t (x i) = 0 :=
      Finset.sum_eq_zero (fun i _ => by simp [stb, h16])
    have : 0 ≤ 28 * (K : ℝ) * (if 2 ≤ t then 1 / (t : ℝ) else 0) := by
      have : 0 ≤ (if 2 ≤ t then 1 / (t : ℝ) else 0) := by split_ifs <;> positivity
      positivity
    rw [hz]
    linarith
  · rw [if_neg h16, if_neg h16, if_pos (by omega)]
    have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast ht)
    have hs2 : Real.sqrt (t : ℝ) ^ 2 = (t : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    have e : ∀ i, (1 + lam) * (7 * (4 / Real.sqrt (t : ℝ)) ^ 2 / 8 +
        4 / Real.sqrt (t : ℝ) / 8 * Real.sqrt (x i) * (1 - x i)) =
        (1 + lam) * (14 * (1 / (t : ℝ))) + stb lam (Real.sqrt (t : ℝ)) t (x i) := by
      intro i
      simp only [stb, if_neg h16]
      rw [div_pow, hs2]
      ring
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h0 : 0 ≤ (K : ℝ) * (14 * (1 / (t : ℝ))) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.2 hl1) h0]

set_option maxHeartbeats 1000000 in
lemma round_sb {K : ℕ} (x : Fin K → ℝ) (hx : x ∈ stdSimplex ℝ (Fin K)) (t : ℕ) (ht : 1 ≤ t)
    (Δ : Fin K → ℝ) (istar : Fin K) (hΔ : ∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1)
    (hpos : ∀ i, i ≠ istar → 0 < Δ i) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1) (T0 : ℕ)
    (hT0 : T0 < t → ∀ i, i ≠ istar → 2 ≤ lam * Δ i * Real.sqrt t) :
    (1 + lam) * (bRx t x + (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) * (Gx x - 1 / 2)) -
      lam * ∑ i ∈ univ.erase istar, x i * Δ i ≤ U K Δ istar lam T0 t := by
  have hA := stbA x t ht lam hl1
  unfold U
  have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast ht)
  have hs2 : Real.sqrt (t : ℝ) ^ 2 = (t : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have ha := at_ge t ht
  set s := Real.sqrt (t : ℝ) with hs_def
  set a := s - Real.sqrt ((t - 1 : ℕ) : ℝ) with ha_def
  have hc2 : 0 < 1 / (2 * s) := one_div_pos.2 (by linarith)
  have hc1 : 0 < 1 / s := one_div_pos.2 hs
  have hx0 := hx.1
  have hmem : istar ∈ (univ : Finset (Fin K)) := mem_univ _
  have hx1 : ∀ i, x i ≤ 1 := fun i => by
    rw [← hx.2]
    exact Finset.single_le_sum (fun j _ => hx0 j) (mem_univ i)
  have hsum1 : x istar + ∑ i ∈ univ.erase istar, x i = 1 := by
    rw [Finset.add_sum_erase _ _ hmem]; exact hx.2
  -- stability split
  have hsplitS : ∑ i, stb lam s t (x i) =
      stb lam s t (x istar) + ∑ i ∈ univ.erase istar, stb lam s t (x i) :=
    (Finset.add_sum_erase _ _ hmem).symm
  -- penalty
  have hGsplit : Gx x = (Real.sqrt (x istar) - x istar / 2) +
      ∑ i ∈ univ.erase istar, (Real.sqrt (x i) - x i / 2) := by
    unfold Gx; exact (Finset.add_sum_erase _ _ hmem).symm
  have hgs : Real.sqrt (x istar) - x istar / 2 - 1 / 2 ≤ 0 := by
    have := Real.sq_sqrt (hx0 istar)
    linarith only [sq_nonneg (Real.sqrt (x istar) - 1), this]
  have hEle : ∑ i ∈ univ.erase istar, (Real.sqrt (x i) - x i / 2) ≤
      ∑ i ∈ univ.erase istar, Real.sqrt (x i) :=
    Finset.sum_le_sum (fun i _ => by linarith [hx0 i])
  have hEnn : 0 ≤ ∑ i ∈ univ.erase istar, (Real.sqrt (x i) - x i / 2) := by
    apply Finset.sum_nonneg
    intro i _
    have h2 := Real.sq_sqrt (hx0 i)
    have h3 : Real.sqrt (x i) ≤ 1 := Real.sqrt_le_one.mpr (hx1 i)
    have h4 := Real.sqrt_nonneg (x i)
    have h5 : Real.sqrt (x i) ^ 2 ≤ Real.sqrt (x i) := pow_le_of_le_one h4 h3 two_ne_zero
    linarith only [h2, h5, h4]
  have hSle : ∑ i ∈ univ.erase istar, Real.sqrt (x i) ≤ Real.sqrt K :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun i _ _ => Real.sqrt_nonneg _)).trans (sum_sqrt_le x hx)
  have hd0 : 0 ≤ a - 1 / (2 * s) := by linarith
  have ha0 : 0 ≤ a := le_trans hc2.le ha
  set E := ∑ i ∈ univ.erase istar, (Real.sqrt (x i) - x i / 2) with hE_def
  have hB : (1 + lam) * (a * (Gx x - 1 / 2)) ≤ 2 * Real.sqrt K * (a - 1 / (2 * s)) +
      ∑ i ∈ univ.erase istar, (1 + lam) * (Real.sqrt (x i) / (2 * s)) := by
    rw [hGsplit]
    have h1 : (1 + lam) * (a * (Real.sqrt (x istar) - x istar / 2 - 1 / 2)) ≤ 0 := by
      have hneg := mul_nonneg (by linarith : (0:ℝ) ≤ 1 + lam) (mul_nonneg ha0 (neg_nonneg.2 hgs))
      linarith only [hneg]
    have h2 : (1 + lam) * ((1 / (2 * s)) * E) ≤
        (1 + lam) * ((1 / (2 * s)) * ∑ i ∈ univ.erase istar, Real.sqrt (x i)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEle hc2.le) (by linarith)
    have h3 : (1 + lam) * ((a - 1 / (2 * s)) * E) ≤ 2 * ((a - 1 / (2 * s)) * Real.sqrt K) := by
      have hY : 0 ≤ (a - 1 / (2 * s)) * E := mul_nonneg hd0 hEnn
      have hZ : (a - 1 / (2 * s)) * E ≤ (a - 1 / (2 * s)) * Real.sqrt K :=
        mul_le_mul_of_nonneg_left (hEle.trans hSle) hd0
      linarith only [mul_nonneg (sub_nonneg.2 hl1) hY, hZ]
    have h4 : ∑ i ∈ univ.erase istar, (1 + lam) * (Real.sqrt (x i) / (2 * s)) =
        (1 + lam) * ((1 / (2 * s)) * ∑ i ∈ univ.erase istar, Real.sqrt (x i)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have e : (1 + lam) * (a * ((Real.sqrt (x istar) - x istar / 2) + E - 1 / 2)) =
        (1 + lam) * (a * (Real.sqrt (x istar) - x istar / 2 - 1 / 2)) +
        (1 + lam) * ((1 / (2 * s)) * E) + (1 + lam) * ((a - 1 / (2 * s)) * E) := by ring
    rw [e]
    linarith
  -- per-arm generic bound
  have hstb : ∀ i, stb lam s t (x i) + (1 + lam) * (Real.sqrt (x i) / (2 * s)) ≤
      2 * Real.sqrt (x i) * (1 / s) := by
    intro i
    have h1 := stb_le lam s t (x i) hl0.le hs (hx0 i) (hx1 i)
    have hr := Real.sqrt_nonneg (x i)
    have h2 : Real.sqrt (x i) * (1 - x i) ≤ Real.sqrt (x i) := by
      linarith only [mul_nonneg hr (hx0 i)]
    have h3 : (1 + lam) * (Real.sqrt (x i) * (1 - x i) / (2 * s)) ≤
        (1 + lam) * (Real.sqrt (x i) / (2 * s)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 (by linarith)) (by linarith)
    have h4 : (1 + lam) * (Real.sqrt (x i) / (2 * s)) ≤ 2 * (Real.sqrt (x i) / (2 * s)) :=
      mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hr (by linarith))
    have e : 2 * (Real.sqrt (x i) / (2 * s)) = Real.sqrt (x i) * (1 / s) := by
      ring
    linarith
  have hlm : lam * ∑ i ∈ univ.erase istar, x i * Δ i =
      ∑ i ∈ univ.erase istar, lam * (x i * Δ i) := Finset.mul_sum _ _ _
  have hmuladd : (1 + lam) * (bRx t x + a * (Gx x - 1 / 2)) =
      (1 + lam) * bRx t x + (1 + lam) * (a * (Gx x - 1 / 2)) := mul_add _ _ _
  rw [hmuladd, hlm]
  by_cases hT : T0 < t
  · simp only [hT, ↓reduceIte]
    have hb2 := hT0 hT
    have hC : stb lam s t (x istar) ≤ ∑ i ∈ univ.erase istar, x i / s := by
      rw [← Finset.sum_div, show ∑ i ∈ univ.erase istar, x i = 1 - x istar by linarith]
      have h1 := stb_le lam s t (x istar) hl0.le hs (hx0 istar) (hx1 istar)
      have hr1 : Real.sqrt (x istar) ≤ 1 := Real.sqrt_le_one.mpr (hx1 istar)
      have hr0 := Real.sqrt_nonneg (x istar)
      have hq : 0 ≤ (1 - x istar) / s := div_nonneg (by linarith [hx1 istar]) hs.le
      have e : (1 + lam) * (Real.sqrt (x istar) * (1 - x istar) / (2 * s)) =
          ((1 + lam) * Real.sqrt (x istar) / 2) * ((1 - x istar) / s) := by ring
      have h5' : (1 + lam) * Real.sqrt (x istar) ≤ 2 * 1 :=
        mul_le_mul (by linarith) hr1 hr0 (by norm_num)
      have h5 : (1 + lam) * Real.sqrt (x istar) / 2 ≤ 1 := by linarith only [h5']
      have h6 := mul_le_of_le_one_left hq h5
      linarith only [h1, e, h6]
    have hD : ∀ i ∈ univ.erase istar, stb lam s t (x i) + (1 + lam) * (Real.sqrt (x i) / (2 * s)) +
        x i / s - lam * (x i * Δ i) ≤
        1 / (lam * Δ i) * (1 / (t : ℝ)) + 2 / (lam * Δ i) ^ 2 * (1 / ((t : ℝ) * s)) := by
      intro i hi
      have hne : i ≠ istar := Finset.ne_of_mem_erase hi
      have hb : 0 < lam * Δ i := mul_pos hl0 (hpos i hne)
      have hcb : 2 * (1 / s) ≤ lam * Δ i := by
        have := hb2 i hne
        rw [← mul_div_assoc, mul_one, div_le_iff₀ hs]
        linarith
      have key := amgm2 (Real.sqrt (x i)) (1 / s) (lam * Δ i) hc1 hb hcb
      have hr2 := Real.sq_sqrt (hx0 i)
      have e1 : (1 / s) ^ 2 / (lam * Δ i) = 1 / (lam * Δ i) * (1 / (t : ℝ)) := by
        rw [← hs2]; ring
      have e2 : 2 * (1 / s) ^ 3 / (lam * Δ i) ^ 2 = 2 / (lam * Δ i) ^ 2 * (1 / ((t : ℝ) * s)) := by
        rw [← hs2]; ring
      have e3 : x i / s = Real.sqrt (x i) ^ 2 * (1 / s) := by rw [hr2]; ring
      have e4 : lam * (x i * Δ i) = lam * Δ i * Real.sqrt (x i) ^ 2 := by rw [hr2]; ring
      have h0 := hstb i
      linarith only [key, e1, e2, e3, e4, h0]
    have hDs := Finset.sum_le_sum hD
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hDs ⊢
    linarith only [hA, hsplitS, hB, hC, hDs]
  · simp only [hT, ↓reduceIte, add_zero]
    have hC : stb lam s t (x istar) ≤ 1 / (2 * s) := by
      have h1 := stb_le lam s t (x istar) hl0.le hs (hx0 istar) (hx1 istar)
      have h2 := sqrt_mul_one_sub_le (x istar) (hx0 istar) (hx1 istar)
      have hp : 0 ≤ Real.sqrt (x istar) * (1 - x istar) :=
        mul_nonneg (Real.sqrt_nonneg _) (by linarith [hx1 istar])
      have e : (1 + lam) * (Real.sqrt (x istar) * (1 - x istar) / (2 * s)) =
          ((1 + lam) * (Real.sqrt (x istar) * (1 - x istar))) * (1 / (2 * s)) := by ring
      have h5' : (1 + lam) * (Real.sqrt (x istar) * (1 - x istar)) ≤ 2 * (1 / 2) :=
        mul_le_mul (by linarith) h2 hp (by norm_num)
      have h5 : (1 + lam) * (Real.sqrt (x istar) * (1 - x istar)) ≤ 1 := by linarith only [h5']
      have h6 := mul_le_of_le_one_left hc2.le h5
      linarith only [h1, e, h6]
    have hD : ∀ i ∈ univ.erase istar, stb lam s t (x i) + (1 + lam) * (Real.sqrt (x i) / (2 * s)) -
        lam * (x i * Δ i) ≤ 1 / (lam * Δ i) * (1 / (t : ℝ)) := by
      intro i hi
      have hne : i ≠ istar := Finset.ne_of_mem_erase hi
      have hb : 0 < lam * Δ i := mul_pos hl0 (hpos i hne)
      have key := amgm1 (Real.sqrt (x i)) (1 / s) (lam * Δ i) hb
      have hr2 := Real.sq_sqrt (hx0 i)
      have e1 : (1 / s) ^ 2 / (lam * Δ i) = 1 / (lam * Δ i) * (1 / (t : ℝ)) := by
        rw [← hs2]; ring
      have e4 : lam * (x i * Δ i) = lam * Δ i * Real.sqrt (x i) ^ 2 := by rw [hr2]; ring
      have h0 := hstb i
      linarith only [key, e1, e4, h0]
    have hDs := Finset.sum_le_sum hD
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hDs ⊢
    linarith only [hA, hsplitS, hB, hC, hDs]

lemma sum_U {K : ℕ} (Δ : Fin K → ℝ) (istar : Fin K) (hpos : ∀ i, i ≠ istar → 0 < Δ i)
    (lam : ℝ) (hl0 : 0 < lam) (T0 : ℕ) (h0 : 1 ≤ T0)
    (hT0 : ∀ i, i ≠ istar → 2 ≤ lam * Δ i * Real.sqrt T0) (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Icc 1 T, U K Δ istar lam T0 t ≤
      30 + 28 * (K : ℝ) * Real.log T + 3 / 2 * Real.sqrt K + Real.sqrt T0 +
        ∑ i ∈ univ.erase istar, (Real.log T + 3) / (lam * Δ i) := by
  unfold U
  simp only [Finset.sum_add_distrib]
  have p1 : ∑ t ∈ Icc 1 T, (2 : ℝ) * (if t < 16 then 1 else 0) ≤ 30 := by
    rw [← Finset.mul_sum]; linarith [sum_lt16 T]
  have p2 : ∑ t ∈ Icc 1 T, 28 * (K : ℝ) * (if 2 ≤ t then 1 / (t : ℝ) else 0) ≤
      28 * (K : ℝ) * Real.log T := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_harm_ite T hT) (by positivity)
  have p3 : ∑ t ∈ Icc 1 T, 2 * Real.sqrt K *
      ((Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) - 1 / (2 * Real.sqrt (t : ℝ))) ≤
      3 / 2 * Real.sqrt K := by
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left (d_sum T hT) (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt K)
    linarith
  have p4 := head_sum T0 T
  have p5 : ∑ t ∈ Icc 1 T, ∑ i ∈ univ.erase istar, 1 / (lam * Δ i) * (1 / (t : ℝ)) ≤
      ∑ i ∈ univ.erase istar, 1 / (lam * Δ i) * (1 + Real.log T) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i hi
    have hb : 0 < lam * Δ i := mul_pos hl0 (hpos i (Finset.ne_of_mem_erase hi))
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (harm_full T hT) (one_div_pos.2 hb).le
  have p6 : ∑ t ∈ Icc 1 T, ∑ i ∈ univ.erase istar,
      (if T0 < t then 2 / (lam * Δ i) ^ 2 * (1 / ((t : ℝ) * Real.sqrt t)) else 0) ≤
      ∑ i ∈ univ.erase istar, 2 / (lam * Δ i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i hi
    have hne := Finset.ne_of_mem_erase hi
    have hb : 0 < lam * Δ i := mul_pos hl0 (hpos i hne)
    have hsT : 0 < Real.sqrt (T0 : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast h0)
    calc _ = 2 / (lam * Δ i) ^ 2 *
          ∑ t ∈ Icc 1 T, (if T0 < t then 1 / ((t : ℝ) * Real.sqrt t) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          split_ifs <;> ring
      _ ≤ 2 / (lam * Δ i) ^ 2 * (2 / Real.sqrt (T0 : ℝ)) :=
          mul_le_mul_of_nonneg_left (tail_sum' T0 h0 T) (by positivity)
      _ = 2 / (lam * Δ i) * (2 / (lam * Δ i * Real.sqrt (T0 : ℝ))) := by ring
      _ ≤ 2 / (lam * Δ i) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)]
          exact hT0 i hne
      _ = 2 / (lam * Δ i) := mul_one _
  have p56 : ∑ i ∈ univ.erase istar, 1 / (lam * Δ i) * (1 + Real.log T) +
      ∑ i ∈ univ.erase istar, 2 / (lam * Δ i) =
      ∑ i ∈ univ.erase istar, (Real.log T + 3) / (lam * Δ i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith only [p1, p2, p3, p4, p5, p6, p56]

set_option maxHeartbeats 1000000 in
lemma sb_total {K : ℕ} (x : ℕ → Fin K → ℝ) (hx : ∀ t, 1 ≤ t → x t ∈ stdSimplex ℝ (Fin K))
    (T : ℕ) (hT : 1 ≤ T) (hK : 1 < K) (Δ : Fin K → ℝ) (istar : Fin K)
    (hΔ : ∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ i, i ≠ istar → 0 < Δ i)
    (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1) :
    (1 + lam) * ((∑ t ∈ Icc 1 T, bRx t (x t)) +
      ((∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) * Gx (x t)) -
        Real.sqrt (T : ℝ) / 2)) -
      lam * ∑ t ∈ Icc 1 T, ∑ i ∈ univ.erase istar, x t i * Δ i ≤
    ((∑ i ∈ univ.erase istar, (Real.log (T : ℝ) + 3) / Δ i) +
        2 / (⨅ i : {i : Fin K // i ≠ istar}, Δ i)) / lam +
      28 * (K : ℝ) * Real.log (T : ℝ) + 3 / 2 * Real.sqrt (K : ℝ) + 32 := by
  have : Nontrivial (Fin K) := Fin.nontrivial_iff_two_le.2 hK
  obtain ⟨j, hj⟩ := exists_ne istar
  have : Nonempty {i : Fin K // i ≠ istar} := ⟨⟨j, hj⟩⟩
  set dm := ⨅ i : {i : Fin K // i ≠ istar}, Δ i with hdm_def
  have hdm_le : ∀ i, i ≠ istar → dm ≤ Δ i := fun i hi =>
    ciInf_le (Finite.bddBelow_range _) (⟨i, hi⟩ : {i : Fin K // i ≠ istar})
  have hdm_pos : 0 < dm := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun i : {i : Fin K // i ≠ istar} => Δ i)
    rw [hdm_def, ← hk]; exact hpos k.1 k.2
  have hdm1 : dm ≤ 1 := (hdm_le j hj).trans (hΔ j).2
  have hld : 0 < lam * dm := mul_pos hl0 hdm_pos
  have hld1 : lam * dm ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hl1 hdm_pos.le
    linarith
  set B := 2 / (lam * dm) with hB_def
  have hB2 : 2 ≤ B := by rw [hB_def, le_div_iff₀ hld]; linarith
  have hBld : lam * dm * B = 2 := by rw [hB_def]; field_simp
  set T0 := ⌈B ^ 2⌉₊ with hT0_def
  have hT0a : B ^ 2 ≤ (T0 : ℝ) := Nat.le_ceil _
  have hT0b : (T0 : ℝ) < B ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hT01 : 1 ≤ T0 := by
    have : (1 : ℝ) ≤ T0 := by nlinarith
    exact_mod_cast this
  have hBs : B ≤ Real.sqrt T0 := by
    have := Real.sqrt_le_sqrt hT0a
    rwa [Real.sqrt_sq (by linarith)] at this
  have hsT0 : Real.sqrt T0 ≤ B + 1 := by
    have h : (T0 : ℝ) ≤ (B + 1) ^ 2 := by nlinarith
    have := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (by linarith)] at this
  have key2 : ∀ i, i ≠ istar → ∀ y : ℝ, B ≤ y → 2 ≤ lam * Δ i * y := by
    intro i hi y hy
    calc (2 : ℝ) = lam * dm * B := hBld.symm
      _ ≤ lam * dm * y := mul_le_mul_of_nonneg_left hy hld.le
      _ ≤ lam * Δ i * y := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hdm_le i hi) hl0.le) (by linarith)
  have hround : ∀ t ∈ Icc 1 T, (1 + lam) * (bRx t (x t) +
      (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) * (Gx (x t) - 1 / 2)) -
      lam * ∑ i ∈ univ.erase istar, x t i * Δ i ≤ U K Δ istar lam T0 t := by
    intro t ht
    have ht1 := (Finset.mem_Icc.1 ht).1
    apply round_sb (x t) (hx t ht1) t ht1 Δ istar hΔ hpos lam hl0 hl1 T0
    intro hlt i hi
    apply key2 i hi
    exact hBs.trans (Real.sqrt_le_sqrt (by exact_mod_cast hlt.le))
  have hsum := Finset.sum_le_sum hround
  have hSU := sum_U Δ istar hpos lam hl0 T0 hT01 (fun i hi => key2 i hi _ hBs) T hT
  have e1 : ∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) * (Gx (x t) - 1 / 2) =
      ∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) * Gx (x t) -
      (∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ))) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro t _; ring
  have e2 : ∑ t ∈ Icc 1 T, ((1 + lam) * (bRx t (x t) +
      (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) * (Gx (x t) - 1 / 2)) -
      lam * ∑ i ∈ univ.erase istar, x t i * Δ i) =
      (1 + lam) * ((∑ t ∈ Icc 1 T, bRx t (x t)) +
        ∑ t ∈ Icc 1 T, (Real.sqrt (t : ℝ) - Real.sqrt ((t - 1 : ℕ) : ℝ)) * (Gx (x t) - 1 / 2)) -
      lam * ∑ t ∈ Icc 1 T, ∑ i ∈ univ.erase istar, x t i * Δ i := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [e1, sum_at_eq] at e2
  have hX : ((∑ i ∈ univ.erase istar, (Real.log (T : ℝ) + 3) / Δ i) + 2 / dm) / lam =
      ∑ i ∈ univ.erase istar, (Real.log (T : ℝ) + 3) / (lam * Δ i) + B := by
    rw [add_div, Finset.sum_div, hB_def]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; rw [div_div, mul_comm (Δ i)]
    · rw [div_div, mul_comm dm]
  rw [hX]
  linarith only [hsum, hSU, hsT0, e2]

lemma dm_pos {K : ℕ} (hK : 1 < K) (Δ : Fin K → ℝ) (istar : Fin K)
    (hpos : ∀ i, i ≠ istar → 0 < Δ i) : 0 < ⨅ i : {i : Fin K // i ≠ istar}, Δ i := by
  have : Nontrivial (Fin K) := Fin.nontrivial_iff_two_le.2 hK
  obtain ⟨j, hj⟩ := exists_ne istar
  have : Nonempty {i : Fin K // i ≠ istar} := ⟨⟨j, hj⟩⟩
  obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun i : {i : Fin K // i ≠ istar} => Δ i)
  rw [← hk]; exact hpos k.1 k.2

lemma sb_bound {K : ℕ} (x : ℕ → Fin K → ℝ) (hx : ∀ t, 1 ≤ t → x t ∈ stdSimplex ℝ (Fin K))
    (Δ : Fin K → ℝ) (hΔ : ∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1) (istar : Fin K) (T : ℕ) :
    |∑ t ∈ Icc 1 T, ∑ j ∈ univ.erase istar, x t j * Δ j| ≤ T := by
  have hnn : ∀ t ∈ Icc 1 T, 0 ≤ ∑ j ∈ univ.erase istar, x t j * Δ j := fun t ht =>
    Finset.sum_nonneg (fun j _ => mul_nonneg ((hx t (Finset.mem_Icc.1 ht).1).1 j) (hΔ j).1)
  have hle : ∀ t ∈ Icc 1 T, ∑ j ∈ univ.erase istar, x t j * Δ j ≤ 1 := by
    intro t ht
    have hs := hx t (Finset.mem_Icc.1 ht).1
    calc _ ≤ ∑ j ∈ univ.erase istar, x t j :=
          Finset.sum_le_sum (fun j _ => mul_le_of_le_one_right (hs.1 j) (hΔ j).2)
      _ ≤ ∑ j, x t j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun j _ _ => hs.1 j)
      _ = 1 := hs.2
  rw [abs_le]
  constructor
  · have := Finset.sum_nonneg hnn
    have : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    linarith
  · calc _ ≤ ∑ t ∈ Icc 1 T, (1 : ℝ) := Finset.sum_le_sum hle
      _ = T := by simp

end SC5

section SInt

open Finset TsallisINF.Half RegretBandits.Adversarial MeasureTheory

lemma hyp_ofR {K : ℕ} {Ω : Type*} (hK : 0 < K) (adv : Ω → Adversary K)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsTsallisINF etaRV (estRV etaRV adv W) W) (ω : Ω) :
    HypR (adv ω).val (fun t => W t ω) where
  l0 := fun t h k => ((adv ω).val_mem t h k).1
  l1 := fun t h k => ((adv ω).val_mem t h k).2
  lc := fun t h h' hag => (adv ω).nonanticipating t h h' hag
  pc := fun s hs h h' hag => W_causal hK etaRV (fun s hs => etaRV_pos s hs) adv W hW s hs ω h h' hag
  smp := fun t ht h => (hW t ht ω h).1
  pos := fun t ht h k => argmax_pos (1 / 2) (etaRV t) half_mem _ (W t ω h)
    (isArgmax_of (etaRV t) (etaRV_pos t ht) _ _ (hW t ht ω h).1 (hW t ht ω h).2) k
  arg := fun t ht h => isArgmax_of (etaRV t) (etaRV_pos t ht) _ _ (hW t ht ω h).1 (hW t ht ω h).2

lemma expect_eqR {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ) (F : Ω → (ℕ → Fin K) → ℝ) :
    expect μ W i₀ T F = ∫ ω, E (fun t => W t ω) i₀ T (F ω) ∂μ := rfl

lemma sum_val_abs_leR {K : ℕ} (g : Adversary K) (T : ℕ) (h j : ℕ → Fin K) :
    |∑ t ∈ Icc 1 T, g.val t h (j t)| ≤ T := by
  rw [abs_le]
  constructor
  · have h1 : 0 ≤ ∑ t ∈ Icc 1 T, g.val t h (j t) :=
      Finset.sum_nonneg (fun t _ => (g.val_mem t h (j t)).1)
    have h2 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    linarith
  · calc _ ≤ ∑ t ∈ Icc 1 T, (1 : ℝ) := Finset.sum_le_sum (fun t _ => (g.val_mem t h (j t)).2)
      _ = T := by simp

lemma integrable_ER {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hK : 0 < K)
    (adv : Ω → Adversary K) (hadv : ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsTsallisINF etaRV (estRV etaRV adv W) W)
    (i₀ : Fin K) (T : ℕ) (F : Ω → (ℕ → Fin K) → ℝ) (hFm : ∀ h, Measurable (fun ω => F ω h))
    (C : ℝ) (hFb : ∀ ω h, |F ω h| ≤ C) :
    Integrable (fun ω => E (fun t => W t ω) i₀ T (F ω)) μ := by
  have hWm := W_measurable hK etaRV (fun s hs => etaRV_pos s hs) adv hadv W hW
  refine Integrable.of_bound ?_ C ?_
  · apply Measurable.aestronglyMeasurable
    unfold E
    apply Finset.measurable_fun_sum
    intro a _
    apply Measurable.mul
    · apply Finset.measurable_prod
      intro t ht
      exact hWm t (Finset.mem_Icc.1 ht).1 _ _
    · exact hFm _
  · apply Filter.Eventually.of_forall
    intro ω
    have H := hyp_ofR hK adv W hW ω
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := E_mono (fun t => W t ω) H.p0 i₀ T (fun _ => -C) (F ω)
        (fun h => (abs_le.1 (hFb ω h)).1)
      rwa [E_const _ H.pc H.sum1] at this
    · have := E_mono (fun t => W t ω) H.p0 i₀ T (F ω) (fun _ => C)
        (fun h => (abs_le.1 (hFb ω h)).2)
      rwa [E_const _ H.pc H.sum1] at this

/-- Regret as an integral of per-seed differences against a minimizing arm. -/
lemma regret_eq {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (adv : Ω → Adversary K) (hadv : ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsTsallisINF etaRV (estRV etaRV adv W) W) (T : ℕ) :
    ∃ i : Fin K, TsallisINF.Half.pseudoRegret μ adv W ⟨0, hK⟩ T =
      ∫ ω, (E (fun t => W t ω) ⟨0, hK⟩ T (fun h => ∑ t ∈ Icc 1 T, (adv ω).val t h (h t)) -
        E (fun t => W t ω) ⟨0, hK⟩ T (fun h => ∑ t ∈ Icc 1 T, (adv ω).val t h i)) ∂μ ∧
      Integrable (fun ω => E (fun t => W t ω) ⟨0, hK⟩ T
        (fun h => ∑ t ∈ Icc 1 T, (adv ω).val t h (h t)) -
        E (fun t => W t ω) ⟨0, hK⟩ T (fun h => ∑ t ∈ Icc 1 T, (adv ω).val t h i)) μ := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite
    (f := fun i : Fin K => expect μ W ⟨0, hK⟩ T (fun ω h => ∑ t ∈ Icc 1 T, (adv ω).val t h i))
  have hIA := integrable_ER μ hK adv hadv W hW ⟨0, hK⟩ T
    (fun ω h => ∑ t ∈ Icc 1 T, (adv ω).val t h (h t))
    (fun h => Finset.measurable_fun_sum _ (fun t ht => hadv t (Finset.mem_Icc.1 ht).1 h (h t))) T
    (fun ω h => sum_val_abs_leR (adv ω) T h h)
  have hIi := integrable_ER μ hK adv hadv W hW ⟨0, hK⟩ T
    (fun ω h => ∑ t ∈ Icc 1 T, (adv ω).val t h i)
    (fun h => Finset.measurable_fun_sum _ (fun t ht => hadv t (Finset.mem_Icc.1 ht).1 h i)) T
    (fun ω h => sum_val_abs_leR (adv ω) T h (fun _ => i))
  refine ⟨i, ?_, hIA.sub hIi⟩
  unfold TsallisINF.Half.pseudoRegret
  rw [← hi]
  simp only [expect_eqR]
  rw [integral_sub hIA hIi]

/-- Part 1: adversarial bound. -/
theorem part1 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (adv : Ω → Adversary K) (hadv : ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsTsallisINF etaRV (estRV etaRV adv W) W) (T : ℕ) (hT : 1 ≤ T) :
    TsallisINF.Half.pseudoRegret μ adv W ⟨0, hK⟩ T ≤
      2 * Real.sqrt ((K : ℝ) * (T : ℝ)) + 14 * (K : ℝ) * Real.log (T : ℝ) + 16 := by
  obtain ⟨i, hR, hI⟩ := regret_eq hK μ adv hadv W hW T
  rw [hR]
  calc _ ≤ ∫ _ω, (2 * Real.sqrt ((K : ℝ) * (T : ℝ)) + 14 * (K : ℝ) * Real.log (T : ℝ) + 16) ∂μ := by
        apply integral_mono hI (integrable_const _)
        intro ω
        have H := hyp_ofR hK adv W hW ω
        have h1 := perSeedR H ⟨0, hK⟩ T hT i
        have h2 := E_mono (fun t => W t ω) H.p0 ⟨0, hK⟩ T _ (fun _ =>
          2 * Real.sqrt ((K : ℝ) * (T : ℝ)) + 14 * (K : ℝ) * Real.log (T : ℝ) + 16)
          (fun h => BP_le_adv (fun t => W t ω) T hT h (fun t ht => H.smp t ht h))
        rw [E_const _ H.pc H.sum1] at h2
        exact h1.trans h2
    _ = _ := by simp

end SInt

section SPart2

open Finset TsallisINF.Half RegretBandits.Adversarial MeasureTheory

lemma BP_sb {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (T : ℕ) (hT : 1 ≤ T) (h : ℕ → Fin K)
    (hs : ∀ t, 1 ≤ t → p t h ∈ stdSimplex ℝ (Fin K)) (hK : 1 < K) (Δ : Fin K → ℝ)
    (istar : Fin K) (hΔ : ∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ i, i ≠ istar → 0 < Δ i)
    (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1) :
    (1 + lam) * BP p T h - lam * ∑ t ∈ Icc 1 T, ∑ i ∈ univ.erase istar, p t h i * Δ i ≤
    ((∑ i ∈ univ.erase istar, (Real.log (T : ℝ) + 3) / Δ i) + 2 / deltaMin Δ istar) / lam +
      28 * (K : ℝ) * Real.log (T : ℝ) + 3 / 2 * Real.sqrt (K : ℝ) + 32 := by
  have hb : ∀ t, bR p t h = bRx t (p t h) := fun t => by simp only [bR, bRx, etaRV_eq]
  have := sb_total (fun t => p t h) hs T hT hK Δ istar hΔ hpos lam hl0 hl1
  unfold BP
  simp only [hb]
  exact this

/-- Part 2: self-bounding bound for a parameter `lam ∈ (0, 1]`. -/
theorem part2 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (adv : Ω → Adversary K) (hadv : ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsTsallisINF etaRV (estRV etaRV adv W) W) (T : ℕ) (hT : 1 ≤ T)
    (Δ : Fin K → ℝ) (istar : Fin K) (C : ℝ) (hK1 : 1 < K)
    (hΔ : ∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ i, i ≠ istar → 0 < Δ i)
    (hSB : SelfBounding μ adv W ⟨0, hK⟩ T Δ istar C) (lam : ℝ) (hl0 : 0 < lam)
    (hl1 : lam ≤ 1) :
    TsallisINF.Half.pseudoRegret μ adv W ⟨0, hK⟩ T ≤
      (((∑ i ∈ univ.erase istar, (Real.log (T : ℝ) + 3) / Δ i) + 2 / deltaMin Δ istar) / lam +
      28 * (K : ℝ) * Real.log (T : ℝ) + 3 / 2 * Real.sqrt (K : ℝ) + 32) + lam * C := by
  set M := ((∑ i ∈ univ.erase istar, (Real.log (T : ℝ) + 3) / Δ i) + 2 / deltaMin Δ istar) / lam +
      28 * (K : ℝ) * Real.log (T : ℝ) + 3 / 2 * Real.sqrt (K : ℝ) + 32 with hM
  obtain ⟨i, hR, hI⟩ := regret_eq hK μ adv hadv W hW T
  have hWm := W_measurable hK etaRV (fun s hs => etaRV_pos s hs) adv hadv W hW
  have hIS := integrable_ER μ hK adv hadv W hW ⟨0, hK⟩ T
    (fun ω h => ∑ t ∈ Icc 1 T, ∑ j ∈ univ.erase istar, W t ω h j * Δ j)
    (fun h => Finset.measurable_fun_sum _ (fun t ht => Finset.measurable_fun_sum _
      (fun j _ => (hWm t (Finset.mem_Icc.1 ht).1 h j).mul_const _))) (T : ℝ)
    (fun ω h => sb_bound (fun t => W t ω h) (fun t ht => (hW t ht ω h).1) Δ hΔ istar T)
  have hper : ∀ ω, (1 + lam) * (E (fun t => W t ω) ⟨0, hK⟩ T
        (fun h => ∑ t ∈ Icc 1 T, (adv ω).val t h (h t)) -
        E (fun t => W t ω) ⟨0, hK⟩ T (fun h => ∑ t ∈ Icc 1 T, (adv ω).val t h i)) -
      lam * E (fun t => W t ω) ⟨0, hK⟩ T
        (fun h => ∑ t ∈ Icc 1 T, ∑ j ∈ univ.erase istar, W t ω h j * Δ j) ≤ M := by
    intro ω
    have H := hyp_ofR hK adv W hW ω
    have h1 : E (fun t => W t ω) ⟨0, hK⟩ T (fun h => ∑ t ∈ Icc 1 T, (adv ω).val t h (h t)) -
        E (fun t => W t ω) ⟨0, hK⟩ T (fun h => ∑ t ∈ Icc 1 T, (adv ω).val t h i) ≤
        E (fun t => W t ω) ⟨0, hK⟩ T (fun h => BP (fun t => W t ω) T h) :=
      perSeedR H ⟨0, hK⟩ T hT i
    have h2 := E_mono (fun t => W t ω) H.p0 ⟨0, hK⟩ T
      (fun h => (1 + lam) * BP (fun t => W t ω) T h -
        lam * ∑ t ∈ Icc 1 T, ∑ j ∈ univ.erase istar, W t ω h j * Δ j) (fun _ => M)
      (fun h => BP_sb (fun t => W t ω) T hT h (fun t ht => H.smp t ht h) hK1 Δ istar hΔ hpos
        lam hl0 hl1)
    rw [E_const _ H.pc H.sum1, E_sub, E_mul, E_mul] at h2
    have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + lam)
    linarith
  have hint := integral_mono ((hI.const_mul (1 + lam)).sub (hIS.const_mul lam))
    (integrable_const M) hper
  simp only [Pi.sub_apply] at hint
  rw [integral_sub (hI.const_mul (1 + lam)) (hIS.const_mul lam), integral_const_mul,
    integral_const_mul] at hint
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
  unfold SelfBounding at hSB
  rw [expect_eqR] at hSB
  rw [← hR] at hint
  have h4 := mul_le_mul_of_nonneg_left hSB hl0.le
  nlinarith

end SPart2

end TsallisINF.AdvAlpha.P64936

open MeasureTheory TsallisINF.Half in
theorem solution {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (hadv : ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsTsallisINF etaRV (estRV etaRV adv W) W)
    (T : ℕ) (hT : 1 ≤ T) :
    pseudoRegret μ adv W (⟨0, hK⟩ : Fin K) T ≤
        2 * Real.sqrt ((K : ℝ) * (T : ℝ)) +
          14 * (K : ℝ) * Real.log (T : ℝ) + 16 ∧
      ∀ (Δ : Fin K → ℝ) (istar : Fin K) (C : ℝ),
        1 < K →
        0 ≤ C →
        (∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1) →
        Δ istar = 0 →
        (∀ i, i ≠ istar → 0 < Δ i) →
        SelfBounding μ adv W (⟨0, hK⟩ : Fin K) T Δ istar C →
        let X : ℝ :=
          (∑ i ∈ Finset.univ.erase istar,
            (Real.log (T : ℝ) + 3) / Δ i) + 2 / deltaMin Δ istar
        pseudoRegret μ adv W (⟨0, hK⟩ : Fin K) T ≤
            X + 28 * (K : ℝ) * Real.log (T : ℝ) +
              (3 / 2 : ℝ) * Real.sqrt (K : ℝ) + 32 + C ∧
          (X < C → pseudoRegret μ adv W (⟨0, hK⟩ : Fin K) T ≤
            2 * Real.sqrt (X * C) + 28 * (K : ℝ) * Real.log (T : ℝ) +
              (3 / 2 : ℝ) * Real.sqrt (K : ℝ) + 32) := by
  refine ⟨TsallisINF.AdvAlpha.P64936.part1 hK μ adv hadv W hW T hT, ?_⟩
  intro Δ istar C hK1 hC0 hΔ _hstar hpos hSB
  intro X
  have hXdef : X = (∑ i ∈ Finset.univ.erase istar, (Real.log (T : ℝ) + 3) / Δ i) +
      2 / deltaMin Δ istar := rfl
  have hdm : 0 < deltaMin Δ istar := TsallisINF.AdvAlpha.P64936.dm_pos hK1 Δ istar hpos
  have hlog : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT)
  have hX0 : 0 < X := by
    rw [hXdef]
    have : 0 ≤ ∑ i ∈ Finset.univ.erase istar, (Real.log (T : ℝ) + 3) / Δ i :=
      Finset.sum_nonneg (fun i hi => div_nonneg (by linarith)
        (hpos i (Finset.ne_of_mem_erase hi)).le)
    have : 0 < 2 / deltaMin Δ istar := div_pos two_pos hdm
    linarith
  have P := fun lam hl0 hl1 => TsallisINF.AdvAlpha.P64936.part2 hK μ adv hadv W hW T hT Δ istar C
    hK1 hΔ hpos hSB lam hl0 hl1
  rw [← hXdef] at P
  constructor
  · have := P 1 one_pos le_rfl
    rw [div_one, one_mul] at this
    linarith
  · intro hXC
    have hC : 0 < C := lt_trans hX0 hXC
    have hq : 0 < X / C := div_pos hX0 hC
    have hq1 : X / C < 1 := (div_lt_one hC).2 hXC
    have hl0 : 0 < Real.sqrt (X / C) := Real.sqrt_pos.2 hq
    have hl1 : Real.sqrt (X / C) ≤ 1 := Real.sqrt_le_one.mpr hq1.le
    have := P (Real.sqrt (X / C)) hl0 hl1
    have e1 : X / Real.sqrt (X / C) = Real.sqrt (X * C) := by
      rw [div_eq_iff hl0.ne', ← Real.sqrt_mul (by positivity)]
      rw [show X * C * (X / C) = X ^ 2 by field_simp]
      exact (Real.sqrt_sq hX0.le).symm
    have hCs : Real.sqrt (C ^ 2) = C := Real.sqrt_sq hC.le
    have e2 : Real.sqrt (X / C) * C = Real.sqrt (X * C) := by
      calc Real.sqrt (X / C) * C = Real.sqrt (X / C) * Real.sqrt (C ^ 2) := by rw [hCs]
        _ = Real.sqrt (X / C * C ^ 2) := (Real.sqrt_mul hq.le _).symm
        _ = Real.sqrt (X * C) := by
          rw [pow_two, ← mul_assoc, div_mul_cancel₀ X hC.ne']
    rw [e1, e2] at this
    linarith
