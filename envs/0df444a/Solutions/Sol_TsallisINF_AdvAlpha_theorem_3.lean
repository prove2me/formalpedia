-- Prove2me | solution 1 for TsallisINF.AdvAlpha.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T14:45:16.479542+00:00
-- url     : https://prove2.me/submissions/955abec4-b376-4f59-9a4f-16ac96dd6ed8

import Mathlib
import Definitions.Def_TsallisINF_AdvAlpha_Setting

set_option autoImplicit false

namespace TsallisINF.AdvAlpha.P50255

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
    rw [hsa]; nlinarith
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
    have := neg_abs_le (e * (L j - L i))
    nlinarith
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
      nlinarith
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

lemma W_eq_G {K : ℕ} {Ω : Type*} (hK : 0 < K) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℕ → ℝ) (adv : Ω → Adversary K) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α (fun _ => 1) η (estIW adv W) W) (t : ℕ) (ht : 1 ≤ t) (ω : Ω)
    (h : ℕ → Fin K) : W t ω h = G α (η t) (fun i => Lhat (estIW adv W) t ω h i) :=
  eq_G hK α (η t) hα _ _ ⟨(hW t ht ω h).1, (hW t ht ω h).2⟩

lemma W_causal {K : ℕ} {Ω : Type*} (hK : 0 < K) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℕ → ℝ) (adv : Ω → Adversary K) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α (fun _ => 1) η (estIW adv W) W) :
    ∀ t, 1 ≤ t → ∀ ω h h', AgreeBefore t h h' → W t ω h = W t ω h' := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht ω h h' hag
  rw [W_eq_G hK α hα η adv W hW t ht ω h, W_eq_G hK α hα η adv W hW t ht ω h']
  congr 1
  funext i
  unfold Lhat
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_Ico] at hs
  unfold estIW
  have hs' : h s = h' s := hag s hs.1 hs.2
  have hag' : AgreeBefore s h h' := fun r hr1 hr2 => hag r hr1 (lt_trans hr2 hs.2)
  have hadv : (adv ω).val s h = (adv ω).val s h' := (adv ω).nonanticipating s h h' hag'
  have hWs : W s ω h = W s ω h' := ih s hs.2 hs.1 ω h h' hag'
  rw [hs', hadv, hWs]

lemma W_measurable {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (hK : 0 < K) (α : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (η : ℕ → ℝ) (adv : Ω → Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α (fun _ => 1) η (estIW adv W) W) :
    ∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => W t ω h i) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht h i
  have hL : Measurable (fun ω => (fun j => Lhat (estIW adv W) t ω h j)) := by
    apply measurable_pi_lambda
    intro j
    unfold Lhat
    apply Finset.measurable_fun_sum
    intro s hs
    rw [Finset.mem_Ico] at hs
    unfold estIW
    by_cases hj : h s = j
    · simp only [hj, if_true]
      exact (hadv s h j).div (ih s hs.2 hs.1 h j)
    · simp only [hj, if_false]
      exact measurable_const
  have hG : Measurable (fun ω => G α (η t) (fun j => Lhat (estIW adv W) t ω h j)) :=
    (G_continuous hK α (η t) hα).measurable.comp hL
  have : (fun ω => W t ω h i) = fun ω => G α (η t) (fun j => Lhat (estIW adv W) t ω h j) i := by
    funext ω; rw [W_eq_G hK α hα η adv W hW t ht ω h]
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

section SArith

/-- Tangent-line bound for a concave power: `X^p ≤ Y^p + p Y^(p-1) (X - Y)`. -/
lemma rpow_le_tangent (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X Y : ℝ) (hY : 0 < Y) (hX : 0 ≤ X) :
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

/-- The Agarwal et al. `u`-trick bound of Lemma 12 (paper p. 42):
`K^{1-α} - (K-1)^{1-α} T^{-α} - (1 - 1/T)^α ≤ (K^{1-α} - 1)(1 - T^{-α})` for `K, T ≥ 2`. -/
lemma u_trick_bound (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (k x : ℝ) (hk : 2 ≤ k) (hx : 2 ≤ x) :
    k ^ (1 - α) - (k - 1) ^ (1 - α) * x ^ (-α) - (1 - x⁻¹) ^ α ≤
      (k ^ (1 - α) - 1) * (1 - x ^ (-α)) := by
  obtain ⟨ha0, ha1⟩ := hα
  have hk1 : 0 < k - 1 := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hx0 : 0 < x := by linarith
  -- tangent bounds
  have hK := rpow_le_tangent (1 - α) (by linarith) (by linarith) k (k - 1) hk1 (by linarith)
  have hT := rpow_le_tangent α ha0.le ha1.le x (x - 1) hx1 hx0.le
  have hK' : (k - 1) ^ (1 - α - 1) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hT' : (x - 1) ^ (α - 1) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hKs : k ^ (1 - α) ≤ (k - 1) ^ (1 - α) + (1 - α) := by
    have : (1 - α) * (k - 1) ^ (1 - α - 1) * (k - (k - 1)) ≤ 1 - α := by
      have := mul_le_mul_of_nonneg_left hK' (by linarith : (0:ℝ) ≤ 1 - α)
      nlinarith
    linarith
  have hTs : x ^ α ≤ (x - 1) ^ α + α := by
    have : α * (x - 1) ^ (α - 1) * (x - (x - 1)) ≤ α := by
      have := mul_le_mul_of_nonneg_left hT' ha0.le
      nlinarith
    linarith
  -- (1 - 1/x)^α = (x-1)^α * x^(-α)
  have hfrac : (1 - x⁻¹) ^ α = (x - 1) ^ α * x ^ (-α) := by
    have : 1 - x⁻¹ = (x - 1) * x⁻¹ := by field_simp
    rw [this, Real.mul_rpow hx1.le (inv_nonneg.mpr hx0.le), Real.rpow_neg hx0.le,
      Real.inv_rpow hx0.le]
  have hxa : x ^ (-α) * x ^ α = 1 := by
    rw [← Real.rpow_add hx0]; simp
  have hpos : 0 < x ^ (-α) := Real.rpow_pos_of_pos hx0 _
  rw [hfrac]
  -- K^{1-α} + x^α - 1 ≤ (k-1)^{1-α} + (x-1)^α
  have hsum : k ^ (1 - α) + x ^ α - 1 ≤ (k - 1) ^ (1 - α) + (x - 1) ^ α := by linarith
  have := mul_le_mul_of_nonneg_left hsum hpos.le
  nlinarith [this, hxa]

/-- `x ↦ (1 - x^{-α})/x` is antitone on `[3, ∞)` (its derivative is `((1+α)x^{-α} - 1)/x²`). -/
lemma g_antitoneOn (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    AntitoneOn (fun x : ℝ => (1 - x ^ (-α)) / x) (Set.Ici 3) := by
  obtain ⟨ha0, ha1⟩ := hα
  have heq : Set.EqOn (fun x : ℝ => (1 - x ^ (-α)) / x) (fun x : ℝ => x⁻¹ - x ^ (-α - 1))
      (Set.Ici 3) := by
    intro x hx
    have hx0 : 0 < x := by simp only [Set.mem_Ici] at hx; linarith
    simp only
    rw [Real.rpow_sub hx0, Real.rpow_one]; field_simp
  refine (AntitoneOn.congr ?_ heq.symm)
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  apply antitoneOn_of_deriv_nonpos (convex_Ici 3)
  · intro x hx
    have hx0 : x ≠ 0 := by simp only [Set.mem_Ici] at hx; linarith
    exact (continuousAt_inv₀ hx0).continuousWithinAt.sub
      (Real.continuousAt_rpow_const x _ (Or.inl hx0)).continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : x ≠ 0 := by simp only [Set.mem_Ioi] at hx; linarith
    exact ((hasDerivAt_inv hx0).sub (Real.hasDerivAt_rpow_const (Or.inl hx0))).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    simp only [Set.mem_Ioi] at hx
    have hx0 : 0 < x := by linarith
    have hd : HasDerivAt (fun x : ℝ => x⁻¹ - x ^ (-α - 1))
        (-(x ^ 2)⁻¹ - (-α - 1) * x ^ (-α - 1 - 1)) x :=
      (hasDerivAt_inv hx0.ne').sub (Real.hasDerivAt_rpow_const (p := -α - 1) (Or.inl hx0.ne'))
    rw [hd.deriv]
    -- x^α ≥ 1 + α
    have h3 : 1 + α ≤ x ^ α := by
      have e1 : (3:ℝ) ^ α = Real.exp (α * Real.log 3) := by
        rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
      have e2 : 1 + α * Real.log 3 ≤ Real.exp (α * Real.log 3) := by
        have := Real.add_one_le_exp (α * Real.log 3); linarith
      have e3 : (3:ℝ) ^ α ≤ x ^ α := Real.rpow_le_rpow (by norm_num) hx.le ha0.le
      nlinarith
    have hxa : x ^ (-α - 1 - 1) = x ^ (-α) * (x ^ 2)⁻¹ := by
      rw [show -α - 1 - 1 = -α + (-2 : ℝ) by ring, Real.rpow_add hx0, Real.rpow_neg hx0.le,
        Real.rpow_neg hx0.le]
      norm_num
    rw [hxa]
    have hpos : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
    have hneg : x ^ (-α) = (x ^ α)⁻¹ := Real.rpow_neg hx0.le α
    rw [hneg]
    have hx2 : 0 < (x ^ 2)⁻¹ := by positivity
    have key : (-α - 1) * (x ^ α)⁻¹ ≥ -1 := by
      rw [ge_iff_le, ← sub_nonneg]
      have : (-α - 1) * (x ^ α)⁻¹ - -1 = (x ^ α - (1 + α)) / x ^ α := by field_simp; ring
      rw [this]; exact div_nonneg (by linarith) hpos.le
    nlinarith

/-- `etaThm3` is antitone from round 3 on. -/
lemma etaThm3_succ_le (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (K : ℕ) (hK : 1 ≤ K) (t : ℕ)
    (ht : 3 ≤ t) : etaThm3 α K (t + 1) ≤ etaThm3 α K t := by
  have ha0 := hα.1
  unfold etaThm3
  apply Real.sqrt_le_sqrt
  have hc : 0 ≤ ((K : ℝ) ^ (1 - 2 * α) - (K : ℝ) ^ (-α)) / (1 - α) := by
    apply div_nonneg _ (by linarith [hα.2])
    rw [sub_nonneg]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hK) (by linarith [hα.2])
  apply mul_le_mul_of_nonneg_left _ hc
  have h3 : (3:ℝ) ≤ t := by exact_mod_cast ht
  have hg := g_antitoneOn α hα (show (t:ℝ) ∈ Set.Ici 3 from h3)
    (show ((t + 1 : ℕ) : ℝ) ∈ Set.Ici 3 by simp only [Set.mem_Ici]; push_cast; linarith)
    (by push_cast; linarith)
  simp only at hg
  have ht0 : (0:ℝ) < t := by linarith
  rw [show ((1 - ((t + 1 : ℕ) : ℝ) ^ (-α)) / (α * ((t + 1 : ℕ) : ℝ))) =
      ((1 - ((t + 1 : ℕ) : ℝ) ^ (-α)) / ((t + 1 : ℕ) : ℝ)) / α by
      rw [div_div, mul_comm],
    show (1 - (t : ℝ) ^ (-α)) / (α * t) = ((1 - (t : ℝ) ^ (-α)) / t) / α by rw [div_div, mul_comm]]
  exact div_le_div_of_nonneg_right hg ha0.le

lemma sum_inv_sqrt_le (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt t ≤ 2 * Real.sqrt T - 1 := by
  induction T, hT using Nat.le_induction with
  | base => simp; norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hs := Real.sqrt_nonneg (n : ℝ)
    have hr : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hs2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
    have hr2 : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = n + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have key : 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((n + 1 : ℕ) : ℝ) - 2 * Real.sqrt n := by
      rw [div_le_iff₀ hr]
      nlinarith [sq_nonneg (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n)]
    linarith

lemma rpow_neg_anti (α : ℝ) (ha : 0 ≤ α) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    y ^ (-α) ≤ x ^ (-α) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg (by linarith)]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx α) (Real.rpow_le_rpow hx.le hxy ha)

set_option maxHeartbeats 1000000 in
/-- Pure arithmetic of Theorem 3 (`K, T ≥ 2`): stability sum (with `η_1` replaced by `η_2`), the
refined penalty, and the extra `t = 3` term `2·(η_3/η_2 - 1)^+` fit under `2√(m K T)`. -/
lemma final_arith (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (K T : ℕ) (hK : 2 ≤ K) (hT : 2 ≤ T) :
    (K : ℝ) ^ α / 2 * (etaThm3 α K 2 + ∑ t ∈ Finset.Icc 2 T, etaThm3 α K t) +
      ((K : ℝ) ^ (1 - α) - 1) * (1 - (T : ℝ) ^ (-α)) / ((1 - α) * α * etaThm3 α K T) +
      2 * max 0 (etaThm3 α K 3 / etaThm3 α K 2 - 1) ≤
    2 * Real.sqrt (min (min (1 / (α - α ^ 2)) (Real.log K / α)) (Real.log T / (1 - α)) *
        K * T) := by
  obtain ⟨ha0, ha1⟩ := hα
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  set c : ℝ := ((K : ℝ) ^ (1 - 2 * α) - (K : ℝ) ^ (-α)) / (1 - α) with hc_def
  set A : ℝ → ℝ := fun x => (1 - x ^ (-α)) / α with hA_def
  have heta : ∀ t : ℕ, etaThm3 α K t = Real.sqrt (c * A t / t) := by
    intro t; unfold etaThm3; congr 1; simp only [hA_def, hc_def]; ring
  have hc : 0 < c := by
    apply div_pos _ (by linarith)
    rw [sub_pos]
    exact Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  have hA_mono : ∀ x y : ℝ, 0 < x → x ≤ y → A x ≤ A y := by
    intro x y hx hxy
    simp only [hA_def]
    exact div_le_div_of_nonneg_right (by linarith [rpow_neg_anti α ha0.le x y hx hxy]) ha0.le
  -- A 2 ≥ 1/2
  have hA2 : 1 / 2 ≤ A 2 := by
    have hb := rpow_one_add_le_one_add_mul_self (s := -1 / 2) (by norm_num) ha0.le ha1.le
    have e : (2 : ℝ) ^ (-α) = (1 + -1 / 2) ^ α := by
      rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]; norm_num
    simp only [hA_def]
    rw [le_div_iff₀ ha0, e]; linarith
  have hAT : 1 / 2 ≤ A T := le_trans hA2 (hA_mono 2 T (by norm_num) hT2)
  have hAT0 : 0 < A T := by linarith
  -- K^α K^α c = (K - K^α)/(1-α)
  have hKK : (K : ℝ) ^ α * (K : ℝ) ^ α * c = ((K : ℝ) - (K : ℝ) ^ α) / (1 - α) := by
    simp only [hc_def]
    have e1 : (K : ℝ) ^ α * (K : ℝ) ^ α * (K : ℝ) ^ (1 - 2 * α) = K := by
      rw [← Real.rpow_add hK0, ← Real.rpow_add hK0, show α + α + (1 - 2 * α) = 1 by ring,
        Real.rpow_one]
    have e2 : (K : ℝ) ^ α * (K : ℝ) ^ α * (K : ℝ) ^ (-α) = (K : ℝ) ^ α := by
      rw [mul_assoc, ← Real.rpow_add hK0, show α + -α = 0 by ring, Real.rpow_zero, mul_one]
    rw [mul_div_assoc', mul_sub, e1, e2]
  -- K^{1-α} - 1 = K^α c (1-α)
  have hK1 : (K : ℝ) ^ (1 - α) - 1 = (K : ℝ) ^ α * c * (1 - α) := by
    simp only [hc_def]
    have e1 : (K : ℝ) ^ α * (K : ℝ) ^ (1 - 2 * α) = (K : ℝ) ^ (1 - α) := by
      rw [← Real.rpow_add hK0]; ring_nf
    have e2 : (K : ℝ) ^ α * (K : ℝ) ^ (-α) = 1 := by
      rw [← Real.rpow_add hK0]; simp
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt (by linarith : (0:ℝ) < 1 - α)), mul_sub, e1, e2]
  set B : ℝ := (K : ℝ) ^ α * (K : ℝ) ^ α * c * A T with hB_def
  -- lower bound B ≥ 1/2
  have hKa : (K : ℝ) ^ α ≤ 1 + α * ((K : ℝ) - 1) := by
    have := rpow_one_add_le_one_add_mul_self (s := (K : ℝ) - 1) (by linarith) ha0.le ha1.le
    simpa using this
  have hp1 : 1 ≤ ((K : ℝ) - (K : ℝ) ^ α) / (1 - α) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hB1 : 1 / 2 ≤ B := by
    rw [hB_def, hKK]; nlinarith
  -- upper bound B ≤ m K
  have hpK : ((K : ℝ) - (K : ℝ) ^ α) / (1 - α) ≤ K * min (1 / (1 - α)) (Real.log K) := by
    have hKam : (K : ℝ) ^ α = K * (K : ℝ) ^ (α - 1) := by
      rw [Real.rpow_sub_one hK0.ne']; field_simp
    have hpos : 0 ≤ (K : ℝ) ^ (α - 1) := Real.rpow_nonneg hK0.le _
    have hexp : 1 + (α - 1) * Real.log K ≤ (K : ℝ) ^ (α - 1) := by
      rw [Real.rpow_def_of_pos hK0]
      have := Real.add_one_le_exp (Real.log K * (α - 1)); linarith [mul_comm (Real.log K) (α - 1)]
    rw [hKam, div_le_iff₀ (by linarith)]
    rcases min_cases (1 / (1 - α)) (Real.log K) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
    · have e : (K : ℝ) * (1 / (1 - α)) * (1 - α) = K := by field_simp
      rw [e]; nlinarith [mul_nonneg hK0.le hpos]
    · nlinarith [mul_le_mul_of_nonneg_left hexp hK0.le]
  have hAT1 : A T ≤ min (1 / α) (Real.log T) := by
    simp only [hA_def]
    have hpos : 0 ≤ (T : ℝ) ^ (-α) := Real.rpow_nonneg hT0.le _
    have hexp : 1 + (-α) * Real.log T ≤ (T : ℝ) ^ (-α) := by
      rw [Real.rpow_def_of_pos hT0]
      have := Real.add_one_le_exp (Real.log T * (-α)); linarith [mul_comm (Real.log T) (-α)]
    apply le_min
    · exact div_le_div_of_nonneg_right (by linarith) ha0.le
    · rw [div_le_iff₀ ha0]; nlinarith
  have hBm : B ≤ min (min (1 / (α - α ^ 2)) (Real.log K / α)) (Real.log T / (1 - α)) * K := by
    have hB' : B = ((K : ℝ) - (K : ℝ) ^ α) / (1 - α) * A T := by rw [hB_def, hKK]
    have hP0 : 0 ≤ ((K : ℝ) - (K : ℝ) ^ α) / (1 - α) := by linarith
    have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have h1 := hpK.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hK0.le)
    have h2 := hpK.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK0.le)
    have h3 := hAT1.trans (min_le_left _ _)
    have h4 := hAT1.trans (min_le_right _ _)
    rw [hB']
    have hA0 : 0 ≤ A T := hAT0.le
    have g1 : ((K : ℝ) - (K : ℝ) ^ α) / (1 - α) * A T ≤ K * (1 / (α - α ^ 2)) := by
      have := mul_le_mul h1 h3 hA0 (by positivity)
      have e : (K : ℝ) * (1 / (1 - α)) * (1 / α) = K * (1 / (α - α ^ 2)) := by
        have : α - α ^ 2 = α * (1 - α) := by ring
        rw [this]; field_simp
      linarith
    have g2 : ((K : ℝ) - (K : ℝ) ^ α) / (1 - α) * A T ≤ K * (Real.log K / α) := by
      have := mul_le_mul h2 h3 hA0 (by positivity)
      have e : (K : ℝ) * Real.log K * (1 / α) = K * (Real.log K / α) := by ring
      linarith
    have g3 : ((K : ℝ) - (K : ℝ) ^ α) / (1 - α) * A T ≤ K * (Real.log T / (1 - α)) := by
      have := mul_le_mul h1 h4 hA0 (by positivity)
      have e : (K : ℝ) * (1 / (1 - α)) * Real.log T = K * (Real.log T / (1 - α)) := by ring
      linarith
    rw [mul_comm _ (K : ℝ), mul_min_of_nonneg _ _ hK0.le, mul_min_of_nonneg _ _ hK0.le]
    exact le_min (le_min g1 g2) g3
  -- the main estimate
  set Q : ℝ := Real.sqrt (c * A T) with hQ_def
  have hQ2 : Q ^ 2 = c * A T := Real.sq_sqrt (by positivity)
  have hQ0 : 0 < Q := Real.sqrt_pos.mpr (by positivity)
  set Ka : ℝ := (K : ℝ) ^ α with hKa_def
  have hKa0 : 0 < Ka := Real.rpow_pos_of_pos hK0 α
  have hsT : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hT0
  have hη_le : ∀ t : ℕ, 1 ≤ t → t ≤ T → etaThm3 α K t ≤ Q * (1 / Real.sqrt t) := by
    intro t ht1 htT
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
    rw [heta t, mul_one_div, hQ_def, ← Real.sqrt_div' _ ht0.le]
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ ht0.le
    exact mul_le_mul_of_nonneg_left (hA_mono t T ht0 (by exact_mod_cast htT)) hc.le
  -- stability part
  have hS : etaThm3 α K 2 + ∑ t ∈ Finset.Icc 2 T, etaThm3 α K t ≤
      Q * (2 * Real.sqrt T - 1) := by
    have h2 : etaThm3 α K 2 ≤ Q * (1 / Real.sqrt ((1 : ℕ) : ℝ)) := by
      have := hη_le 2 (by norm_num) hT
      have hs : Q * (1 / Real.sqrt ((2 : ℕ) : ℝ)) ≤ Q * (1 / Real.sqrt ((1 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hQ0.le
        apply one_div_le_one_div_of_le (by simp)
        apply Real.sqrt_le_sqrt; norm_num
      linarith
    have hsum : ∑ t ∈ Finset.Icc 2 T, etaThm3 α K t ≤
        ∑ t ∈ Finset.Icc 2 T, Q * (1 / Real.sqrt t) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.mem_Icc] at ht
      exact hη_le t (by omega) ht.2
    have hfull : ∑ t ∈ Finset.Icc 1 T, Q * (1 / Real.sqrt t) =
        Q * (1 / Real.sqrt ((1 : ℕ) : ℝ)) + ∑ t ∈ Finset.Icc 2 T, Q * (1 / Real.sqrt t) := by
      rw [← Finset.insert_Icc_add_one_left_eq_Icc (show 1 ≤ T by omega),
        Finset.sum_insert (by simp)]
      rfl
    have hb := sum_inv_sqrt_le T (by omega)
    rw [← Finset.mul_sum] at hfull
    have : Q * ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt t ≤ Q * (2 * Real.sqrt T - 1) :=
      mul_le_mul_of_nonneg_left hb hQ0.le
    linarith
  -- penalty part
  have hP : ((K : ℝ) ^ (1 - α) - 1) * (1 - (T : ℝ) ^ (-α)) / ((1 - α) * α * etaThm3 α K T) =
      Ka * Q * Real.sqrt T := by
    have hηT : etaThm3 α K T = Q / Real.sqrt T := by
      rw [heta T, hQ_def, Real.sqrt_div' _ hT0.le]
    have h1T : 1 - (T : ℝ) ^ (-α) = α * A T := by
      simp only [hA_def]; field_simp
    rw [hK1, h1T, hηT, div_eq_iff (by
      have : 0 < 1 - α := by linarith
      positivity)]
    have e : Ka * Q * Real.sqrt T * ((1 - α) * α * (Q / Real.sqrt T)) =
        Ka * Q ^ 2 * (1 - α) * α := by
      field_simp
    rw [e, hQ2]; ring
  -- the t = 3 extra term
  have hX : 2 * max 0 (etaThm3 α K 3 / etaThm3 α K 2 - 1) ≤ 1 / 3 := by
    have hA32 : A 3 ≤ 2 * A 2 := by
      have h43 := rpow_neg_anti α ha0.le 3 4 (by norm_num) (by norm_num)
      have e4 : (4 : ℝ) ^ (-α) = (2 : ℝ) ^ (-α) * (2 : ℝ) ^ (-α) := by
        rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
      have hy : (2 : ℝ) ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      simp only [hA_def]
      rw [mul_div_assoc', div_le_div_iff_of_pos_right ha0]
      nlinarith [sq_nonneg (1 - (2 : ℝ) ^ (-α))]
    have hη2 : 0 < etaThm3 α K 2 := by
      rw [heta 2]; apply Real.sqrt_pos.mpr
      have : 0 < A 2 := by linarith
      positivity
    have hη3 : etaThm3 α K 3 ≤ 7 / 6 * etaThm3 α K 2 := by
      rw [heta 3, heta 2]
      have e : (7 / 6 : ℝ) * Real.sqrt (c * A ((2 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) =
          Real.sqrt ((7 / 6) ^ 2 * (c * A ((2 : ℕ) : ℝ) / ((2 : ℕ) : ℝ))) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
      rw [e]
      apply Real.sqrt_le_sqrt
      push_cast
      have hcA : c * A 3 ≤ c * (2 * A 2) := mul_le_mul_of_nonneg_left hA32 hc.le
      have hcA2 : 0 ≤ c * A 2 := mul_nonneg hc.le (by linarith)
      linarith
    have h76 : etaThm3 α K 3 / etaThm3 α K 2 ≤ 7 / 6 := by rw [div_le_iff₀ hη2]; linarith
    have : etaThm3 α K 3 / etaThm3 α K 2 - 1 ≤ 1 / 6 := by linarith
    have := max_le (show (0 : ℝ) ≤ 1 / 6 by norm_num) this
    linarith
  -- B = (Ka Q)^2
  have hBQ : (Ka * Q) ^ 2 = B := by rw [mul_pow, hQ2, hB_def]; ring
  have hKQ : 2 / 3 ≤ Ka * Q := by nlinarith [mul_pos hKa0 hQ0]
  -- assemble
  have hfin : Ka * Q * Real.sqrt T ≤
      Real.sqrt (min (min (1 / (α - α ^ 2)) (Real.log K / α)) (Real.log T / (1 - α)) * K * T) := by
    rw [← Real.sqrt_sq (show 0 ≤ Ka * Q * Real.sqrt T by positivity)]
    apply Real.sqrt_le_sqrt
    rw [mul_pow, hBQ, Real.sq_sqrt hT0.le]
    exact mul_le_mul_of_nonneg_right hBm hT0.le
  have hS' := mul_le_mul_of_nonneg_left hS (show 0 ≤ Ka / 2 by positivity)
  rw [hP]
  nlinarith

end SArith

section SAssembly

open Finset TsallisINF.Half RegretBandits.Adversarial MeasureTheory

noncomputable def lh {K : ℕ} (ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (t : ℕ) (h : ℕ → Fin K)
    (k : Fin K) : ℝ :=
  if h t = k then ℓ t h k / p t h k else 0

noncomputable def qf {K : ℕ} (α : ℝ) (ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (t : ℕ)
    (h : ℕ → Fin K) : ℝ :=
  ∑ k, p t h k ^ (2 - α) * lh ℓ p t h k ^ 2

noncomputable def xf {K : ℕ} (ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (s : ℕ) (h : ℕ → Fin K) : ℝ :=
  ∑ k, p 1 h k * lh ℓ p s h k

noncomputable def rf {K : ℕ} (ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (u : Fin K → ℝ) (t : ℕ)
    (h : ℕ → Fin K) : ℝ :=
  ∑ k, (p t h k - u k) * lh ℓ p t h k

noncomputable def gf {K : ℕ} (ℓ : ℕ → (ℕ → Fin K) → Fin K → ℝ) (u : Fin K → ℝ) (t : ℕ)
    (h : ℕ → Fin K) : ℝ :=
  ℓ t h (h t) - ∑ k, u k * ℓ t h k

noncomputable def eP (α : ℝ) (K : ℕ) (t : ℕ) : ℝ :=
  if t ≤ 1 then etaThm3 α K 2 else etaThm3 α K t

noncomputable def uvec (K T : ℕ) (i : Fin K) (k : Fin K) : ℝ :=
  if k = i then 1 - (T : ℝ)⁻¹ else ((T : ℝ) * ((K : ℝ) - 1))⁻¹

/-- Per-seed hypotheses: losses in `[0,1]`, causal weights in the open simplex maximizing the
OMD objective with importance-weighted estimates and learning rate `etaThm3`. -/
structure Hyp {K : ℕ} (α : ℝ) (ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ) : Prop where
  l0 : ∀ t h k, 0 ≤ ℓ t h k
  l1 : ∀ t h k, ℓ t h k ≤ 1
  lc : ∀ t h h', AgreeBefore t h h' → ℓ t h = ℓ t h'
  pc : Causal p
  smp : ∀ t, 1 ≤ t → ∀ h, p t h ∈ stdSimplex ℝ (Fin K)
  pos : ∀ t, 1 ≤ t → ∀ h k, 0 < p t h k
  arg : ∀ t, 1 ≤ t → ∀ h,
    IsArgmax α (etaThm3 α K t) (fun k => ∑ s ∈ Ico 1 t, lh ℓ p s h k) (p t h)

lemma Hyp.sum1 {K : ℕ} {α : ℝ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ} (H : Hyp α ℓ p) :
    ∀ s, 1 ≤ s → ∀ h, ∑ j, p s h j = 1 := fun s hs h => (H.smp s hs h).2

lemma Hyp.p0 {K : ℕ} {α : ℝ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ} (H : Hyp α ℓ p) :
    ∀ s, 1 ≤ s → ∀ h j, 0 ≤ p s h j := fun s hs h j => (H.pos s hs h j).le

lemma lh_nonneg {K : ℕ} {α : ℝ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ} (H : Hyp α ℓ p)
    (t : ℕ) (ht : 1 ≤ t) (h : ℕ → Fin K) (k : Fin K) : 0 ≤ lh ℓ p t h k := by
  unfold lh
  split_ifs
  · exact div_nonneg (H.l0 t h k) (H.pos t ht h k).le
  · exact le_rfl

lemma agree_of_upto {K : ℕ} {h h' : ℕ → Fin K} {t : ℕ}
    (hh : ∀ s, 1 ≤ s → s ≤ t → h s = h' s) : AgreeBefore t h h' :=
  fun s h1 h2 => hh s h1 h2.le

lemma upd_agree {K : ℕ} (h : ℕ → Fin K) (t : ℕ) (j : Fin K) :
    AgreeBefore t (Function.update h t j) h :=
  fun s _ hs => Function.update_of_ne (ne_of_lt hs) _ _

lemma lh_congr {K : ℕ} {α : ℝ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ} (H : Hyp α ℓ p)
    (t : ℕ) (ht : 1 ≤ t) (h h' : ℕ → Fin K) (hh : ∀ s, 1 ≤ s → s ≤ t → h s = h' s) :
    lh ℓ p t h = lh ℓ p t h' := by
  funext k
  unfold lh
  rw [hh t ht le_rfl, H.lc t h h' (agree_of_upto hh), H.pc t ht h h' (agree_of_upto hh)]

lemma lh_update {K : ℕ} {α : ℝ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ} (H : Hyp α ℓ p)
    (t : ℕ) (ht : 1 ≤ t) (h : ℕ → Fin K) (j k : Fin K) :
    lh ℓ p t (Function.update h t j) k = if j = k then ℓ t h k / p t h k else 0 := by
  unfold lh
  rw [Function.update_self, H.lc t _ h (upd_agree h t j), H.pc t ht _ h (upd_agree h t j)]

lemma cond_unbiased {K : ℕ} {α : ℝ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ} (H : Hyp α ℓ p)
    (t : ℕ) (ht : 1 ≤ t) (h : ℕ → Fin K) (v : Fin K → ℝ) :
    ∑ j, p t h j * ∑ k, v k * lh ℓ p t (Function.update h t j) k = ∑ k, v k * ℓ t h k := by
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [lh_update H t ht h j, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  have := (H.pos t ht h j).ne'
  field_simp

lemma E_le_of_cond {K : ℕ} (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hc : Causal p)
    (hsum : ∀ s, 1 ≤ s → ∀ h, ∑ j, p s h j = 1) (hp : ∀ s, 1 ≤ s → ∀ h j, 0 ≤ p s h j)
    (i₀ : Fin K) (t T : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (F G : (ℕ → Fin K) → ℝ)
    (hF : DepUpTo t F) (hG : DepUpTo t G)
    (hFG : ∀ h, ∑ j, p t h j * F (Function.update h t j) ≤
      ∑ j, p t h j * G (Function.update h t j)) :
    E p i₀ T F ≤ E p i₀ T G := by
  rw [E_cond p hc hsum i₀ t T ht htT F hF, E_cond p hc hsum i₀ t T ht htT G hG]
  exact E_mono p hp i₀ (t - 1) _ _ hFG

lemma rpow_tangent_sum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) (hK : 0 < K)
    (w : Fin K → ℝ) (hw : w ∈ stdSimplex ℝ (Fin K)) : ∑ i, w i ^ q ≤ (K : ℝ) ^ (1 - q) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hY : (0 : ℝ) < (K : ℝ)⁻¹ := inv_pos.2 hK0
  calc ∑ i, w i ^ q ≤ ∑ i, ((K : ℝ)⁻¹ ^ q + q * (K : ℝ)⁻¹ ^ (q - 1) * (w i - (K : ℝ)⁻¹)) :=
        Finset.sum_le_sum (fun i _ => rpow_le_tangent q hq0 hq1 (w i) _ hY (hw.1 i))
    _ = K * (K : ℝ)⁻¹ ^ q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hw.2,
          Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          nsmul_eq_mul, mul_inv_cancel₀ hK0.ne', sub_self, mul_zero, add_zero]
    _ = (K : ℝ) ^ (1 - q) := by
        rw [Real.inv_rpow hK0.le, Real.rpow_sub hK0, Real.rpow_one, div_eq_mul_inv]

lemma psi_simplex {K : ℕ} (α : ℝ) (w : Fin K → ℝ) (hw : w ∈ stdSimplex ℝ (Fin K)) :
    tsallisPsi α (fun _ => 1) w = -(∑ i, w i ^ α - α) / (α * (1 - α)) := by
  unfold tsallisPsi
  simp only [mul_one]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hw.2]
  ring

lemma Ico_one_succ (T : ℕ) : Finset.Ico 1 (T + 1) = Finset.Icc 1 T := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

lemma tel_sum (f : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Icc 2 T, (f t - f (t - 1)) = f T - f 1 := by
  induction T, hT using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel]
    ring

lemma eta_pos (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (K : ℕ) (hK : 2 ≤ K) (t : ℕ) (ht : 2 ≤ t) :
    0 < etaThm3 α K t := by
  obtain ⟨ha0, ha1⟩ := hα
  unfold etaThm3
  apply Real.sqrt_pos.mpr
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (show 1 < K by omega)
  have ht1 : (1 : ℝ) < t := by exact_mod_cast (show 1 < t by omega)
  apply mul_pos
  · apply div_pos _ (by linarith)
    rw [sub_pos]
    exact Real.rpow_lt_rpow_of_exponent_lt hK1 (by linarith)
  · apply div_pos
    · rw [sub_pos]
      exact Real.rpow_lt_one_of_one_lt_of_neg ht1 (by linarith)
    · exact mul_pos ha0 (by linarith)

lemma eP_pos (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (K : ℕ) (hK : 2 ≤ K) (t : ℕ) (ht : 1 ≤ t) :
    0 < eP α K t := by
  unfold eP
  split_ifs with h1
  · exact eta_pos α hα K hK 2 le_rfl
  · exact eta_pos α hα K hK t (by omega)

lemma sum_uvec {K T : ℕ} (i : Fin K) (hK : 1 ≤ K) (f : ℝ → ℝ) :
    ∑ k, f (uvec K T i k) =
      f (1 - (T : ℝ)⁻¹) + ((K : ℝ) - 1) * f (((T : ℝ) * ((K : ℝ) - 1))⁻¹) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h1 : uvec K T i i = 1 - (T : ℝ)⁻¹ := by simp [uvec]
  have h2 : ∀ k ∈ Finset.univ.erase i, f (uvec K T i k) = f (((T : ℝ) * ((K : ℝ) - 1))⁻¹) := by
    intro k hk
    rw [Finset.mem_erase] at hk
    simp [uvec, hk.1]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hK, Nat.cast_one]

lemma uvec_simplex {K T : ℕ} (i : Fin K) (hK : 2 ≤ K) (hT : 1 ≤ T) :
    uvec K T i ∈ stdSimplex ℝ (Fin K) := by
  have hk1 : (0 : ℝ) < (K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  refine ⟨fun k => ?_, ?_⟩
  · unfold uvec
    split_ifs
    · have : (T : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT1
      linarith
    · exact (inv_pos.2 (mul_pos hT0 hk1)).le
  · have hs := sum_uvec (T := T) i (by omega : 1 ≤ K) id
    simp only [id] at hs
    rw [hs, mul_inv, ← mul_assoc, mul_comm ((K : ℝ) - 1) (T : ℝ)⁻¹, mul_assoc,
      mul_inv_cancel₀ hk1.ne', mul_one, sub_add_cancel]

lemma uvec_sum_rpow {K T : ℕ} (i : Fin K) (hK : 2 ≤ K) (hT : 1 ≤ T) (α : ℝ) :
    ∑ k, uvec K T i k ^ α = (1 - (T : ℝ)⁻¹) ^ α + ((K : ℝ) - 1) ^ (1 - α) * (T : ℝ) ^ (-α) := by
  have hs := sum_uvec (T := T) i (by omega : 1 ≤ K) (fun x => x ^ α)
  rw [hs]
  have hk1 : (0 : ℝ) < (K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  rw [Real.inv_rpow (mul_pos hT0 hk1).le, Real.mul_rpow hT0.le hk1.le, Real.rpow_sub hk1,
    Real.rpow_one, Real.rpow_neg hT0.le]
  congr 1
  rw [mul_inv]
  ring

lemma uvec_dot_le {K T : ℕ} (i : Fin K) (hK : 2 ≤ K) (hT : 1 ≤ T) (v : Fin K → ℝ)
    (hv0 : ∀ k, 0 ≤ v k) (hv1 : ∀ k, v k ≤ 1) :
    ∑ k, uvec K T i k * v k - v i ≤ (T : ℝ)⁻¹ := by
  have hk1 : (0 : ℝ) < (K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hc : 0 ≤ ((T : ℝ) * ((K : ℝ) - 1))⁻¹ := (inv_pos.2 (mul_pos hT0 hk1)).le
  have h1 : ∑ k ∈ Finset.univ.erase i, uvec K T i k * v k ≤
      ∑ k ∈ Finset.univ.erase i, ((T : ℝ) * ((K : ℝ) - 1))⁻¹ := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_erase] at hk
    simp only [uvec, if_neg hk.1]
    exact mul_le_of_le_one_right hc (hv1 k)
  have h2 : ∑ k ∈ Finset.univ.erase i, ((T : ℝ) * ((K : ℝ) - 1))⁻¹ = (T : ℝ)⁻¹ := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one, mul_inv,
      ← mul_assoc, mul_comm ((K : ℝ) - 1) (T : ℝ)⁻¹, mul_assoc, mul_inv_cancel₀ hk1.ne', mul_one]
  have h3 : uvec K T i i * v i = (1 - (T : ℝ)⁻¹) * v i := by simp [uvec]
  rw [h3]
  have hTi : 0 ≤ (T : ℝ)⁻¹ * v i := mul_nonneg (inv_nonneg.2 hT0.le) (hv0 i)
  nlinarith

lemma E_round1 {K : ℕ} {α : ℝ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ} (H : Hyp α ℓ p)
    (i₀ : Fin K) (t T : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (u : Fin K → ℝ) :
    E p i₀ T (gf ℓ u t) = E p i₀ T (rf ℓ p u t) := by
  have hF : DepUpTo t (gf ℓ u t) := by
    intro h h' hh
    unfold gf
    rw [H.lc t h h' (agree_of_upto hh), hh t ht le_rfl]
  have hG : DepUpTo t (rf ℓ p u t) := by
    intro h h' hh
    unfold rf
    rw [H.pc t ht h h' (agree_of_upto hh), lh_congr H t ht h h' hh]
  have hc : ∀ h, ∑ j, p t h j * gf ℓ u t (Function.update h t j) =
      ∑ j, p t h j * rf ℓ p u t (Function.update h t j) := by
    intro h
    have e1 : ∀ j, ℓ t (Function.update h t j) = ℓ t h := fun j => H.lc t _ h (upd_agree h t j)
    have e2 : ∀ j, p t (Function.update h t j) = p t h :=
      fun j => H.pc t ht _ h (upd_agree h t j)
    unfold gf rf
    simp only [e1, e2, Function.update_self]
    have hu := cond_unbiased H t ht h (fun k => p t h k - u k)
    rw [hu]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, H.sum1 t ht h, one_mul]
  exact le_antisymm
    (E_le_of_cond p H.pc H.sum1 H.p0 i₀ t T ht htT _ _ hF hG (fun h => (hc h).le))
    (E_le_of_cond p H.pc H.sum1 H.p0 i₀ t T ht htT _ _ hG hF (fun h => (hc h).ge))

lemma E_round2 {K : ℕ} {α : ℝ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (H : Hyp α ℓ p) (hK : 0 < K) (i₀ : Fin K) (t T : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ T) : E p i₀ T (qf α ℓ p t) ≤ (K : ℝ) ^ α := by
  have hF : DepUpTo t (qf α ℓ p t) := by
    intro h h' hh
    unfold qf
    rw [H.pc t ht h h' (agree_of_upto hh), lh_congr H t ht h h' hh]
  have key := E_le_of_cond p H.pc H.sum1 H.p0 i₀ t T ht htT (qf α ℓ p t)
    (fun _ => (K : ℝ) ^ α) hF (fun _ _ _ => rfl) ?_
  · rwa [E_const p H.pc H.sum1] at key
  intro h
  rw [← Finset.sum_mul, H.sum1 t ht h, one_mul]
  have e2 : ∀ j, p t (Function.update h t j) = p t h := fun j => H.pc t ht _ h (upd_agree h t j)
  unfold qf
  simp only [e2]
  have hj : ∀ j, p t h j * ∑ k, p t h k ^ (2 - α) * lh ℓ p t (Function.update h t j) k ^ 2 ≤
      p t h j ^ (1 - α) := by
    intro j
    have hsum : ∑ k, p t h k ^ (2 - α) * lh ℓ p t (Function.update h t j) k ^ 2 =
        p t h j ^ (2 - α) * (ℓ t h j / p t h j) ^ 2 := by
      rw [Finset.sum_eq_single j]
      · rw [lh_update H t ht h j j, if_pos rfl]
      · intro k _ hkj
        rw [lh_update H t ht h j k, if_neg (Ne.symm hkj)]
        ring
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hsum]
    have hp := H.pos t ht h j
    have hl0 := H.l0 t h j
    have hl1 := H.l1 t h j
    rw [show (2 : ℝ) - α = (1 - α) + 1 by ring, Real.rpow_add_one hp.ne']
    have hpa : 0 ≤ p t h j ^ (1 - α) := Real.rpow_nonneg hp.le _
    have heq : p t h j * (p t h j ^ (1 - α) * p t h j * (ℓ t h j / p t h j) ^ 2) =
        p t h j ^ (1 - α) * ℓ t h j ^ 2 := by
      field_simp
    rw [heq]
    have : ℓ t h j ^ 2 ≤ 1 := by nlinarith
    calc _ ≤ p t h j ^ (1 - α) * 1 := mul_le_mul_of_nonneg_left this hpa
      _ = _ := mul_one _
  calc _ ≤ ∑ j, p t h j ^ (1 - α) := Finset.sum_le_sum (fun j _ => hj j)
    _ ≤ (K : ℝ) ^ (1 - (1 - α)) :=
        rpow_tangent_sum (1 - α) (by linarith [hα.2]) (by linarith [hα.1]) K hK (p t h)
          (H.smp t ht h)
    _ = (K : ℝ) ^ α := by rw [sub_sub_cancel]

lemma E_round3 {K : ℕ} {α : ℝ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ} (H : Hyp α ℓ p)
    (i₀ : Fin K) (s T : ℕ) (hs : 1 ≤ s) (hsT : s ≤ T) : E p i₀ T (xf ℓ p s) ≤ 1 := by
  have h1 : ∀ h h' : ℕ → Fin K, p 1 h = p 1 h' :=
    fun h h' => H.pc 1 le_rfl h h' (fun r hr1 hr2 => absurd hr1 (by omega))
  have hF : DepUpTo s (xf ℓ p s) := by
    intro h h' hh
    unfold xf
    rw [h1 h h', lh_congr H s hs h h' hh]
  have key := E_le_of_cond p H.pc H.sum1 H.p0 i₀ s T hs hsT (xf ℓ p s) (fun _ => (1 : ℝ))
    hF (fun _ _ _ => rfl) ?_
  · rwa [E_const p H.pc H.sum1] at key
  intro h
  rw [← Finset.sum_mul, H.sum1 s hs h, one_mul]
  unfold xf
  have e1 : ∀ j, p 1 (Function.update h s j) = p 1 h := fun j => h1 _ _
  simp only [e1]
  rw [cond_unbiased H s hs h (p 1 h)]
  calc ∑ k, p 1 h k * ℓ s h k ≤ ∑ k, p 1 h k :=
        Finset.sum_le_sum (fun k _ => mul_le_of_le_one_right (H.p0 1 le_rfl h k) (H.l1 s h k))
    _ = 1 := H.sum1 1 le_rfl h

set_option maxHeartbeats 1000000 in
lemma pathwise {K : ℕ} {α : ℝ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (H : Hyp α ℓ p) (hK : 2 ≤ K) (T : ℕ) (hT : 2 ≤ T)
    (i : Fin K) (h : ℕ → Fin K) :
    ∑ t ∈ Icc 1 T, rf ℓ p (uvec K T i) t h ≤
      ∑ t ∈ Icc 1 T, eP α K t / 2 * qf α ℓ p t h +
      ((K : ℝ) ^ (1 - α) - 1) * (1 - (T : ℝ) ^ (-α)) / ((1 - α) * α * etaThm3 α K T) +
      max 0 (etaThm3 α K 3 / etaThm3 α K 2 - 1) * (xf ℓ p 1 h + xf ℓ p 2 h) := by
  have ha0 := hα.1
  have ha1 := hα.2
  have hηpos : ∀ t, 2 ≤ t → 0 < etaThm3 α K t := fun t ht => eta_pos α hα K hK t ht
  have hepos : ∀ t, 1 ≤ t → 0 < eP α K t := fun t ht => eP_pos α hα K hK t ht
  obtain ⟨Lh, hLh⟩ : ∃ Lh : ℕ → Fin K → ℝ, Lh = fun t k => ∑ s ∈ Ico 1 t, lh ℓ p s h k :=
    ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℕ → Fin K → ℝ, l = fun t k => if 1 ≤ t then lh ℓ p t h k else 0 :=
    ⟨_, rfl⟩
  have hL1 : ∀ k, Lh 1 k = 0 := by intro k; rw [hLh]; simp
  have hLs : ∀ t k, Lh (t + 1) k = Lh t k + l t k := by
    intro t k
    rw [hLh, hl]
    simp only
    split_ifs with ht
    · rw [Finset.sum_Ico_succ_top ht]
    · have : t = 0 := by omega
      subst this
      simp
  have hlnn : ∀ t k, 0 ≤ l t k := by
    intro t k
    rw [hl]
    simp only
    split_ifs with ht
    · exact lh_nonneg H t ht h k
    · exact le_rfl
  have hx : ∀ t, 1 ≤ t → IsArgmax α (eP α K t) (Lh t) (p t h) := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have h1 : t = 1 := by omega
      subst h1
      refine ⟨(H.arg 1 le_rfl h).1, fun v hv => ?_⟩
      have := (H.arg 1 le_rfl h).2 v hv
      rw [hLh]
      simp [obj] at this ⊢
      linarith
    · have : eP α K t = etaThm3 α K t := by unfold eP; rw [if_neg ht1]
      rw [this, hLh]
      exact H.arg t ht h
  have hu : uvec K T i ∈ stdSimplex ℝ (Fin K) := uvec_simplex i hK (by omega)
  have htel := telescope α hα (eP α K) (fun t => p t h) l Lh hL1 hLs hepos hx hlnn T (by omega)
    (uvec K T i) hu
  simp only at htel
  have hlI : ∀ t ∈ Icc 1 T, l t = lh ℓ p t h := by
    intro t ht
    rw [hl]
    funext k
    simp only
    rw [if_pos (Finset.mem_Icc.1 ht).1]
  have hA : ∑ t ∈ Icc 1 T, ∑ i, p t h i * l t i =
      ∑ t ∈ Icc 1 T, ∑ k, p t h k * lh ℓ p t h k :=
    Finset.sum_congr rfl (fun t ht => by rw [hlI t ht])
  have hB : ∑ t ∈ Icc 1 T, eP α K t / 2 * ∑ i, p t h i ^ (2 - α) * l t i ^ 2 =
      ∑ t ∈ Icc 1 T, eP α K t / 2 * qf α ℓ p t h :=
    Finset.sum_congr rfl (fun t ht => by simp only [hlI t ht, qf])
  have hC : ∑ k, uvec K T i k * -Lh (T + 1) k =
      -∑ t ∈ Icc 1 T, ∑ k, uvec K T i k * lh ℓ p t h k := by
    rw [hLh]
    simp only
    rw [Ico_one_succ T]
    simp_rw [mul_neg, Finset.mul_sum]
    rw [Finset.sum_neg_distrib, Finset.sum_comm]
  rw [hA, hB, hC] at htel
  -- the regularizer terms
  have htel2 := tel_sum (fun t => 1 / eP α K t) T (by omega)
  have hsplit : ∑ t ∈ Icc 2 T, (1 / eP α K t - 1 / eP α K (t - 1)) *
        tsallisPsi α (fun _ => 1) (p t h) =
      ∑ t ∈ Icc 2 T, (1 / eP α K t - 1 / eP α K (t - 1)) *
        (tsallisPsi α (fun _ => 1) (p t h) - tsallisPsi α (fun _ => 1) (p 1 h)) +
      (tsallisPsi α (fun _ => 1) (p 1 h) / eP α K T -
        tsallisPsi α (fun _ => 1) (p 1 h) / eP α K 1) := by
    have e : tsallisPsi α (fun _ => 1) (p 1 h) / eP α K T -
        tsallisPsi α (fun _ => 1) (p 1 h) / eP α K 1 =
        ∑ t ∈ Icc 2 T, (1 / eP α K t - 1 / eP α K (t - 1)) *
          tsallisPsi α (fun _ => 1) (p 1 h) := by
      rw [← Finset.sum_mul, htel2]
      ring
    rw [e, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hD : ∀ t, 1 ≤ t →
      tsallisPsi α (fun _ => 1) (p 1 h) ≤ tsallisPsi α (fun _ => 1) (p t h) := by
    intro t ht
    have := (H.arg 1 le_rfl h).2 (p t h) (H.smp t ht h)
    simp [obj] at this
    linarith
  set M := max 0 (etaThm3 α K 3 / etaThm3 α K 2 - 1) with hM
  have hM0 : 0 ≤ M := le_max_left _ _
  have hX0 : 0 ≤ xf ℓ p 1 h + xf ℓ p 2 h := by
    unfold xf
    apply add_nonneg
    · exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (H.p0 1 le_rfl h k) (lh_nonneg H 1 le_rfl h k))
    · exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (H.p0 1 le_rfl h k) (lh_nonneg H 2 (by norm_num) h k))
  have h3bound : tsallisPsi α (fun _ => 1) (p 3 h) - tsallisPsi α (fun _ => 1) (p 1 h) ≤
      etaThm3 α K 3 * (xf ℓ p 1 h + xf ℓ p 2 h) := by
    have h3 := (H.arg 3 (by norm_num) h).2 (p 1 h) (H.smp 1 le_rfl h)
    unfold obj at h3
    simp only at h3
    have hI : Finset.Ico 1 3 = {1, 2} := by decide
    have e1 : ∑ k, p 1 h k * -(∑ s ∈ Ico 1 3, lh ℓ p s h k) = -(xf ℓ p 1 h + xf ℓ p 2 h) := by
      unfold xf
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [hI, Finset.sum_pair (by norm_num)]
      ring
    have e2 : ∑ k, p 3 h k * -(∑ s ∈ Ico 1 3, lh ℓ p s h k) ≤ 0 := by
      apply Finset.sum_nonpos
      intro k _
      have h1 := H.p0 3 (by norm_num) h k
      have h2 : 0 ≤ ∑ s ∈ Ico 1 3, lh ℓ p s h k :=
        Finset.sum_nonneg (fun s hs => lh_nonneg H s (Finset.mem_Ico.1 hs).1 h k)
      nlinarith
    rw [e1] at h3
    have h4 := mul_le_mul_of_nonneg_left e2 (hηpos 3 (by norm_num)).le
    rw [mul_zero] at h4
    nlinarith
  have hterm : ∀ t ∈ Icc 2 T, -((1 / eP α K t - 1 / eP α K (t - 1)) *
      (tsallisPsi α (fun _ => 1) (p t h) - tsallisPsi α (fun _ => 1) (p 1 h))) ≤
      if t = 3 then M * (xf ℓ p 1 h + xf ℓ p 2 h) else 0 := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have hDt := hD t (by omega)
    rcases (show t = 2 ∨ t = 3 ∨ 4 ≤ t by omega) with rfl | rfl | h4
    · simp [eP]
    · rw [if_pos rfl]
      have e3 : eP α K 3 = etaThm3 α K 3 := by simp [eP]
      have e2 : eP α K (3 - 1) = etaThm3 α K 2 := by simp [eP]
      rw [e3, e2]
      have hη2 := hηpos 2 le_rfl
      have hη3 := hηpos 3 (by norm_num)
      rcases le_total (1 / etaThm3 α K 2 - 1 / etaThm3 α K 3) 0 with hc | hc
      · have h5 := mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤
          tsallisPsi α (fun _ => 1) (p 3 h) - tsallisPsi α (fun _ => 1) (p 1 h))
        have h6 := mul_nonneg hM0 hX0
        nlinarith
      · have h5 := mul_le_mul_of_nonneg_left h3bound hc
        have h6 : (1 / etaThm3 α K 2 - 1 / etaThm3 α K 3) *
            (etaThm3 α K 3 * (xf ℓ p 1 h + xf ℓ p 2 h)) =
            (etaThm3 α K 3 / etaThm3 α K 2 - 1) * (xf ℓ p 1 h + xf ℓ p 2 h) := by
          field_simp
        have h7 : (etaThm3 α K 3 / etaThm3 α K 2 - 1) * (xf ℓ p 1 h + xf ℓ p 2 h) ≤
            M * (xf ℓ p 1 h + xf ℓ p 2 h) := mul_le_mul_of_nonneg_right (le_max_right _ _) hX0
        nlinarith
    · have ht3 : t ≠ 3 := by omega
      rw [if_neg ht3]
      have e1 : eP α K t = etaThm3 α K t := by unfold eP; rw [if_neg (by omega)]
      have e2 : eP α K (t - 1) = etaThm3 α K (t - 1) := by unfold eP; rw [if_neg (by omega)]
      rw [e1, e2]
      have hle : etaThm3 α K t ≤ etaThm3 α K (t - 1) := by
        have := etaThm3_succ_le α hα K (by omega) (t - 1) (by omega)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ t)] at this
      have hc : 0 ≤ 1 / etaThm3 α K t - 1 / etaThm3 α K (t - 1) := by
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le (hηpos t (by omega)) hle
      have := mul_nonneg hc (by linarith : (0 : ℝ) ≤
        tsallisPsi α (fun _ => 1) (p t h) - tsallisPsi α (fun _ => 1) (p 1 h))
      linarith
  have hb : -∑ t ∈ Icc 2 T, (1 / eP α K t - 1 / eP α K (t - 1)) *
      (tsallisPsi α (fun _ => 1) (p t h) - tsallisPsi α (fun _ => 1) (p 1 h)) ≤
      M * (xf ℓ p 1 h + xf ℓ p 2 h) := by
    rw [← Finset.sum_neg_distrib]
    calc _ ≤ ∑ t ∈ Icc 2 T, (if t = 3 then M * (xf ℓ p 1 h + xf ℓ p 2 h) else 0) :=
          Finset.sum_le_sum hterm
      _ ≤ _ := by
          rw [Finset.sum_ite_eq']
          split_ifs
          · exact le_rfl
          · exact mul_nonneg hM0 hX0
  -- the penalty term
  have hpen : tsallisPsi α (fun _ => 1) (uvec K T i) - tsallisPsi α (fun _ => 1) (p 1 h) ≤
      ((K : ℝ) ^ (1 - α) - 1) * (1 - (T : ℝ) ^ (-α)) / (α * (1 - α)) := by
    rw [psi_simplex α _ hu, psi_simplex α (p 1 h) (H.smp 1 le_rfl h),
      uvec_sum_rpow i hK (by omega) α]
    have hs := rpow_tangent_sum α ha0.le ha1.le K (by omega) (p 1 h) (H.smp 1 le_rfl h)
    have hut := u_trick_bound α hα K T (by exact_mod_cast hK) (by exact_mod_cast hT)
    have hd : 0 < α * (1 - α) := mul_pos ha0 (by linarith)
    rw [show ∀ a b : ℝ, -(a - α) / (α * (1 - α)) - -(b - α) / (α * (1 - α)) =
      (b - a) / (α * (1 - α)) from fun a b => by ring]
    apply div_le_div_of_nonneg_right _ hd.le
    linarith
  have eT : eP α K T = etaThm3 α K T := by unfold eP; rw [if_neg (by omega)]
  have hηT := hηpos T hT
  have ha : tsallisPsi α (fun _ => 1) (uvec K T i) / etaThm3 α K T -
      tsallisPsi α (fun _ => 1) (p 1 h) / etaThm3 α K T ≤
      ((K : ℝ) ^ (1 - α) - 1) * (1 - (T : ℝ) ^ (-α)) / ((1 - α) * α * etaThm3 α K T) := by
    have := div_le_div_of_nonneg_right hpen hηT.le
    rw [sub_div, div_div] at this
    rwa [show α * (1 - α) * etaThm3 α K T = (1 - α) * α * etaThm3 α K T by ring] at this
  rw [eT] at htel hsplit
  have hrf : ∑ t ∈ Icc 1 T, rf ℓ p (uvec K T i) t h =
      ∑ t ∈ Icc 1 T, ∑ k, p t h k * lh ℓ p t h k -
        ∑ t ∈ Icc 1 T, ∑ k, uvec K T i k * lh ℓ p t h k := by
    unfold rf
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hrf]
  linarith

set_option maxHeartbeats 1000000 in
lemma per_omega {K : ℕ} {α : ℝ} {ℓ p : ℕ → (ℕ → Fin K) → Fin K → ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (H : Hyp α ℓ p) (hK : 2 ≤ K) (T : ℕ) (hT : 2 ≤ T)
    (i₀ i : Fin K) :
    E p i₀ T (fun h => ∑ t ∈ Icc 1 T, ℓ t h (h t)) - E p i₀ T (fun h => ∑ t ∈ Icc 1 T, ℓ t h i) ≤
      (K : ℝ) ^ α / 2 * (etaThm3 α K 2 + ∑ t ∈ Icc 2 T, etaThm3 α K t) +
      ((K : ℝ) ^ (1 - α) - 1) * (1 - (T : ℝ) ^ (-α)) / ((1 - α) * α * etaThm3 α K T) +
      2 * max 0 (etaThm3 α K 3 / etaThm3 α K 2 - 1) + 1 := by
  set M := max 0 (etaThm3 α K 3 / etaThm3 α K 2 - 1) with hM
  set P := ((K : ℝ) ^ (1 - α) - 1) * (1 - (T : ℝ) ^ (-α)) / ((1 - α) * α * etaThm3 α K T)
    with hP
  have hM0 : 0 ≤ M := le_max_left _ _
  have hsplit : E p i₀ T (fun h => ∑ t ∈ Icc 1 T, ℓ t h (h t)) -
      E p i₀ T (fun h => ∑ t ∈ Icc 1 T, ℓ t h i) =
      E p i₀ T (fun h => ∑ t ∈ Icc 1 T, gf ℓ (uvec K T i) t h) +
      E p i₀ T (fun h => ∑ t ∈ Icc 1 T, (∑ k, uvec K T i k * ℓ t h k - ℓ t h i)) := by
    rw [← E_sub, ← E_add]
    apply E_congr
    intro h
    simp only [gf, Finset.sum_sub_distrib]
    ring
  have hsecond : E p i₀ T (fun h => ∑ t ∈ Icc 1 T, (∑ k, uvec K T i k * ℓ t h k - ℓ t h i)) ≤
      1 := by
    calc _ ≤ E p i₀ T (fun _ => (1 : ℝ)) := by
          apply E_mono p H.p0
          intro h
          calc ∑ t ∈ Icc 1 T, (∑ k, uvec K T i k * ℓ t h k - ℓ t h i) ≤
                ∑ t ∈ Icc 1 T, (T : ℝ)⁻¹ :=
                Finset.sum_le_sum (fun t _ =>
                  uvec_dot_le i hK (by omega) (ℓ t h) (H.l0 t h) (H.l1 t h))
            _ = 1 := by
                rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
                exact mul_inv_cancel₀ (by exact_mod_cast (show T ≠ 0 by omega))
      _ = 1 := E_const p H.pc H.sum1 i₀ T 1
  have hepos : ∀ t, 1 ≤ t → 0 < eP α K t := fun t ht => eP_pos α hα K hK t ht
  have hfirst : E p i₀ T (fun h => ∑ t ∈ Icc 1 T, gf ℓ (uvec K T i) t h) ≤
      ∑ t ∈ Icc 1 T, eP α K t / 2 * (K : ℝ) ^ α + P + M * 2 := by
    have e1 : E p i₀ T (fun h => ∑ t ∈ Icc 1 T, gf ℓ (uvec K T i) t h) =
        E p i₀ T (fun h => ∑ t ∈ Icc 1 T, rf ℓ p (uvec K T i) t h) := by
      rw [E_sum p i₀ T (Icc 1 T) (gf ℓ (uvec K T i)), E_sum p i₀ T (Icc 1 T) (rf ℓ p (uvec K T i))]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_Icc] at ht
      exact E_round1 H i₀ t T ht.1 ht.2 (uvec K T i)
    rw [e1]
    calc _ ≤ E p i₀ T (fun h => ∑ t ∈ Icc 1 T, eP α K t / 2 * qf α ℓ p t h + P +
          M * (xf ℓ p 1 h + xf ℓ p 2 h)) :=
          E_mono p H.p0 i₀ T _ _ (fun h => pathwise hα H hK T hT i h)
      _ = ∑ t ∈ Icc 1 T, eP α K t / 2 * E p i₀ T (qf α ℓ p t) + P +
          M * (E p i₀ T (xf ℓ p 1) + E p i₀ T (xf ℓ p 2)) := by
          simp only [E_add, E_mul, E_sum, E_const p H.pc H.sum1]
      _ ≤ _ := by
          have h1 : ∑ t ∈ Icc 1 T, eP α K t / 2 * E p i₀ T (qf α ℓ p t) ≤
              ∑ t ∈ Icc 1 T, eP α K t / 2 * (K : ℝ) ^ α := by
            apply Finset.sum_le_sum
            intro t ht
            rw [Finset.mem_Icc] at ht
            apply mul_le_mul_of_nonneg_left (E_round2 hα H (by omega) i₀ t T ht.1 ht.2)
            have := hepos t ht.1
            positivity
          have h2 := E_round3 H i₀ 1 T le_rfl (by omega)
          have h3 := E_round3 H i₀ 2 T (by norm_num) hT
          have h4 := mul_le_mul_of_nonneg_left (add_le_add h2 h3) hM0
          linarith
  have hsumeq : ∑ t ∈ Icc 1 T, eP α K t / 2 * (K : ℝ) ^ α =
      (K : ℝ) ^ α / 2 * (etaThm3 α K 2 + ∑ t ∈ Icc 2 T, etaThm3 α K t) := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (show 1 ≤ T by omega),
      Finset.sum_insert (by simp)]
    have e : ∑ t ∈ Icc (1 + 1) T, eP α K t / 2 * (K : ℝ) ^ α =
        (K : ℝ) ^ α / 2 * ∑ t ∈ Icc 2 T, etaThm3 α K t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_Icc] at ht
      rw [show eP α K t = etaThm3 α K t by unfold eP; rw [if_neg (by omega)]]
      ring
    rw [e, show eP α K 1 = etaThm3 α K 2 by simp [eP]]
    ring
  rw [hsplit]
  linarith

lemma expect_eq {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ) (F : Ω → (ℕ → Fin K) → ℝ) :
    expect μ W i₀ T F = ∫ ω, E (fun t => W t ω) i₀ T (F ω) ∂μ := rfl

lemma hyp_of {K : ℕ} {Ω : Type*} (hK : 0 < K) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (adv : Ω → Adversary K) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α (fun _ => 1) (etaThm3 α K) (estIW adv W) W) (ω : Ω) :
    Hyp α (adv ω).val (fun t => W t ω) :=
  { l0 := fun t h k => ((adv ω).val_mem t h k).1
    l1 := fun t h k => ((adv ω).val_mem t h k).2
    lc := fun t h h' hag => (adv ω).nonanticipating t h h' hag
    pc := fun s hs h h' hag => W_causal hK α hα (etaThm3 α K) adv W hW s hs ω h h' hag
    smp := fun t ht h => (hW t ht ω h).1
    pos := fun t ht h k => argmax_pos α (etaThm3 α K t) hα
      (fun i => Lhat (estIW adv W) t ω h i) (W t ω h) ⟨(hW t ht ω h).1, (hW t ht ω h).2⟩ k
    arg := fun t ht h => ⟨(hW t ht ω h).1, (hW t ht ω h).2⟩ }

lemma sum_val_abs_le {K : ℕ} (g : Adversary K) (T : ℕ) (h j : ℕ → Fin K) :
    |∑ t ∈ Icc 1 T, g.val t h (j t)| ≤ T := by
  rw [abs_le]
  constructor
  · have h1 : 0 ≤ ∑ t ∈ Icc 1 T, g.val t h (j t) :=
      Finset.sum_nonneg (fun t _ => (g.val_mem t h (j t)).1)
    have h2 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    linarith
  · calc _ ≤ ∑ t ∈ Icc 1 T, (1 : ℝ) := Finset.sum_le_sum (fun t _ => (g.val_mem t h (j t)).2)
      _ = T := by simp

lemma integrable_E {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hK : 0 < K) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (adv : Ω → Adversary K) (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α (fun _ => 1) (etaThm3 α K) (estIW adv W) W)
    (i₀ : Fin K) (T : ℕ) (F : Ω → (ℕ → Fin K) → ℝ) (hFm : ∀ h, Measurable (fun ω => F ω h))
    (C : ℝ) (hFb : ∀ ω h, |F ω h| ≤ C) :
    Integrable (fun ω => E (fun t => W t ω) i₀ T (F ω)) μ := by
  have hWm := W_measurable hK α hα (etaThm3 α K) adv hadv W hW
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
    have H := hyp_of hK α hα adv W hW ω
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := E_mono (fun t => W t ω) H.p0 i₀ T (fun _ => -C) (F ω)
        (fun h => (abs_le.1 (hFb ω h)).1)
      rwa [E_const _ H.pc H.sum1] at this
    · have := E_mono (fun t => W t ω) H.p0 i₀ T (F ω) (fun _ => C)
        (fun h => (abs_le.1 (hFb ω h)).2)
      rwa [E_const _ H.pc H.sum1] at this

set_option maxHeartbeats 1000000 in
theorem main {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α (fun _ => 1) (etaThm3 α K) (TsallisINF.Half.estIW adv W) W)
    (T : ℕ) (hT : 1 ≤ T) :
    TsallisINF.Half.pseudoRegret μ adv W ⟨0, hK⟩ T ≤
      2 * Real.sqrt (min (min (1 / (α - α ^ 2)) (Real.log K / α)) (Real.log T / (1 - α)) *
        K * T) + 1 := by
  have hS := Real.sqrt_nonneg
    (min (min (1 / (α - α ^ 2)) (Real.log K / α)) (Real.log T / (1 - α)) * K * T)
  have hper : ∀ ω (i : Fin K),
      E (fun t => W t ω) ⟨0, hK⟩ T (fun h => ∑ t ∈ Icc 1 T, (adv ω).val t h (h t)) -
      E (fun t => W t ω) ⟨0, hK⟩ T (fun h => ∑ t ∈ Icc 1 T, (adv ω).val t h i) ≤
      2 * Real.sqrt (min (min (1 / (α - α ^ 2)) (Real.log K / α)) (Real.log T / (1 - α)) *
        K * T) + 1 := by
    intro ω i
    have H := hyp_of hK α hα adv W hW ω
    rcases (show K = 1 ∨ 2 ≤ K by omega) with hK1 | hK2
    · have e : (fun h : ℕ → Fin K => ∑ t ∈ Icc 1 T, (adv ω).val t h (h t)) =
          (fun h => ∑ t ∈ Icc 1 T, (adv ω).val t h i) := by
        funext h
        apply Finset.sum_congr rfl
        intro t _
        congr 1
        apply Fin.ext
        have h1 := (h t).isLt
        have h2 := i.isLt
        omega
      rw [e, sub_self]
      linarith
    rcases (show T = 1 ∨ 2 ≤ T by omega) with hT1 | hT2
    · subst hT1
      calc _ = E (fun t => W t ω) ⟨0, hK⟩ 1 (fun h => ∑ t ∈ Icc 1 1, (adv ω).val t h (h t) -
              ∑ t ∈ Icc 1 1, (adv ω).val t h i) := (E_sub _ _ _ _ _).symm
        _ ≤ E (fun t => W t ω) ⟨0, hK⟩ 1 (fun _ => (1 : ℝ)) := by
            apply E_mono _ H.p0
            intro h
            simp only [Finset.Icc_self, Finset.sum_singleton]
            have h1 := ((adv ω).val_mem 1 h (h 1)).2
            have h2 := ((adv ω).val_mem 1 h i).1
            linarith
        _ = 1 := E_const _ H.pc H.sum1 _ _ _
        _ ≤ _ := by linarith
    · have h1 := per_omega hα H hK2 T hT2 ⟨0, hK⟩ i
      have h2 := final_arith α hα K T hK2 hT2
      linarith
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite
    (f := fun i : Fin K => expect μ W ⟨0, hK⟩ T (fun ω h => ∑ t ∈ Icc 1 T, (adv ω).val t h i))
  unfold TsallisINF.Half.pseudoRegret
  rw [← hi]
  simp only [expect_eq]
  have hIA := integrable_E μ hK α hα adv hadv W hW ⟨0, hK⟩ T
    (fun ω h => ∑ t ∈ Icc 1 T, (adv ω).val t h (h t))
    (fun h => Finset.measurable_fun_sum _ (fun t _ => hadv t h (h t))) T
    (fun ω h => sum_val_abs_le (adv ω) T h h)
  have hIi := integrable_E μ hK α hα adv hadv W hW ⟨0, hK⟩ T
    (fun ω h => ∑ t ∈ Icc 1 T, (adv ω).val t h i)
    (fun h => Finset.measurable_fun_sum _ (fun t _ => hadv t h i)) T
    (fun ω h => sum_val_abs_le (adv ω) T h (fun _ => i))
  rw [← integral_sub hIA hIi]
  calc _ ≤ ∫ _ω, (2 * Real.sqrt (min (min (1 / (α - α ^ 2)) (Real.log K / α))
          (Real.log T / (1 - α)) * K * T) + 1) ∂μ :=
        integral_mono (hIA.sub hIi) (integrable_const _) (fun ω => hper ω i)
    _ = _ := by simp

end SAssembly

end TsallisINF.AdvAlpha.P50255

open TsallisINF.AdvAlpha in
theorem solution {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α (fun _ => 1) (etaThm3 α K) (TsallisINF.Half.estIW adv W) W)
    (T : ℕ) (hT : 1 ≤ T) :
    TsallisINF.Half.pseudoRegret μ adv W ⟨0, hK⟩ T ≤
      2 * Real.sqrt (min (min (1 / (α - α ^ 2)) (Real.log K / α)) (Real.log T / (1 - α)) *
        K * T) + 1 := by
  exact TsallisINF.AdvAlpha.P50255.main hK μ adv hadv α hα W hW T hT
