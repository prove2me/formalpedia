-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P25.discreteJensen
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:11:32.011245+00:00
-- url     : https://prove2.me/submissions/040a1a40-c424-4eba-80d5-8f9216c53b88

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P25

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P25

namespace X5DiscreteJensen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A norm-convergent convex combination of points of a closed convex set lies in the set. -/
lemma hasSum_mem {A : Set E} (hA : Convex ℝ A) (hcl : IsClosed A)
    (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) (hsum : HasSum v 1)
    (x : ℕ → E) (hx : ∀ i, x i ∈ A) {S : E} (hS : HasSum (fun i => v i • x i) S) : S ∈ A := by
  set z : ℕ → E := fun m => (∑ i ∈ range m, v i • x i) + (1 - ∑ i ∈ range m, v i) • x 0
  have hz : Tendsto z atTop (𝓝 S) := by
    have h1 := hS.tendsto_sum_nat
    have h2 : Tendsto (fun m => (1 - ∑ i ∈ range m, v i) • x 0) atTop (𝓝 ((1 - 1 : ℝ) • x 0)) :=
      ((tendsto_const_nhds.sub hsum.tendsto_sum_nat).smul_const _)
    simpa using h1.add h2
  refine hcl.mem_of_tendsto hz (Eventually.of_forall fun m => ?_)
  have hle : ∑ i ∈ range m, v i ≤ 1 := sum_le_hasSum (range m) (fun i _ => hv i) hsum
  set u : ℕ → ℝ := fun i => if i < m then v i else 1 - ∑ j ∈ range m, v j
  set p : ℕ → E := fun i => if i < m then x i else x 0
  have hzu : z m = ∑ i ∈ range (m + 1), u i • p i := by
    rw [sum_range_succ]
    simp only [z, u, p, lt_irrefl, if_false]
    congr 1
    exact sum_congr rfl fun i hi => by simp [mem_range.1 hi]
  rw [hzu]
  refine hA.sum_mem (fun i _ => ?_) ?_ (fun i _ => ?_)
  · simp only [u]; split_ifs
    · exact hv i
    · linarith
  · rw [sum_range_succ]
    simp only [u, lt_irrefl, if_false]
    rw [sum_congr rfl fun i hi => (if_pos (mem_range.1 hi) : (if i < m then v i else _) = v i)]
    ring
  · simp only [p]; split_ifs
    · exact hx i
    · exact hx 0

lemma real_jensen [CompleteSpace E] {A : Set E} (hA : Convex ℝ A) (hcl : IsClosed A)
    (hbd : Bornology.IsBounded A)
    (g : E → ℝ) (hg : ConvexOn ℝ A g) (M L : ℝ) (hM : ∀ y ∈ A, g y ≤ M) (hL : ∀ y ∈ A, L ≤ g y)
    (x : ℕ → E) (hx : ∀ i, x i ∈ A) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (htotal : HasSum w 1) :
    g (∑' i, w i • x i) ≤ ∑' i, w i * g (x i) := by
  obtain ⟨C, hC⟩ := hbd.exists_norm_le
  have hsx : Summable (fun i => w i • x i) := by
    refine Summable.of_norm_bounded (htotal.summable.mul_right C) (fun i => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hw i)]
    exact mul_le_mul_of_nonneg_left (hC _ (hx i)) (hw i)
  have hsg : Summable (fun i => w i * g (x i)) := by
    refine Summable.of_norm_bounded (htotal.summable.mul_right (max |L| |M|)) (fun i => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hw i), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_le_max_abs_abs (hL _ (hx i)) (hM _ (hx i))) (hw i)
  set S := ∑' i, w i • x i with hSdef
  have key : ∀ n, g S ≤ ∑ i ∈ range n, w i * g (x i) + (1 - ∑ i ∈ range n, w i) * M := by
    intro n
    set t := 1 - ∑ i ∈ range n, w i with htdef
    have ht : HasSum (fun i => w (i + n)) t := (hasSum_nat_add_iff' n).mpr htotal
    have hT : HasSum (fun i => w (i + n) • x (i + n)) (S - ∑ i ∈ range n, w i • x i) :=
      (hasSum_nat_add_iff' n).mpr hsx.hasSum
    set T := S - ∑ i ∈ range n, w i • x i with hTdef
    have ht0 : 0 ≤ t := ht.nonneg (fun i => hw _)
    set y : E := if t = 0 then x 0 else t⁻¹ • T with hydef
    have hyA : y ∈ A := by
      by_cases h : t = 0
      · simp only [y, h, if_true]; exact hx 0
      · simp only [y, h, if_false]
        refine hasSum_mem hA hcl (fun i => t⁻¹ * w (i + n))
          (fun i => mul_nonneg (inv_nonneg.2 ht0) (hw _)) ?_ (fun i => x (i + n)) (fun i => hx _) ?_
        · simpa [inv_mul_cancel₀ h] using ht.mul_left t⁻¹
        · simpa [mul_smul] using hT.const_smul t⁻¹
    have htyT : t • y = T := by
      by_cases h : t = 0
      · have hz : (fun i => w (i + n)) = 0 :=
          (hasSum_zero_iff_of_nonneg (fun i => hw _)).1 (h ▸ ht)
        have hT0 : T = 0 := by
          have h0 : HasSum (fun i => w (i + n) • x (i + n)) 0 := by
            have : ∀ i, w (i + n) = 0 := fun i => congrFun hz i
            simpa [this] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : E)) 0)
          exact hT.unique h0
        simp [h, hT0]
      · simp [y, h, smul_smul, mul_inv_cancel₀ h]
    set u : ℕ → ℝ := fun i => if i < n then w i else t with hudef
    set p : ℕ → E := fun i => if i < n then x i else y with hpdef
    have hJ := hg.map_sum_le (t := range (n + 1)) (w := u) (p := p)
      (fun i _ => by simp only [u]; split_ifs; exacts [hw i, ht0])
      (by rw [sum_range_succ]; simp only [u, lt_irrefl, if_false]
          rw [sum_congr rfl fun i hi => (if_pos (mem_range.1 hi) : (if i < n then w i else t) = w i)]
          ring)
      (fun i _ => by simp only [p]; split_ifs; exacts [hx i, hyA])
    have hL1 : ∑ i ∈ range (n + 1), u i • p i = S := by
      rw [sum_range_succ]; simp only [u, p, lt_irrefl, if_false]
      rw [sum_congr rfl fun i hi => (by simp [mem_range.1 hi] :
        (if i < n then w i else t) • (if i < n then x i else y) = w i • x i), htyT]
      simp [T]
    have hR1 : ∑ i ∈ range (n + 1), u i • g (p i) = ∑ i ∈ range n, w i * g (x i) + t * g y := by
      rw [sum_range_succ]; simp only [u, p, lt_irrefl, if_false, smul_eq_mul]
      congr 1
      exact sum_congr rfl fun i hi => by simp [mem_range.1 hi]
    rw [hL1, hR1] at hJ
    have := mul_le_mul_of_nonneg_left (hM y hyA) ht0
    linarith
  have hlim : Tendsto (fun n => ∑ i ∈ range n, w i * g (x i) + (1 - ∑ i ∈ range n, w i) * M)
      atTop (𝓝 (∑' i, w i * g (x i) + (1 - 1) * M)) :=
    hsg.hasSum.tendsto_sum_nat.add ((tendsto_const_nhds.sub htotal.tendsto_sum_nat).mul_const M)
  simp only [sub_self, zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim key

lemma key_id (a : EReal) (ha : a ≠ ⊤) (K : ℕ) :
    (max a (-(K : EReal))).toReal =
      a.toENNReal.toReal - (min (-a).toENNReal (K : ℝ≥0∞)).toReal := by
  induction a using EReal.rec with
  | bot =>
    simp
    exact EReal.toReal_coe (K : ℝ)
  | top => exact absurd rfl ha
  | coe r =>
    have hK : ((K : ℝ≥0∞)) = ENNReal.ofReal (K : ℝ) := by simp
    have hneg : (-(K : EReal)) = (((-(K : ℝ)) : ℝ) : EReal) := by simp
    rw [hneg, ← EReal.coe_neg, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal, hK]
    rw [← (EReal.coe_strictMono.monotone.map_max : ((max r (-(K : ℝ)) : ℝ) : EReal) = _),
      EReal.toReal_coe, ENNReal.toReal_min ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal', ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    rw [max_eq_left hK0]
    rcases le_total r 0 with h | h <;> rcases le_total (-r) K with h' | h' <;>
      simp only [max_def, min_def] <;> split_ifs <;> linarith

lemma tsum_coe_ennreal (a : ℕ → ℝ≥0∞) : ∑' i, ((a i : ℝ≥0∞) : EReal) = ((∑' i, a i : ℝ≥0∞) : EReal) := by
  let φ : ℝ≥0∞ →+ EReal :=
    { toFun := fun t => (t : EReal), map_zero' := EReal.coe_ennreal_zero,
      map_add' := EReal.coe_ennreal_add }
  exact (ENNReal.summable.hasSum.map φ continuous_coe_ennreal_ereal).tsum_eq

end X5DiscreteJensen

open X5DiscreteJensen in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : Set E) (hclosed : IsClosed A)
    (hbounded : Bornology.IsBounded A) (f : E → EReal)
    (hconvex : extendedConvexOn A f)
    (hupper : ∃ M : ℝ, ∀ x ∈ A, f x ≤ (M : EReal))
    (x : ℕ → E) (hx : ∀ i, x i ∈ A)
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (htotal : HasSum w 1) :
    f (∑' i : ℕ, w i • x i) ≤ extendedSeries w (fun i => f (x i)) := by
  obtain ⟨M, hM⟩ := hupper
  obtain ⟨hA, hcv⟩ := hconvex
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  have hsx : Summable (fun i => w i • x i) := by
    refine Summable.of_norm_bounded (htotal.summable.mul_right C) (fun i => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hw i)]
    exact mul_le_mul_of_nonneg_left (hC _ (hx i)) (hw i)
  have hSA : ∑' i, w i • x i ∈ A := hasSum_mem hA hclosed w hw htotal x hx hsx.hasSum
  set S := ∑' i, w i • x i with hSdef
  have hfne : ∀ y ∈ A, f y ≠ ⊤ := fun y hy => ne_top_of_le_ne_top (EReal.coe_ne_top M) (hM y hy)
  -- truncations `g K = max f (-K)`, real valued on `A`
  set g : ℕ → E → ℝ := fun K y => (max (f y) (-(K : EReal))).toReal with hgdef
  have hKcoe : ∀ K : ℕ, (-(K : EReal)) = (((-(K : ℝ)) : ℝ) : EReal) := fun K => by
    rw [EReal.coe_neg]; rfl
  have hgcoe : ∀ K : ℕ, ∀ y ∈ A, max (f y) (-(K : EReal)) = ((g K y : ℝ) : EReal) := by
    intro K y hy
    simp only [g]
    rw [EReal.coe_toReal]
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top (max M (-(K : ℝ))))
        (by rw [hKcoe, (EReal.coe_strictMono.monotone.map_max :
              ((max M (-(K : ℝ)) : ℝ) : EReal) = _)]
            exact max_le_max (hM y hy) le_rfl)
    · exact ne_bot_of_le_ne_bot (by rw [hKcoe]; exact EReal.coe_ne_bot _) (le_max_right _ _)
  have hgL : ∀ K : ℕ, ∀ y ∈ A, -(K : ℝ) ≤ g K y := by
    intro K y hy
    have := le_max_right (f y) (-(K : EReal))
    rw [hgcoe K y hy, hKcoe] at this
    exact EReal.coe_le_coe_iff.1 this
  have hgM : ∀ K : ℕ, ∀ y ∈ A, g K y ≤ max M (-(K : ℝ)) := by
    intro K y hy
    have := max_le_max (hM y hy) (le_refl (-(K : EReal)))
    rw [hgcoe K y hy, hKcoe, ← (EReal.coe_strictMono.monotone.map_max :
              ((max M (-(K : ℝ)) : ℝ) : EReal) = _)] at this
    exact EReal.coe_le_coe_iff.1 this
  have hgconv : ∀ K : ℕ, ConvexOn ℝ A (g K) := by
    refine fun K => ⟨hA, fun y hy z hz a b ha hb hab => ?_⟩
    rw [smul_eq_mul, smul_eq_mul, ← EReal.coe_le_coe_iff, EReal.coe_add, EReal.coe_mul,
      EReal.coe_mul, ← hgcoe K _ (hA hy hz ha hb hab), ← hgcoe K y hy, ← hgcoe K z hz]
    refine max_le ?_ ?_
    · calc f (a • y + b • z) ≤ (a : EReal) * f y + (b : EReal) * f z :=
            hcv y hy z hz a b ha hb hab
        _ ≤ (a : EReal) * max (f y) (-(K : EReal)) + (b : EReal) * max (f z) (-(K : EReal)) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (EReal.coe_nonneg.2 ha))
              (mul_le_mul_of_nonneg_left (le_max_left _ _) (EReal.coe_nonneg.2 hb))
    · rw [hgcoe K y hy, hgcoe K z hz, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, hKcoe,
        EReal.coe_le_coe_iff]
      have h1 := hgL K y hy
      have h2 := hgL K z hz
      nlinarith
  -- per-truncation bound
  have hstep : ∀ K : ℕ, f S ≤ ((∑' i, w i * g K (x i) : ℝ) : EReal) := by
    intro K
    calc f S ≤ max (f S) (-(K : EReal)) := le_max_left _ _
      _ = ((g K S : ℝ) : EReal) := hgcoe K S hSA
      _ ≤ _ := EReal.coe_le_coe_iff.2 (real_jensen hA hclosed hbounded (g K) (hgconv K)
            (max M (-(K : ℝ))) (-(K : ℝ)) (hgM K) (hgL K) x hx w hw htotal)
  -- positive and negative parts
  set pp : ℕ → ℝ≥0∞ := fun i => (f (x i)).toENNReal with hppdef
  set nn : ℕ → ℝ≥0∞ := fun i => (-f (x i)).toENNReal with hnndef
  set P : ℝ≥0∞ := ∑' i, ENNReal.ofReal (w i) * pp i with hPdef
  set N : ℝ≥0∞ := ∑' i, ENNReal.ofReal (w i) * nn i with hNdef
  set NK : ℕ → ℝ≥0∞ := fun K => ∑' i, ENNReal.ofReal (w i) * min (nn i) (K : ℝ≥0∞) with hNKdef
  have hES : extendedSeries w (fun i => f (x i)) = (P : EReal) - (N : EReal) := by
    rw [extendedSeries]
    simp_rw [← EReal.coe_ennreal_mul]
    rw [tsum_coe_ennreal, tsum_coe_ennreal]
  have hw1 : ∑' i, ENNReal.ofReal (w i) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hw htotal.summable, htotal.tsum_eq, ENNReal.ofReal_one]
  have hppM : ∀ i, pp i ≤ ENNReal.ofReal M := fun i => by
    simpa using EReal.toENNReal_le_toENNReal (hM _ (hx i))
  have hPne : P ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal M) ENNReal.ofReal_ne_top ?_
    calc P ≤ ∑' i, ENNReal.ofReal (w i) * ENNReal.ofReal M :=
          ENNReal.tsum_le_tsum fun i => by gcongr; exact hppM i
      _ = ENNReal.ofReal M := by rw [ENNReal.tsum_mul_right, hw1, one_mul]
  have hNKne : ∀ K : ℕ, NK K ≠ ⊤ := by
    intro K
    refine ne_top_of_le_ne_top (b := (K : ℝ≥0∞)) (ENNReal.natCast_ne_top K) ?_
    calc NK K ≤ ∑' i, ENNReal.ofReal (w i) * (K : ℝ≥0∞) :=
          ENNReal.tsum_le_tsum fun i => by gcongr; exact min_le_right _ _
      _ = K := by rw [ENNReal.tsum_mul_right, hw1, one_mul]
  have hppne : ∀ i, pp i ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hppM i)
  have hmne : ∀ (K : ℕ) i, min (nn i) (K : ℝ≥0∞) ≠ ⊤ := fun K i =>
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top K) (min_le_right _ _)
  have hident : ∀ K : ℕ, ∑' i, w i * g K (x i) = P.toReal - (NK K).toReal := by
    intro K
    have hterm : ∀ i, w i * g K (x i) = (ENNReal.ofReal (w i) * pp i).toReal -
        (ENNReal.ofReal (w i) * min (nn i) (K : ℝ≥0∞)).toReal := by
      intro i
      simp only [g]
      rw [key_id _ (hfne _ (hx i)) K, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (hw i)]
      ring
    simp_rw [hterm]
    rw [Summable.tsum_sub (ENNReal.summable_toReal hPne) (ENNReal.summable_toReal (hNKne K)),
      ENNReal.tsum_toReal_eq (fun i => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hppne i)),
      ENNReal.tsum_toReal_eq (fun i => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmne K i))]
  have hbound : ∀ K : ℕ, f S ≤ (((P.toReal - (NK K).toReal) : ℝ) : EReal) := fun K =>
    (hstep K).trans_eq (by rw [hident K])
  rw [hES]
  by_cases hbot : f S = ⊥
  · rw [hbot]; exact bot_le
  have htop : f S ≠ ⊤ := hfne S hSA
  lift f S to ℝ using ⟨htop, hbot⟩ with r hr
  have hrK : ∀ K : ℕ, r ≤ P.toReal - (NK K).toReal := fun K =>
    EReal.coe_le_coe_iff.1 (hbound K)
  have hB : ∀ K : ℕ, NK K ≤ ENNReal.ofReal (P.toReal - r) := by
    intro K
    rw [← ENNReal.ofReal_toReal (hNKne K)]
    exact ENNReal.ofReal_le_ofReal (by linarith [hrK K])
  have hN : N ≤ ENNReal.ofReal (P.toReal - r) := by
    refine ENNReal.tsum_le_of_sum_range_le fun m => ?_
    have hsup : ∀ i, ENNReal.ofReal (w i) * nn i =
        ⨆ K : ℕ, ENNReal.ofReal (w i) * min (nn i) (K : ℝ≥0∞) := by
      intro i
      rw [← ENNReal.mul_iSup]
      congr 1
      have : ⨆ K : ℕ, min (nn i) (K : ℝ≥0∞) = min (nn i) (⨆ K : ℕ, (K : ℝ≥0∞)) :=
        (inf_iSup_eq (nn i) fun K : ℕ => (K : ℝ≥0∞)).symm
      rw [this, ENNReal.iSup_natCast, min_top_right]
    rw [Finset.sum_congr rfl fun i _ => hsup i,
      ENNReal.finsetSum_iSup_of_monotone (fun i K L hKL =>
        by gcongr)]
    exact iSup_le fun K => (ENNReal.sum_le_tsum _).trans (hB K)
  have hNne : N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hN
  have hNr : N.toReal ≤ P.toReal - r := by
    have h0 := hrK 0
    have : (NK 0).toReal = 0 := by simp [NK]
    have hnn : 0 ≤ P.toReal - r := by linarith
    calc N.toReal ≤ (ENNReal.ofReal (P.toReal - r)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hN
      _ = P.toReal - r := ENNReal.toReal_ofReal hnn
  rw [← EReal.coe_ennreal_toReal hPne, ← EReal.coe_ennreal_toReal hNne, ← EReal.coe_sub,
    EReal.coe_le_coe_iff]
  linarith
