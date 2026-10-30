-- Prove2me | solution 1 for SemilinearHJ.Verification.theorem_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:33:40.790853+00:00
-- url     : https://prove2.me/submissions/a6bb2565-897b-4d7c-92da-a505fac84086
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting
import Theorems.Thm_SemilinearHJ_Verification_theorem_3_2

open scoped BigOperators

namespace HJCone

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {ι : Type*} [DecidableEq ι]

/-- Nonnegative combinations of `f i`, `i ∈ G`. -/
def coneOf (G : Finset ι) (f : ι → V) : Set V :=
  {v | ∃ c : ι → ℝ, (∀ i ∈ G, 0 ≤ c i) ∧ v = ∑ i ∈ G, c i • f i}

/-- Conic Carathéodory. -/
theorem cara (f : ι → V) : ∀ (G : Finset ι) (v : V), v ∈ coneOf G f →
    ∃ J ⊆ G, LinearIndependent ℝ (fun i : J => f i) ∧ v ∈ coneOf J f := by
  intro G
  induction G using Finset.strongInduction with
  | H G ih =>
  intro v hv
  by_cases hli : LinearIndependent ℝ (fun i : G => f i)
  · exact ⟨G, le_rfl, hli, hv⟩
  obtain ⟨c, hc0, rfl⟩ := hv
  rw [not_linearIndependent_iff] at hli
  obtain ⟨s, g, hg, i0, hi0s, hi0⟩ := hli
  -- extend g to a function on ι supported in G
  let a : ι → ℝ := fun i => if h : i ∈ G then (if (⟨i, h⟩ : G) ∈ s then g ⟨i, h⟩ else 0) else 0
  have ha : ∑ i ∈ G, a i • f i = 0 := by
    rw [← hg, ← Finset.sum_coe_sort G]
    rw [← Finset.sum_subset (Finset.subset_univ s)]
    · refine Finset.sum_congr rfl ?_
      intro x hx
      have : (x : ι) ∈ G := x.2
      simp only [a, this, dif_pos]
      rw [if_pos (by simpa using hx)]
    · intro x _ hx
      have : (x : ι) ∈ G := x.2
      simp only [a, this, dif_pos]
      rw [if_neg (by simpa using hx), zero_smul]
  have hai0 : a i0 ≠ 0 := by
    have : (i0 : ι) ∈ G := i0.2
    simp only [a, this, dif_pos]
    rw [if_pos (by simpa using hi0s)]
    simpa using hi0
  -- WLOG some coefficient positive
  have key : ∀ b : ι → ℝ, ∑ i ∈ G, b i • f i = 0 → (∃ i ∈ G, 0 < b i) →
      ∃ J ⊆ G, LinearIndependent ℝ (fun i : J => f i) ∧
        (∑ i ∈ G, c i • f i) ∈ coneOf J f := by
    intro b hb ⟨j, hjG, hj⟩
    let P := G.filter (fun i => 0 < b i)
    have hPne : P.Nonempty := ⟨j, by simp [P, hjG, hj]⟩
    obtain ⟨k, hkP, hkmin⟩ := P.exists_min_image (fun i => c i / b i) hPne
    have hkG : k ∈ G := (Finset.mem_filter.1 hkP).1
    have hbk : 0 < b k := (Finset.mem_filter.1 hkP).2
    set lam := c k / b k with hlam
    have hlam0 : 0 ≤ lam := div_nonneg (hc0 k hkG) hbk.le
    let c' : ι → ℝ := fun i => c i - lam * b i
    have hc'0 : ∀ i ∈ G, 0 ≤ c' i := by
      intro i hi
      by_cases hbi : 0 < b i
      · have := hkmin i (by simp [P, hi, hbi])
        have : lam * b i ≤ c i := by
          rw [le_div_iff₀ hbi] at this; linarith
        simp only [c']; linarith
      · push Not at hbi
        have := hc0 i hi
        simp only [c']; nlinarith
    have hc'k : c' k = 0 := by
      simp only [c', hlam]; field_simp; ring
    have hsum : ∑ i ∈ G, c i • f i = ∑ i ∈ G.erase k, c' i • f i := by
      rw [Finset.sum_erase _ (by rw [hc'k, zero_smul])]
      simp only [c', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hb,
        smul_zero, sub_zero]
    obtain ⟨J, hJ, hJli, hJv⟩ := ih (G.erase k) (Finset.erase_ssubset hkG)
      (∑ i ∈ G.erase k, c' i • f i)
      ⟨c', fun i hi => hc'0 i (Finset.mem_of_mem_erase hi), rfl⟩
    exact ⟨J, hJ.trans (Finset.erase_subset _ _), hJli, hsum ▸ hJv⟩
  by_cases hpos : ∃ i ∈ G, 0 < a i
  · exact key a ha hpos
  · push Not at hpos
    refine key (fun i => -a i) (by simp [neg_smul, Finset.sum_neg_distrib, ha]) ?_
    have : (i0 : ι) ∈ G := i0.2
    refine ⟨i0, this, ?_⟩
    have := hpos i0 this
    have : a i0 < 0 := lt_of_le_of_ne this hai0
    linarith

theorem isClosed_coneOf_li [FiniteDimensional ℝ V] (J : Finset ι) (f : ι → V)
    (hJ : LinearIndependent ℝ (fun i : J => f i)) : IsClosed (coneOf J f) := by
  let L : (J → ℝ) →ₗ[ℝ] V := Fintype.linearCombination ℝ (fun i : J => f i)
  have hL : Function.Injective L := by
    intro c d hcd
    have h0 : ∑ i, (c - d) i • f i = 0 := by
      simp only [L, Fintype.linearCombination_apply] at hcd
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcd, sub_self]
    funext i
    have := Fintype.linearIndependent_iff.1 hJ _ h0 i
    simpa [sub_eq_zero] using this
  have hset : coneOf J f = L '' {c | ∀ i, 0 ≤ c i} := by
    ext v
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun i => c i, fun i => hc i i.2, ?_⟩
      simp only [L, Fintype.linearCombination_apply]
      exact (Finset.sum_coe_sort J (fun i => c i • f i))
    · rintro ⟨c, hc, rfl⟩
      classical
      refine ⟨fun i => if h : i ∈ J then c ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i hi; simp only [hi, dif_pos]; exact hc _
      · simp only [L, Fintype.linearCombination_apply]
        rw [← Finset.sum_coe_sort J]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [i.2]
  rw [hset]
  exact (L.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.2 hL)).isClosedMap _
    (by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))

theorem isClosed_coneOf [FiniteDimensional ℝ V] (G : Finset ι) (f : ι → V) :
    IsClosed (coneOf G f) := by
  classical
  let P : Finset (Finset ι) :=
    G.powerset.filter (fun J : Finset ι => LinearIndependent ℝ (fun i : (J : Finset ι) => f i))
  have : coneOf G f = ⋃ J ∈ P, coneOf J f := by
    ext v
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hv
      obtain ⟨J, hJ, hli, hv⟩ := cara f G v hv
      exact ⟨J, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hJ, hli⟩, hv⟩
    · rintro ⟨J, hJP, c, hc, rfl⟩
      have hJ := Finset.mem_powerset.1 (Finset.mem_filter.1 hJP).1
      refine ⟨fun i => if i ∈ J then c i else 0, fun i _ => ?_, ?_⟩
      · show 0 ≤ if i ∈ J then c i else 0
        split_ifs with h
        · exact hc i h
        · exact le_rfl
      · rw [← Finset.sum_subset hJ]
        · exact Finset.sum_congr rfl fun i hi => by simp [hi]
        · intro i _ hi; simp [hi]
  rw [this]
  exact isClosed_biUnion_finset fun J hJ =>
    isClosed_coneOf_li J f (Finset.mem_filter.1 hJ).2

end HJCone


open SemilinearHJ.Verification HJCone Filter Topology
open scoped ENNReal MeasureTheory Pointwise

namespace HJRev

variable {n : ℕ}

lemma tanCone_eq (S : Finset (E n)) (x : E n) (hx : x ∈ convexHull ℝ (S : Set (E n))) :
    tanCone (convexHull ℝ (S : Set (E n))) x = coneOf S (fun s => s - x) := by
  ext v; constructor
  · rintro ⟨y, hy, t, ht, rfl⟩
    obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.1 hy
    refine ⟨fun s => t * w s, fun s hs => mul_nonneg ht (hw0 s hs), ?_⟩
    have : ∑ s ∈ S, w s • s - x = ∑ s ∈ S, w s • (s - x) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul]
    rw [this, Finset.smul_sum]; simp only [mul_smul]
  · rintro ⟨c, hc, rfl⟩
    by_cases hC : ∑ s ∈ S, c s = 0
    · have hz : ∀ s ∈ S, c s = 0 := (Finset.sum_eq_zero_iff_of_nonneg hc).1 hC
      refine ⟨x, hx, 0, le_rfl, ?_⟩
      rw [Finset.sum_eq_zero (fun s hs => by rw [hz s hs, zero_smul])]
      simp
    · have hCpos : 0 < ∑ s ∈ S, c s := lt_of_le_of_ne (Finset.sum_nonneg hc) (Ne.symm hC)
      set C := ∑ s ∈ S, c s with hCdef
      refine ⟨∑ s ∈ S, (c s / C) • s, ?_, C, hCpos.le, ?_⟩
      · exact Finset.mem_convexHull'.2 ⟨fun s => c s / C,
          fun s hs => div_nonneg (hc s hs) hCpos.le, by rw [← Finset.sum_div, div_self hC], rfl⟩
      · rw [smul_sub, Finset.smul_sum]
        simp only [smul_smul, mul_div_cancel₀ _ hC, smul_sub, Finset.sum_sub_distrib]
        rw [hCdef, Finset.sum_smul]

lemma isClosed_tanCone {X : Set (E n)} (hX : IsPolytope X) {x : E n} (hx : x ∈ X) :
    IsClosed (tanCone X x) := by
  obtain ⟨S, -, rfl⟩ := hX
  rw [tanCone_eq S x hx]
  exact isClosed_coneOf S _

lemma deriv_mem_tanCone {X : Set (E n)} (hX : IsPolytope X) {T : ℝ} {φ : ℝ → E n}
    (hφ : Set.MapsTo φ (Set.Icc 0 T) X) {s : ℝ} (hs : s ∈ Set.Ioo 0 T) :
    deriv φ s ∈ tanCone X (φ s) ∧ -deriv φ s ∈ tanCone X (φ s) := by
  have hxs : φ s ∈ X := hφ (Set.Ioo_subset_Icc_self hs)
  have hcl := isClosed_tanCone hX hxs
  by_cases hd : DifferentiableAt ℝ φ s
  · have hD := hd.hasDerivAt
    constructor
    · refine hcl.mem_of_tendsto hD.tendsto_slope_zero_right ?_
      have h1 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < T - s :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [hs.2]))
      filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
      have ht0' : 0 < t := ht0
      exact ⟨φ (s + t), hφ ⟨by linarith [hs.1], by linarith⟩, t⁻¹, inv_nonneg.2 ht0'.le, rfl⟩
    · have := hD.tendsto_slope_zero_left.neg
      refine hcl.mem_of_tendsto this ?_
      have h1 : ∀ᶠ t in 𝓝[<] (0:ℝ), -s < t :=
        nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith [hs.1]))
      filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
      have ht0' : t < 0 := ht0
      refine ⟨φ (s + t), hφ ⟨by linarith, by linarith [hs.2]⟩, (-t)⁻¹,
        inv_nonneg.2 (by linarith), ?_⟩
      rw [inv_neg, neg_smul]
  · rw [deriv_zero_of_not_differentiableAt hd, neg_zero]
    exact ⟨⟨φ s, hxs, 0, le_rfl, by simp⟩, ⟨φ s, hxs, 0, le_rfl, by simp⟩⟩

lemma mem_tanCone_neg (X : Set (E n)) (x v : E n) :
    v ∈ tanCone (-X) (-x) ↔ -v ∈ tanCone X x := by
  constructor
  · rintro ⟨y, hy, t, ht, rfl⟩
    refine ⟨-y, hy, t, ht, ?_⟩
    rw [← smul_neg]; congr 1; abel
  · rintro ⟨y, hy, t, ht, h⟩
    refine ⟨-y, by simpa using hy, t, ht, ?_⟩
    rw [← neg_neg v, h, ← smul_neg]; congr 1; abel

lemma vectorSpan_neg (X : Set (E n)) : vectorSpan ℝ (-X) = vectorSpan ℝ X := by
  have : (-X) -ᵥ (-X) = X -ᵥ X := by
    ext z
    simp only [Set.mem_vsub, Set.mem_neg, vsub_eq_sub]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨-b, hb, -a, ha, by abel⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨-b, by simpa using hb, -a, by simpa using ha, by abel⟩
  simp only [vectorSpan_def, this]

lemma ballR_neg (X : Set (E n)) (r : ℝ) : ballR (-X) r = ballR X r := by
  simp only [ballR, vectorSpan_neg]

lemma ham_neg (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (x u : E n) :
    ham (-X) (fun y => Ψ (-y)) r (-x) u = ham X Ψ r x u := by
  simp only [ham, ballR_neg, neg_neg]

lemma runCost_neg (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (x v : E n)
    (h : v ∈ tanCone X x ↔ -v ∈ tanCone X x) :
    runCost (-X) (fun y => Ψ (-y)) r (-x) v = runCost X Ψ r x v := by
  unfold runCost
  rw [ballR_neg, mem_tanCone_neg, ← h]
  simp only [neg_neg]

/-- Reflected time-reversal of a path. -/
def rev (T : ℝ) (φ : ℝ → E n) : ℝ → E n := fun t => -φ (T - t)

lemma isPath_rev {X : Set (E n)} {T : ℝ} {φ : ℝ → E n} (h : IsPath X T φ) :
    IsPath (-X) T (rev T φ) := by
  obtain ⟨hT, ⟨K, hK⟩, hmap⟩ := h
  have hm : Set.MapsTo (fun t : ℝ => T - t) (Set.Icc 0 T) (Set.Icc 0 T) := by
    intro t ht; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨hT, ⟨K, ?_⟩, ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    simp only [rev, dist_neg_neg]
    have := hK.dist_le_mul (T - a) (hm ha) (T - b) (hm hb)
    rwa [Real.dist_eq, show T - a - (T - b) = -(a - b) by ring, abs_neg, ← Real.dist_eq] at this
  · intro t ht
    show -φ (T - t) ∈ -X
    rw [Set.neg_mem_neg]; exact hmap (hm ht)

lemma derivWithin_rev {T : ℝ} (φ : ℝ → E n) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    derivWithin (rev T φ) (Set.Icc 0 T) t = deriv φ (T - t) := by
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have : rev T φ = -(fun u => φ (T - u)) := rfl
  rw [this, deriv.neg, deriv_comp_const_sub, neg_neg]

lemma lintegral_reflect (T : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Icc 0 T, F (T - t) = ∫⁻ t in Set.Icc 0 T, F t := by
  rw [← MeasureTheory.lintegral_indicator measurableSet_Icc,
    ← MeasureTheory.lintegral_indicator measurableSet_Icc]
  have : (Set.Icc 0 T).indicator (fun t => F (T - t)) =
      fun t => (Set.Icc 0 T).indicator F (T - t) := by
    funext t
    by_cases ht : t ∈ Set.Icc 0 T
    · have ht' : T - t ∈ Set.Icc 0 T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simp [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
    · have ht' : T - t ∉ Set.Icc 0 T := by
        intro h; exact ht ⟨by linarith [h.2], by linarith [h.1]⟩
      simp [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']
  rw [this]
  exact (MeasureTheory.Measure.measurePreserving_sub_left MeasureTheory.volume T).lintegral_comp_emb
    (MeasurableEquiv.subLeft T).measurableEmbedding _

lemma pathCost_rev {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n) (r : ℝ) {T : ℝ}
    {φ : ℝ → E n} (h : IsPath X T φ) :
    pathCost (-X) (fun y => Ψ (-y)) r T (rev T φ) = pathCost X Ψ r T φ := by
  unfold pathCost
  rw [← lintegral_reflect T (fun t => runCost X Ψ r (φ t) (derivWithin φ (Set.Icc 0 T) t))]
  rw [MeasureTheory.setLIntegral_congr MeasureTheory.Ioo_ae_eq_Icc.symm,
    MeasureTheory.setLIntegral_congr MeasureTheory.Ioo_ae_eq_Icc.symm]
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hs : T - t ∈ Set.Ioo 0 T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  show runCost (-X) (fun y => Ψ (-y)) r (-φ (T - t)) (derivWithin (rev T φ) (Set.Icc 0 T) t) = _
  rw [derivWithin_rev φ ht, derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
  have hD := deriv_mem_tanCone hX h.2.2 hs
  exact runCost_neg X Ψ r (φ (T - t)) _ ⟨fun _ => hD.2, fun _ => hD.1⟩

lemma rev_rev (T : ℝ) (φ : ℝ → E n) : rev T (rev T φ) = φ := by
  funext t; simp [rev]

lemma tgtVal_eq {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n) (r : ℝ) (Y : Set (E n))
    (x : E n) : tgtVal X Ψ r Y x = srcVal (-X) (fun y => Ψ (-y)) r (-Y) (-x) := by
  have hX' : IsPolytope (-X) := by
    obtain ⟨S, hS, rfl⟩ := hX
    exact ⟨-S, hS.neg, by rw [Finset.coe_neg, convexHull_neg]⟩
  unfold tgtVal srcVal
  apply le_antisymm
  · refine le_iInf fun T => le_iInf fun ψ => le_iInf fun hψ => ?_
    obtain ⟨hp, h0, hT⟩ := hψ
    have hp' := isPath_rev hp
    rw [neg_neg] at hp'
    have hc := pathCost_rev hX' (fun y => Ψ (-y)) r hp
    simp only [neg_neg] at hc
    rw [← hc]
    refine iInf_le_of_le T (iInf_le_of_le (rev T ψ) (iInf_le_of_le ⟨hp', ?_, ?_⟩ le_rfl))
    · simp [rev, hT]
    · simpa [rev, Set.mem_neg] using h0
  · refine le_iInf fun T => le_iInf fun φ => le_iInf fun hφ => ?_
    obtain ⟨hp, h0, hT⟩ := hφ
    rw [← pathCost_rev hX Ψ r hp]
    refine iInf_le_of_le T (iInf_le_of_le (rev T φ) (iInf_le_of_le ⟨isPath_rev hp, ?_, ?_⟩ le_rfl))
    · simpa [rev, Set.mem_neg] using hT
    · simp [rev, h0]

lemma isPolytope_neg {X : Set (E n)} (hX : IsPolytope X) : IsPolytope (-X) := by
  obtain ⟨S, hS, rfl⟩ := hX
  exact ⟨-S, hS.neg, by rw [Finset.coe_neg, convexHull_neg]⟩

lemma intrinsicInterior_neg (X : Set (E n)) :
    intrinsicInterior ℝ (-X) = -intrinsicInterior ℝ X := by
  have := AffineEquiv.intrinsicInterior_image (LinearEquiv.neg ℝ : E n ≃ₗ[ℝ] E n).toAffineEquiv X
  simpa [Set.image_neg_eq_neg] using this

lemma interiorMeasure_neg (X : Set (E n)) :
    interiorMeasure (-X) = MeasureTheory.Measure.map (Neg.neg : E n → E n) (interiorMeasure X) := by
  unfold interiorMeasure
  rw [vectorSpan_neg]
  set d : ℝ := (Module.finrank ℝ (vectorSpan ℝ X) : ℝ)
  have hiso : Isometry (Neg.neg : E n → E n) := (LinearIsometryEquiv.neg ℝ (E := E n)).isometry
  have hH : MeasureTheory.Measure.map (Neg.neg : E n → E n) μH[d] = μH[d] := by
    rw [hiso.map_hausdorffMeasure (Or.inr neg_surjective), neg_surjective.range_eq,
      MeasureTheory.Measure.restrict_univ]
  have hemb : MeasurableEmbedding (Neg.neg : E n → E n) :=
    (MeasurableEquiv.neg (E n)).measurableEmbedding
  conv_lhs => rw [← hH, hemb.restrict_map, intrinsicInterior_neg]
  congr 2
  ext z; simp

lemma ae_neg_iff (X : Set (E n)) (P : E n → Prop) :
    (∀ᵐ y ∂(interiorMeasure (-X)), P y) ↔ ∀ᵐ x ∂(interiorMeasure X), P (-x) := by
  rw [interiorMeasure_neg]
  exact (MeasurableEquiv.neg (E n)).measurableEmbedding.ae_map_iff

lemma relGrad_neg {X : Set (E n)} {V : E n → ℝ} {x w : E n} (h : relGrad X V x w) :
    relGrad (-X) (fun y => V (-y)) (-x) (-w) := by
  refine ⟨by rw [vectorSpan_neg]; exact neg_mem h.1, ?_⟩
  have h2 : HasFDerivWithinAt V (innerSL ℝ w) X (-(-x)) := by rw [neg_neg]; exact h.2
  have hn : HasFDerivWithinAt (fun y : E n => -y) (-ContinuousLinearMap.id ℝ (E n)) (-X) (-x) :=
    (hasFDerivAt_id (-x)).neg.hasFDerivWithinAt
  have hmap : Set.MapsTo (fun y : E n => -y) (-X) X := fun y hy => hy
  have := h2.comp (-x) hn hmap
  have heq : (innerSL ℝ w).comp (-ContinuousLinearMap.id ℝ (E n)) = innerSL ℝ (-w) := by
    ext z; simp
  rw [heq] at this
  exact this

lemma aeSubsol_of_neg {X : Set (E n)} {Ψ : E n → E n} {r : ℝ} {W : E n → ℝ}
    (h : AESubsolNeg X Ψ r W) : AESubsol (-X) (fun y => Ψ (-y)) r (fun y => W (-y)) := by
  unfold AESubsol
  rw [ae_neg_iff]
  filter_upwards [h] with x ⟨w, hw, hh⟩
  exact ⟨-w, relGrad_neg hw, by rw [ham_neg]; exact hh⟩

lemma aeSubsolNeg_of_sub {X : Set (E n)} {Ψ : E n → E n} {r : ℝ} {V : E n → ℝ}
    (h : AESubsol (-X) (fun y => Ψ (-y)) r V) : AESubsolNeg X Ψ r (fun x => V (-x)) := by
  unfold AESubsolNeg
  let Q : E n → Prop := fun x => ∃ w, relGrad X (fun x => V (-x)) x w ∧ ham X Ψ r x (-w) ≤ 0
  have key : ∀ᵐ y ∂(interiorMeasure (-X)), Q (-y) := by
    filter_upwards [h] with y ⟨w, hw, hh⟩
    refine ⟨-w, ?_, ?_⟩
    · have := relGrad_neg hw
      rw [neg_neg] at this
      exact this
    · rw [neg_neg, ← ham_neg X Ψ r (-y) w, neg_neg]
      exact hh
  have := (ae_neg_iff (-X) Q).2 key
  rw [neg_neg] at this
  exact this

end HJRev


open SemilinearHJ.Verification HJRev
open scoped ENNReal MeasureTheory Pointwise

theorem solution {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (Y : Set (E n)) (hYc : IsCompact Y) (hYX : Y ⊆ X) (hY : Y.Nonempty) :
    (∀ x ∈ X, tgtVal X Ψ r Y x ≠ ⊤) ∧
      (∃ K : NNReal, LipschitzOnWith K (fun x => (tgtVal X Ψ r Y x).toReal) X) ∧
      AESubsolNeg X Ψ r (fun x => (tgtVal X Ψ r Y x).toReal) ∧
      (∀ y ∈ Y, (tgtVal X Ψ r Y y).toReal = 0) ∧
      ∀ W' : E n → ℝ, (∃ K : NNReal, LipschitzOnWith K W' X) → AESubsolNeg X Ψ r W' →
        (∀ y ∈ Y, W' y = 0) → ∀ x ∈ X, W' x ≤ (tgtVal X Ψ r Y x).toReal := by
  have hneg : LipschitzWith 1 (fun y : E n => -y) := LipschitzWith.id.neg
  have hmapX : Set.MapsTo (fun y : E n => -y) (-X) X := fun y hy => hy
  have hmapX' : Set.MapsTo (fun y : E n => -y) X (-X) := fun y hy => by simpa using hy
  have hΨL' : ∃ K : NNReal, LipschitzOnWith K (fun y => Ψ (-y)) (-X) := by
    obtain ⟨K, hK⟩ := hΨL
    exact ⟨K * 1, hK.comp hneg.lipschitzOnWith hmapX⟩
  have hΨ0' : ∀ x ∈ -X, ∀ i, 0 ≤ (fun y => Ψ (-y)) x i := fun x hx i => hΨ0 (-x) hx i
  obtain ⟨hfin, ⟨K, hK⟩, hsub, hzero, hmax⟩ := theorem_3_2 (-X) (isPolytope_neg hX)
    (fun y => Ψ (-y)) hΨL' hΨ0' r hr (-Y) hYc.neg (Set.neg_subset_neg.2 hYX) hY.neg
  have hT : ∀ x, tgtVal X Ψ r Y x = srcVal (-X) (fun y => Ψ (-y)) r (-Y) (-x) :=
    fun x => tgtVal_eq hX Ψ r Y x
  simp only [hT]
  refine ⟨fun x hx => hfin (-x) (by simpa using hx), ⟨K * 1, hK.comp hneg.lipschitzOnWith hmapX'⟩,
    aeSubsolNeg_of_sub hsub, fun y hy => hzero (-y) (by simpa using hy), ?_⟩
  intro W' ⟨K', hK'⟩ hW'sub hW'0 x hx
  have := hmax (fun y => W' (-y)) ⟨K' * 1, hK'.comp hneg.lipschitzOnWith hmapX⟩
    (aeSubsol_of_neg hW'sub) (fun y hy => hW'0 (-y) hy) (-x) (by simpa using hx)
  simpa using this
