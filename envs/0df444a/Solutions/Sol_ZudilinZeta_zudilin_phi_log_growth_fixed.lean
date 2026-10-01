-- Prove2me | solution 1 for ZudilinZeta.zudilin_phi_log_growth_fixed
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T11:13:41.96587+00:00
-- url     : https://prove2.me/submissions/758bbe50-eaf1-4ea8-ab2a-0e7c81bfd6f9

import Definitions.Def_ZudilinZetaArith
import Theorems.Thm_MediumPNT
import Theorems.Thm_ZudilinZeta_zudilin_phi_nonneg_periodic

set_option autoImplicit false


-- PrimeGrowth

open Filter Asymptotics ZudilinZeta MeasureTheory Set
open scoped Topology

private lemma psi_div_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  have hlog : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp Real.tendsto_log_atTop
  have hexp : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg (neg_lt_zero.mpr hc))
  have hsmall : (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      =o[atTop] (fun x : ℝ => x) := by
    apply (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr
    apply hexp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [hx.ne']
  have hzero : Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / x) atTop (𝓝 0) :=
    (hO.trans_isLittleO hsmall).tendsto_div_nhds_zero
  have hlim : Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / x + 1) atTop (𝓝 1) := by
    simpa only [zero_add] using hzero.add_const 1
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp
  ring

private lemma theta_div_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have hsqrt : Real.sqrt =o[atTop] (fun x : ℝ => x) := by
    apply (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr
    simpa only [Real.sqrt_div_self, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)
  have hzero : Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x)
      atTop (𝓝 0) :=
    (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt).tendsto_div_nhds_zero
  have h := psi_div_tendsto_one.sub hzero
  simpa only [sub_div, sub_sub_cancel, sub_zero] using h

private lemma theta_scaled_tendsto (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => Chebyshev.theta (c * n) / n) atTop (𝓝 c) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp [Chebyshev.theta_eq_zero_of_le_one (by norm_num : (0 : ℝ) ≤ 1)]
  have hn : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have h := (theta_div_tendsto_one.comp hn).mul_const c
  simp only [one_mul] at h
  apply h.congr
  intro n
  dsimp only [Function.comp_def]
  field_simp

-- PhiStep

open Set ZudilinZeta MeasureTheory

private def FiniteConvexPartition (s : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℤ) : Prop :=
  ∃ C : Finset (Set (ℝ × ℝ)),
    (∀ c ∈ C, Convex ℝ c) ∧ (∀ c ∈ C, c ⊆ s) ∧
    s = ⋃ c ∈ C, c ∧ (∀ c ∈ C, ∃ v : ℤ, ∀ z ∈ c, f z = v)

private lemma partition_const {s : Set (ℝ × ℝ)} (hs : Convex ℝ s) (v : ℤ) :
    FiniteConvexPartition s (fun _ => v) := by
  classical
  refine ⟨{s}, ?_, ?_, ?_, ?_⟩
  · simpa only [Finset.mem_singleton, forall_eq] using hs
  · simp
  · simp
  · intro c hc
    exact ⟨v, fun _ _ => rfl⟩

private lemma partition_op {s : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℤ}
    (hf : FiniteConvexPartition s f) (hg : FiniteConvexPartition s g)
    (op : ℤ → ℤ → ℤ) : FiniteConvexPartition s (fun z => op (f z) (g z)) := by
  classical
  obtain ⟨C, hCc, hCs, hCu, hCv⟩ := hf
  obtain ⟨D, hDc, hDs, hDu, hDv⟩ := hg
  refine ⟨(C ×ˢ D).image (fun p => p.1 ∩ p.2), ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨⟨c,d⟩, hcd, rfl⟩ := Finset.mem_image.mp hc
    exact (hCc c (Finset.mem_product.mp hcd).1).inter (hDc d (Finset.mem_product.mp hcd).2)
  · intro c hc
    obtain ⟨⟨c,d⟩, hcd, rfl⟩ := Finset.mem_image.mp hc
    exact inter_subset_left.trans (hCs c (Finset.mem_product.mp hcd).1)
  · ext z
    constructor
    · intro hz
      obtain ⟨c,hc,hzc⟩ := (mem_iUnion₂.mp (hCu ▸ hz))
      obtain ⟨d,hd,hzd⟩ := (mem_iUnion₂.mp (hDu ▸ hz))
      exact mem_iUnion₂.mpr ⟨c ∩ d, Finset.mem_image.mpr
        ⟨(c,d), Finset.mem_product.mpr ⟨hc,hd⟩, rfl⟩, hzc, hzd⟩
    · intro hz
      obtain ⟨c,hc,hzc⟩ := mem_iUnion₂.mp hz
      obtain ⟨⟨c,d⟩, hcd, rfl⟩ := Finset.mem_image.mp hc
      exact hCs c (Finset.mem_product.mp hcd).1 hzc.1
  · intro c hc
    obtain ⟨⟨c,d⟩, hcd, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨v,hv⟩ := hCv c (Finset.mem_product.mp hcd).1
    obtain ⟨w,hw⟩ := hDv d (Finset.mem_product.mp hcd).2
    exact ⟨op v w, fun z hz => by dsimp only; rw [hv z hz.1, hw z hz.2]⟩

private lemma partition_floor {s : Set (ℝ × ℝ)} (hs : IsCompact s) (hc : Convex ℝ s)
    {f : ℝ × ℝ → ℝ} (hf : Continuous f) (hlin : IsLinearMap ℝ f) :
    FiniteConvexPartition s (fun z => ⌊f z⌋) := by
  classical
  obtain ⟨a, ha⟩ := hs.bddBelow_image hf.continuousOn
  obtain ⟨b, hb⟩ := hs.bddAbove_image hf.continuousOn
  let cell : ℤ → Set (ℝ × ℝ) := fun k => s ∩ {z | ⌊f z⌋ = k}
  refine ⟨(Finset.Icc ⌊a⌋ ⌊b⌋).image cell, ?_, ?_, ?_, ?_⟩
  · intro c hc'
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hc'
    have he : {z | ⌊f z⌋ = k} = {z | (k : ℝ) ≤ f z} ∩ {z | f z < (k : ℝ) + 1} := by
      ext z
      simp only [mem_ofPred_eq, mem_inter_iff, Int.floor_eq_iff]
    exact hc.inter (he ▸ ((convex_halfSpace_ge hlin (k : ℝ)).inter
      (convex_halfSpace_lt hlin ((k : ℝ) + 1))))
  · intro c hc'
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hc'
    exact inter_subset_left
  · ext z
    constructor
    · intro hz
      have hk : ⌊f z⌋ ∈ Finset.Icc ⌊a⌋ ⌊b⌋ := Finset.mem_Icc.mpr
        ⟨Int.floor_mono (ha (mem_image_of_mem f hz)), Int.floor_mono (hb (mem_image_of_mem f hz))⟩
      exact mem_iUnion₂.mpr ⟨cell ⌊f z⌋, Finset.mem_image.mpr ⟨⌊f z⌋, hk, rfl⟩, hz, rfl⟩
    · intro hz
      obtain ⟨c,hc',hzc⟩ := mem_iUnion₂.mp hz
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hc'
      exact hzc.1
  · intro c hc'
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hc'
    exact ⟨k, fun z hz => hz.2⟩

private lemma partition_sum {s : Set (ℝ × ℝ)} (hc : Convex ℝ s)
    {ι : Type*} (t : Finset ι) (f : ι → ℝ × ℝ → ℤ)
    (hf : ∀ i ∈ t, FiniteConvexPartition s (f i)) :
    FiniteConvexPartition s (fun z => ∑ i ∈ t, f i z) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using partition_const hc 0
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact partition_op (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) (· + ·)

private lemma phiExpr_partition (P : Params) (s : Set (ℝ × ℝ))
    (hs : IsCompact s) (hc : Convex ℝ s) :
    FiniteConvexPartition s (fun z => phiExpr P z.1 z.2) := by
  unfold phiExpr
  apply partition_op _ _ (· + ·)
  · apply partition_sum hc
    intro j hj
    repeat' first | apply partition_op _ _ (· - ·)
                  | apply partition_op _ _ (· + ·)
                  | apply partition_op _ _ (· * ·)
                  | apply partition_const hc
                  | apply partition_floor hs hc
    all_goals first | fun_prop | (constructor <;> intros <;> simp <;> ring)
  · apply partition_sum hc
    intro j hj
    repeat' first | apply partition_op _ _ (· - ·)
                  | apply partition_floor hs hc
    all_goals first | fun_prop | (constructor <;> intros <;> simp <;> ring)

private lemma phiExpr_nonneg (P : Params) (x y : ℝ) : 0 ≤ phiExpr P x y := by
  have h1 (e0 ej : ℝ) :
      0 ≤ ⌊y⌋ + ⌊e0 * x - y⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ - 2 * ⌊ej * x⌋ := by
    have ha : ⌊(e0 - ej) * x - y⌋ + ⌊ej * x⌋ ≤ ⌊e0 * x - y⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le ((e0 - ej) * x - y), Int.floor_le (ej * x)]
    have hb : ⌊ej * x⌋ + ⌊y - ej * x⌋ ≤ ⌊y⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le (y - ej * x), Int.floor_le (ej * x)]
    omega
  have h2 (e0 ej : ℝ) :
      0 ≤ ⌊(e0 - 2 * ej) * x⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ := by
    have h : ⌊y - ej * x⌋ + ⌊(e0 - ej) * x - y⌋ ≤ ⌊(e0 - 2 * ej) * x⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le (y - ej * x), Int.floor_le ((e0 - ej) * x - y)]
    omega
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => h1 _ _))
    (Finset.sum_nonneg (fun _ _ => h2 _ _))

private lemma phiExpr_bddBelow (P : Params) (x : ℝ) :
    BddBelow (phiExpr P x '' Ico (0 : ℝ) 1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, _, rfl⟩
  exact phiExpr_nonneg P x y


private lemma phi_sublevel_intervals (P : Params) (a b : ℝ) (k : ℤ) :
    ∃ C : Finset (Set ℝ), (∀ c ∈ C, Convex ℝ c ∧ c ⊆ Icc a b) ∧
      {x | x ∈ Icc a b ∧ phi P x ≤ k} = ⋃ c ∈ C, c := by
  classical
  let s : Set (ℝ × ℝ) := Icc a b ×ˢ Icc 0 1
  obtain ⟨C, hCc, hCs, hCu, hCv⟩ := phiExpr_partition P s
    (isCompact_Icc.prod isCompact_Icc) ((convex_Icc a b).prod (convex_Icc 0 1))
  let D := C.filter (fun c => ∀ z ∈ c, phiExpr P z.1 z.2 ≤ k)
  let proj : Set (ℝ × ℝ) → Set ℝ := fun c =>
    Prod.fst '' (c ∩ (univ ×ˢ Ico (0 : ℝ) 1))
  refine ⟨D.image proj, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    have hdC := (Finset.mem_filter.mp hd).1
    constructor
    · exact ((hCc d hdC).inter (convex_univ.prod (convex_Ico 0 1))).linear_image
        (LinearMap.fst ℝ ℝ ℝ)
    · rintro _ ⟨z, hz, rfl⟩
      exact (hCs d hdC hz.1).1
  · ext x
    constructor
    · rintro ⟨hx, hxk⟩
      obtain ⟨y, hy, he⟩ := Int.csInf_mem
        (show (phiExpr P x '' Ico (0 : ℝ) 1).Nonempty from
          ⟨_, 0, ⟨le_rfl, one_pos⟩, rfl⟩) (phiExpr_bddBelow P x)
      have hz : (x,y) ∈ s := ⟨hx, hy.1, hy.2.le⟩
      obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp (hCu ▸ hz)
      have hd : c ∈ D := by
        refine Finset.mem_filter.mpr ⟨hc, ?_⟩
        obtain ⟨v, hv⟩ := hCv c hc
        dsimp only at hv
        intro z hz
        rw [hv z hz, ← hv (x,y) hzc]
        exact he.trans_le hxk
      exact mem_iUnion₂.mpr ⟨proj c, Finset.mem_image.mpr ⟨c, hd, rfl⟩,
        (x,y), ⟨hzc, mem_univ _, hy⟩, rfl⟩
    · intro hx
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨⟨x,y⟩, hz, rfl⟩ := hxc
      have hd' := Finset.mem_filter.mp hd
      refine ⟨(hCs d hd'.1 hz.1).1, ?_⟩
      exact (csInf_le (phiExpr_bddBelow P x) ⟨y, hz.2.2, rfl⟩).trans (hd'.2 (x,y) hz.1)

private lemma inv_preimage_convex {s : Set ℝ} (hs : Convex ℝ s) :
    Convex ℝ {x | 0 < x ∧ x⁻¹ ∈ s} := by
  apply Set.OrdConnected.convex
  constructor
  intro x hx y hy z hz
  refine ⟨lt_of_lt_of_le hx.1 hz.1, ?_⟩
  exact hs.ordConnected.out hy.2 hx.2
    ⟨by simpa only [one_div] using one_div_le_one_div_of_le (hx.1.trans_le hz.1) hz.2,
     by simpa only [one_div] using one_div_le_one_div_of_le hx.1 hz.1⟩

private lemma phi_inv_sublevel_intervals (P : Params) (a b : ℝ) (ha : 0 < a) (k : ℤ) :
    ∃ C : Finset (Set ℝ), (∀ c ∈ C, Convex ℝ c ∧ c ⊆ Icc a b) ∧
      {x | x ∈ Icc a b ∧ phi P x⁻¹ ≤ k} = ⋃ c ∈ C, c := by
  classical
  obtain ⟨C, hC, he⟩ := phi_sublevel_intervals P b⁻¹ a⁻¹ k
  let pre : Set ℝ → Set ℝ := fun c => Icc a b ∩ {x | 0 < x ∧ x⁻¹ ∈ c}
  refine ⟨C.image pre, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨(convex_Icc a b).inter (inv_preimage_convex (hC d hd).1), inter_subset_left⟩
  · ext x
    constructor
    · rintro ⟨hx, hk⟩
      have hxp : 0 < x := ha.trans_le hx.1
      have hxi : x⁻¹ ∈ Icc b⁻¹ a⁻¹ :=
        ⟨by simpa only [one_div] using one_div_le_one_div_of_le hxp hx.2,
         by simpa only [one_div] using one_div_le_one_div_of_le ha hx.1⟩
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (he ▸ (show x⁻¹ ∈ {x | x ∈ Icc b⁻¹ a⁻¹ ∧ phi P x ≤ k} from ⟨hxi, hk⟩))
      exact mem_iUnion₂.mpr ⟨pre c, Finset.mem_image.mpr ⟨c, hc, rfl⟩, hx, hxp, hxc⟩
    · intro hx
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      refine ⟨hxc.1, ?_⟩
      have hi : x⁻¹ ∈ ⋃ c ∈ C, c := mem_iUnion₂.mpr ⟨d, hd, hxc.2.2⟩
      rw [← he] at hi
      exact hi.2


private lemma phi_measurable (P : Params) : Measurable (phi P) := by
  apply measurable_of_Iic
  intro k
  have hm (n : ℕ) : MeasurableSet {x : ℝ | x ∈ Icc (-(n : ℝ)) n ∧ phi P x ≤ k} := by
    obtain ⟨C, hC, he⟩ := phi_sublevel_intervals P (-(n : ℝ)) n k
    rw [he]
    exact Finset.measurableSet_biUnion C (fun c hc => (hC c hc).1.ordConnected.measurableSet)
  have he : phi P ⁻¹' Iic k = ⋃ n : ℕ, {x : ℝ | x ∈ Icc (-(n : ℝ)) n ∧ phi P x ≤ k} := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      exact mem_iUnion.mpr ⟨n, ⟨by have := neg_abs_le x; linarith,
        by have := le_abs_self x; linarith⟩, hx⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact hn.2
  rw [he]
  exact MeasurableSet.iUnion hm

private lemma phi_bounded (P : Params) (x : ℝ) :
    phi P x ≤ 2 * ((Finset.Icc 1 P.r).card : ℤ) + (Finset.Icc (P.r + 1) P.q).card := by
  have h1 (e0 ej y : ℝ) :
      ⌊y⌋ + ⌊e0 * x - y⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ - 2 * ⌊ej * x⌋ ≤ 2 := by
    have ha := Int.le_floor_add_floor ((e0 - ej) * x - y) (ej * x)
    have hb := Int.le_floor_add_floor (ej * x) (y - ej * x)
    rw [show (e0 - ej) * x - y + ej * x = e0 * x - y by ring] at ha
    rw [show ej * x + (y - ej * x) = y by ring] at hb
    omega
  have h2 (e0 ej y : ℝ) :
      ⌊(e0 - 2 * ej) * x⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ ≤ 1 := by
    have h := Int.le_floor_add_floor (y - ej * x) ((e0 - ej) * x - y)
    rw [show y - ej * x + ((e0 - ej) * x - y) = (e0 - 2 * ej) * x by ring] at h
    omega
  apply (csInf_le (phiExpr_bddBelow P x) (show phiExpr P x 0 ∈ _ from
    ⟨0, ⟨le_rfl, one_pos⟩, rfl⟩)).trans
  have hsum := add_le_add (Finset.sum_le_sum (s := Finset.Icc 1 P.r) (fun j _ => h1 (P.eta 0) (P.eta j) 0))
    (Finset.sum_le_sum (s := Finset.Icc (P.r + 1) P.q) (fun j _ => h2 (P.eta 0) (P.eta j) 0))
  simpa [phiExpr, mul_comm] using hsum


-- PrimeMeasure

open MeasureTheory Filter Set
open scoped Topology

open Classical in
private noncomputable def primeMeasure (M n : ℕ) : Measure ℝ :=
  ∑ p ∈ (Finset.Icc 1 (M * n)).filter Nat.Prime,
    Real.toNNReal (Real.log (p : ℝ) / (n : ℝ)) • Measure.dirac ((p : ℝ) / n)

private instance primeMeasure_finite (M n : ℕ) : IsFiniteMeasure (primeMeasure M n) := by
  unfold primeMeasure
  infer_instance

open Classical in
private lemma primeMeasure_apply (M n : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    (primeMeasure M n).real s =
      ∑ p ∈ (Finset.Icc 1 (M * n)).filter Nat.Prime,
        if (p : ℝ) / n ∈ s then Real.log (p : ℝ) / n else 0 := by
  classical
  simp only [primeMeasure, measureReal_def, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, Measure.dirac_apply' _ hs, Set.indicator_apply, Pi.one_apply]
  rw [ENNReal.toReal_sum (by intros; split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp [Real.toNNReal_of_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg n))]

private lemma primeMeasure_Iic (M n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M)
    (hn : 0 < n) :
    (primeMeasure M n).real (Iic x) = Chebyshev.theta (x * n) / n := by
  classical
  rw [primeMeasure_apply M n _ measurableSet_Iic]
  rw [Chebyshev.theta, Finset.sum_div]
  trans ∑ p ∈ ((Finset.Icc 1 (M * n)).filter Nat.Prime).filter
      (fun p : ℕ => (p : ℝ) / n ∈ Iic x), Real.log (p : ℝ) / n
  · exact (Finset.sum_filter _ _).symm
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, mem_Iic]
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [div_le_iff₀ hn', Nat.le_floor_iff (mul_nonneg hx hn'.le)]
    constructor
    · rintro ⟨⟨⟨hp, hpM⟩, hprime⟩, hpx⟩
      exact ⟨⟨by omega, hpx⟩, hprime⟩
    · rintro ⟨⟨hp, hpx⟩, hprime⟩
      refine ⟨⟨⟨by omega, ?_⟩, hprime⟩, hpx⟩
      exact_mod_cast hpx.trans (mul_le_mul_of_nonneg_right hxM hn'.le)
  · intros
    rfl

private lemma primeMeasure_integral (M n : ℕ) (f : ℝ → ℝ) :
    (∫ x, f x ∂primeMeasure M n) =
      ∑ p ∈ (Finset.Icc 1 (M * n)).filter Nat.Prime,
        Real.log (p : ℝ) / n * f ((p : ℝ) / n) := by
  classical
  unfold primeMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul,
      Real.toNNReal_of_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg n))]
    rfl
  · intro p hp
    exact (integrable_dirac (by finiteness)).smul_measure_nnreal

private lemma primeMeasure_integral_Icc (M n : ℕ) (f : ℝ → ℝ) :
    (∫ x in Icc 0 (M : ℝ), f x ∂primeMeasure M n) =
      ∫ x, f x ∂primeMeasure M n := by
  classical
  rw [← integral_indicator measurableSet_Icc, primeMeasure_integral, primeMeasure_integral]
  apply Finset.sum_congr rfl
  intro p hp
  have hpM := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  have hp0 := (Finset.mem_filter.mp hp).2.pos
  have hn : 0 < n := by nlinarith
  rw [indicator_of_mem]
  constructor
  · positivity
  · rw [div_le_iff₀ (show 0 < (n : ℝ) by exact_mod_cast hn)]
    exact_mod_cast hpM

-- MeasureLimits

open MeasureTheory Filter Set
open scoped Topology

private lemma cdf_Iio_tendsto {μ : ℕ → Measure ℝ} [∀ n, IsFiniteMeasure (μ n)]
    {M : ℝ} (h : ∀ x ∈ Icc 0 M, Tendsto (fun n => (μ n).real (Iic x)) atTop (𝓝 x))
    {x : ℝ} (hx : x ∈ Icc 0 M) :
    Tendsto (fun n => (μ n).real (Iio x)) atTop (𝓝 x) := by
  apply tendsto_order.mpr
  constructor
  · intro y hy
    by_cases hy0 : y < 0
    · exact Filter.Eventually.of_forall (fun n => hy0.trans_le (measureReal_nonneg))
    obtain ⟨z, hyz, hzx⟩ := exists_between hy
    have hz : z ∈ Icc 0 M := ⟨(le_of_not_gt hy0).trans hyz.le, hzx.le.trans hx.2⟩
    filter_upwards [(h z hz).eventually_const_lt hyz] with n hn
    exact hn.trans_le (measureReal_mono (Iic_subset_Iio.mpr hzx))
  · intro y hy
    filter_upwards [(h x hx).eventually_lt_const hy] with n hn
    exact (measureReal_mono Iio_subset_Iic_self).trans_lt hn

private lemma interval_mass_tendsto {μ : ℕ → Measure ℝ} [∀ n, IsFiniteMeasure (μ n)]
    {M : ℝ} (h : ∀ x ∈ Icc 0 M, Tendsto (fun n => (μ n).real (Iic x)) atTop (𝓝 x))
    {a b : ℝ} (ha : a ∈ Icc 0 M) (hb : b ∈ Icc 0 M) (hab : a ≤ b) :
    Tendsto (fun n => (μ n).real (Icc a b)) atTop (𝓝 (b-a)) ∧
    Tendsto (fun n => (μ n).real (Ioo a b)) atTop (𝓝 (b-a)) := by
  constructor
  · have ht := (h b hb).sub (cdf_Iio_tendsto h ha)
    convert ht using 1
    funext n
    rw [← measureReal_sdiff (show Iio a ⊆ Iic b from fun x hx => hx.le.trans hab) measurableSet_Iio]
    congr 1
    ext x
    simp only [Set.mem_sdiff, mem_Iic, mem_Iio, mem_Icc, not_lt]
    tauto
  · by_cases he : a = b
    · subst b
      simp
    have ht := (cdf_Iio_tendsto h hb).sub (h a ha)
    convert ht using 1
    funext n
    rw [← measureReal_sdiff (show Iic a ⊆ Iio b from fun x hx => hx.trans_lt (lt_of_le_of_ne hab he)) measurableSet_Iic]
    congr 1
    ext x
    simp only [Set.mem_sdiff, mem_Iic, mem_Iio, mem_Ioo, not_le]
    tauto

private lemma convex_mass_tendsto {μ : ℕ → Measure ℝ} [∀ n, IsFiniteMeasure (μ n)]
    {M : ℝ} (h : ∀ x ∈ Icc 0 M, Tendsto (fun n => (μ n).real (Iic x)) atTop (𝓝 x))
    {s : Set ℝ} (hs : Convex ℝ s) (hsM : s ⊆ Icc 0 M) :
    Tendsto (fun n => (μ n).real s) atTop (𝓝 (volume.real s)) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hlo : BddBelow s := ⟨0, fun x hx => (hsM hx).1⟩
  have hhi : BddAbove s := ⟨M, fun x hx => (hsM hx).2⟩
  have hin : Ioo (sInf s) (sSup s) ⊆ s := (show IsConnected s from ⟨hne, hs.isPreconnected⟩).Ioo_csInf_csSup_subset hlo hhi
  have hout : s ⊆ Icc (sInf s) (sSup s) := subset_Icc_csInf_csSup hlo hhi
  have hab : sInf s ≤ sSup s := csInf_le_csSup hne hlo hhi
  have ha : sInf s ∈ Icc 0 M :=
    ⟨le_csInf hne (fun x hx => (hsM hx).1), hab.trans (csSup_le hne (fun x hx => (hsM hx).2))⟩
  have hb : sSup s ∈ Icc 0 M :=
    ⟨ha.1.trans hab, csSup_le hne (fun x hx => (hsM hx).2)⟩
  have hfinite : volume s ≠ ⊤ := measure_ne_top_of_subset hsM (by simp [Real.volume_Icc])
  have hv : volume.real s = sSup s - sInf s := by
    apply le_antisymm
    · simpa only [Real.volume_real_Icc_of_le hab] using measureReal_mono (μ := volume) hout (by simp [Real.volume_Icc])
    · simpa only [Real.volume_real_Ioo_of_le hab] using measureReal_mono hin hfinite
  rw [hv]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (interval_mass_tendsto h ha hb hab).2 (interval_mass_tendsto h ha hb hab).1
    (fun n => measureReal_mono hin) (fun n => measureReal_mono hout)

private lemma union_convex_mass_tendsto {μ : ℕ → Measure ℝ} [∀ n, IsFiniteMeasure (μ n)]
    {M : ℝ} (h : ∀ x ∈ Icc 0 M, Tendsto (fun n => (μ n).real (Iic x)) atTop (𝓝 x))
    {C : Finset (Set ℝ)} (hC : ∀ c ∈ C, Convex ℝ c ∧ c ⊆ Icc 0 M) :
    Tendsto (fun n => (μ n).real (⋃ c ∈ C, c)) atTop (𝓝 (volume.real (⋃ c ∈ C, c))) := by
  let S : Set (Set ℝ) := {s | Convex ℝ s ∧ s ⊆ Icc 0 M}
  have hS : IsPiSystem S := by
    intro s hs t ht hne
    exact ⟨hs.1.inter ht.1, inter_subset_left.trans hs.2⟩
  exact hS.tendsto_measureReal_biUnion hC (fun s hs => hs.1.ordConnected.measurableSet)
    (fun s hs => convex_mass_tendsto h hs.1 hs.2)
    (fun s hs => measure_ne_top_of_subset hs.2 (by simp [Real.volume_Icc]))

open Classical in
private lemma finite_range_integral (μ : Measure ℝ) (f : ℝ → ℤ) (s : Set ℝ)
    (hs : MeasurableSet s) (hsf : μ s ≠ ⊤) (B : ℤ)
    (hf : ∀ x ∈ s, f x ∈ Finset.Icc 0 B)
    (hmeas : ∀ k, MeasurableSet {x | x ∈ s ∧ f x = k}) :
    (∫ x in s, (f x : ℝ) ∂μ) =
      ∑ k ∈ Finset.Icc 0 B, (k : ℝ) * μ.real {x | x ∈ s ∧ f x = k} := by
  have he : s.indicator (fun x => (f x : ℝ)) =
      fun x => ∑ k ∈ Finset.Icc 0 B, ({x | x ∈ s ∧ f x = k}).indicator (fun _ => (k : ℝ)) x := by
    funext x
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]
      symm
      apply (Finset.sum_eq_single (f x) ?_ ?_).trans
      · simp only [mem_ofPred_eq, hx, and_self, indicator_of_mem]
      · intro k hk hne
        rw [indicator_of_notMem]
        simp only [mem_ofPred_eq, hx, true_and]
        exact Ne.symm hne
      · intro h
        exact (h (hf x hx)).elim
    · rw [indicator_of_notMem hx]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      rw [indicator_of_notMem]
      simp only [mem_ofPred_eq, hx, false_and, not_false_eq_true]
  rw [← integral_indicator hs, he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_indicator_const _ (hmeas k), smul_eq_mul, mul_comm]
  · intro k hk
    apply (integrable_indicator_iff (hmeas k)).mpr
    exact integrableOn_const (measure_ne_top_of_subset (fun x hx => hx.1) hsf)

private lemma finite_range_integral_tendsto {μ : ℕ → Measure ℝ} [∀ n, IsFiniteMeasure (μ n)]
    (f : ℝ → ℤ) (s : Set ℝ) (hs : MeasurableSet s) (hsf : volume s ≠ ⊤) (B : ℤ)
    (hf : ∀ x ∈ s, f x ∈ Finset.Icc 0 B)
    (hmeas : ∀ k, MeasurableSet {x | x ∈ s ∧ f x ≤ k})
    (hlim : ∀ k, Tendsto (fun n => (μ n).real {x | x ∈ s ∧ f x ≤ k}) atTop
      (𝓝 (volume.real {x | x ∈ s ∧ f x ≤ k}))) :
    Tendsto (fun n => ∫ x in s, (f x : ℝ) ∂μ n) atTop
      (𝓝 (∫ x in s, (f x : ℝ))) := by
  have he (k : ℤ) : {x | x ∈ s ∧ f x = k} =
      {x | x ∈ s ∧ f x ≤ k} \ {x | x ∈ s ∧ f x ≤ k-1} := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    constructor <;> intro hx
    · rcases hx with ⟨hs, rfl⟩
      exact ⟨⟨hs, le_rfl⟩, fun h => by have := h.2; omega⟩
    · exact ⟨hx.1.1, by have : ¬ f x ≤ k - 1 := fun h => hx.2 ⟨hx.1.1, h⟩; have := hx.1.2; omega⟩
  have hm (k : ℤ) : MeasurableSet {x | x ∈ s ∧ f x = k} := by
    rw [he k]
    exact (hmeas k).diff (hmeas (k-1))
  have ht (k : ℤ) : Tendsto (fun n => (μ n).real {x | x ∈ s ∧ f x = k}) atTop
      (𝓝 (volume.real {x | x ∈ s ∧ f x = k})) := by
    have hsub : {x | x ∈ s ∧ f x ≤ k-1} ⊆ {x | x ∈ s ∧ f x ≤ k} :=
      fun x hx => ⟨hx.1, by have := hx.2; omega⟩
    have hmμ (n : ℕ) : (μ n).real {x | x ∈ s ∧ f x = k} =
        (μ n).real {x | x ∈ s ∧ f x ≤ k} - (μ n).real {x | x ∈ s ∧ f x ≤ k-1} := by
      rw [he k, measureReal_sdiff hsub (hmeas (k-1))]
    have hmv : volume.real {x | x ∈ s ∧ f x = k} =
        volume.real {x | x ∈ s ∧ f x ≤ k} - volume.real {x | x ∈ s ∧ f x ≤ k-1} := by
      rw [he k, measureReal_sdiff hsub (hmeas (k-1)) (measure_ne_top_of_subset (fun x hx => hx.1) hsf)]
    simp_rw [hmμ, hmv]
    exact (hlim k).sub (hlim (k-1))
  have hi (n : ℕ) := finite_range_integral (μ n) f s hs (by finiteness) B hf hm
  simp_rw [hi, finite_range_integral volume f s hs hsf B hf hm]
  exact tendsto_finsetSum _ (fun k hk => (ht k).const_mul (k : ℝ))

-- Truncation

open MeasureTheory Filter Set
open scoped Topology

private lemma bounded_integrableOn (μ : Measure ℝ) {f : ℝ → ℝ} (hm : Measurable f)
    {B : ℝ} (hb : ∀ x, |f x| ≤ B) {s : Set ℝ} (hs : μ s ≠ ⊤) : IntegrableOn f s μ := by
  apply (integrableOn_const (C := B) hs).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)

private lemma truncation_bound (μ : Measure ℝ) {f : ℝ → ℝ} (hm : Measurable f)
    {B : ℝ} (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, f x ≤ B)
    {M δ : ℝ} (hδ : 0 ≤ δ) (hδM : δ ≤ M) (hs : μ (Icc 0 M) ≠ ⊤) :
    0 ≤ (∫ x in Icc 0 M, f x ∂μ) - (∫ x in Icc δ M, f x ∂μ) ∧
    (∫ x in Icc 0 M, f x ∂μ) - (∫ x in Icc δ M, f x ∂μ) ≤ B * μ.real (Icc 0 δ) := by
  have hB : 0 ≤ B := (hf 0).trans (hb 0)
  have hba (x : ℝ) : |f x| ≤ B := by rw [abs_of_nonneg (hf x)]; exact hb x
  have hi := bounded_integrableOn μ hm hba hs
  have hlo : Ico (0 : ℝ) δ ⊆ Icc 0 M := fun x hx => ⟨hx.1, hx.2.le.trans hδM⟩
  have hup : Icc δ M ⊆ Icc 0 M := Icc_subset_Icc_left hδ
  have he := setIntegral_union (show Disjoint (Ico (0 : ℝ) δ) (Icc δ M) from by
      rw [disjoint_left]; intro x hx hy; exact hx.2.not_ge hy.1)
    measurableSet_Icc (hi.mono_set hlo) (hi.mono_set hup)
  rw [Ico_union_Icc_eq_Icc hδ hδM] at he
  rw [he, add_sub_cancel_right]
  constructor
  · exact setIntegral_nonneg measurableSet_Ico (fun x hx => hf x)
  · calc
      (∫ x in Ico 0 δ, f x ∂μ) ≤ ∫ x in Ico 0 δ, B ∂μ :=
        integral_mono_ae (hi.mono_set hlo) (integrableOn_const (measure_ne_top_of_subset hlo hs))
          (Filter.Eventually.of_forall hb)
      _ = B * μ.real (Ico 0 δ) := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ B * μ.real (Icc 0 δ) := mul_le_mul_of_nonneg_left
        (measureReal_mono Ico_subset_Icc_self (measure_ne_top_of_subset (Icc_subset_Icc_right hδM) hs)) hB

private lemma truncated_integrals_tendsto {μ : ℕ → Measure ℝ} [∀ n, IsFiniteMeasure (μ n)]
    {f : ℝ → ℝ} (hm : Measurable f) {B M : ℝ} (hf : ∀ x, 0 ≤ f x)
    (hb : ∀ x, f x ≤ B) (hM : 0 < M)
    (hcdf : ∀ x ∈ Icc 0 M, Tendsto (fun n => (μ n).real (Iic x)) atTop (𝓝 x))
    (hlim : ∀ δ, 0 < δ → δ ≤ M →
      Tendsto (fun n => ∫ x in Icc δ M, f x ∂μ n) atTop (𝓝 (∫ x in Icc δ M, f x))) :
    Tendsto (fun n => ∫ x in Icc 0 M, f x ∂μ n) atTop (𝓝 (∫ x in Icc 0 M, f x)) := by
  have hB : 0 ≤ B := (hf 0).trans (hb 0)
  have hv := fun (δ : ℝ) (hδ : 0 ≤ δ) (hδM : δ ≤ M) => truncation_bound volume hm hf hb hδ hδM
    (by simp [Real.volume_Icc])
  have hμ := fun (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hδM : δ ≤ M) => truncation_bound (μ n) hm hf hb hδ hδM (by finiteness)
  apply tendsto_order.mpr
  constructor
  · intro r hr
    obtain ⟨δ, hδ, hδM, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ M ∧
        B * δ < (∫ x in Icc 0 M, f x) - r := by
      let δ := min M (((∫ x in Icc 0 M, f x) - r) / (2 * (B+1)))
      have hd : 0 < δ := lt_min hM (div_pos (sub_pos.mpr hr) (by positivity))
      refine ⟨δ, hd, min_le_left _ _, ?_⟩
      have hle := min_le_right M (((∫ x in Icc 0 M, f x) - r) / (2 * (B+1)))
      have hden : 0 < 2 * (B+1) := by positivity
      have h := (le_div_iff₀ hden).mp hle
      nlinarith
    have hv' := hv δ hδ.le hδM
    rw [Real.volume_real_Icc_of_le hδ.le, sub_zero] at hv'
    have hr' : r < ∫ x in Icc δ M, f x := by linarith
    filter_upwards [(hlim δ hδ hδM).eventually_const_lt hr'] with n hn
    have hμ' := (hμ n δ hδ.le hδM).1
    linarith
  · intro r hr
    obtain ⟨δ, hδ, hδM, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ M ∧
        B * δ < r - (∫ x in Icc 0 M, f x) := by
      let δ := min M ((r - (∫ x in Icc 0 M, f x)) / (2 * (B+1)))
      have hd : 0 < δ := lt_min hM (div_pos (sub_pos.mpr hr) (by positivity))
      refine ⟨δ, hd, min_le_left _ _, ?_⟩
      have hle := min_le_right M ((r - (∫ x in Icc 0 M, f x)) / (2 * (B+1)))
      have hden : 0 < 2 * (B+1) := by positivity
      have h := (le_div_iff₀ hden).mp hle
      nlinarith
    have hv' := (hv δ hδ.le hδM).1
    have ht := (hlim δ hδ hδM).add ((hcdf δ ⟨hδ.le, hδM⟩).const_mul B)
    have hlt : (∫ x in Icc δ M, f x) + B * δ < r := by linarith
    filter_upwards [ht.eventually_lt_const hlt] with n hn
    have hμ' := (hμ n δ hδ.le hδM).2
    have hmono : (μ n).real (Icc 0 δ) ≤ (μ n).real (Iic δ) :=
      measureReal_mono Icc_subset_Iic_self
    have := mul_le_mul_of_nonneg_left hmono hB
    linarith

-- IntegralInversion
open ZudilinZeta MeasureTheory Set

private lemma weighted_integral_inversion (P : Params) {M : ℝ} (hM : 0 < M) :
    (∫ x in Icc 0 M, (phi P x⁻¹ : ℝ)) =
      ∫ x in Ioi (1/M), (phi P x : ℝ) / x^2 := by
  have hset : Inv.inv '' Ioi (1/M) = Ioo (0 : ℝ) M := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxp : 0 < x := (one_div_pos.mpr hM).trans hx
      exact ⟨inv_pos.mpr hxp, (inv_lt_comm₀ hxp hM).mpr (by simpa only [one_div, mem_Ioi] using hx)⟩
    · intro hy
      refine ⟨y⁻¹, ?_, inv_inv _⟩
      simpa only [one_div, mem_Ioi] using (one_div_lt_one_div_of_lt hy.1 hy.2)
  have hderiv : ∀ x ∈ Ioi (1/M), HasDerivWithinAt Inv.inv (-(x^2)⁻¹) (Ioi (1/M)) x := by
    intro x hx
    exact (hasDerivAt_inv (ne_of_gt ((one_div_pos.mpr hM).trans hx))).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv
    (inv_injective.injOn) (fun x : ℝ => (phi P x⁻¹ : ℝ))
  rw [hset] at h
  rw [integral_Icc_eq_integral_Ioo, h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [abs_neg, abs_inv, abs_pow, inv_inv, smul_eq_mul, sq_abs]
  ring

-- PhiGrowthAssembly
private lemma primeMeasure_cdf_tendsto (M : ℕ) (x : ℝ) (hx : x ∈ Icc 0 (M : ℝ)) :
    Tendsto (fun n => (primeMeasure M n).real (Iic x)) atTop (𝓝 x) := by
  apply (theta_scaled_tendsto x hx.1).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (primeMeasure_Iic M n hx.1 hx.2 hn).symm

private lemma phi_prime_sum_tendsto (P : Params) (M : ℕ) (hM : 0 < M) :
    Tendsto (fun n : ℕ => ∑ p ∈ (Finset.Icc 1 (M * n)).filter Nat.Prime,
      Real.log (p : ℝ) / n * (phi P ((n : ℝ) / p) : ℝ)) atTop
      (𝓝 (∫ x in Ioi (1 / (M : ℝ)), (phi P x : ℝ) / x^2)) := by
  let B : ℤ := 2 * ((Finset.Icc 1 P.r).card : ℤ) + (Finset.Icc (P.r+1) P.q).card
  have hφ : ∀ x, 0 ≤ phi P x ∧ phi P x ≤ B :=
    fun x => ⟨(zudilin_phi_nonneg_periodic P).1 x, phi_bounded P x⟩
  have hm : Measurable (fun x : ℝ => (phi P x⁻¹ : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp ((phi_measurable P).comp measurable_inv)
  have hf (x : ℝ) : 0 ≤ (phi P x⁻¹ : ℝ) := by exact_mod_cast (hφ x⁻¹).1
  have hb (x : ℝ) : (phi P x⁻¹ : ℝ) ≤ (B : ℝ) := by exact_mod_cast (hφ x⁻¹).2
  have hi := truncated_integrals_tendsto (μ := primeMeasure M) hm hf hb
    (Nat.cast_pos.mpr hM) (primeMeasure_cdf_tendsto M)
  have hlim : ∀ δ : ℝ, 0 < δ → δ ≤ (M : ℝ) →
      Tendsto (fun n => ∫ x in Icc δ (M : ℝ), (phi P x⁻¹ : ℝ) ∂primeMeasure M n)
        atTop (𝓝 (∫ x in Icc δ (M : ℝ), (phi P x⁻¹ : ℝ))) := by
    intro δ hδ hδM
    apply finite_range_integral_tendsto (fun x => phi P x⁻¹) (Icc δ (M : ℝ))
      measurableSet_Icc (by simp [Real.volume_Icc]) B
      (fun x hx => Finset.mem_Icc.mpr (hφ x⁻¹))
    · intro k
      exact measurableSet_Icc.inter
        (measurableSet_le ((phi_measurable P).comp measurable_inv) measurable_const)
    · intro k
      obtain ⟨C, hC, he⟩ := phi_inv_sublevel_intervals P δ M hδ k
      rw [he]
      apply union_convex_mass_tendsto (primeMeasure_cdf_tendsto M)
      intro c hc
      exact ⟨(hC c hc).1, (hC c hc).2.trans (Icc_subset_Icc_left hδ.le)⟩
  have ht := hi hlim
  rw [weighted_integral_inversion P (Nat.cast_pos.mpr hM)] at ht
  simpa only [primeMeasure_integral_Icc, primeMeasure_integral, inv_div] using ht

-- PhiGrowthCutoff
private lemma log_Phi_eq_sum (P : Params) (n : ℕ) :
    Real.log (Phi P n : ℝ) / n =
      ∑ p ∈ ((Finset.Icc 1 (m P (P.q-P.r) * n)).filter Nat.Prime).filter
        (fun p => P.eta 0 * n < p * p),
        Real.log (p : ℝ) / n * (phi P ((n : ℝ) / p) : ℝ) := by
  classical
  have he : ((Finset.Icc 1 (m P (P.q-P.r) * n)).filter Nat.Prime).filter
        (fun p => P.eta 0 * n < p * p) =
      (Finset.Icc 1 (m P (P.q-P.r) * n)).filter (fun p => Nat.Prime p ∧ P.eta 0 * n < p * p) := by
    ext p
    simp only [Finset.mem_filter, and_assoc]
  rw [he, Phi, Nat.cast_prod, Real.log_prod, Finset.sum_div]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
    have hφ := (zudilin_phi_nonneg_periodic P).1 ((n : ℝ) / p)
    rw [show ((phi P ((n : ℝ) / p)).toNat : ℝ) = (phi P ((n : ℝ) / p) : ℝ) by exact_mod_cast Int.toNat_of_nonneg hφ]
    ring
  · intro p hp
    have hp0 : 0 < p := (Finset.mem_filter.mp hp).2.1.pos
    positivity

private lemma prime_cutoff_bound (P : Params) (n : ℕ) :
    let B : ℝ := 2 * ((Finset.Icc 1 P.r).card : ℝ) + (Finset.Icc (P.r+1) P.q).card
    let S := (Finset.Icc 1 (m P (P.q-P.r) * n)).filter Nat.Prime
    let A := ∑ p ∈ S, Real.log (p : ℝ) / n * (phi P ((n : ℝ) / p) : ℝ)
    0 ≤ A - Real.log (Phi P n : ℝ) / n ∧
    A - Real.log (Phi P n : ℝ) / n ≤ B * (Chebyshev.theta (Real.sqrt ((P.eta 0 : ℝ) * n)) / n) := by
  classical
  dsimp only
  let S := (Finset.Icc 1 (m P (P.q-P.r) * n)).filter Nat.Prime
  let w : ℕ → ℝ := fun p => Real.log (p : ℝ) / n * (phi P ((n : ℝ) / p) : ℝ)
  let B : ℝ := 2 * ((Finset.Icc 1 P.r).card : ℝ) + (Finset.Icc (P.r+1) P.q).card
  have hb (p : ℕ) : (phi P ((n : ℝ) / p) : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast phi_bounded P ((n : ℝ) / p)
  have hw (p : ℕ) : 0 ≤ w p :=
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg n))
      (by exact_mod_cast (zudilin_phi_nonneg_periodic P).1 ((n : ℝ) / p))
  have he := Finset.sum_filter_add_sum_filter_not S (fun p => P.eta 0 * n < p * p) w
  rw [log_Phi_eq_sum]
  change 0 ≤ (∑ p ∈ S, w p) - (∑ p ∈ S with P.eta 0 * n < p * p, w p) ∧
    (∑ p ∈ S, w p) - (∑ p ∈ S with P.eta 0 * n < p * p, w p) ≤ _
  have hd : (∑ p ∈ S, w p) - (∑ p ∈ S with P.eta 0 * n < p * p, w p) =
      ∑ p ∈ S with ¬ P.eta 0 * n < p * p, w p := by linarith
  rw [hd]
  refine ⟨Finset.sum_nonneg (fun p hp => hw p), ?_⟩
  calc
    (∑ p ∈ S with ¬ P.eta 0 * n < p * p, w p) ≤
        ∑ p ∈ S with ¬ P.eta 0 * n < p * p, B * (Real.log (p : ℝ) / n) := by
      apply Finset.sum_le_sum
      intro p hp
      dsimp [w]
      rw [mul_comm B]
      exact mul_le_mul_of_nonneg_left (hb p) (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg n))
    _ = B * ∑ p ∈ S with ¬ P.eta 0 * n < p * p, Real.log (p : ℝ) / n := by rw [Finset.mul_sum]
    _ ≤ B * (Chebyshev.theta (Real.sqrt ((P.eta 0 : ℝ) * n)) / n) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [B]; positivity)
      rw [Chebyshev.theta, Finset.sum_div]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpS, hpCut⟩ := Finset.mem_filter.mp hp
        have hpP := (Finset.mem_filter.mp hpS).2
        have hp0 := hpP.pos
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp0, ?_⟩, hpP⟩
        rw [Nat.le_floor_iff (Real.sqrt_nonneg _)]
        apply (Real.le_sqrt (Nat.cast_nonneg _) (by positivity)).mpr
        have hc : p*p ≤ P.eta 0 * n := Nat.le_of_not_gt hpCut
        simpa only [pow_two] using (show (p : ℝ) * p ≤ (P.eta 0 : ℝ) * n by exact_mod_cast hc)
      · intro p hp hp'
        exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg n)

private lemma theta_sqrt_div_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Chebyshev.theta (Real.sqrt (c*n)) / n) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt (c*n) / n) atTop (𝓝 0) := by
    have ht := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul (Real.sqrt c)
    simpa only [Function.comp_def, Real.sqrt_mul hc.le, mul_div_assoc, Real.sqrt_div_self, mul_zero] using ht
  have hθ := theta_div_tendsto_one.comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hc))
  have ht := hθ.mul hs
  rw [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hspos : 0 < Real.sqrt (c * (n : ℝ)) := Real.sqrt_pos.mpr (mul_pos hc (Nat.cast_pos.mpr hn))
  dsimp only [Function.comp_def]
  field_simp

theorem solution (P : Params) :
    Filter.Tendsto (fun n : ℕ => Real.log (Phi P n : ℝ) / (n : ℝ)) Filter.atTop
      (nhds (∫ x in Set.Ioi (1 / (m P (P.q - P.r) : ℝ)), (phi P x : ℝ) / x ^ 2)) := by
  have hm : 0 < m P (P.q-P.r) := by
    have he : 0 < P.eta P.r := P.eta_pos P.r (Finset.mem_Icc.mpr ⟨Nat.zero_le _, by have := P.q_ge; omega⟩)
    exact lt_of_lt_of_le he (le_max_left _ _)
  have hη : 0 < (P.eta 0 : ℝ) := by
    exact_mod_cast P.eta_pos 0 (Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩)
  let B : ℝ := 2 * ((Finset.Icc 1 P.r).card : ℝ) + (Finset.Icc (P.r+1) P.q).card
  have herr : Tendsto (fun n : ℕ =>
      (∑ p ∈ (Finset.Icc 1 (m P (P.q-P.r) * n)).filter Nat.Prime,
        Real.log (p : ℝ) / n * (phi P ((n : ℝ) / p) : ℝ)) - Real.log (Phi P n : ℝ) / n)
      atTop (𝓝 0) := by
    have hu := (theta_sqrt_div_tendsto_zero (P.eta 0) hη).const_mul B
    rw [mul_zero] at hu
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun n => (prime_cutoff_bound P n).1) (fun n => (prime_cutoff_bound P n).2)
  have ht := (phi_prime_sum_tendsto P (m P (P.q-P.r)) hm).sub herr
  simpa only [sub_sub_cancel, sub_zero] using ht
