-- Prove2me | solution 1 for TalagrandConc.LinearSuprema.theorem_8_1_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-13T01:04:36.936981+00:00
-- url     : https://prove2.me/submissions/bb7e38c3-f877-4274-9179-23600ac115c0

-- Complete checked reconstruction of the native Talagrand linear-supremum concentration theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_TalagrandConc_LinearSuprema_Basic
import Mathlib


-- Begin Canonical

-- End Canonical

-- Begin GridBasic

namespace TalagrandConc.LinearSuprema.Proof
open MeasureTheory Filter
open scoped Topology

noncomputable def gridIndex (m : ℕ) (x : unitInterval) : Fin (m + 2) :=
  ⟨⌊((m : ℝ) + 1) * x⌋₊, by
    apply (Nat.floor_lt (mul_nonneg (by positivity) x.property.1)).mpr
    have hx := x.property.2
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith⟩

noncomputable def gridValue (m : ℕ) (j : Fin (m + 2)) : unitInterval :=
  ⟨(j : ℝ) / ((m : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      have hj : j.val ≤ m + 1 := Nat.le_of_lt_succ j.isLt
      exact_mod_cast hj⟩

noncomputable def grid (m : ℕ) (x : unitInterval) : unitInterval :=
  gridValue m (gridIndex m x)

lemma grid_le (m : ℕ) (x : unitInterval) : (grid m x : ℝ) ≤ x := by
  change (⌊((m : ℝ) + 1) * x⌋₊ : ℝ) / ((m : ℝ) + 1) ≤ x
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using Nat.floor_le (mul_nonneg (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity) x.property.1)

lemma grid_error (m : ℕ) (x : unitInterval) :
    (x : ℝ) - (grid m x : ℝ) ≤ 1 / ((m : ℝ) + 1) := by
  have h := Nat.lt_floor_add_one (((m : ℝ) + 1) * (x : ℝ))
  change (x : ℝ) - (⌊((m : ℝ) + 1) * x⌋₊ : ℝ) / ((m : ℝ) + 1) ≤ _
  apply (le_div_iff₀ (by positivity)).mpr
  have hd : (⌊((m : ℝ) + 1) * x⌋₊ : ℝ) / ((m : ℝ) + 1) * ((m : ℝ) + 1) =
      ⌊((m : ℝ) + 1) * x⌋₊ := div_mul_cancel₀ _ (by positivity)
  nlinarith

lemma measurable_gridIndex (m : ℕ) : Measurable (gridIndex m) := by
  apply measurable_to_countable'
  intro j
  have h := ((measurable_const.mul measurable_subtype_coe).nat_floor :
    Measurable (fun x : unitInterval => ⌊((m : ℝ) + 1) * (x : ℝ)⌋₊))
  simpa only [Set.preimage, Set.mem_singleton_iff, Pi.mul_apply, gridIndex, Fin.ext_iff] using
    h (measurableSet_singleton j.val)

lemma measurable_grid (m : ℕ) : Measurable (grid m) := by
  exact (measurable_of_finite (gridValue m)).comp (measurable_gridIndex m)

lemma grid_tendsto (x : unitInterval) : Tendsto (fun m => grid m x) atTop (𝓝 x) := by
  apply tendsto_subtype_rng.mpr
  have hz : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have he : Tendsto (fun m => (x : ℝ) - grid m x) atTop (𝓝 0) :=
    squeeze_zero (fun m => sub_nonneg.mpr (grid_le m x)) (fun m => grid_error m x) hz
  simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := (x : ℝ))).sub he

end TalagrandConc.LinearSuprema.Proof
-- End GridBasic

-- Begin ShiftedGrid

namespace TalagrandConc.LinearSuprema.Proof
open MeasureTheory Set Filter
open scoped Topology

noncomputable def clipUnit (r x : ℝ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (x-r)

lemma measurable_clipUnit (r : ℝ) : Measurable (clipUnit r) := by
  exact (continuous_projIcc.comp (continuous_id.sub continuous_const)).measurable

lemma clipUnit_coe {r x : ℝ} (hx : x ∈ Icc r (r+1)) : (clipUnit r x : ℝ)=x-r := by
  have h : x-r ∈ Icc (0:ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  simp only [clipUnit, Set.projIcc_of_mem zero_le_one h]

noncomputable def realGridIndex (r : ℝ) (m : ℕ) (x : ℝ) : Fin (m+2) :=
  gridIndex m (clipUnit r x)

noncomputable def realGridValue (r : ℝ) (m : ℕ) (j : Fin (m+2)) : ℝ :=
  r + gridValue m j

noncomputable def realGrid (r : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  realGridValue r m (realGridIndex r m x)

lemma measurable_realGridIndex (r : ℝ) (m : ℕ) : Measurable (realGridIndex r m) :=
  (measurable_gridIndex m).comp (measurable_clipUnit r)

lemma realGridValue_mem (r : ℝ) (m : ℕ) (j : Fin (m+2)) :
    realGridValue r m j ∈ Icc r (r+1) := by
  have h := (gridValue m j).property
  constructor <;> dsimp [realGridValue] <;> linarith [h.1,h.2]

lemma realGrid_error (r : ℝ) (m : ℕ) {x : ℝ} (hx : x ∈ Icc r (r+1)) :
    |realGrid r m x-x| ≤ 1/((m:ℝ)+1) := by
  have hl := grid_le m (clipUnit r x)
  have he := grid_error m (clipUnit r x)
  rw [clipUnit_coe hx] at hl he
  change |r+(grid m (clipUnit r x):ℝ)-x| ≤ _
  rw [abs_of_nonpos (by linarith : r+(grid m (clipUnit r x):ℝ)-x ≤ 0)]
  linarith

noncomputable def realGridLaw (μ : Measure ℝ) (r : ℝ) (m : ℕ) : Measure (Fin (m+2)) :=
  μ.map (realGridIndex r m)

instance realGridLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ) (m : ℕ) :
    IsProbabilityMeasure (realGridLaw μ r m) :=
  Measure.isProbabilityMeasure_map (measurable_realGridIndex r m).aemeasurable

lemma realGridLaw_product {N : ℕ} (μ : Fin N → Measure ℝ)
    [∀i, IsProbabilityMeasure (μ i)] (r : Fin N → ℝ) (m : ℕ) :
    (Measure.pi μ).map (fun x i => realGridIndex (r i) m (x i)) =
      Measure.pi (fun i => realGridLaw (μ i) (r i) m) :=
  Measure.pi_map_pi (fun i => (measurable_realGridIndex (r i) m).aemeasurable)

lemma coordinate_box_ae {N : ℕ} (μ : Fin N → Measure ℝ)
    [∀i, IsProbabilityMeasure (μ i)] (r : Fin N → ℝ)
    (hμ : ∀ i, μ i (Icc (r i) (r i+1))=1) :
    ∀ᵐ x ∂Measure.pi μ, ∀ i, x i ∈ Icc (r i) (r i+1) := by
  apply ae_all_iff.mpr
  intro i
  have hi : ∀ᵐ y ∂μ i, y ∈ Icc (r i) (r i+1) := by
    rw [ae_iff]
    change μ i (Icc (r i) (r i+1))ᶜ = 0
    rw [measure_compl measurableSet_Icc (measure_ne_top _ _), hμ i]
    simp
  exact (measurePreserving_eval μ i).quasiMeasurePreserving.ae hi

end TalagrandConc.LinearSuprema.Proof
-- End ShiftedGrid

-- Begin SupremumBasic

open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof

lemma coeffNorm_nonneg {N : ℕ} (a : Fin N → ℝ) : 0 ≤ coeffNorm a := Real.sqrt_nonneg _
lemma coeffNorm_sq {N : ℕ} (a : Fin N → ℝ) : coeffNorm a ^ 2 = ∑ i,a i^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma abs_coeff_le {N : ℕ} (a : Fin N → ℝ) (i : Fin N) : |a i| ≤ coeffNorm a := by
  have hi : a i^2 ≤ ∑ j,a j^2 := Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
  have hs := coeffNorm_sq a
  have hn := coeffNorm_nonneg a
  nlinarith [sq_abs (a i),abs_nonneg (a i)]

lemma coeffNorm_le_sigma {N : ℕ} {F : Set (Fin N → ℝ)}
    (hb : BddAbove (coeffNorm '' F)) {a : Fin N → ℝ} (ha : a∈F) : coeffNorm a ≤ sigma F :=
  le_csSup hb ⟨a,ha,rfl⟩

lemma sigma_nonneg {N : ℕ} {F : Set (Fin N → ℝ)}
    (hne : F.Nonempty) (hb : BddAbove (coeffNorm '' F)) : 0 ≤ sigma F := by
  obtain ⟨a,ha⟩ := hne
  exact (coeffNorm_nonneg a).trans (coeffNorm_le_sigma hb ha)

lemma linear_form_abs_le {N : ℕ} {F : Set (Fin N → ℝ)}
    (hb : BddAbove (coeffNorm '' F)) {a : Fin N → ℝ} (ha : a∈F) (x : Fin N → ℝ) :
    |∑ i,a i*x i| ≤ sigma F * ∑ i,|x i| := by
  calc
    _ ≤ ∑ i,|a i*x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,sigma F*|x i| := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right ((abs_coeff_le a i).trans (coeffNorm_le_sigma hb ha)) (abs_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma linear_image_bddAbove {N : ℕ} {F : Set (Fin N → ℝ)}
    (hb : BddAbove (coeffNorm '' F)) (x : Fin N → ℝ) :
    BddAbove ((fun a => ∑ i,a i*x i) '' F) := by
  refine ⟨sigma F * ∑ i,|x i|,?_⟩
  rintro _ ⟨a,ha,rfl⟩
  exact (le_abs_self _).trans (linear_form_abs_le hb ha x)

lemma linear_form_le_supremum {N : ℕ} {F : Set (Fin N → ℝ)}
    (hb : BddAbove (coeffNorm '' F)) {a : Fin N → ℝ} (ha : a∈F) (x : Fin N → ℝ) :
    (∑ i,a i*x i) ≤ linearSupremum F x :=
  le_csSup (linear_image_bddAbove hb x) ⟨a,ha,rfl⟩

lemma linearSupremum_le {N : ℕ} {F : Set (Fin N → ℝ)} (hne : F.Nonempty)
    {x : Fin N → ℝ} {b : ℝ} (h : ∀ a∈F,(∑ i,a i*x i)≤b) : linearSupremum F x ≤ b := by
  apply csSup_le (hne.image _)
  rintro _ ⟨a,ha,rfl⟩
  exact h a ha

lemma linearSupremum_sub_le {N : ℕ} {F : Set (Fin N → ℝ)}
    (hne : F.Nonempty) (hb : BddAbove (coeffNorm '' F)) (x y : Fin N → ℝ) :
    linearSupremum F x-linearSupremum F y ≤ sigma F*∑ i,|x i-y i| := by
  suffices h : linearSupremum F x ≤ linearSupremum F y+sigma F*∑ i,|x i-y i| by linarith
  apply linearSupremum_le hne
  intro a ha
  have h1 := linear_form_le_supremum hb ha y
  have h2 := (le_abs_self _).trans (linear_form_abs_le hb ha (fun i => x i-y i))
  simp only [mul_sub,Finset.sum_sub_distrib] at h2
  linarith

lemma linearSupremum_l1 {N : ℕ} {F : Set (Fin N → ℝ)}
    (hne : F.Nonempty) (hb : BddAbove (coeffNorm '' F)) (x y : Fin N → ℝ) :
    |linearSupremum F x-linearSupremum F y| ≤ sigma F*∑ i,|x i-y i| := by
  apply abs_le.mpr
  constructor
  · have h := linearSupremum_sub_le hne hb y x
    simp only [abs_sub_comm (y _)] at h
    linarith
  · exact linearSupremum_sub_le hne hb x y

end TalagrandConc.LinearSuprema.Proof
-- End SupremumBasic

-- Begin GridApproximation

namespace TalagrandConc.LinearSuprema.Proof
open MeasureTheory Set Filter
open scoped Topology BigOperators

lemma realGridLaw_event {N : ℕ} (μ : Fin N → Measure ℝ)
    [∀i, IsProbabilityMeasure (μ i)] (r : Fin N → ℝ) (m : ℕ)
    (S : Set (Fin N → Fin (m+2))) :
    (Measure.pi (fun i => realGridLaw (μ i) (r i) m)).real S =
      (Measure.pi μ).real {x | (fun i => realGridIndex (r i) m (x i)) ∈ S} := by
  rw [← realGridLaw_product, measureReal_def, Measure.map_apply]
  · rfl
  · exact measurable_pi_lambda _ fun i =>
      (measurable_realGridIndex (r i) m).comp (measurable_pi_apply i)
  · exact (Set.toFinite S).measurableSet

lemma linear_grid_error {N : ℕ} {F : Set (Fin N → ℝ)} (hF : F.Nonempty)
    (hσfinite : BddAbove (coeffNorm '' F)) (r : Fin N → ℝ) (m : ℕ)
    {x : Fin N → ℝ} (hx : ∀ i, x i ∈ Icc (r i) (r i+1)) :
    |linearSupremum F (fun i => realGrid (r i) m (x i))-linearSupremum F x| ≤
      sigma F * ((N:ℝ) / ((m:ℝ)+1)) := by
  apply (linearSupremum_l1 hF hσfinite _ _).trans
  have hs : (∑ i : Fin N, |realGrid (r i) m (x i)-x i|) ≤
      (N:ℝ)/((m:ℝ)+1) := by
    calc
      _ ≤ ∑ _i : Fin N, 1/((m:ℝ)+1) :=
        Finset.sum_le_sum (fun i _ => realGrid_error (r i) m (hx i))
      _ = _ := by simp [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hs (sigma_nonneg hF hσfinite)

lemma exists_grid_error_le {N : ℕ} {F : Set (Fin N → ℝ)} {η : ℝ} (hη : 0<η) :
    ∃ m : ℕ, sigma F * ((N:ℝ)/((m:ℝ)+1)) ≤ η := by
  have ht : Tendsto (fun m : ℕ => sigma F * ((N:ℝ)/((m:ℝ)+1))) atTop (nhds 0) := by
    have hh : Tendsto (fun m : ℕ => (N:ℝ)/((m:ℝ)+1)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [mul_zero] using hh.const_mul (sigma F)
  obtain ⟨m,hm⟩ := (ht.eventually (gt_mem_nhds hη)).exists
  exact ⟨m,hm.le⟩

end TalagrandConc.LinearSuprema.Proof
-- End GridApproximation

-- Begin FiniteDistance

open Set
open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof

noncomputable def sqNorm {N : ℕ} (s : Fin N → ℝ) : ℝ := ∑ i,s i^2
lemma sqNorm_nonneg {N : ℕ} (s : Fin N → ℝ) : 0 ≤ sqNorm s := Finset.sum_nonneg (fun i _ => sq_nonneg (s i))
lemma continuous_sqNorm (N : ℕ) : Continuous (sqNorm (N := N)) := by unfold sqNorm; fun_prop

lemma masks_finite {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) :
    (TalagrandConc.ConvexHull.U A x).Finite := by
  classical
  let f : (Fin N → Bool) → (Fin N → ℝ) := fun b i => if b i then 1 else 0
  apply (Set.finite_range f).subset
  intro s hs
  refine ⟨fun i => decide (s i=1),?_⟩
  funext i
  rcases hs.1 i with hi | hi <;> simp [f,hi]

lemma masks_nonempty {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    (TalagrandConc.ConvexHull.U A x).Nonempty := by
  obtain ⟨y,hy⟩ := hA
  refine ⟨fun _ => 1,?_,y,hy,?_⟩
  · intro i; exact Or.inr rfl
  · intro i hi; norm_num at hi

lemma hull_compact {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) :
    IsCompact (TalagrandConc.ConvexHull.V A x) := (masks_finite A x).isCompact_convexHull ℝ

lemma hull_nonempty {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    (TalagrandConc.ConvexHull.V A x).Nonempty := (masks_nonempty hA x).mono (subset_convexHull ℝ _)

lemma exists_min_mask {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    ∃ s ∈ TalagrandConc.ConvexHull.V A x, ∀ t ∈ TalagrandConc.ConvexHull.V A x,sqNorm s ≤ sqNorm t :=
  (hull_compact A x).exists_isMinOn (hull_nonempty hA x) (continuous_sqNorm N).continuousOn

noncomputable def minMask {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) : Fin N → ℝ :=
  by
    classical
    exact if hA : A.Nonempty then Classical.choose (exists_min_mask hA x) else 0

noncomputable def distSq {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) : ℝ := sqNorm (minMask A x)

lemma minMask_mem {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    minMask A x ∈ TalagrandConc.ConvexHull.V A x := by
  rw [minMask,dif_pos hA]
  exact (Classical.choose_spec (exists_min_mask hA x)).1

lemma distSq_le {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K)
    {s : Fin N → ℝ} (hs : s ∈ TalagrandConc.ConvexHull.V A x) : distSq A x ≤ sqNorm s := by
  rw [distSq,minMask,dif_pos hA]
  exact (Classical.choose_spec (exists_min_mask hA x)).2 s hs

lemma distSq_nonneg {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) : 0 ≤ distSq A x :=
  sqNorm_nonneg _

lemma sqNorm_cons {N : ℕ} (a : ℝ) (s : Fin N → ℝ) : sqNorm (Fin.cons a s)=a^2+sqNorm s := by
  simp [sqNorm,Fin.sum_univ_succ]

lemma distSq_zero_dim {K : Type*} (A : Set (Fin 0 → K)) (x : Fin 0 → K) : distSq A x=0 := by
  simp [distSq,sqNorm]

end TalagrandConc.LinearSuprema.Proof
-- End FiniteDistance

-- Begin LinearDistance

open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof

lemma linear_mask_bound {K : Type*} {N : ℕ} (r : Fin N → ℝ) (v : Fin N → K → ℝ)
    (hv : ∀ i k,v i k∈Set.Icc (r i) (r i+1)) (a : Fin N → ℝ)
    (x y : Fin N → K) (s : Fin N → ℝ) (hs : ∀ i,s i=0 ∨ s i=1)
    (he : ∀ i,s i=0 → x i=y i) :
    (∑ i,a i*v i (x i))-(∑ i,a i*v i (y i)) ≤ ∑ i,|a i| *s i := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  rcases hs i with hi | hi
  · rw [he i hi,sub_self,hi,mul_zero]
  · rw [hi,mul_one]
    have hd : |v i (x i)-v i (y i)| ≤ 1 := abs_le.mpr ⟨by linarith [(hv i (x i)).1,(hv i (y i)).2],by linarith [(hv i (x i)).2,(hv i (y i)).1]⟩
    calc
      _ = a i*(v i (x i)-v i (y i)) := by ring
      _ ≤ |a i*(v i (x i)-v i (y i))| := le_abs_self _
      _ = |a i| *|v i (x i)-v i (y i)| := abs_mul _ _
      _ ≤ |a i| *1 := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = _ := mul_one _

lemma linear_hull_bound {K : Type*} {N : ℕ} {F : Set (Fin N → ℝ)}
    (hb : BddAbove (coeffNorm '' F)) (r : Fin N → ℝ) (v : Fin N → K → ℝ)
    (hv : ∀ i k,v i k∈Set.Icc (r i) (r i+1))
    {A : Set (Fin N → K)} {b : ℝ} (hA : ∀ y∈A,linearSupremum F (fun i=>v i (y i))≤b)
    (x : Fin N → K) {a : Fin N → ℝ} (ha : a∈F) {s : Fin N → ℝ}
    (hs : s∈TalagrandConc.ConvexHull.V A x) :
    (∑ i,a i*v i (x i))-b ≤ ∑ i,|a i| *s i := by
  let f : (Fin N → ℝ) → ℝ := fun t => ∑ i,|a i| *t i
  have hf : IsLinearMap ℝ f := by
    constructor
    · intro t u; simp [f,mul_add,Finset.sum_add_distrib]
    · intro c t; simp [f,Finset.mul_sum,mul_left_comm]
  have hm : TalagrandConc.ConvexHull.U A x ⊆ {t | (∑ i,a i*v i (x i))-b ≤ f t} := by
    rintro t ⟨ht,y,hy,he⟩
    have h1 := linear_mask_bound r v hv a x y t ht he
    have h2 := (linear_form_le_supremum hb ha (fun i=>v i (y i))).trans (hA y hy)
    change (∑ i,a i*v i (x i))-b ≤ ∑ i,|a i| *t i
    linarith
  exact convexHull_min hm (convex_halfSpace_ge hf _) hs

lemma linear_distance_bound {K : Type*} {N : ℕ} {F : Set (Fin N → ℝ)}
    (hne : F.Nonempty) (hb : BddAbove (coeffNorm '' F))
    (r : Fin N → ℝ) (v : Fin N → K → ℝ)
    (hv : ∀ i k,v i k∈Set.Icc (r i) (r i+1))
    {A : Set (Fin N → K)} {b : ℝ} (hAn : A.Nonempty)
    (hA : ∀ y∈A,linearSupremum F (fun i=>v i (y i))≤b) (x : Fin N → K) :
    linearSupremum F (fun i=>v i (x i)) ≤ b+sigma F*Real.sqrt (distSq A x) := by
  apply linearSupremum_le hne
  intro a ha
  have h1 := linear_hull_bound hb r v hv hA x ha (minMask_mem hAn x)
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i=>|a i|) (minMask A x)
  simp only [sq_abs] at h2
  change (∑ i,|a i| *minMask A x i) ≤ coeffNorm a*Real.sqrt (distSq A x) at h2
  have h3 := mul_le_mul_of_nonneg_right (coeffNorm_le_sigma hb ha) (Real.sqrt_nonneg (distSq A x))
  linarith

end TalagrandConc.LinearSuprema.Proof
-- End LinearDistance

-- Begin DistanceLift

open Set
open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof

noncomputable def liftMask {N : ℕ} (b : ℝ) : (Fin N → ℝ) →ᵃ[ℝ] (Fin (N+1) → ℝ) where
  toFun := fun s => (Fin.cons b s : Fin (N+1) → ℝ)
  linear :=
    { toFun := fun s => (Fin.cons 0 s : Fin (N+1) → ℝ)
      map_add' := by intro x y; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := by intro a x; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  map_vadd' := by
    intro x y
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

def fiber {K : Type*} {N : ℕ} (A : Set (Fin (N+1) → K)) (z : K) : Set (Fin N → K) :=
  {x | Fin.cons z x ∈ A}
def projection {K : Type*} {N : ℕ} (A : Set (Fin (N+1) → K)) : Set (Fin N → K) :=
  {x | ∃ z,Fin.cons z x ∈ A}

lemma fiber_subset_projection {K : Type*} {N : ℕ} (A : Set (Fin (N+1) → K)) (z : K) :
    fiber A z ⊆ projection A := fun _ hx => ⟨z,hx⟩

lemma projection_nonempty {K : Type*} {N : ℕ} {A : Set (Fin (N+1) → K)} (hA : A.Nonempty) :
    (projection A).Nonempty := by
  obtain ⟨x,hx⟩ := hA
  exact ⟨Fin.tail x,x 0,by simpa using hx⟩

lemma lift_fiber_mask {K : Type*} {N : ℕ} (A : Set (Fin (N+1) → K)) (x : Fin N → K) (z : K)
    {s : Fin N → ℝ} (hs : s ∈ TalagrandConc.ConvexHull.U (fiber A z) x) :
    liftMask 0 s ∈ TalagrandConc.ConvexHull.U A (Fin.cons z x) := by
  obtain ⟨hb,y,hy,he⟩ := hs
  refine ⟨?_,Fin.cons z y,hy,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · exact hb j
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _; rfl
    · exact he j

lemma lift_projection_mask {K : Type*} {N : ℕ} (A : Set (Fin (N+1) → K)) (x : Fin N → K) (z : K)
    {s : Fin N → ℝ} (hs : s ∈ TalagrandConc.ConvexHull.U (projection A) x) :
    liftMask 1 s ∈ TalagrandConc.ConvexHull.U A (Fin.cons z x) := by
  obtain ⟨hb,y,⟨v,hy⟩,he⟩ := hs
  refine ⟨?_,Fin.cons v y,hy,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inr rfl
    · exact hb j
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi; norm_num [liftMask] at hi
    · exact he j

lemma lift_hull {K : Type*} {N : ℕ} {A : Set (Fin (N+1) → K)} {B : Set (Fin N → K)}
    {x : Fin N → K} {z : K} {b : ℝ}
    (h : ∀ s ∈ TalagrandConc.ConvexHull.U B x,liftMask b s ∈ TalagrandConc.ConvexHull.U A (Fin.cons z x))
    {s : Fin N → ℝ} (hs : s ∈ TalagrandConc.ConvexHull.V B x) :
    liftMask b s ∈ TalagrandConc.ConvexHull.V A (Fin.cons z x) := by
  have hi : liftMask b '' TalagrandConc.ConvexHull.U B x ⊆ TalagrandConc.ConvexHull.U A (Fin.cons z x) := by
    rintro _ ⟨s,hs,rfl⟩; exact h s hs
  apply convexHull_mono hi
  rw [← AffineMap.image_convexHull]
  exact ⟨s,hs,rfl⟩

lemma distSq_projection {K : Type*} {N : ℕ} {A : Set (Fin (N+1) → K)} (hA : A.Nonempty)
    (x : Fin N → K) (z : K) : distSq A (Fin.cons z x) ≤ 1+distSq (projection A) x := by
  have hm := lift_hull (fun s hs => lift_projection_mask A x z hs) (minMask_mem (projection_nonempty hA) x)
  have hd := distSq_le hA (Fin.cons z x) hm
  simpa only [liftMask,AffineMap.coe_mk,sqNorm_cons,one_pow,distSq] using hd

end TalagrandConc.LinearSuprema.Proof
-- End DistanceLift

-- Begin DistanceInterpolation

open Set
open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof

lemma sqNorm_interpolate {N : ℕ} (s t : Fin N → ℝ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    sqNorm (a • liftMask 0 s+(1-a) • liftMask 1 t) ≤
      (1-a)^2+a*sqNorm s+(1-a)*sqNorm t := by
  simp only [sqNorm,Fin.sum_univ_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    liftMask,AffineMap.coe_mk,Fin.cons_zero,Fin.cons_succ,mul_zero,mul_one,zero_add]
  have hb : (∑ i : Fin N,(a*s i+(1-a)*t i)^2) ≤
      a*(∑ i,s i^2)+(1-a)*(∑ i,t i^2) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ha1)) (sq_nonneg (s i-t i))]
  linarith

lemma distSq_interpolate {K : Type*} {N : ℕ} {A : Set (Fin (N+1) → K)}
    (hA : A.Nonempty) (x : Fin N → K) (z : K) (hF : (fiber A z).Nonempty)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    distSq A (Fin.cons z x) ≤ (1-a)^2+a*distSq (fiber A z) x+(1-a)*distSq (projection A) x := by
  let s := minMask (fiber A z) x
  let t := minMask (projection A) x
  have hs := lift_hull (fun v hv => lift_fiber_mask A x z hv) (minMask_mem hF x)
  have ht := lift_hull (fun v hv => lift_projection_mask A x z hv) (minMask_mem (projection_nonempty hA) x)
  have hm : a • liftMask 0 s+(1-a) • liftMask 1 t ∈ TalagrandConc.ConvexHull.V A (Fin.cons z x) :=
    (convex_convexHull ℝ _) hs ht ha (sub_nonneg.mpr ha1) (by ring)
  exact (distSq_le hA (Fin.cons z x) hm).trans (sqNorm_interpolate s t ha ha1)

end TalagrandConc.LinearSuprema.Proof
-- End DistanceInterpolation

-- Begin FiniteLaw

open Set
open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof

noncomputable def configWeight {K : Type*} {N : ℕ} (p : K → ℝ) (x : Fin N → K) : ℝ := ∏ i,p (x i)
noncomputable def finiteExpect {K : Type*} [Fintype K] {N : ℕ} (p : K → ℝ) (f : (Fin N → K) → ℝ) : ℝ :=
  ∑ x,configWeight p x*f x
noncomputable def finiteMass {K : Type*} [Fintype K] {N : ℕ} (p : K → ℝ) (A : Set (Fin N → K)) : ℝ :=
  finiteExpect p (A.indicator (fun _ => 1))

lemma configWeight_nonneg {K : Type*} {N : ℕ} {p : K → ℝ} (hp : ∀ k,0 ≤ p k) (x : Fin N → K) :
    0 ≤ configWeight p x := Finset.prod_nonneg (fun i _ => hp (x i))

lemma configWeight_sum {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∑ k,p k=1) :
    (∑ x : Fin N → K,configWeight p x)=1 := by
  classical
  simp only [configWeight]
  rw [← Fintype.prod_sum]
  simp [hp]

lemma finiteExpect_one {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∑ k,p k=1) :
    finiteExpect (N := N) p (fun _ => 1)=1 := by
  simp only [finiteExpect,mul_one]
  exact configWeight_sum hp

lemma finiteMass_nonneg {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∀ k,0 ≤ p k)
    (A : Set (Fin N → K)) : 0 ≤ finiteMass p A := by
  classical
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (configWeight_nonneg hp x)
  by_cases hx : x∈A <;> simp [hx]

lemma finiteMass_le_one {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    (hp0 : ∀ k,0 ≤ p k) (hp : ∑ k,p k=1) (A : Set (Fin N → K)) : finiteMass p A ≤ 1 := by
  classical
  rw [← finiteExpect_one (N := N) hp]
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (configWeight_nonneg hp0 x)
  by_cases hx : x∈A <;> simp [hx]

lemma finiteMass_pos_nonempty {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    {A : Set (Fin N → K)} (hA : 0 < finiteMass p A) : A.Nonempty := by
  by_contra hn
  have he : A=∅ := Set.not_nonempty_iff_eq_empty.mp hn
  simp [he,finiteMass,finiteExpect] at hA

lemma configWeight_cons {K : Type*} {N : ℕ} (p : K → ℝ) (z : K) (x : Fin N → K) :
    configWeight p (Fin.cons z x)=p z*configWeight p x := by
  simp [configWeight,Fin.prod_univ_succ]

lemma finiteExpect_nonneg {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∀ k,0 ≤ p k)
    {f : (Fin N → K) → ℝ} (hf : ∀ x,0 ≤ f x) : 0 ≤ finiteExpect p f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (configWeight_nonneg hp x) (hf x))

end TalagrandConc.LinearSuprema.Proof
-- End FiniteLaw

-- Begin FiniteProduct

open Set
open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof

def configEquiv (K : Type*) (N : ℕ) : (K × (Fin N → K)) ≃ (Fin (N+1) → K) where
  toFun := fun y => Fin.cons y.1 y.2
  invFun := fun x => (x 0,Fin.tail x)
  left_inv := by intro y; cases y; simp
  right_inv := by intro x; simp

lemma finiteExpect_succ {K : Type*} [Fintype K] {N : ℕ} (p : K → ℝ)
    (f : (Fin (N+1) → K) → ℝ) :
    finiteExpect p f = ∑ z,p z*finiteExpect p (fun x => f (Fin.cons z x)) := by
  classical
  unfold finiteExpect
  rw [← (configEquiv K N).sum_comp (fun x => configWeight p x*f x),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  simp only [configEquiv,Equiv.coe_fn_mk,configWeight_cons,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma finiteMass_succ {K : Type*} [Fintype K] {N : ℕ} (p : K → ℝ)
    (A : Set (Fin (N+1) → K)) : finiteMass p A=∑ z,p z*finiteMass p (fiber A z) := by
  classical
  rw [finiteMass,finiteExpect_succ]
  apply Finset.sum_congr rfl
  intro z _
  congr 1

lemma finiteMass_mono {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∀ k,0 ≤ p k)
    {A B : Set (Fin N → K)} (hAB : A ⊆ B) : finiteMass p A ≤ finiteMass p B := by
  classical
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (configWeight_nonneg hp x)
  by_cases hx : x∈A
  · simp [hx,hAB hx]
  · by_cases hy : x∈B <;> simp [hx,hy]

lemma finiteMass_le_projection {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    (hp0 : ∀ k,0 ≤ p k) (hp : ∑ k,p k=1) (A : Set (Fin (N+1) → K)) :
    finiteMass p A ≤ finiteMass p (projection A) := by
  rw [finiteMass_succ]
  calc
    _ ≤ ∑ z,p z*finiteMass p (projection A) := Finset.sum_le_sum (fun z _ =>
      mul_le_mul_of_nonneg_left (finiteMass_mono hp0 (fiber_subset_projection A z)) (hp0 z))
    _ = _ := by rw [← Finset.sum_mul,hp,one_mul]

lemma finiteExpect_mono {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∀ k,0 ≤ p k)
    {f g : (Fin N → K) → ℝ} (h : ∀ x,f x ≤ g x) : finiteExpect p f ≤ finiteExpect p g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (configWeight_nonneg hp x))

lemma finiteExpect_const_mul {K : Type*} [Fintype K] {N : ℕ} (p : K → ℝ)
    (f : (Fin N → K) → ℝ) (c : ℝ) : finiteExpect p (fun x => c*f x)=c*finiteExpect p f := by
  unfold finiteExpect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end TalagrandConc.LinearSuprema.Proof
-- End FiniteProduct

-- Begin FiniteHolder

open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof

lemma finite_holder_bound {I : Type*} [Fintype I] (w a b : I → ℝ)
    (hw : ∀ i,0 ≤ w i) (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i)
    {A B l : ℝ} (hA : 0 < A) (hB : 0 < B) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hsa : ∑ i,w i*a i ≤ A) (hsb : ∑ i,w i*b i ≤ B) :
    (∑ i,w i*(a i^l*b i^(1-l))) ≤ A^l*B^(1-l) := by
  let C := A^l*B^(1-l)
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _)
  have he (i : I) : a i^l*b i^(1-l)=C*((a i/A)^l*(b i/B)^(1-l)) := by
    rw [Real.div_rpow (ha i) hA.le,Real.div_rpow (hb i) hB.le]
    dsimp [C]
    field_simp [(Real.rpow_pos_of_pos hA l).ne',(Real.rpow_pos_of_pos hB (1-l)).ne']
  have hm (i : I) : a i^l*b i^(1-l) ≤ C*(l*(a i/A)+(1-l)*(b i/B)) := by
    rw [he]
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.geom_mean_le_arith_mean2_weighted hl (sub_nonneg.mpr hl1)
      (div_nonneg (ha i) hA.le) (div_nonneg (hb i) hB.le) (by ring)
  have hs : (∑ i,w i*(l*(a i/A)+(1-l)*(b i/B))) ≤ 1 := by
    have he' : (∑ i,w i*(l*(a i/A)+(1-l)*(b i/B)))=
        (l/A)*(∑ i,w i*a i)+((1-l)/B)*(∑ i,w i*b i) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he']
    calc
      _ ≤ (l/A)*A+((1-l)/B)*B := add_le_add
        (mul_le_mul_of_nonneg_left hsa (div_nonneg hl hA.le))
        (mul_le_mul_of_nonneg_left hsb (div_nonneg (sub_nonneg.mpr hl1) hB.le))
      _ = 1 := by field_simp; ring
  calc
    _ ≤ ∑ i,w i*(C*(l*(a i/A)+(1-l)*(b i/B))) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hm i) (hw i))
    _ = C*(∑ i,w i*(l*(a i/A)+(1-l)*(b i/B))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ C*1 := mul_le_mul_of_nonneg_left hs hC
    _ = _ := mul_one _

end TalagrandConc.LinearSuprema.Proof
-- End FiniteHolder

-- Begin ScalarInterpolation

open Set
namespace TalagrandConc.LinearSuprema.Proof

lemma derivative_mono_Icc {f g : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, 0 ≤ g x) : MonotoneOn f (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact hg x (interior_subset hx)

lemma derivative_anti_Icc {f g : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, g x ≤ 0) : AntitoneOn f (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact hg x (interior_subset hx)

noncomputable def logDeficit (r : ℝ) : ℝ := Real.log (2-r)+Real.log r+(Real.log r)^2
noncomputable def logSlope (r : ℝ) : ℝ := -r/(2-r)+1+2*Real.log r

lemma logSlope_deriv {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    HasDerivAt logSlope (2/r-2/(2-r)^2) r := by
  have hn : 2-r ≠ 0 := by linarith
  have hd := (((hasDerivAt_id r).neg.div ((hasDerivAt_const r 2).sub (hasDerivAt_id r)) hn).add_const 1).add
    ((Real.hasDerivAt_log hr.ne').const_mul 2)
  convert! hd using 1
  dsimp
  field_simp
  ring

lemma logSlope_nonpos {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : logSlope r ≤ 0 := by
  have hm : MonotoneOn logSlope (Icc r 1) := by
    apply derivative_mono_Icc (fun x hx => logSlope_deriv (hr.trans_le hx.1) hx.2)
    intro x hx
    have hxp := hr.trans_le hx.1
    have hx2 : 1 ≤ 2-x := by linarith [hx.2]
    have hsq : 1 ≤ (2-x)^2 := by nlinarith
    have ha : 2 ≤ 2/x := (le_div_iff₀ hxp).mpr (by linarith [hx.2])
    have hb : 2/(2-x)^2 ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    linarith
  have hh := hm ⟨le_rfl,hr1⟩ ⟨hr1,le_rfl⟩ hr1
  norm_num [logSlope] at hh ⊢
  exact hh

lemma logDeficit_deriv {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    HasDerivAt logDeficit (logSlope r/r) r := by
  have hn : 2-r ≠ 0 := by linarith
  have hd := (((Real.hasDerivAt_log hn).comp r
    ((hasDerivAt_const r 2).sub (hasDerivAt_id r))).add (Real.hasDerivAt_log hr.ne')).add
      ((Real.hasDerivAt_log hr.ne').pow 2)
  convert! hd using 1
  dsimp [logSlope]
  field_simp
  ring

lemma logDeficit_nonneg {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : 0 ≤ logDeficit r := by
  have hm : AntitoneOn logDeficit (Icc r 1) := by
    apply derivative_anti_Icc (fun x hx => logDeficit_deriv (hr.trans_le hx.1) hx.2)
    intro x hx
    exact div_nonpos_of_nonpos_of_nonneg (logSlope_nonpos (hr.trans_le hx.1) hx.2) (hr.trans_le hx.1).le
  have hh := hm ⟨le_rfl,hr1⟩ ⟨hr1,le_rfl⟩ hr1
  norm_num [logDeficit] at hh ⊢
  exact hh

lemma scalar_interpolation {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ a ∈ Icc (0:ℝ) 1, Real.exp ((1-a)^2/4)*r^(-a) ≤ 2-r := by
  by_cases hb : Real.exp (-(1/2:ℝ)) ≤ r
  · refine ⟨1+2*Real.log r,⟨?_,?_⟩,?_⟩
    · have hl := Real.log_le_log (Real.exp_pos _) hb
      rw [Real.log_exp] at hl
      linarith
    · have hl := Real.log_nonpos hr.le hr1
      linarith
    · rw [Real.rpow_def_of_pos hr,← Real.exp_add]
      apply (Real.le_log_iff_exp_le (by linarith : 0 < 2-r)).mp
      have hf := logDeficit_nonneg hr hr1
      dsimp [logDeficit] at hf
      nlinarith
  · refine ⟨0,⟨le_rfl,zero_le_one⟩,?_⟩
    simp only [sub_zero,one_pow,neg_zero,Real.rpow_zero,mul_one]
    have he : Real.exp (-(1/2:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hf := logDeficit_nonneg (Real.exp_pos (-(1/2:ℝ))) he
    dsimp [logDeficit] at hf
    rw [Real.log_exp] at hf
    have hh : Real.exp (1/4:ℝ) ≤ 2-Real.exp (-(1/2:ℝ)) := by
      apply (Real.le_log_iff_exp_le (by linarith : 0 < 2-Real.exp (-(1/2:ℝ)))).mp
      nlinarith
    exact hh.trans (by linarith [lt_of_not_ge hb])

end TalagrandConc.LinearSuprema.Proof
-- End ScalarInterpolation

-- Begin DistanceConditional

open Set
open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof

lemma holder_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (l : ℝ) :
    (1/a)^l*(1/b)^(1-l)=(1/b)*(a/b)^(-l) := by
  rw [Real.div_rpow (by norm_num) ha.le,Real.div_rpow (by norm_num) hb.le,
    Real.one_rpow,Real.one_rpow,Real.rpow_neg (div_nonneg ha.le hb.le),
    Real.div_rpow ha.le hb.le,Real.rpow_sub hb,Real.rpow_one]
  field_simp [(Real.rpow_pos_of_pos ha l).ne',(Real.rpow_pos_of_pos hb l).ne']

lemma distance_exp_interpolate {K : Type*} {N : ℕ} {A : Set (Fin (N+1) → K)}
    (hA : A.Nonempty) (x : Fin N → K) (z : K) (hF : (fiber A z).Nonempty)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp (distSq A (Fin.cons z x)/4) ≤ Real.exp ((1-a)^2/4)*
      (Real.exp (distSq (fiber A z) x/4)^a*Real.exp (distSq (projection A) x/4)^(1-a)) := by
  have hd := distSq_interpolate hA x z hF ha ha1
  calc
    _ ≤ Real.exp (((1-a)^2+a*distSq (fiber A z) x+(1-a)*distSq (projection A) x)/4) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [← Real.exp_mul,← Real.exp_mul,← Real.exp_add,← Real.exp_add]
      congr 1
      ring

lemma conditional_positive_bound {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    (hp : ∀ k,0 ≤ p k) {A : Set (Fin (N+1) → K)} (hA : A.Nonempty) (z : K)
    (ha : 0 < finiteMass p (fiber A z)) (hb : 0 < finiteMass p (projection A))
    (hsub : finiteMass p (fiber A z) ≤ finiteMass p (projection A))
    (hf : finiteExpect p (fun x => Real.exp (distSq (fiber A z) x/4)) ≤ 1/finiteMass p (fiber A z))
    (hg : finiteExpect p (fun x => Real.exp (distSq (projection A) x/4)) ≤ 1/finiteMass p (projection A)) :
    finiteExpect p (fun x => Real.exp (distSq A (Fin.cons z x)/4)) ≤
      (2-finiteMass p (fiber A z)/finiteMass p (projection A))/finiteMass p (projection A) := by
  obtain ⟨a,ha01,hs⟩ := scalar_interpolation (div_pos ha hb) ((div_le_one hb).mpr hsub)
  have hh := finite_holder_bound (configWeight p)
    (fun x => Real.exp (distSq (fiber A z) x/4)) (fun x => Real.exp (distSq (projection A) x/4))
    (configWeight_nonneg hp) (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    (one_div_pos.mpr ha) (one_div_pos.mpr hb) ha01.1 ha01.2 hf hg
  calc
    _ ≤ finiteExpect p (fun x => Real.exp ((1-a)^2/4)*
      (Real.exp (distSq (fiber A z) x/4)^a*Real.exp (distSq (projection A) x/4)^(1-a))) :=
        finiteExpect_mono hp (fun x => distance_exp_interpolate hA x z (finiteMass_pos_nonempty ha) ha01.1 ha01.2)
    _ = Real.exp ((1-a)^2/4)*finiteExpect p (fun x =>
      Real.exp (distSq (fiber A z) x/4)^a*Real.exp (distSq (projection A) x/4)^(1-a)) := finiteExpect_const_mul _ _ _
    _ ≤ Real.exp ((1-a)^2/4)*((1/finiteMass p (fiber A z))^a*(1/finiteMass p (projection A))^(1-a)) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = (Real.exp ((1-a)^2/4)*(finiteMass p (fiber A z)/finiteMass p (projection A))^(-a))/finiteMass p (projection A) := by
      rw [holder_ratio ha hb]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hs hb.le

end TalagrandConc.LinearSuprema.Proof
-- End DistanceConditional

-- Begin DistanceInduction

open Set
open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof

lemma exp_quarter_le_two : Real.exp (1/4:ℝ) ≤ 2 := by
  have he : Real.exp (-(1/2:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hf := logDeficit_nonneg (Real.exp_pos (-(1/2:ℝ))) he
  dsimp [logDeficit] at hf
  rw [Real.log_exp] at hf
  have hh : Real.exp (1/4:ℝ) ≤ 2-Real.exp (-(1/2:ℝ)) := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < 2-Real.exp (-(1/2:ℝ)))).mp
    nlinarith
  exact hh.trans (by linarith [Real.exp_pos (-(1/2:ℝ))])

lemma conditional_zero_bound {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    (hp : ∀ k,0 ≤ p k) {A : Set (Fin (N+1) → K)} (hA : A.Nonempty) (z : K)
    (hb : 0 < finiteMass p (projection A))
    (hg : finiteExpect p (fun x => Real.exp (distSq (projection A) x/4)) ≤ 1/finiteMass p (projection A)) :
    finiteExpect p (fun x => Real.exp (distSq A (Fin.cons z x)/4)) ≤ 2/finiteMass p (projection A) := by
  have he (x : Fin N → K) : Real.exp (distSq A (Fin.cons z x)/4) ≤
      Real.exp (1/4:ℝ)*Real.exp (distSq (projection A) x/4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hd := distSq_projection hA x z
    linarith
  calc
    _ ≤ finiteExpect p (fun x => Real.exp (1/4:ℝ)*Real.exp (distSq (projection A) x/4)) := finiteExpect_mono hp he
    _ = Real.exp (1/4:ℝ)*finiteExpect p (fun x => Real.exp (distSq (projection A) x/4)) := finiteExpect_const_mul _ _ _
    _ ≤ Real.exp (1/4:ℝ)*(1/finiteMass p (projection A)) := mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
    _ ≤ 2*(1/finiteMass p (projection A)) := mul_le_mul_of_nonneg_right exp_quarter_le_two (one_div_nonneg.mpr hb.le)
    _ = _ := by ring

lemma projection_final_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (2-a/b)/b ≤ 1/a := by
  apply (div_le_div_iff₀ hb ha).mpr
  have he : (2-a/b)*a*b=2*a*b-a^2 := by field_simp
  have hs := sq_nonneg (b-a)
  apply (mul_le_mul_iff_of_pos_right hb).mp
  nlinarith

lemma finite_distance_exponential {K : Type*} [Fintype K] (p : K → ℝ)
    (hp0 : ∀ k,0 ≤ p k) (hp : ∑ k,p k=1) (N : ℕ)
    (A : Set (Fin N → K)) (hA : 0 < finiteMass p A) :
    finiteExpect p (fun x => Real.exp (distSq A x/4)) ≤ 1/finiteMass p A := by
  induction N with
  | zero =>
    simp only [distSq_zero_dim,zero_div,Real.exp_zero,finiteExpect_one hp]
    exact (one_le_div hA).mpr (finiteMass_le_one hp0 hp A)
  | succ N ih =>
    have hB : 0 < finiteMass p (projection A) := hA.trans_le (finiteMass_le_projection hp0 hp A)
    have hnon := finiteMass_pos_nonempty hA
    have hg := ih (projection A) hB
    have hc (z : K) : finiteExpect p (fun x => Real.exp (distSq A (Fin.cons z x)/4)) ≤
        (2-finiteMass p (fiber A z)/finiteMass p (projection A))/finiteMass p (projection A) := by
      by_cases hz : 0 < finiteMass p (fiber A z)
      · exact conditional_positive_bound hp0 hnon z hz hB
          (finiteMass_mono hp0 (fiber_subset_projection A z)) (ih (fiber A z) hz) hg
      · have he : finiteMass p (fiber A z)=0 := le_antisymm (le_of_not_gt hz) (finiteMass_nonneg hp0 _)
        simpa only [he,zero_div,sub_zero] using conditional_zero_bound hp0 hnon z hB hg
    rw [finiteExpect_succ]
    calc
      _ ≤ ∑ z,p z*((2-finiteMass p (fiber A z)/finiteMass p (projection A))/finiteMass p (projection A)) :=
        Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hc z) (hp0 z))
      _ = (2-finiteMass p A/finiteMass p (projection A))/finiteMass p (projection A) := by
        rw [finiteMass_succ]
        simp only [← mul_div_assoc,mul_sub,Finset.sum_sub_distrib,← Finset.sum_div,← Finset.sum_mul,hp]
        ring
      _ ≤ _ := projection_final_bound hA hB

end TalagrandConc.LinearSuprema.Proof
-- End DistanceInduction

-- Begin DistanceTail

open Set
open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof

lemma finite_exp_markov {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    (hp : ∀ k,0 ≤ p k) (f : (Fin N → K) → ℝ) (b : ℝ) :
    finiteMass p {x | b ≤ f x} ≤ Real.exp (-b)*finiteExpect p (fun x => Real.exp (f x)) := by
  unfold finiteMass
  rw [← finiteExpect_const_mul]
  apply finiteExpect_mono hp
  intro x
  by_cases hx : b ≤ f x
  · rw [Set.indicator_of_mem (show x ∈ {x | b ≤ f x} from hx)]
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by linarith)
  · rw [Set.indicator_of_notMem (show x ∉ {x | b ≤ f x} from hx)]
    positivity

lemma finite_distance_product {K : Type*} [Fintype K] (p : K → ℝ)
    (hp0 : ∀ k,0 ≤ p k) (hp : ∑ k,p k=1) (N : ℕ)
    (A : Set (Fin N → K)) (t : ℝ) :
    finiteMass p A*finiteMass p {x | t^2 ≤ distSq A x} ≤ Real.exp (-(t^2/4)) := by
  by_cases hA : 0 < finiteMass p A
  · have hm := finite_exp_markov hp0 (fun x => distSq A x/4) (t^2/4)
    have he : {x | t^2/4 ≤ distSq A x/4}={x | t^2 ≤ distSq A x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    rw [he] at hm
    have hd := finite_distance_exponential p hp0 hp N A hA
    calc
      _ ≤ finiteMass p A*(Real.exp (-(t^2/4))*finiteExpect p (fun x => Real.exp (distSq A x/4))) :=
        mul_le_mul_of_nonneg_left hm hA.le
      _ ≤ finiteMass p A*(Real.exp (-(t^2/4))*(1/finiteMass p A)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le) hA.le
      _ = _ := by field_simp
  · have he : finiteMass p A=0 := le_antisymm (le_of_not_gt hA) (finiteMass_nonneg hp0 A)
    rw [he,zero_mul]
    exact (Real.exp_pos _).le

end TalagrandConc.LinearSuprema.Proof
-- End DistanceTail

-- Begin FiniteMeasure

namespace TalagrandConc.LinearSuprema.Proof
open MeasureTheory
open scoped BigOperators

lemma singleton_weights_nonneg {K : Type*} [MeasurableSpace K] (ρ : Measure K) (k : K) :
    0 ≤ ρ.real {k} := ENNReal.toReal_nonneg

lemma singleton_weights_sum {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (ρ : Measure K) [IsProbabilityMeasure ρ] :
    ∑ k, ρ.real {k} = 1 := by
  simp

lemma configWeight_eq_singleton {K : Type*} [MeasurableSpace K] (ρ : Measure K)
    [IsProbabilityMeasure ρ] {N : ℕ} (x : Fin N → K) :
    configWeight (fun k => ρ.real {k}) x = (Measure.pi (fun _ : Fin N => ρ)).real {x} := by
  simp only [configWeight, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]

lemma finiteExpect_eq_integral {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (ρ : Measure K) [IsProbabilityMeasure ρ] {N : ℕ}
    (f : (Fin N → K) → ℝ) :
    finiteExpect (fun k => ρ.real {k}) f = ∫ x, f x ∂Measure.pi (fun _ : Fin N => ρ) := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [finiteExpect, configWeight_eq_singleton, smul_eq_mul]

lemma finiteMass_eq_real {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (ρ : Measure K) [IsProbabilityMeasure ρ] {N : ℕ}
    (A : Set (Fin N → K)) :
    finiteMass (fun k => ρ.real {k}) A = (Measure.pi (fun _ : Fin N => ρ)).real A := by
  rw [finiteMass, finiteExpect_eq_integral, integral_indicator (Set.toFinite A).measurableSet]
  simp

lemma weighted_sum_eq_integral {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (ρ : Measure K) [IsProbabilityMeasure ρ] (f : K → ℝ) :
    (∑ k, ρ.real {k} * f k) = ∫ k, f k ∂ρ := by
  rw [integral_fintype (Integrable.of_finite)]
  rfl

end TalagrandConc.LinearSuprema.Proof
-- End FiniteMeasure

-- Begin FiniteLinearTail

open scoped BigOperators
namespace TalagrandConc.LinearSuprema.Proof
open MeasureTheory

lemma finite_linear_product {K : Type*} [Fintype K] {N : ℕ} {F : Set (Fin N → ℝ)}
    (hne : F.Nonempty) (hb : BddAbove (coeffNorm '' F)) (hs : 0<sigma F)
    (r : Fin N → ℝ) (v : Fin N → K → ℝ)
    (hv : ∀ i k,v i k∈Set.Icc (r i) (r i+1))
    (p : K → ℝ) (hp0 : ∀ k,0≤p k) (hp : ∑ k,p k=1) {a b : ℝ} (hab : a<b) :
    finiteMass p {x | linearSupremum F (fun i=>v i (x i))≤a} *
    finiteMass p {x | b≤linearSupremum F (fun i=>v i (x i))} ≤
      Real.exp (-(b-a)^2/(4*sigma F^2)) := by
  let A : Set (Fin N → K) := {x | linearSupremum F (fun i=>v i (x i))≤a}
  by_cases hA : 0<finiteMass p A
  · have hsub : {x | b≤linearSupremum F (fun i=>v i (x i))} ⊆
        {x | ((b-a)/sigma F)^2≤distSq A x} := by
      intro x hx
      change b≤linearSupremum F (fun i=>v i (x i)) at hx
      have hd := linear_distance_bound hne hb r v hv (finiteMass_pos_nonempty hA) (fun _ hy=>hy) x
      have hle : (b-a)/sigma F ≤ Real.sqrt (distSq A x) := (div_le_iff₀ hs).mpr (by nlinarith)
      have hpos : 0≤(b-a)/sigma F := div_nonneg (sub_nonneg.mpr hab.le) hs.le
      have hsq := Real.sq_sqrt (distSq_nonneg A x)
      change ((b-a)/sigma F)^2≤distSq A x
      nlinarith [Real.sqrt_nonneg (distSq A x)]
    have hmass := finiteMass_mono hp0 hsub
    have htail := finite_distance_product p hp0 hp N A ((b-a)/sigma F)
    have he : -(((b-a)/sigma F)^2/4)=-(b-a)^2/(4*sigma F^2) := by ring
    rw [he] at htail
    exact (mul_le_mul_of_nonneg_left hmass hA.le).trans htail
  · have he : finiteMass p A=0 := le_antisymm (le_of_not_gt hA) (finiteMass_nonneg hp0 A)
    change finiteMass p A*_≤_
    rw [he,zero_mul]
    exact (Real.exp_pos _).le

lemma iid_linear_product {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] {N : ℕ} {F : Set (Fin N → ℝ)}
    (hne : F.Nonempty) (hb : BddAbove (coeffNorm '' F)) (hs : 0<sigma F)
    (r : Fin N → ℝ) (v : Fin N → K → ℝ)
    (hv : ∀ i k,v i k∈Set.Icc (r i) (r i+1))
    (ρ : Measure K) [IsProbabilityMeasure ρ] {a b : ℝ} (hab : a<b) :
    (Measure.pi (fun _ : Fin N=>ρ)).real {x | linearSupremum F (fun i=>v i (x i))≤a} *
    (Measure.pi (fun _ : Fin N=>ρ)).real {x | b≤linearSupremum F (fun i=>v i (x i))} ≤
      Real.exp (-(b-a)^2/(4*sigma F^2)) := by
  simpa only [finiteMass_eq_real] using finite_linear_product hne hb hs r v hv
    (fun k=>ρ.real {k}) (singleton_weights_nonneg ρ) (singleton_weights_sum ρ) hab

end TalagrandConc.LinearSuprema.Proof
-- End FiniteLinearTail

-- Begin DiagonalLaw

namespace TalagrandConc.LinearSuprema.Proof
open MeasureTheory

lemma diagonal_law {K : Type*} [MeasurableSpace K] {N : ℕ}
    (ρ : Fin N → Measure K) [∀ i,IsProbabilityMeasure (ρ i)] :
    (Measure.pi (fun _ : Fin N=>Measure.pi ρ)).map (fun x i=>x i i)=Measure.pi ρ := by
  have hm (i : Fin N) : (Measure.pi ρ).map (fun x=>x i)=ρ i := (measurePreserving_eval ρ i).map_eq
  have h := Measure.pi_map_pi (μ := fun _ : Fin N=>Measure.pi ρ)
    (f := fun i x=>x i) (fun i=>(measurable_pi_apply i).aemeasurable)
  simpa only [hm] using h

lemma nonidentical_linear_product {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] {N : ℕ} {F : Set (Fin N → ℝ)}
    (hne : F.Nonempty) (hb : BddAbove (coeffNorm '' F)) (hs : 0<sigma F)
    (r : Fin N → ℝ) (v : Fin N → K → ℝ)
    (hv : ∀ i k,v i k∈Set.Icc (r i) (r i+1))
    (ρ : Fin N → Measure K) [∀ i,IsProbabilityMeasure (ρ i)] {a b : ℝ} (hab : a<b) :
    (Measure.pi ρ).real {x | linearSupremum F (fun i=>v i (x i))≤a} *
    (Measure.pi ρ).real {x | b≤linearSupremum F (fun i=>v i (x i))} ≤
      Real.exp (-(b-a)^2/(4*sigma F^2)) := by
  have h := iid_linear_product hne hb hs r (fun i (x : Fin N → K)=>v i (x i))
    (fun i x=>hv i (x i)) (Measure.pi ρ) hab
  have hd : Measurable (fun (x : Fin N → Fin N → K) i=>x i i) :=
    measurable_pi_lambda _ (fun i=>(measurable_pi_apply i).comp (measurable_pi_apply i))
  have hmass (A : Set (Fin N → K)) :
      (Measure.pi ρ).real A=(Measure.pi (fun _ : Fin N=>Measure.pi ρ)).real
        ((fun x i=>x i i) ⁻¹' A) := by
    conv_lhs => rw [← diagonal_law ρ]
    rw [measureReal_def,Measure.map_apply hd (Set.toFinite A).measurableSet]
    rfl
  rw [hmass,hmass]
  exact h

end TalagrandConc.LinearSuprema.Proof
-- End DiagonalLaw

-- Begin NativeProduct

namespace TalagrandConc.LinearSuprema.Proof
open MeasureTheory Set Filter
open scoped Topology

lemma real_measure_mono_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {A B : Set Ω} (h : A ≤ᵐ[P] B) : P.real A ≤ P.real B :=
  ENNReal.toReal_mono (measure_ne_top P B) (measure_mono_ae h)

lemma approximate_linear_product {N : ℕ} {F : Set (Fin N → ℝ)} (hF : F.Nonempty)
    (hσfinite : BddAbove (coeffNorm '' F)) (hσ : 0<sigma F)
    (r : Fin N → ℝ) (μ : Fin N → Measure ℝ) [∀i,IsProbabilityMeasure (μ i)]
    (hμ : ∀i,μ i (Icc (r i) (r i+1))=1)
    {a b η : ℝ} (hη : 0<η) (hgap : 2*η<b-a) :
    (Measure.pi μ).real {x | linearSupremum F x≤a} *
      (Measure.pi μ).real {x | b≤linearSupremum F x} ≤
      Real.exp (-((b-a)-2*η)^2/(4*sigma F^2)) := by
  obtain ⟨m,hm⟩ := exists_grid_error_le (N := N) (F := F) hη
  have hfinite := nonidentical_linear_product hF hσfinite hσ r
    (fun i => realGridValue (r i) m) (fun i j => realGridValue_mem (r i) m j)
    (fun i => realGridLaw (μ i) (r i) m) (a := a+η) (b := b-η) (by linarith)
  rw [realGridLaw_event, realGridLaw_event] at hfinite
  have hlow : (Measure.pi μ).real {x | linearSupremum F x≤a} ≤
      (Measure.pi μ).real {x | linearSupremum F (fun i=>realGrid (r i) m (x i))≤a+η} := by
    apply real_measure_mono_ae
    filter_upwards [coordinate_box_ae μ r hμ] with x hx
    intro hxa
    have he := (linear_grid_error hF hσfinite r m hx).trans hm
    have hh := (abs_le.mp he).2
    change linearSupremum F x≤a at hxa
    change linearSupremum F (fun i=>realGrid (r i) m (x i))≤a+η
    linarith
  have hhigh : (Measure.pi μ).real {x | b≤linearSupremum F x} ≤
      (Measure.pi μ).real {x | b-η≤linearSupremum F (fun i=>realGrid (r i) m (x i))} := by
    apply real_measure_mono_ae
    filter_upwards [coordinate_box_ae μ r hμ] with x hx
    intro hxb
    have he := (linear_grid_error hF hσfinite r m hx).trans hm
    have hh := (abs_le.mp he).1
    change b≤linearSupremum F x at hxb
    change b-η≤linearSupremum F (fun i=>realGrid (r i) m (x i))
    linarith
  rw [show b-η-(a+η)=b-a-2*η by ring] at hfinite
  exact (mul_le_mul hlow hhigh (measureReal_nonneg) (measureReal_nonneg)).trans hfinite

lemma native_linear_product {N : ℕ} {F : Set (Fin N → ℝ)} (hF : F.Nonempty)
    (hσfinite : BddAbove (coeffNorm '' F)) (hσ : 0<sigma F)
    (r : Fin N → ℝ) (μ : Fin N → Measure ℝ) [∀i,IsProbabilityMeasure (μ i)]
    (hμ : ∀i,μ i (Icc (r i) (r i+1))=1) {a b : ℝ} (hab : a<b) :
    (Measure.pi μ).real {x | linearSupremum F x≤a} *
      (Measure.pi μ).real {x | b≤linearSupremum F x} ≤
      Real.exp (-(b-a)^2/(4*sigma F^2)) := by
  let η : ℕ → ℝ := fun n => (b-a)/(4*((n:ℝ)+1))
  have hp (n : ℕ) : 0<η n := div_pos (sub_pos.mpr hab) (by positivity)
  have hg (n : ℕ) : 2*η n<b-a := by
    dsimp [η]
    have hn : (0:ℝ)≤n := Nat.cast_nonneg n
    apply (mul_lt_mul_iff_of_pos_right (show 0<4*((n:ℝ)+1) by positivity)).mp
    have he : 2*((b-a)/(4*((n:ℝ)+1)))*(4*((n:ℝ)+1))=2*(b-a) := by field_simp
    rw [he]
    nlinarith
  have ht : Tendsto η atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop ((tendsto_atTop_add_const_right atTop 1
      tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0:ℝ)<4))
  have he : Tendsto (fun n => Real.exp (-((b-a)-2*η n)^2/(4*sigma F^2))) atTop
      (nhds (Real.exp (-(b-a)^2/(4*sigma F^2)))) := by
    have hc : Continuous (fun t : ℝ => Real.exp (-((b-a)-2*t)^2/(4*sigma F^2))) := by
      fun_prop
    simpa only [Function.comp_def,mul_zero,sub_zero] using hc.continuousAt.tendsto.comp ht
  exact ge_of_tendsto he (Filter.Eventually.of_forall fun n =>
    approximate_linear_product hF hσfinite hσ r μ hμ (hp n) (hg n))

end TalagrandConc.LinearSuprema.Proof
-- End NativeProduct

-- Begin MedianBound

namespace TalagrandConc.LinearSuprema.Proof
open MeasureTheory Set

lemma median_two_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (M u C : ℝ)
    (hM : TalagrandConc.BinPacking.IsMedian P Z M)
    (hlo : P.real {x | Z x≤M-u} * P.real {x | M≤Z x} ≤ C)
    (hhi : P.real {x | Z x≤M} * P.real {x | M+u≤Z x} ≤ C) :
    P {x | |Z x-M|≥u} ≤ ENNReal.ofReal (4*C) := by
  have hmlo : (1/2:ℝ) ≤ P.real {x | Z x≤M} := by
    have hh := ENNReal.toReal_mono (measure_ne_top P _) hM.1
    norm_num at hh ⊢
    exact hh
  have hmhi : (1/2:ℝ) ≤ P.real {x | M≤Z x} := by
    have hh := ENNReal.toReal_mono (measure_ne_top P _) hM.2
    norm_num at hh ⊢
    exact hh
  have hl : P.real {x | Z x≤M-u} ≤ 2*C := by
    have hn := measureReal_nonneg (μ := P) (s := {x | Z x≤M-u})
    nlinarith
  have hh : P.real {x | M+u≤Z x} ≤ 2*C := by
    have hn := measureReal_nonneg (μ := P) (s := {x | M+u≤Z x})
    nlinarith
  have he : {x | |Z x-M|≥u} = {x | Z x≤M-u} ∪ {x | M+u≤Z x} := by
    ext x
    simp only [mem_ofPred_eq, mem_union, le_abs]
    constructor
    · intro hx; rcases hx with hx|hx
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · intro hx; rcases hx with hx|hx
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
  have hb : P.real {x | |Z x-M|≥u} ≤ 4*C := by
    rw [he]
    exact (measureReal_union_le _ _).trans (by linarith)
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hb

end TalagrandConc.LinearSuprema.Proof
-- End MedianBound

-- Begin RootAssembly

namespace TalagrandConc.LinearSuprema

theorem theorem_8_1_1 {N : ℕ} (F : Set (Fin N → ℝ))
    (hF : F.Nonempty) (hσfinite : BddAbove (coeffNorm '' F))
    (hσ : 0 < sigma F) (r : Fin N → ℝ)
    (μ : Fin N → MeasureTheory.Measure ℝ)
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, μ i (Set.Icc (r i) (r i + 1)) = 1)
    (hZmeas : Measurable (linearSupremum F))
    (M : ℝ)
    (hM : TalagrandConc.BinPacking.IsMedian (MeasureTheory.Measure.pi μ) (linearSupremum F) M)
    (u : ℝ) (hu : 0 < u) :
    (MeasureTheory.Measure.pi μ) {x | |linearSupremum F x - M| ≥ u} ≤
      ENNReal.ofReal (4 * Real.exp (-(u ^ 2) / (4 * (sigma F) ^ 2))) := by
  have _meas := hZmeas
  have hlo := Proof.native_linear_product hF hσfinite hσ r μ hμ
    (a := M-u) (b := M) (by linarith)
  have hhi := Proof.native_linear_product hF hσfinite hσ r μ hμ
    (a := M) (b := M+u) (by linarith)
  rw [show M-(M-u)=u by ring] at hlo
  rw [show M+u-M=u by ring] at hhi
  exact Proof.median_two_tail (MeasureTheory.Measure.pi μ) (linearSupremum F) M u
    (Real.exp (-(u^2)/(4*sigma F^2))) hM hlo hhi

end TalagrandConc.LinearSuprema
-- End RootAssembly

-- Begin Solution

open TalagrandConc.LinearSuprema

theorem solution {N : ℕ} (F : Set (Fin N → ℝ))
    (hF : F.Nonempty) (hσfinite : BddAbove (coeffNorm '' F))
    (hσ : 0 < sigma F) (r : Fin N → ℝ)
    (μ : Fin N → MeasureTheory.Measure ℝ)
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, μ i (Set.Icc (r i) (r i + 1)) = 1)
    (hZmeas : Measurable (linearSupremum F))
    (M : ℝ)
    (hM : TalagrandConc.BinPacking.IsMedian (MeasureTheory.Measure.pi μ) (linearSupremum F) M)
    (u : ℝ) (hu : 0 < u) :
    (MeasureTheory.Measure.pi μ) {x | |linearSupremum F x - M| ≥ u} ≤
      ENNReal.ofReal (4 * Real.exp (-(u ^ 2) / (4 * (sigma F) ^ 2))) := by
  exact theorem_8_1_1 F hF hσfinite hσ r μ hμ hZmeas M hM u hu

-- End Solution
