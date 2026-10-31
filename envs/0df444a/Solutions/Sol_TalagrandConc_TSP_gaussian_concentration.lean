-- Prove2me | solution 1 for TalagrandConc.TSP.gaussian_concentration
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T16:45:01.355549+00:00
-- url     : https://prove2.me/submissions/9cb22419-2141-4c23-b15b-ca6d4f93ccb6

import Mathlib
import Definitions.Def_TalagrandConc_TSP_Basic

-- BEGIN TCProof.SharedBasics
section Assembled_TCProof_SharedBasics

open scoped BigOperators
open MeasureTheory

namespace TalagrandConc.TSP.TCFresh

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_SharedBasics
-- END TCProof.SharedBasics

-- BEGIN TCProof.CellScalar
section Assembled_TCProof_CellScalar

namespace TalagrandConc.TSP.TCFresh

noncomputable def clampedCell (m : ℕ) (t : ℝ) : ℕ := min (Nat.floor t) (m-1)

theorem clampedCell_lt (m : ℕ) (hm : 0 < m) (t : ℝ) : clampedCell m t < m := by
  unfold clampedCell
  exact (min_le_right _ _).trans_lt (by omega)

theorem clampedCell_bounds (m : ℕ) (hm : 0 < m) (t : ℝ)
    (ht0 : 0 ≤ t) (htm : t ≤ m) :
    (clampedCell m t : ℝ) ≤ t ∧ t ≤ (clampedCell m t : ℝ)+1 := by
  constructor
  · exact (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le ht0)
  · unfold clampedCell
    by_cases h : Nat.floor t ≤ m-1
    · rw [min_eq_left h]
      exact (Nat.lt_floor_add_one t).le
    · rw [min_eq_right (by omega)]
      have he : ((m-1:ℕ):ℝ)+1=(m:ℝ) := by
        exact_mod_cast (show m-1+1=m by omega)
      rwa [he]

theorem dyadicSide_eq_inv (k : ℕ) : (2:ℝ)^(-(k:ℤ))=((2:ℝ)^k)⁻¹ := by
  rw [zpow_neg,zpow_natCast]

theorem dyadicSide_pos (k : ℕ) : 0 < (2:ℝ)^(-(k:ℤ)) := by positivity

theorem dyadicSide_mul (k : ℕ) : (2:ℝ)^k*(2:ℝ)^(-(k:ℤ))=1 := by
  rw [dyadicSide_eq_inv]
  exact mul_inv_cancel₀ (by positivity)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CellScalar
-- END TCProof.CellScalar

-- BEGIN TCProof.DyadicContainment
section Assembled_TCProof_DyadicContainment

namespace TalagrandConc.TSP.TCFresh

theorem squareIndex_val (k : ℕ) (x : Point) (i : Fin 2) :
    (squareIndex k x i).val=clampedCell (2^k) ((2:ℝ)^k*(x i:ℝ)) := by
  unfold squareIndex clampedCell
  rw [Fin.val_ofNat]
  apply Nat.mod_eq_of_lt
  have hp : 0 < 2^k := by positivity
  exact (min_le_right _ _).trans_lt (by omega)

theorem mem_dyadicSquare_index (k : ℕ) (x : Point) :
    x ∈ dyadicSquare k (squareIndex k x) := by
  intro i
  have hp : 0 < (2:ℝ)^k := by positivity
  have hx0 := (x i).property.1
  have hx1 := (x i).property.2
  have hb := clampedCell_bounds (2^k) (by positivity)
    ((2:ℝ)^k*(x i:ℝ)) (mul_nonneg hp.le hx0) (by
      push_cast
      nlinarith)
  rw [← squareIndex_val k x i] at hb
  have hs := dyadicSide_pos k
  have he := dyadicSide_mul k
  constructor
  · have h := mul_le_mul_of_nonneg_right hb.1 hs.le
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hb.2 hs.le
    nlinarith

theorem dyadicSquare_coordinate_close {k : ℕ} {c : Grid k} {x y : Point}
    (hx : x ∈ dyadicSquare k c) (hy : y ∈ dyadicSquare k c) (i : Fin 2) :
    |(x i:ℝ)-(y i:ℝ)| ≤ (2:ℝ)^(-(k:ℤ)) := by
  rcases hx i with ⟨hx0,hx1⟩
  rcases hy i with ⟨hy0,hy1⟩
  rw [abs_le]
  constructor <;> nlinarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_DyadicContainment
-- END TCProof.DyadicContainment

-- BEGIN TCProof.DyadicEndpoints
section Assembled_TCProof_DyadicEndpoints

namespace TalagrandConc.TSP.TCFresh

noncomputable def cellLower (k : ℕ) (j : Fin (2^k)) : unitInterval :=
  ⟨(j.val:ℝ)/(2:ℝ)^k, by
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (2:ℝ)^k)).mpr
      exact_mod_cast j.isLt.le⟩

noncomputable def cellUpper (k : ℕ) (j : Fin (2^k)) : unitInterval :=
  ⟨((j.val:ℝ)+1)/(2:ℝ)^k, by
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (2:ℝ)^k)).mpr
      exact_mod_cast (show j.val+1 ≤ 2^k from j.isLt)⟩

theorem cellUpper_sub_lower (k : ℕ) (j : Fin (2^k)) :
    (cellUpper k j:ℝ)-(cellLower k j:ℝ)=(2:ℝ)^(-(k:ℤ)) := by
  change ((j.val:ℝ)+1)/(2:ℝ)^k-(j.val:ℝ)/(2:ℝ)^k=_
  rw [dyadicSide_eq_inv]
  ring

theorem dyadicSquare_eq_pi (k : ℕ) (c : Grid k) :
    dyadicSquare k c=Set.pi Set.univ (fun i => Set.Icc (cellLower k (c i)) (cellUpper k (c i))) := by
  ext x
  simp only [dyadicSquare,Set.mem_ofPred_eq,Set.mem_pi,Set.mem_univ,true_implies,Set.mem_Icc]
  change (∀ i, (c i).val*(2:ℝ)^(-(k:ℤ)) ≤ (x i:ℝ) ∧
    (x i:ℝ) ≤ ((c i).val+1)*(2:ℝ)^(-(k:ℤ))) ↔
    (∀ i, (c i).val/(2:ℝ)^k ≤ (x i:ℝ) ∧ (x i:ℝ) ≤ ((c i).val+1)/(2:ℝ)^k)
  simp only [dyadicSide_eq_inv,div_eq_mul_inv]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_DyadicEndpoints
-- END TCProof.DyadicEndpoints

-- BEGIN TCProof.CellVolume
section Assembled_TCProof_CellVolume

open MeasureTheory
open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

noncomputable def pointLaw : Measure Point := Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))

instance pointLaw_probability : IsProbabilityMeasure pointLaw := by
  unfold pointLaw
  infer_instance

theorem measurableSet_dyadicSquare (k : ℕ) (c : Grid k) : MeasurableSet (dyadicSquare k c) := by
  rw [dyadicSquare_eq_pi]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem pointLaw_dyadicSquare (k : ℕ) (c : Grid k) :
    pointLaw (dyadicSquare k c)=(ENNReal.ofReal ((2:ℝ)^(-(k:ℤ))))^2 := by
  rw [dyadicSquare_eq_pi]
  change (Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) _=_
  rw [Measure.pi_pi]
  simp only [unitInterval.volume_Icc,cellUpper_sub_lower,Fin.prod_univ_two,pow_two]

instance pointLaw_nullSingleton : NullSingletonClass pointLaw := by
  unfold pointLaw
  infer_instance

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CellVolume
-- END TCProof.CellVolume

-- BEGIN TCProof.CellFiber
section Assembled_TCProof_CellFiber

namespace TalagrandConc.TSP.TCFresh

theorem clampedCell_eq_iff {m j : ℕ} (_hm : 0 < m) (hj : j < m)
    (t : ℝ) (ht0 : 0 ≤ t) (_htm : t ≤ m) :
    clampedCell m t=j ↔ (j:ℝ) ≤ t ∧ (j+1=m ∨ t < (j:ℝ)+1) := by
  unfold clampedCell
  constructor
  · intro h
    have hlow : j ≤ Nat.floor t := by rw [← h]; exact min_le_left _ _
    refine ⟨(Nat.cast_le.mpr hlow).trans (Nat.floor_le ht0),?_⟩
    by_cases he : j+1=m
    · exact Or.inl he
    · right
      have hfloor : Nat.floor t=j := by omega
      rw [← hfloor]
      exact Nat.lt_floor_add_one t
  · rintro ⟨hlo,hhi⟩
    have hfloor : j ≤ Nat.floor t := Nat.le_floor hlo
    rcases hhi with he | hhi
    · have hpred : m-1=j := by omega
      rw [hpred,min_eq_right hfloor]
    · have heq : Nat.floor t=j := (Nat.floor_eq_iff ht0).mpr ⟨hlo,hhi⟩
      rw [heq,min_eq_left (by omega)]

theorem clampedCell_eq_of_open {m j : ℕ} (hj : j < m) (t : ℝ)
    (ht : (j:ℝ) ≤ t) (ht' : t < (j:ℝ)+1) : clampedCell m t=j := by
  unfold clampedCell
  have h0 : 0 ≤ t := (Nat.cast_nonneg j).trans ht
  rw [(Nat.floor_eq_iff h0).mpr ⟨ht,ht'⟩,min_eq_left (by omega)]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CellFiber
-- END TCProof.CellFiber

-- BEGIN TCProof.OpenCell
section Assembled_TCProof_OpenCell

namespace TalagrandConc.TSP.TCFresh

def openCell (k : ℕ) (c : Grid k) : Set Point :=
  Set.pi Set.univ (fun i => Set.Ioo (cellLower k (c i)) (cellUpper k (c i)))

theorem openCell_subset_fiber (k : ℕ) (c : Grid k) :
    openCell k c ⊆ {x | squareIndex k x=c} := by
  intro x hx
  apply funext
  intro i
  apply Fin.ext
  rw [squareIndex_val]
  have hi := hx i (Set.mem_univ i)
  change (c i).val/(2:ℝ)^k < (x i:ℝ) ∧
    (x i:ℝ) < ((c i).val+1)/(2:ℝ)^k at hi
  apply clampedCell_eq_of_open (c i).isLt
  · have h := (div_lt_iff₀ (by positivity : 0 < (2:ℝ)^k)).mp hi.1
    nlinarith
  · have h := (lt_div_iff₀ (by positivity : 0 < (2:ℝ)^k)).mp hi.2
    nlinarith

theorem fiber_subset_dyadicSquare (k : ℕ) (c : Grid k) :
    {x | squareIndex k x=c} ⊆ dyadicSquare k c := by
  intro x hx
  rw [← hx]
  exact mem_dyadicSquare_index k x

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_OpenCell
-- END TCProof.OpenCell

-- BEGIN TCProof.QuantizerMeasurable
section Assembled_TCProof_QuantizerMeasurable

open MeasureTheory

namespace TalagrandConc.TSP.TCFresh

theorem measurable_squareIndex (k : ℕ) : Measurable (squareIndex k) := by
  apply measurable_pi_lambda
  intro i
  have ht : Measurable (fun x : Point => (2:ℝ)^k*(x i:ℝ)) := by fun_prop
  have hf : Measurable (fun x : Point => Nat.floor ((2:ℝ)^k*(x i:ℝ))) :=
    Nat.measurable_floor.comp ht
  have hm : Measurable (fun x : Point => min (Nat.floor ((2:ℝ)^k*(x i:ℝ))) (2^k-1)) :=
    hf.min measurable_const
  exact (measurable_of_countable (Fin.ofNat (2^k))).comp hm

theorem measurableSet_squareIndex_fiber (k : ℕ) (c : Grid k) :
    MeasurableSet {x | squareIndex k x=c} :=
  (measurable_squareIndex k) (measurableSet_singleton c)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_QuantizerMeasurable
-- END TCProof.QuantizerMeasurable

-- BEGIN TCProof.FiberVolume
section Assembled_TCProof_FiberVolume

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.TSP.TCFresh

theorem pointLaw_openCell (k : ℕ) (c : Grid k) :
    pointLaw (openCell k c)=(ENNReal.ofReal ((2:ℝ)^(-(k:ℤ))))^2 := by
  unfold pointLaw openCell
  rw [Measure.pi_pi]
  simp only [unitInterval.volume_Ioo,cellUpper_sub_lower,Fin.prod_univ_two,pow_two]

theorem pointLaw_squareIndex_fiber (k : ℕ) (c : Grid k) :
    pointLaw {x | squareIndex k x=c}=(ENNReal.ofReal ((2:ℝ)^(-(k:ℤ))))^2 := by
  apply le_antisymm
  · exact (measure_mono (fiber_subset_dyadicSquare k c)).trans_eq (pointLaw_dyadicSquare k c)
  · exact (pointLaw_openCell k c).symm.trans_le (measure_mono (openCell_subset_fiber k c))

theorem grid_card (k : ℕ) : Fintype.card (Grid k)=4^k := by
  simp only [Grid,Fintype.card_fun,Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
  norm_num

theorem grid_atom_value (k : ℕ) :
    (ENNReal.ofReal ((2:ℝ)^(-(k:ℤ))))^2=(Fintype.card (Grid k):ℝ≥0∞)⁻¹ := by
  rw [grid_card,dyadicSide_eq_inv]
  rw [ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [← ENNReal.inv_pow]
  congr 1
  rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
  norm_num

theorem pointLaw_grid_atom (k : ℕ) (c : Grid k) :
    pointLaw {x | squareIndex k x=c}=(Fintype.card (Grid k):ℝ≥0∞)⁻¹ := by
  rw [pointLaw_squareIndex_fiber,grid_atom_value]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_FiberVolume
-- END TCProof.FiberVolume

-- BEGIN TCProof.SampleGrid
section Assembled_TCProof_SampleGrid

open MeasureTheory
open scoped ENNReal BigOperators

namespace TalagrandConc.TSP.TCFresh

noncomputable def sampleGrid (N k : ℕ) (x : Fin N → Point) : Fin N → Grid k :=
  fun i => squareIndex k (x i)

theorem measurable_sampleGrid (N k : ℕ) : Measurable (sampleGrid N k) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_squareIndex k).comp (measurable_pi_apply i)

theorem sampleLaw_grid_fiber (N k : ℕ) (c : Fin N → Grid k) :
    sampleLaw N {x | sampleGrid N k x=c}=
      ((Fintype.card (Grid k):ℝ≥0∞)⁻¹)^N := by
  have he : {x | sampleGrid N k x=c}=
      Set.pi Set.univ (fun i => {y | squareIndex k y=c i}) := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_pi,Set.mem_univ,true_implies]
    exact funext_iff
  rw [he]
  change (Measure.pi (fun _ : Fin N => pointLaw)) _=_
  rw [Measure.pi_pi]
  simp only [pointLaw_grid_atom,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem measurableSet_sampleGrid_fiber (N k : ℕ) (c : Fin N → Grid k) :
    MeasurableSet {x | sampleGrid N k x=c} :=
  (measurable_sampleGrid N k) (measurableSet_singleton c)

theorem sampleLaw_grid_set (N k : ℕ) (C : Finset (Fin N → Grid k)) :
    sampleLaw N {x | sampleGrid N k x ∈ C}=
      C.card*((Fintype.card (Grid k):ℝ≥0∞)⁻¹)^N := by
  classical
  have h := sum_measure_preimage_singleton (μ := sampleLaw N) C
    (f := sampleGrid N k) (fun c _ => measurableSet_sampleGrid_fiber N k c)
  change sampleLaw N (sampleGrid N k ⁻¹' (C : Set (Fin N → Grid k)))=_
  rw [← h]
  change (∑ c ∈ C, sampleLaw N {x | sampleGrid N k x=c})=_
  simp only [sampleLaw_grid_fiber,Finset.sum_const,nsmul_eq_mul]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_SampleGrid
-- END TCProof.SampleGrid

-- BEGIN TCProof.FiniteMean
section Assembled_TCProof_FiniteMean

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (w f : Ω → ℝ) : ℝ :=
  ∑ a, w a * f a

lemma finiteMean_nonneg {Ω : Type*} [Fintype Ω] {w f : Ω → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hf : ∀ a, 0 ≤ f a) : 0 ≤ finiteMean w f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (hf a)

lemma finiteMean_mono {Ω : Type*} [Fintype Ω] {w f g : Ω → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hfg : ∀ a, f a ≤ g a) :
    finiteMean w f ≤ finiteMean w g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hfg a) (hw a)

lemma finiteMean_const {Ω : Type*} [Fintype Ω] {w : Ω → ℝ}
    (hw : ∑ a, w a = 1) (c : ℝ) : finiteMean w (fun _ => c) = c := by
  simp only [finiteMean, ← Finset.sum_mul, hw, one_mul]

lemma finiteMean_add {Ω : Type*} [Fintype Ω] (w f g : Ω → ℝ) :
    finiteMean w (fun a => f a + g a) = finiteMean w f + finiteMean w g := by
  simp only [finiteMean, mul_add, Finset.sum_add_distrib]

lemma finiteMean_mul_const {Ω : Type*} [Fintype Ω] (w f : Ω → ℝ) (c : ℝ) :
    finiteMean w (fun a => f a * c) = finiteMean w f * c := by
  simp only [finiteMean, ← mul_assoc, Finset.sum_mul]

lemma finiteMean_pos {Ω : Type*} [Fintype Ω] {w f : Ω → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (hf : ∀ a, 0 < f a) :
    0 < finiteMean w f := by
  have hex : ∃ a, 0 < w a := by
    by_contra h
    have hz : ∀ a, w a = 0 := fun a => le_antisymm (not_lt.mp (fun ha => h ⟨a, ha⟩)) (hw a)
    simp [hz] at hs
  obtain ⟨a, ha⟩ := hex
  exact Finset.sum_pos' (fun b _ => mul_nonneg (hw b) (hf b).le)
    ⟨a, Finset.mem_univ a, mul_pos ha (hf a)⟩

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_FiniteMean
-- END TCProof.FiniteMean

-- BEGIN TCProof.ProductMean
section Assembled_TCProof_ProductMean

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

noncomputable def productWeight {α : Type*} (p : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ :=
  ∏ i, p (x i)

lemma productWeight_nonneg {α : Type*} {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (n : ℕ) (x : Fin n → α) : 0 ≤ productWeight p n x :=
  Finset.prod_nonneg fun i _ => hp (x i)

lemma productWeight_sum {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∑ a, p a = 1) (n : ℕ) : ∑ x, productWeight p n x = 1 := by
  unfold productWeight
  rw [← Fintype.sum_pow p n,hp,one_pow]

lemma productWeight_snoc {α : Type*} (p : α → ℝ) {n : ℕ} (x : Fin n → α) (a : α) :
    productWeight p (n+1) (Fin.snoc x a) = productWeight p n x*p a := by
  simp [productWeight,Fin.prod_univ_castSucc]

noncomputable def productMean {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ)
    (f : (Fin n → α) → ℝ) : ℝ := finiteMean (productWeight p n) f

lemma productMean_succ {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ)
    (f : (Fin (n+1) → α) → ℝ) :
    productMean p (n+1) f = finiteMean p (fun a => productMean p n (fun x => f (Fin.snoc x a))) := by
  unfold productMean finiteMean
  rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => α)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change productWeight p (n+1) (Fin.snoc x a)*f (Fin.snoc x a) = _
  rw [productWeight_snoc]
  ring

lemma productMean_zero {α : Type*} [Fintype α] (p : α → ℝ) (f : (Fin 0 → α) → ℝ) :
    productMean p 0 f = f Fin.elim0 := by
  simp [productMean,finiteMean,productWeight]
  congr 1

noncomputable def productMass {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ)
    (A : Set (Fin n → α)) : ℝ := by
  classical
  exact productMean p n (fun x => if x ∈ A then 1 else 0)

lemma productMass_nonneg {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (n : ℕ) (A : Set (Fin n → α)) : 0 ≤ productMass p n A := by
  classical
  exact finiteMean_nonneg (productWeight_nonneg hp n) (by intro x; split_ifs <;> norm_num)

lemma productMass_mono {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) {n : ℕ} {A B : Set (Fin n → α)} (hAB : A ⊆ B) :
    productMass p n A ≤ productMass p n B := by
  classical
  apply finiteMean_mono (productWeight_nonneg hp n)
  intro x
  by_cases hx : x ∈ A
  · simp [hx,hAB hx]
  · simp only [hx,ite_false]
    split_ifs <;> norm_num

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_ProductMean
-- END TCProof.ProductMean

-- BEGIN TCProof.GridLaw
section Assembled_TCProof_GridLaw

open MeasureTheory
open scoped BigOperators ENNReal
namespace TalagrandConc.TSP.TCFresh

theorem uniform_productMass {α : Type*} [Fintype α] (N : ℕ)
    (B : Set (Fin N → α)) :
    productMass (fun _ : α => 1/(Fintype.card α:ℝ)) N B=
      (B.toFinite.toFinset.card:ℝ)*((Fintype.card α:ℝ)⁻¹)^N := by
  classical
  unfold productMass productMean finiteMean productWeight
  simp only [one_div,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  have he : Finset.univ.filter (fun x => x ∈ B) = B.toFinite.toFinset := by
    ext x
    simp
  rw [he]

theorem sampleLaw_grid_productMass (N k : ℕ) (B : Set (Fin N → Grid k)) :
    sampleLaw N (sampleGrid N k ⁻¹' B)=
      ENNReal.ofReal (productMass (fun _ : Grid k => 1/(Fintype.card (Grid k):ℝ)) N B) := by
  classical
  have h := sampleLaw_grid_set N k B.toFinite.toFinset
  simp only [Set.Finite.mem_toFinset] at h
  rw [uniform_productMass]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_natCast]
  exact h

theorem dist_same_squareIndex {k : ℕ} {x y : Point}
    (h : squareIndex k x=squareIndex k y) : dist x y ≤ (2:ℝ)^(-(k:ℤ)) := by
  apply (dist_pi_le_iff (dyadicSide_pos k).le).mpr
  intro i
  have hx := mem_dyadicSquare_index k x
  have hy := mem_dyadicSquare_index k y
  rw [← h] at hy
  simpa only [Subtype.dist_eq,Real.dist_eq] using dyadicSquare_coordinate_close hx hy i

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_GridLaw
-- END TCProof.GridLaw

-- BEGIN TCProof.ProductLaplace
section Assembled_TCProof_ProductLaplace

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

theorem productMean_exp_sum {α : Type*} [Fintype α]
    (p f : α → ℝ) (N : ℕ) :
    productMean p N (fun x => Real.exp (∑ i, f (x i)))=
      (∑ a, p a*Real.exp (f a))^N := by
  unfold productMean finiteMean productWeight
  simp only [Real.exp_sum,← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun a => p a*Real.exp (f a)) N).symm

theorem productMass_le_exp_moment {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (N : ℕ)
    (f : (Fin N → α) → ℝ) (b : ℝ) :
    productMass p N {x | b ≤ f x} ≤
      Real.exp (-b)*productMean p N (fun x => Real.exp (f x)) := by
  classical
  have h := finiteMean_mono (productWeight_nonneg hp N)
    (f := fun x => if b ≤ f x then (1:ℝ) else 0)
    (g := fun x => Real.exp (-b)*Real.exp (f x)) (by
      intro x
      by_cases hx : b ≤ f x
      · simp only [hx,ite_true]
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      · simp only [hx,ite_false]
        positivity)
  change productMass p N {x | b ≤ f x} ≤ _ at h
  have he : finiteMean (productWeight p N) (fun x => Real.exp (-b)*Real.exp (f x))=
      Real.exp (-b)*productMean p N (fun x => Real.exp (f x)) := by
    unfold productMean
    unfold finiteMean
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  exact h.trans_eq he

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_ProductLaplace
-- END TCProof.ProductLaplace

-- BEGIN TCProof.OccupancyLaplace
section Assembled_TCProof_OccupancyLaplace

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

noncomputable def hitSum {α : Type*} [DecidableEq α] (Q : Finset α)
    {N : ℕ} (x : Fin N → α) : ℝ := ∑ i, if x i ∈ Q then 1 else 0

theorem productMean_negative_hits {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∑ a, p a=1) (Q : Finset α) (N : ℕ) :
    productMean p N (fun x => Real.exp (-hitSum Q x))=
      (1+(Real.exp (-1)-1)*(∑ a ∈ Q, p a))^N := by
  have he : (fun x : Fin N → α => Real.exp (-hitSum Q x))=
      (fun x => Real.exp (∑ i, if x i ∈ Q then (-1:ℝ) else 0)) := by
    funext x
    congr 1
    simp only [hitSum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> norm_num
  rw [he]
  change productMean p N (fun x => Real.exp (∑ i, (fun a => if a ∈ Q then (-1:ℝ) else 0) (x i))) = _
  rw [productMean_exp_sum p (fun a => if a ∈ Q then (-1:ℝ) else 0) N]
  congr 1
  have ht (a : α) : p a*Real.exp (if a ∈ Q then (-1:ℝ) else 0)=
      p a+(Real.exp (-1)-1)*(if a ∈ Q then p a else 0) := by
    by_cases ha : a ∈ Q
    · simp only [ha,ite_true]
      ring
    · simp only [ha,ite_false,Real.exp_zero]
      ring
  simp only [ht,Finset.sum_add_distrib,← Finset.mul_sum,hp]
  congr 2
  simp

theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1:ℝ)/2 := by
  have h : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  rw [Real.exp_neg]
  exact (inv_le_comm₀ (Real.exp_pos 1) (by norm_num)).mpr (by simpa using h)

theorem negative_hit_moment_bound {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp : ∑ a, p a=1)
    (Q : Finset α) (N : ℕ) :
    productMean p N (fun x => Real.exp (-hitSum Q x)) ≤
      Real.exp (-(N:ℝ)*(∑ a ∈ Q, p a)/2) := by
  let s := ∑ a ∈ Q, p a
  have hs : 0 ≤ s := Finset.sum_nonneg (fun a ha => hp0 a)
  have hs1 : s ≤ 1 := by
    rw [← hp]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Q)
      (fun a ha hnot => hp0 a)
  have hbase : 0 ≤ 1+(Real.exp (-1)-1)*s := by
    have hh := mul_nonneg (Real.exp_pos (-1)).le hs
    nlinarith
  have hb : 1+(Real.exp (-1)-1)*s ≤ Real.exp (-s/2) := by
    have hh := mul_le_mul_of_nonneg_right exp_neg_one_le_half hs
    linarith [Real.add_one_le_exp (-s/2)]
  rw [productMean_negative_hits p hp]
  calc
    (1+(Real.exp (-1)-1)*s)^N ≤ (Real.exp (-s/2))^N := pow_le_pow_left₀ hbase hb N
    _ = Real.exp (-(N:ℝ)*s/2) := by rw [← Real.exp_nat_mul]; congr 1; ring

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_OccupancyLaplace
-- END TCProof.OccupancyLaplace

-- BEGIN TCProof.LowOccupancy
section Assembled_TCProof_LowOccupancy

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

theorem low_occupancy_bound {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp : ∑ a, p a=1)
    (Q : Finset α) (N : ℕ) :
    productMass p N {x | hitSum Q x ≤ (N:ℝ)*(∑ a ∈ Q, p a)/64} ≤
      Real.exp (-(N:ℝ)*(∑ a ∈ Q, p a)/4) := by
  let s := ∑ a ∈ Q, p a
  have hs : 0 ≤ s := Finset.sum_nonneg (fun a ha => hp0 a)
  have hm := productMass_le_exp_moment p hp0 N (fun x => -hitSum Q x)
    (-(N:ℝ)*s/64)
  have he : {x : Fin N → α | -(N:ℝ)*s/64 ≤ -hitSum Q x}=
      {x | hitSum Q x ≤ (N:ℝ)*s/64} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [he] at hm
  have hb := negative_hit_moment_bound p hp0 hp Q N
  have hmul := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-(-(N:ℝ)*s/64))).le
  apply hm.trans
  apply hmul.trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hns : 0 ≤ (N:ℝ)*s := mul_nonneg (Nat.cast_nonneg N) hs
  linarith

noncomputable def uniformWeight (α : Type*) [Fintype α] : α → ℝ :=
  fun _ => (Fintype.card α:ℝ)⁻¹

theorem uniformWeight_nonneg (α : Type*) [Fintype α] : ∀ a, 0 ≤ uniformWeight α a := by
  intro a
  unfold uniformWeight
  positivity

theorem uniformWeight_sum (α : Type*) [Fintype α] [Nonempty α] :
    ∑ a, uniformWeight α a=1 := by
  simp only [uniformWeight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

theorem uniformWeight_subset {α : Type*} [Fintype α] (Q : Finset α) :
    ∑ a ∈ Q, uniformWeight α a=(Q.card:ℝ)/(Fintype.card α) := by
  simp only [uniformWeight,Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_LowOccupancy
-- END TCProof.LowOccupancy

-- BEGIN TCProof.ProductUnion
section Assembled_TCProof_ProductUnion

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

theorem productMass_finite_union {α I : Type*} [Fintype α] [DecidableEq I]
    (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (N : ℕ) (S : Finset I)
    (A : I → Set (Fin N → α)) :
    productMass p N {x | ∃ i ∈ S, x ∈ A i} ≤ ∑ i ∈ S, productMass p N (A i) := by
  classical
  unfold productMass productMean finiteMean
  have hp := productWeight_nonneg hp0 N
  calc
    _ ≤ ∑ x, productWeight p N x * (∑ i ∈ S, if x ∈ A i then (1:ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (hp x)
      by_cases h : ∃ i ∈ S, x ∈ A i
      · simp only [Set.mem_ofPred_eq,h,ite_true]
        obtain ⟨i,hi,hxi⟩ := h
        have hh := Finset.single_le_sum (f := fun j => if x ∈ A j then (1:ℝ) else 0)
          (fun j hj => by split_ifs <;> norm_num) hi
        simpa only [hxi,ite_true] using hh
      · simp only [Set.mem_ofPred_eq,h,ite_false]
        exact Finset.sum_nonneg (fun j hj => by split_ifs <;> norm_num)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_ProductUnion
-- END TCProof.ProductUnion

-- BEGIN TCProof.CellOccupancy
section Assembled_TCProof_CellOccupancy

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

def cellCount {α : Type*} [DecidableEq α] {N : ℕ} (x : Fin N → α) (a : α) : ℕ :=
  (Finset.univ.filter (fun i => x i=a)).card

theorem hitSum_eq_sum_cellCount {α : Type*} [DecidableEq α] {N : ℕ}
    (Q : Finset α) (x : Fin N → α) : hitSum Q x=∑ a ∈ Q, (cellCount x a:ℝ) := by
  classical
  simp only [cellCount,Finset.card_eq_sum_ones,Nat.cast_sum,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold hitSum
  apply Finset.sum_congr rfl
  intro i hi
  simp [eq_comm]

noncomputable def lowCells {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (x : Fin N → α) (lam : ℝ) : Finset α :=
  by classical exact Finset.univ.filter (fun a => (cellCount x a:ℝ) ≤ lam/64)

theorem hitSum_low_subset {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (x : Fin N → α) (lam : ℝ) (Q : Finset α)
    (hQ : Q ⊆ lowCells x lam) : hitSum Q x ≤ Q.card*lam/64 := by
  rw [hitSum_eq_sum_cellCount]
  calc
    _ ≤ ∑ a ∈ Q, lam/64 := Finset.sum_le_sum (fun a ha => (Finset.mem_filter.mp (hQ ha)).2)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem fixed_low_cells_bound {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (N : ℕ) (Q : Finset α) :
    productMass (uniformWeight α) N {x | Q ⊆ lowCells x ((N:ℝ)/Fintype.card α)} ≤
      Real.exp (-(N:ℝ)*Q.card/(4*Fintype.card α)) := by
  have hs := low_occupancy_bound (uniformWeight α) (uniformWeight_nonneg α)
    (uniformWeight_sum α) Q N
  rw [uniformWeight_subset] at hs
  have hm := productMass_mono (uniformWeight_nonneg α) (n := N)
    (A := {x | Q ⊆ lowCells x ((N:ℝ)/Fintype.card α)})
    (B := {x | hitSum Q x ≤ (N:ℝ)*((Q.card:ℝ)/Fintype.card α)/64}) (by
      intro x hx
      have h := hitSum_low_subset x ((N:ℝ)/Fintype.card α) Q hx
      dsimp only [Set.mem_ofPred_eq]
      convert h using 1; ring)
  convert hm.trans hs using 1 <;> congr 1; ring

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CellOccupancy
-- END TCProof.CellOccupancy

-- BEGIN TCProof.ManyLowCells
section Assembled_TCProof_ManyLowCells

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

theorem many_low_cells_bound {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (N q : ℕ) :
    productMass (uniformWeight α) N {x | q ≤ (lowCells x ((N:ℝ)/Fintype.card α)).card} ≤
      (Nat.choose (Fintype.card α) q:ℝ)*
        Real.exp (-(N:ℝ)*q/(4*Fintype.card α)) := by
  classical
  let S := Finset.univ.powersetCard q (α := α)
  have he : {x : Fin N → α | q ≤ (lowCells x ((N:ℝ)/Fintype.card α)).card} =
      {x | ∃ Q ∈ S, Q ⊆ lowCells x ((N:ℝ)/Fintype.card α)} := by
    ext x
    constructor
    · intro hx
      obtain ⟨Q,hQ,hcard⟩ := Finset.exists_subset_card_eq hx
      exact ⟨Q,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ Q,hcard⟩,hQ⟩
    · rintro ⟨Q,hQ,hsub⟩
      exact (Finset.mem_powersetCard.mp hQ).2.symm.trans_le (Finset.card_le_card hsub)
  rw [he]
  have hu := productMass_finite_union (uniformWeight α) (uniformWeight_nonneg α) N S
    (fun Q => {x | Q ⊆ lowCells x ((N:ℝ)/Fintype.card α)})
  apply hu.trans
  calc
    _ ≤ ∑ _Q ∈ S, Real.exp (-(N:ℝ)*q/(4*Fintype.card α)) := by
      apply Finset.sum_le_sum
      intro Q hQ
      have h := fixed_low_cells_bound N Q
      simpa only [(Finset.mem_powersetCard.mp hQ).2] using h
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,S,Finset.card_powersetCard,
        Finset.card_univ]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_ManyLowCells
-- END TCProof.ManyLowCells

-- BEGIN TCProof.ChooseExp
section Assembled_TCProof_ChooseExp

namespace TalagrandConc.TSP.TCFresh

theorem choose_le_exp_ratio (M q : ℕ) (hq : 0 < q) :
    (Nat.choose M q:ℝ) ≤ ((M:ℝ)/q)^q*Real.exp q := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hf : (0:ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  have he := Real.pow_div_factorial_le_exp (q:ℝ) hq0.le q
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ ((M:ℝ)/q)^q by positivity)
  have hid : ((M:ℝ)/q)^q*((q:ℝ)^q/q.factorial)=(M:ℝ)^q/q.factorial := by
    rw [div_pow]
    field_simp
  rw [hid] at hm
  exact (Nat.choose_le_pow_div (α := ℝ) q M).trans hm

theorem choose_exp_tail_bound (M q : ℕ) (hq : 0 < q) (lam : ℝ)
    (hthreshold : Real.exp 1*(M:ℝ)*Real.exp (-lam/8) ≤ q) :
    (Nat.choose M q:ℝ)*Real.exp (-lam*q/4) ≤ Real.exp (-lam*q/8) := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hratio : ((M:ℝ)/q)*Real.exp 1 ≤ Real.exp (lam/8) := by
    have h : ((M:ℝ)/q)*Real.exp 1*Real.exp (-lam/8) ≤ 1 := by
      have hh := (div_le_one hq0).mpr hthreshold
      calc
        _ = (Real.exp 1*(M:ℝ)*Real.exp (-lam/8))/(q:ℝ) := by ring
        _ ≤ 1 := hh
    have hh := (le_div_iff₀ (Real.exp_pos (-lam/8))).mpr h
    simpa only [one_div,← Real.exp_neg,neg_div,neg_neg] using hh
  have hp := pow_le_pow_left₀ (show 0 ≤ ((M:ℝ)/q)*Real.exp 1 by positivity) hratio q
  have hc := mul_le_mul_of_nonneg_right (choose_le_exp_ratio M q hq)
    (Real.exp_pos (-lam*q/4)).le
  apply hc.trans
  have hid : ((M:ℝ)/q)^q*Real.exp q=(((M:ℝ)/q)*Real.exp 1)^q := by
    rw [mul_pow,← Real.exp_nat_mul]
    simp
  rw [hid]
  apply (mul_le_mul_of_nonneg_right hp (Real.exp_pos (-lam*q/4)).le).trans_eq
  rw [← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_ChooseExp
-- END TCProof.ChooseExp

-- BEGIN TCProof.OccupancyThreshold
section Assembled_TCProof_OccupancyThreshold

namespace TalagrandConc.TSP.TCFresh

theorem low_cells_threshold_bound {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (N : ℕ) (hN : 0 < N) (u : ℝ) (hu : 0 ≤ u) :
    productMass (uniformWeight α) N
      {x | Real.exp 1*Fintype.card α*Real.exp (-((N:ℝ)/Fintype.card α)/8)+
        8*u/((N:ℝ)/Fintype.card α) < (lowCells x ((N:ℝ)/Fintype.card α)).card} ≤
      Real.exp (-u) := by
  classical
  let M : ℝ := Fintype.card α
  let lam : ℝ := (N:ℝ)/M
  have hM : 0 < M := by dsimp [M]; exact_mod_cast Fintype.card_pos
  have hlam : 0 < lam := div_pos (by exact_mod_cast hN) hM
  let b := Real.exp 1*M*Real.exp (-lam/8)+8*u/lam
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let q := Nat.floor b+1
  have hq : 0 < q := by dsimp [q]; omega
  have hbq : b < (q:ℝ) := by simpa only [q,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one b
  have hth : Real.exp 1*M*Real.exp (-lam/8) ≤ (q:ℝ) := by
    have hh : 0 ≤ 8*u/lam := by positivity
    dsimp [b] at hbq
    linarith
  have huq : u ≤ lam*q/8 := by
    have hpos : 0 ≤ Real.exp 1*M*Real.exp (-lam/8) := by positivity
    have hh : 8*u/lam ≤ (q:ℝ) := by dsimp [b] at hbq; linarith
    have hm := (div_le_iff₀ hlam).mp hh
    nlinarith
  have he : {x : Fin N → α | b < (lowCells x lam).card} =
      {x | q ≤ (lowCells x lam).card} := by
    ext x
    change b < ((lowCells x lam).card:ℝ) ↔ Nat.floor b+1 ≤ (lowCells x lam).card
    exact (Nat.floor_lt hb).symm.trans (by omega)
  change productMass (uniformWeight α) N {x | b < (lowCells x lam).card} ≤ _
  rw [he]
  have hc := many_low_cells_bound (α := α) N q
  have hexp := choose_exp_tail_bound (Fintype.card α) q hq lam hth
  have heq : -(N:ℝ)*q/(4*(Fintype.card α:ℝ)) = -lam*q/4 := by dsimp [lam,M]; ring
  rw [heq] at hc
  exact hc.trans (hexp.trans (Real.exp_le_exp.mpr (by linarith)))

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_OccupancyThreshold
-- END TCProof.OccupancyThreshold

-- BEGIN TCProof.Scales
section Assembled_TCProof_Scales

namespace TalagrandConc.TSP.TCFresh

def terminalLevel (N : ℕ) : ℕ := Nat.log 4 N

noncomputable def expectedCount (N k : ℕ) : ℝ := (N:ℝ)/(4:ℝ)^k

theorem terminalLevel_bounds (N : ℕ) (hN : 0 < N) :
    (4:ℝ)^terminalLevel N ≤ N ∧ (N:ℝ) < 4*(4:ℝ)^terminalLevel N := by
  constructor
  · exact_mod_cast Nat.pow_log_le_self 4 (Nat.ne_of_gt hN)
  · have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) N
    rw [pow_succ] at h
    change (N:ℝ) < 4*(4:ℝ)^(Nat.log 4 N)
    exact_mod_cast (by omega : N < 4*4^(Nat.log 4 N))

theorem expectedCount_terminal (N : ℕ) (hN : 0 < N) :
    1 ≤ expectedCount N (terminalLevel N) ∧ expectedCount N (terminalLevel N) < 4 := by
  have h := terminalLevel_bounds N hN
  have hp : (0:ℝ) < (4:ℝ)^terminalLevel N := by positivity
  exact ⟨(le_div_iff₀ hp).mpr (by simpa using h.1), (div_lt_iff₀ hp).mpr h.2⟩

theorem expectedCount_succ (N k : ℕ) : expectedCount N k=4*expectedCount N (k+1) := by
  unfold expectedCount
  rw [pow_succ]
  field_simp

theorem exists_cutoff (N : ℕ) (hN : 0 < N) (T : ℝ) (hT : 4 ≤ T) :
    ∃ k ≤ terminalLevel N, expectedCount N k ≤ T :=
  ⟨terminalLevel N,le_rfl,(expectedCount_terminal N hN).2.le.trans hT⟩

noncomputable def cutoffLevel (N : ℕ) (hN : 0 < N) (T : ℝ) (hT : 4 ≤ T) : ℕ :=
  Nat.find (exists_cutoff N hN T hT)

theorem cutoffLevel_spec (N : ℕ) (hN : 0 < N) (T : ℝ) (hT : 4 ≤ T) :
    cutoffLevel N hN T hT ≤ terminalLevel N ∧
      expectedCount N (cutoffLevel N hN T hT) ≤ T :=
  Nat.find_spec (exists_cutoff N hN T hT)

theorem cutoffLevel_pos (N : ℕ) (hN : 0 < N) (T : ℝ) (hT : 4 ≤ T)
    (hTN : T < N) : 0 < cutoffLevel N hN T hT := by
  have h := (cutoffLevel_spec N hN T hT).2
  by_contra hh
  have he : cutoffLevel N hN T hT=0 := by omega
  rw [he] at h
  simp only [expectedCount,pow_zero,div_one] at h
  linarith

theorem cutoffLevel_prev (N : ℕ) (hN : 0 < N) (T : ℝ) (hT : 4 ≤ T)
    (hTN : T < N) : T < expectedCount N (cutoffLevel N hN T hT-1) := by
  have hp := cutoffLevel_pos N hN T hT hTN
  have hn := Nat.find_min (exists_cutoff N hN T hT) (show cutoffLevel N hN T hT-1 < cutoffLevel N hN T hT by omega)
  have hk := (cutoffLevel_spec N hN T hT).1
  exact lt_of_not_ge (fun h => hn ⟨by omega,h⟩)

theorem cutoffLevel_lower (N : ℕ) (hN : 0 < N) (T : ℝ) (hT : 4 ≤ T)
    (hTN : T < N) : T/4 < expectedCount N (cutoffLevel N hN T hT) := by
  have hp := cutoffLevel_pos N hN T hT hTN
  have h := cutoffLevel_prev N hN T hT hTN
  rw [expectedCount_succ] at h
  have he : cutoffLevel N hN T hT-1+1=cutoffLevel N hN T hT := by omega
  rw [he] at h
  linarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_Scales
-- END TCProof.Scales

-- BEGIN TCProof.NativeOccupancy
section Assembled_TCProof_NativeOccupancy

open MeasureTheory
namespace TalagrandConc.TSP.TCFresh

lemma native_low_cells_threshold (N : ℕ) (hN : 0 < N) (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    sampleLaw N {x | Real.exp 1*(4:ℝ)^k*Real.exp (-expectedCount N k/8)+
      8*u/expectedCount N k < (lowCells (sampleGrid N k x) (expectedCount N k)).card} ≤
        ENNReal.ofReal (Real.exp (-u)) := by
  classical
  have h := low_cells_threshold_bound (α := Grid k) N hN u hu
  have he : (Fintype.card (Grid k):ℝ)=(4:ℝ)^k := by rw [grid_card]; norm_cast
  rw [he] at h
  change productMass (uniformWeight (Grid k)) N
    {x | Real.exp 1*(4:ℝ)^k*Real.exp (-expectedCount N k/8)+
      8*u/expectedCount N k < (lowCells x (expectedCount N k)).card} ≤ _ at h
  have hh := sampleLaw_grid_productMass N k
    {x | Real.exp 1*(4:ℝ)^k*Real.exp (-expectedCount N k/8)+
      8*u/expectedCount N k < (lowCells x (expectedCount N k)).card}
  change sampleLaw N (sampleGrid N k ⁻¹' {z | Real.exp 1*(4:ℝ)^k*Real.exp (-expectedCount N k/8)+
      8*u/expectedCount N k < (lowCells z (expectedCount N k)).card}) ≤ _
  rw [hh]
  apply ENNReal.ofReal_le_ofReal
  unfold TalagrandConc.TSP.TCFresh.uniformWeight at h
  simpa only [one_div] using h

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_NativeOccupancy
-- END TCProof.NativeOccupancy

-- BEGIN TCProof.ScaleBadEvent
section Assembled_TCProof_ScaleBadEvent

open MeasureTheory
open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

lemma exp_nat_sum_bound (n : ℕ) : (∑ j ∈ Finset.range n, Real.exp (-(j:ℝ))) ≤ 2 := by
  have h (n : ℕ) : (∑ j ∈ Finset.range n, Real.exp (-(j:ℝ))) ≤
      2-2*Real.exp (-(n:ℝ)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have he : Real.exp (-((n+1:ℕ):ℝ))=Real.exp (-(n:ℝ))*Real.exp (-1) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [he]
      have hh := mul_le_mul_of_nonneg_left exp_neg_one_le_half (Real.exp_pos (-(n:ℝ))).le
      linarith
  exact (h n).trans (by linarith [Real.exp_pos (-(n:ℝ))])

lemma exp_shift_sum_bound (u : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, Real.exp (-(u+j))) ≤ 2*Real.exp (-u) := by
  have he : (∑ j ∈ Finset.range n, Real.exp (-(u+j))) =
      Real.exp (-u)*(∑ j ∈ Finset.range n, Real.exp (-(j:ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left (exp_nat_sum_bound n) (Real.exp_pos (-u)).le
  nlinarith

lemma measure_finite_exp_union {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S : ℕ → Set X) (u : ℝ) (n : ℕ)
    (hS : ∀ j < n, μ (S j) ≤ ENNReal.ofReal (Real.exp (-(u+j)))) :
    μ (⋃ j ∈ Finset.range n, S j) ≤ ENNReal.ofReal (2*Real.exp (-u)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, μ (S j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range n, ENNReal.ofReal (Real.exp (-(u+j))) :=
      Finset.sum_le_sum (fun j hj => hS j (Finset.mem_range.mp hj))
    _ = ENNReal.ofReal (∑ j ∈ Finset.range n, Real.exp (-(u+j))) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => (Real.exp_pos _).le)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (exp_shift_sum_bound u n)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_ScaleBadEvent
-- END TCProof.ScaleBadEvent

-- BEGIN TCProof.OccupancyGoodEvent
section Assembled_TCProof_OccupancyGoodEvent

open MeasureTheory
open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

noncomputable def occupancyThresholdEvent (N k : ℕ) (u : ℝ) : Set (Fin N → Point) :=
  {x | Real.exp 1*(4:ℝ)^k*Real.exp (-expectedCount N k/8)+
      8*u/expectedCount N k < (lowCells (sampleGrid N k x) (expectedCount N k)).card}

noncomputable def occupancyBadEvent (N m k₀ : ℕ) (t : ℝ) : Set (Fin N → Point) :=
  ⋃ j ∈ Finset.range (k₀+1-m), occupancyThresholdEvent N (m+j) (t^2+j)

lemma occupancyThresholdEvent_measurable (N k : ℕ) (u : ℝ) :
    MeasurableSet (occupancyThresholdEvent N k u) := by
  change MeasurableSet (sampleGrid N k ⁻¹' {z | Real.exp 1*(4:ℝ)^k*Real.exp (-expectedCount N k/8)+
      8*u/expectedCount N k < (lowCells z (expectedCount N k)).card})
  apply (measurable_sampleGrid N k)
  exact (Set.to_countable _).measurableSet

lemma occupancyBadEvent_measurable (N m k₀ : ℕ) (t : ℝ) :
    MeasurableSet (occupancyBadEvent N m k₀ t) := by
  exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ =>
    occupancyThresholdEvent_measurable N (m+j) (t^2+j)))

lemma occupancyBadEvent_bound (N : ℕ) (hN : 0 < N) (m k₀ : ℕ) (t : ℝ) :
    sampleLaw N (occupancyBadEvent N m k₀ t) ≤ ENNReal.ofReal (2*Real.exp (-(t^2))) := by
  apply measure_finite_exp_union
  intro j _
  exact native_low_cells_threshold N hN (m+j) (t^2+j) (by positivity)

lemma occupancyGoodEvent_counts (N m k₀ : ℕ) (t : ℝ) (x : Fin N → Point)
    (hx : x ∉ occupancyBadEvent N m k₀ t) (k : ℕ) (hm : m ≤ k) (hk : k ≤ k₀) :
    ((lowCells (sampleGrid N k x) (expectedCount N k)).card:ℝ) ≤
      Real.exp 1*(4:ℝ)^k*Real.exp (-expectedCount N k/8)+
        8*(t^2+((k-m:ℕ):ℝ))/expectedCount N k := by
  apply le_of_not_gt
  intro hbad
  apply hx
  apply Set.mem_iUnion.mpr
  refine ⟨k-m,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
  have he : m+(k-m)=k := by omega
  rw [he]
  exact hbad

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_OccupancyGoodEvent
-- END TCProof.OccupancyGoodEvent

-- BEGIN TCProof.EnergySeries
section Assembled_TCProof_EnergySeries

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

theorem weighted_quarter_sum (n : ℕ) (u : ℝ) (hu : 1 ≤ u) :
    ∑ j ∈ Finset.range n, (u+(j:ℝ))*(4:ℝ)⁻¹^j ≤ 2*u := by
  induction n generalizing u with
  | zero => simp; linarith
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have he : (∑ j ∈ Finset.range n, (u+↑(j+1))*(4:ℝ)⁻¹^(j+1))=
        (1/4:ℝ)*(∑ j ∈ Finset.range n, ((u+1)+(j:ℝ))*(4:ℝ)⁻¹^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.cast_add,Nat.cast_one,pow_succ]
      ring
    rw [he]
    have h := ih (u+1) (by linarith)
    norm_num only [Nat.cast_zero,add_zero,pow_zero,mul_one]
    linarith

theorem four_power_sum (n : ℕ) :
    ∑ j ∈ Finset.range (n+1), (4:ℝ)^j ≤ (4/3:ℝ)*(4:ℝ)^n := by
  have h := geom_sum_mul (4:ℝ) (n+1)
  rw [pow_succ] at h
  norm_num at h
  linarith

theorem exponential_quadratic_lower (a : ℝ) (ha : 0 ≤ a) :
    a^2/2 ≤ Real.exp a := by
  have h := Real.sum_le_exp_of_nonneg ha 3
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem decay_expectedCount (a : ℝ) (ha : 0 < a) :
    a*Real.exp (-a/8) ≤ 128/a := by
  have h := exponential_quadratic_lower (a/8) (by positivity)
  have he : Real.exp (-a/8)= (Real.exp (a/8))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [he]
  have hp := Real.exp_pos (a/8)
  apply (le_div_iff₀ ha).mpr
  have hmul := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hp.le)
  rw [mul_inv_cancel₀ hp.ne'] at hmul
  nlinarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_EnergySeries
-- END TCProof.EnergySeries

-- BEGIN TCProof.AlphaBasic
section Assembled_TCProof_AlphaBasic

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

noncomputable def quadraticAlpha {N : ℕ} (S : Finset ℕ) (b : ℝ)
    (w : ℕ → ℝ) (sparse : ℕ → Fin N → Prop) (i : Fin N) : ℝ := by
  classical
  exact Real.sqrt (b + ∑ k ∈ S, @ite ℝ (sparse k i) (Classical.propDecidable _) (w k) 0)

theorem quadraticAlpha_nonneg {N : ℕ} (S : Finset ℕ) (b : ℝ)
    (w : ℕ → ℝ) (sparse : ℕ → Fin N → Prop) (i : Fin N) :
    0 ≤ quadraticAlpha S b w sparse i := Real.sqrt_nonneg _

theorem quadraticAlpha_sq {N : ℕ} (S : Finset ℕ) (b : ℝ) (hb : 0 ≤ b)
    (w : ℕ → ℝ) (hw : ∀ k ∈ S, 0 ≤ w k) (sparse : ℕ → Fin N → Prop)
    (i : Fin N) :
    (quadraticAlpha S b w sparse i)^2=b+∑ k ∈ S, @ite ℝ (sparse k i) (Classical.propDecidable _) (w k) 0 := by
  classical
  apply Real.sq_sqrt
  exact add_nonneg hb (Finset.sum_nonneg (fun k hk => by split_ifs; exact hw k hk; rfl))

theorem quadraticAlpha_baseline {N : ℕ} (S : Finset ℕ) (b : ℝ)
    (w : ℕ → ℝ) (hw : ∀ k ∈ S, 0 ≤ w k) (sparse : ℕ → Fin N → Prop)
    (i : Fin N) : Real.sqrt b ≤ quadraticAlpha S b w sparse i := by
  classical
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k hk => by split_ifs; exact hw k hk; rfl))

theorem quadraticAlpha_sparse {N : ℕ} (S : Finset ℕ) (b : ℝ) (hb : 0 ≤ b)
    (w : ℕ → ℝ) (hw : ∀ k ∈ S, 0 ≤ w k) (sparse : ℕ → Fin N → Prop)
    (i : Fin N) (k : ℕ) (hk : k ∈ S) (hi : sparse k i) :
    Real.sqrt (w k) ≤ quadraticAlpha S b w sparse i := by
  classical
  apply Real.sqrt_le_sqrt
  have h := Finset.single_le_sum (f := fun j => if sparse j i then w j else 0)
    (fun j hj => by split_ifs; exact hw j hj; rfl) hk
  simp only [hi,ite_true] at h
  exact h.trans (le_add_of_nonneg_left hb)

theorem quadraticAlpha_energy {N : ℕ} (S : Finset ℕ) (b : ℝ) (hb : 0 ≤ b)
    (w : ℕ → ℝ) (hw : ∀ k ∈ S, 0 ≤ w k) (sparse : ℕ → Fin N → Prop) :
    (∑ i, (quadraticAlpha S b w sparse i)^2)=
      (N:ℝ)*b+∑ k ∈ S, ∑ i, @ite ℝ (sparse k i) (Classical.propDecidable _) (w k) 0 := by
  classical
  simp only [quadraticAlpha_sq S b hb w hw sparse,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_AlphaBasic
-- END TCProof.AlphaBasic

-- BEGIN TCProof.AlphaGrid
section Assembled_TCProof_AlphaGrid

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

noncomputable def gridArea (k : ℕ) : ℝ := ((4:ℝ)^k)⁻¹

noncomputable def sparseGridCells {N : ℕ} (x : Fin N → Point) (k : ℕ) : Finset (Grid k) :=
  lowCells (sampleGrid N k x) ((N:ℝ)*gridArea k/2)

noncomputable def sampleAlpha {N : ℕ} (x : Fin N → Point) (k₀ k₁ : ℕ) : Fin N → ℝ :=
  quadraticAlpha (Finset.Icc k₁ k₀) (gridArea k₀) gridArea
    (fun k i => squareIndex k (x i) ∈ sparseGridCells x k)

theorem gridArea_pos (k : ℕ) : 0 < gridArea k := by unfold gridArea; positivity

theorem sampleAlpha_nonneg {N : ℕ} (x : Fin N → Point) (k₀ k₁ : ℕ) (i : Fin N) :
    0 ≤ sampleAlpha x k₀ k₁ i := quadraticAlpha_nonneg _ _ _ _ _

theorem sampleAlpha_baseline {N : ℕ} (x : Fin N → Point) (k₀ k₁ : ℕ) (i : Fin N) :
    Real.sqrt (gridArea k₀) ≤ sampleAlpha x k₀ k₁ i :=
  quadraticAlpha_baseline _ _ _ (fun k _ => (gridArea_pos k).le) _ _

theorem sampleAlpha_sparse {N : ℕ} (x : Fin N → Point) (k₀ k₁ k : ℕ)
    (hk : k ∈ Finset.Icc k₁ k₀) (i : Fin N)
    (hi : squareIndex k (x i) ∈ sparseGridCells x k) :
    Real.sqrt (gridArea k) ≤ sampleAlpha x k₀ k₁ i :=
  quadraticAlpha_sparse _ _ (gridArea_pos k₀).le _
    (fun j _ => (gridArea_pos j).le) _ i k hk hi

theorem sampleAlpha_energy {N : ℕ} (x : Fin N → Point) (k₀ k₁ : ℕ) :
    (∑ i, (sampleAlpha x k₀ k₁ i)^2)=(N:ℝ)*gridArea k₀+
      ∑ k ∈ Finset.Icc k₁ k₀, gridArea k*
        ∑ c ∈ sparseGridCells x k, (cellCount (sampleGrid N k x) c:ℝ) := by
  classical
  rw [sampleAlpha,quadraticAlpha_energy _ _ (gridArea_pos k₀).le _
    (fun k _ => (gridArea_pos k).le)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [← hitSum_eq_sum_cellCount]
  unfold hitSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [sampleGrid]
  by_cases hm : squareIndex k (x i) ∈ sparseGridCells x k <;> simp [hm]

theorem sampleAlpha_energy_bound {N : ℕ} (x : Fin N → Point) (k₀ k₁ : ℕ) :
    (∑ i, (sampleAlpha x k₀ k₁ i)^2) ≤ (N:ℝ)*gridArea k₀+
      ∑ k ∈ Finset.Icc k₁ k₀, (N:ℝ)*(gridArea k)^2*(sparseGridCells x k).card/128 := by
  classical
  rw [sampleAlpha_energy]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro k hk
  rw [← hitSum_eq_sum_cellCount]
  have h := hitSum_low_subset (sampleGrid N k x) ((N:ℝ)*gridArea k/2)
    (sparseGridCells x k) (Finset.Subset.refl _)
  have hm := mul_le_mul_of_nonneg_left h (gridArea_pos k).le
  convert hm using 1; ring

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_AlphaGrid
-- END TCProof.AlphaGrid

-- BEGIN TCProof.ScaleEnergy
section Assembled_TCProof_ScaleEnergy

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

theorem gridArea_add (k j : ℕ) : gridArea (k+j)=gridArea k*(4:ℝ)⁻¹^j := by
  simp only [gridArea,pow_add,mul_inv_rev,inv_pow]
  ring

theorem expectedCount_eq_area (N k : ℕ) : expectedCount N k=(N:ℝ)*gridArea k := by
  rfl

theorem weighted_area_sum (k₁ k₀ : ℕ) (u : ℝ) (hu : 1 ≤ u) :
    ∑ k ∈ Finset.Icc k₁ k₀, (u+((k-k₁:ℕ):ℝ))*gridArea k ≤
      2*u*gridArea k₁ := by
  have he : Finset.Icc k₁ k₀=Finset.Ico k₁ (k₀+1) := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left,gridArea_add]
  have h := mul_le_mul_of_nonneg_right (weighted_quarter_sum (k₀+1-k₁) u hu)
    (gridArea_pos k₁).le
  rw [Finset.sum_mul] at h
  calc
    _ = ∑ j ∈ Finset.range (k₀+1-k₁), (u+(j:ℝ))*(4:ℝ)⁻¹^j*gridArea k₁ := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := h

theorem inverse_expected_sum (N : ℕ) (hN : 0 < N) (k₁ : ℕ) :
    ∑ k ∈ Finset.Icc k₁ (terminalLevel N), (expectedCount N k)⁻¹ ≤ (4/3:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have he (k : ℕ) : (expectedCount N k)⁻¹=(4:ℝ)^k/(N:ℝ) := by
    unfold expectedCount
    rw [inv_div]
  simp only [he]
  have hs : (∑ k ∈ Finset.Icc k₁ (terminalLevel N), (4:ℝ)^k) ≤
      ∑ k ∈ Finset.range (terminalLevel N+1), (4:ℝ)^k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have h := (Finset.mem_Icc.mp hk).2
      exact Finset.mem_range.mpr (by omega)
    · intros; positivity
  rw [← Finset.sum_div]
  apply (div_le_iff₀ hn).mpr
  have ht := (terminalLevel_bounds N hN).1
  exact hs.trans ((four_power_sum _).trans (mul_le_mul_of_nonneg_left ht (by norm_num)))

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_ScaleEnergy
-- END TCProof.ScaleEnergy

-- BEGIN TCProof.EnergyBound
section Assembled_TCProof_EnergyBound

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

theorem energy_atom_bound (N k : ℕ) (hN : 0 < N) (m u : ℝ)
    (hm : m ≤ Real.exp 1*(4:ℝ)^k*Real.exp (-expectedCount N k/8)+
      8*u/expectedCount N k) :
    (N:ℝ)*(gridArea k)^2*m/128 ≤ Real.exp 1/(expectedCount N k)+u*gridArea k/16 := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hl : 0 < expectedCount N k := by unfold expectedCount; positivity
  have ha := gridArea_pos k
  calc
    _ ≤ (N:ℝ)*(gridArea k)^2*(Real.exp 1*(4:ℝ)^k*Real.exp (-expectedCount N k/8)+
      8*u/expectedCount N k)/128 := by gcongr
    _ = Real.exp 1/128*(expectedCount N k*Real.exp (-expectedCount N k/8))+
        u*gridArea k/16 := by
      unfold expectedCount gridArea
      field_simp [ne_of_gt hn]
      ring
    _ ≤ Real.exp 1/128*(128/expectedCount N k)+u*gridArea k/16 := by
      apply add_le_add_left
      exact mul_le_mul_of_nonneg_left (decay_expectedCount _ hl) (by positivity)
    _ = _ := by ring

theorem sampleAlpha_energy_of_counts {N : ℕ} (hN : 0 < N) (x : Fin N → Point)
    (k₁ : ℕ) (t : ℝ) (ht : 1 ≤ t) (hscale : t^2*gridArea k₁ ≤ 128)
    (hcounts : ∀ k ∈ Finset.Icc k₁ (terminalLevel N),
      ((sparseGridCells x k).card:ℝ) ≤
        Real.exp 1*(4:ℝ)^k*Real.exp (-expectedCount N k/8)+
          8*(t^2+((k-k₁:ℕ):ℝ)+2)/expectedCount N k) :
    ∑ i, (sampleAlpha x (terminalLevel N) k₁ i)^2 ≤ 1024 := by
  have hbase := (expectedCount_terminal N hN).2.le
  rw [expectedCount_eq_area] at hbase
  have hsum := sampleAlpha_energy_bound x (terminalLevel N) k₁
  have hterm := Finset.sum_le_sum (fun k hk =>
    energy_atom_bound N k hN ((sparseGridCells x k).card:ℝ)
      (t^2+((k-k₁:ℕ):ℝ)+2) (hcounts k hk))
  have hs1 := inverse_expected_sum N hN k₁
  have hs2 := weighted_area_sum k₁ (terminalLevel N) (t^2+2) (by nlinarith [sq_nonneg t])
  have he1 : (∑ k ∈ Finset.Icc k₁ (terminalLevel N), Real.exp 1/expectedCount N k)=
      Real.exp 1*(∑ k ∈ Finset.Icc k₁ (terminalLevel N), (expectedCount N k)⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    rfl
  have he2 : (∑ k ∈ Finset.Icc k₁ (terminalLevel N),
      (t^2+((k-k₁:ℕ):ℝ)+2)*gridArea k/16)=
      (∑ k ∈ Finset.Icc k₁ (terminalLevel N),
        (t^2+2+((k-k₁:ℕ):ℝ))*gridArea k)/16 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [Finset.sum_add_distrib,he1,he2] at hterm
  have hse := mul_le_mul_of_nonneg_left hs1 (Real.exp_pos 1).le
  have he := Real.exp_one_lt_three.le
  have harea := (gridArea_pos k₁).le
  have ht2 : 1 ≤ t^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right (show t^2+2 ≤ 3*t^2 by linarith) harea
  nlinarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_EnergyBound
-- END TCProof.EnergyBound

-- BEGIN TCProof.EnergyRegime
section Assembled_TCProof_EnergyRegime

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

theorem logarithmic_threshold_ge_four (r : ℝ) (hr : (2:ℝ)^20 ≤ r) :
    4 ≤ 128*Real.log r := by
  have hr0 : 0 < r := by norm_num at hr; linarith
  have he : Real.exp 1 ≤ r := by
    have h := Real.exp_one_lt_three
    norm_num at hr
    linarith
  have hl : 1 ≤ Real.log r := (Real.le_log_iff_exp_le hr0).mpr he
  linarith

theorem cutoff_energy_scale (N : ℕ) (hN : 0 < N) (t : ℝ)
    (r : ℝ) (hr : 0 < r) (hrel : r*t^2=(N:ℝ))
    (hT : 4 ≤ 128*Real.log r) :
    t^2*gridArea (cutoffLevel N hN (128*Real.log r) hT) ≤ 128 := by
  let k := cutoffLevel N hN (128*Real.log r) hT
  have h := (cutoffLevel_spec N hN (128*Real.log r) hT).2
  rw [expectedCount_eq_area] at h
  have hl := Real.log_le_sub_one_of_pos hr
  have ha := congrArg (fun z : ℝ => z*gridArea k) hrel
  apply (mul_le_mul_iff_right₀ hr).mp
  dsimp [k] at ha ⊢
  nlinarith

theorem sampleAlpha_energy_cutoff {N : ℕ} (hN : 0 < N) (x : Fin N → Point)
    (t r : ℝ) (ht : 1 ≤ t) (hr : (2:ℝ)^20 ≤ r) (hrel : r*t^2=(N:ℝ))
    (hcounts : ∀ k ∈ Finset.Icc
        (cutoffLevel N hN (128*Real.log r) (logarithmic_threshold_ge_four r hr))
        (terminalLevel N),
      ((sparseGridCells x k).card:ℝ) ≤
        Real.exp 1*(4:ℝ)^k*Real.exp (-expectedCount N k/8)+
          8*(t^2+((k-cutoffLevel N hN (128*Real.log r)
            (logarithmic_threshold_ge_four r hr):ℕ):ℝ)+2)/expectedCount N k) :
    ∑ i, (sampleAlpha x (terminalLevel N)
      (cutoffLevel N hN (128*Real.log r) (logarithmic_threshold_ge_four r hr)) i)^2 ≤ 1024 := by
  apply sampleAlpha_energy_of_counts hN x _ t ht _ hcounts
  exact cutoff_energy_scale N hN t r (by norm_num at hr; linarith)
    hrel (logarithmic_threshold_ge_four r hr)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_EnergyRegime
-- END TCProof.EnergyRegime

-- BEGIN TCProof.EnergyCounts
section Assembled_TCProof_EnergyCounts

namespace TalagrandConc.TSP.TCFresh

theorem sparseGridCells_subset_lowCells {N : ℕ} (x : Fin N → Point) (k : ℕ) :
    sparseGridCells x k ⊆ lowCells (sampleGrid N k x) (expectedCount N k) := by
  classical
  intro c hc
  have h : (cellCount (sampleGrid N k x) c:ℝ) ≤ ((N:ℝ)*gridArea k/2)/64 :=
    (Finset.mem_filter.mp hc).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  rw [expectedCount_eq_area]
  have hnon : 0 ≤ (N:ℝ)*gridArea k := mul_nonneg (Nat.cast_nonneg N) (gridArea_pos k).le
  linarith

theorem sparseGridCells_card_le {N : ℕ} (x : Fin N → Point) (k : ℕ) :
    (sparseGridCells x k).card ≤
      (lowCells (sampleGrid N k x) (expectedCount N k)).card :=
  Finset.card_le_card (sparseGridCells_subset_lowCells x k)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_EnergyCounts
-- END TCProof.EnergyCounts

-- BEGIN TCProof.GoodEnergy
section Assembled_TCProof_GoodEnergy

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

lemma good_event_alpha_energy {N : ℕ} (hN : 0 < N) (x : Fin N → Point)
    (k₁ : ℕ) (hk₁ : 0 < k₁) (t : ℝ) (ht : 1 ≤ t)
    (hscale : t^2*gridArea k₁ ≤ 128)
    (hx : x ∉ occupancyBadEvent N (k₁-1) (terminalLevel N) t) :
    ∑ i, (sampleAlpha x (terminalLevel N) k₁ i)^2 ≤ 1024 := by
  apply sampleAlpha_energy_of_counts hN x k₁ t ht hscale
  intro k hk
  have hkm := (Finset.mem_Icc.mp hk).1
  have hk0 := (Finset.mem_Icc.mp hk).2
  have hb := occupancyGoodEvent_counts N (k₁-1) (terminalLevel N) t x hx k (by omega) hk0
  have hcard := sparseGridCells_card_le x k
  have hcardR : ((sparseGridCells x k).card:ℝ) ≤
      (lowCells (sampleGrid N k x) (expectedCount N k)).card := by exact_mod_cast hcard
  apply hcardR.trans (hb.trans _)
  have he : k-(k₁-1)=k-k₁+1 := by omega
  rw [he]
  push_cast
  have hp : 0 < expectedCount N k := by unfold expectedCount; positivity
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ hp.le
  linarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_GoodEnergy
-- END TCProof.GoodEnergy

-- BEGIN TCProof.CoarseRegime
section Assembled_TCProof_CoarseRegime

namespace TalagrandConc.TSP.TCFresh

lemma coarse_scalar_bound (r t lam : ℝ) (N : ℕ)
    (hr : 0 < r) (ht : 1 ≤ t) (hrel : r*t^2 = (N:ℝ))
    (hlam : 8*Real.log r ≤ lam) :
    Real.exp 1*Real.exp (-lam/8) + 8*(t^2+2)/(N:ℝ) ≤ 27/r := by
  have ht2 : 1 ≤ t^2 := by nlinarith
  have hn : 0 < (N:ℝ) := by rw [← hrel]; positivity
  have hexp : Real.exp (-lam/8) ≤ 1/r := by
    calc
      _ ≤ Real.exp (-Real.log r) := Real.exp_le_exp.mpr (by linarith)
      _ = 1/r := by rw [Real.exp_neg, Real.exp_log hr, one_div]
  have hterm : Real.exp 1*Real.exp (-lam/8) ≤ 3/r := by
    calc
      _ ≤ 3*(1/r) := mul_le_mul Real.exp_one_lt_three.le hexp
        (Real.exp_pos _).le (by norm_num)
      _ = _ := by ring
  have hsecond : 8*(t^2+2)/(N:ℝ) ≤ 24/r := by
    apply (div_le_div_iff₀ hn hr).2
    rw [← hrel]
    nlinarith
  calc
    _ ≤ 3/r + 24/r := add_le_add hterm hsecond
    _ = 27/r := by ring

lemma cutoff_threshold_lt_count (N : ℕ) (t r : ℝ) (ht : 1 ≤ t)
    (hr : (2:ℝ)^20 ≤ r) (hrel : r*t^2 = (N:ℝ)) :
    128*Real.log r < (N:ℝ) := by
  have hr0 : 0 < r := by norm_num at hr; linarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < r/256 by positivity)
  have hlog256 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 256 by norm_num)
  rw [Real.log_div hr0.ne' (by norm_num : (256:ℝ) ≠ 0)] at hlog
  have hsmall : 128*Real.log r < r := by norm_num at hr; linarith
  have ht2 : 1 ≤ t^2 := by nlinarith
  have hrN : r ≤ (N:ℝ) := by rw [← hrel]; nlinarith
  exact hsmall.trans_le hrN

lemma cutoff_coarse_scalar_bound (N : ℕ) (hN : 0 < N) (t r : ℝ)
    (ht : 1 ≤ t) (hr : (2:ℝ)^20 ≤ r) (hrel : r*t^2 = (N:ℝ)) :
    Real.exp 1*Real.exp (-expectedCount N
      (cutoffLevel N hN (128*Real.log r) (logarithmic_threshold_ge_four r hr)-1)/8)
      + 8*(t^2+2)/(N:ℝ) ≤ 27/r := by
  have hr0 : 0 < r := by norm_num at hr; linarith
  apply coarse_scalar_bound r t _ N hr0 ht hrel
  have hp := cutoffLevel_prev N hN (128*Real.log r)
    (logarithmic_threshold_ge_four r hr) (cutoff_threshold_lt_count N t r ht hr hrel)
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by norm_num at hr; linarith)
  linarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CoarseRegime
-- END TCProof.CoarseRegime

-- BEGIN TCProof.GoodCoarseArea
section Assembled_TCProof_GoodCoarseArea

namespace TalagrandConc.TSP.TCFresh

lemma good_coarse_low_area {N : ℕ} (hN : 0 < N) (x : Fin N → Point)
    (t r : ℝ) (ht : 1 ≤ t) (hr : (2:ℝ)^20 ≤ r) (hrel : r*t^2=(N:ℝ))
    (hx : x ∉ occupancyBadEvent N
      (cutoffLevel N hN (128*Real.log r) (logarithmic_threshold_ge_four r hr)-1)
      (terminalLevel N) t) :
    let m := cutoffLevel N hN (128*Real.log r) (logarithmic_threshold_ge_four r hr)-1
    2*((lowCells (sampleGrid N m x) ((N:ℝ)/Fintype.card (Grid m))).card:ℝ)/
      Fintype.card (Grid m) ≤ 54*t^2/(N:ℝ) := by
  dsimp only
  let m := cutoffLevel N hN (128*Real.log r) (logarithmic_threshold_ge_four r hr)-1
  have hm : m ≤ terminalLevel N := by
    have hs := (cutoffLevel_spec N hN (128*Real.log r)
      (logarithmic_threshold_ge_four r hr)).1
    dsimp [m]
    omega
  have hc := occupancyGoodEvent_counts N m (terminalLevel N) t x hx m le_rfl hm
  simp only [Nat.sub_self, Nat.cast_zero, add_zero] at hc
  have hcard : (Fintype.card (Grid m):ℝ)=(4:ℝ)^m := by rw [grid_card]; norm_cast
  have hp : (0:ℝ) < (4:ℝ)^m := by positivity
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hd := div_le_div_of_nonneg_right hc hp.le
  have he : (Real.exp 1*(4:ℝ)^m*Real.exp (-expectedCount N m/8)+
      8*t^2/expectedCount N m)/(4:ℝ)^m =
      Real.exp 1*Real.exp (-expectedCount N m/8)+8*t^2/(N:ℝ) := by
    unfold expectedCount
    field_simp
  rw [he] at hd
  have hu := cutoff_coarse_scalar_bound N hN t r ht hr hrel
  change Real.exp 1*Real.exp (-expectedCount N m/8)+8*(t^2+2)/(N:ℝ) ≤ 27/r at hu
  have hd' : ((lowCells (sampleGrid N m x) (expectedCount N m)).card:ℝ)/(4:ℝ)^m ≤ 27/r := by
    apply hd.trans (le_trans ?_ hu)
    gcongr
    linarith
  have hr0 : 0 < r := by norm_num at hr; linarith
  have heq : 54/r = 54*t^2/(N:ℝ) := by
    apply (div_eq_div_iff hr0.ne' hn.ne').2
    rw [← hrel]
    ring
  change 2*((lowCells (sampleGrid N m x) ((N:ℝ)/Fintype.card (Grid m))).card:ℝ)/
      Fintype.card (Grid m) ≤ _
  rw [hcard]
  change 2*((lowCells (sampleGrid N m x) (expectedCount N m)).card:ℝ)/(4:ℝ)^m ≤ _
  calc
    _ = 2*(((lowCells (sampleGrid N m x) (expectedCount N m)).card:ℝ)/(4:ℝ)^m) := by ring
    _ ≤ 2*(27/r) := mul_le_mul_of_nonneg_left hd' (by norm_num)
    _ = 54/r := by ring
    _ = _ := heq

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_GoodCoarseArea
-- END TCProof.GoodCoarseArea

-- BEGIN TCProof.DyadicParent
section Assembled_TCProof_DyadicParent

namespace TalagrandConc.TSP.TCFresh

theorem clampedCell_double (m : ℕ) (hm : 0 < m) (t : ℝ) :
    clampedCell (2*m) (2*t)/2=clampedCell m t := by
  have hf : Nat.floor (2*t)/2=Nat.floor t := by
    simpa using Nat.cast_mul_floor_div_cancel (R := ℝ) (n := 2) (by omega) t
  unfold clampedCell
  omega

def parentCell (k : ℕ) (c : Grid (k+1)) : Grid k := fun i =>
  ⟨(c i).val/2, by
    have h := (c i).isLt
    have he : 2^(k+1)=2^k*2 := pow_succ 2 k
    have h' : (c i).val < 2^k*2 := by simpa only [he] using h
    omega⟩

theorem squareIndex_parent (k : ℕ) (x : Point) :
    parentCell k (squareIndex (k+1) x)=squareIndex k x := by
  funext i
  apply Fin.ext
  change (squareIndex (k+1) x i).val/2=(squareIndex k x i).val
  rw [squareIndex_val,squareIndex_val]
  have hn : 2^(k+1)=2*2^k := by rw [pow_succ]; omega
  have hr : (2:ℝ)^(k+1)*(x i:ℝ)=2*((2:ℝ)^k*(x i:ℝ)) := by rw [pow_succ]; ring
  rw [hn,hr]
  exact clampedCell_double (2^k) (by positivity) _

theorem squareIndex_same_parent {k : ℕ} {x y : Point}
    (h : squareIndex (k+1) x=squareIndex (k+1) y) :
    squareIndex k x=squareIndex k y := by
  calc
    squareIndex k x = parentCell k (squareIndex (k+1) x) := (squareIndex_parent k x).symm
    _ = parentCell k (squareIndex (k+1) y) := congrArg (parentCell k) h
    _ = squareIndex k y := squareIndex_parent k y

theorem squareIndex_same_ancestor {k l : ℕ} (hkl : k ≤ l) {x y : Point}
    (h : squareIndex l x=squareIndex l y) : squareIndex k x=squareIndex k y := by
  revert h
  induction l, hkl using Nat.le_induction with
  | base => exact fun h => h
  | succ l hl ih => exact fun h => ih (squareIndex_same_parent h)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_DyadicParent
-- END TCProof.DyadicParent

-- BEGIN TCProof.SquareDistance
section Assembled_TCProof_SquareDistance

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

theorem edist_le_of_coordinate_bound (x y : Point) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ i, |(x i:ℝ)-(y i:ℝ)| ≤ a) : edist x y ≤ 2*a := by
  unfold edist
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  have hs : ∑ i : Fin 2, ((x i:ℝ)-(y i:ℝ))^2 ≤ ∑ _i : Fin 2, a^2 := by
    apply Finset.sum_le_sum
    intro i hi
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ha).mpr (h i)
  simp only [Fin.sum_univ_two] at hs ⊢
  nlinarith [sq_nonneg a]

theorem edist_le_two (x y : Point) : edist x y ≤ 2 := by
  have h := edist_le_of_coordinate_bound x y 1 (by norm_num) (by
    intro i
    rw [abs_le]
    constructor <;> linarith [(x i).property.1,(x i).property.2,
      (y i).property.1,(y i).property.2])
  simpa only [mul_one] using h

theorem edist_same_cell {k : ℕ} {c : Grid k} {x y : Point}
    (hx : x ∈ dyadicSquare k c) (hy : y ∈ dyadicSquare k c) :
    edist x y ≤ 2*(2:ℝ)^(-(k:ℤ)) :=
  edist_le_of_coordinate_bound x y _ (dyadicSide_pos k).le
    (dyadicSquare_coordinate_close hx hy)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_SquareDistance
-- END TCProof.SquareDistance

-- BEGIN TCProof.RegularMonotone
section Assembled_TCProof_RegularMonotone

namespace TalagrandConc.TSP.TCFresh

theorem regular_insert (K : ℝ) (L : Finset Point → ℝ) (hL : Regular K L)
    (F : Finset Point) (hF : F.Nonempty) (y : Point) :
    L F ≤ L (insert y F) ∧ L (insert y F) ≤ L F+K/2 := by
  classical
  obtain ⟨x,hx⟩ := hF
  have h := hL 1 (by omega) F {y} (squareIndex 1 y)
    (by intro z hz; simpa only [Finset.mem_singleton.mp hz] using mem_dyadicSquare_index 1 y)
    ⟨x,hx,y,mem_dyadicSquare_index 1 y,by
      simpa using edist_le_two x y⟩
  simpa [Finset.union_singleton, Real.sqrt_one, div_eq_mul_inv] using h

theorem regular_mono_nonempty (K : ℝ) (L : Finset Point → ℝ) (hL : Regular K L)
    {F G : Finset Point} (hF : F.Nonempty) (hFG : F ⊆ G) : L F ≤ L G := by
  classical
  have aux (H : Finset Point) : L F ≤ L (F ∪ H) := by
    induction H using Finset.induction_on with
    | empty => simp
    | @insert y H hy ih =>
      have hne : (F ∪ H).Nonempty := hF.mono Finset.subset_union_left
      have h := (regular_insert K L hL (F ∪ H) hne y).1
      simpa only [Finset.union_insert] using ih.trans h
  simpa only [Finset.union_eq_right.mpr hFG] using aux G

theorem regular_singleton_oscillation (K : ℝ) (L : Finset Point → ℝ)
    (hL : Regular K L) (x y : Point) : |L {x}-L {y}| ≤ K/2 := by
  classical
  have hx := regular_insert K L hL {x} (Finset.singleton_nonempty x) y
  have hy := regular_insert K L hL {y} (Finset.singleton_nonempty y) x
  have he : insert y ({x} : Finset Point)=insert x {y} := by ext z; simp [or_comm]
  rw [he] at hx
  rw [abs_le]
  constructor <;> linarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_RegularMonotone
-- END TCProof.RegularMonotone

-- BEGIN TCProof.GroupInsertion
section Assembled_TCProof_GroupInsertion

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

theorem finite_union_increment {I : Type*} [DecidableEq I]
    (L : Finset Point → ℝ) (F : Finset Point) (S : Finset I)
    (G : I → Finset Point) (c : I → ℝ)
    (h : ∀ j ∈ S, ∀ H : Finset Point, F ⊆ H → L (H ∪ G j) ≤ L H+c j) :
    L (F ∪ S.biUnion G) ≤ L F+∑ j ∈ S, c j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    have hS := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hj' := h j (Finset.mem_insert_self _ _) (F ∪ S.biUnion G) Finset.subset_union_left
    rw [Finset.biUnion_insert,Finset.sum_insert hj]
    have he : F ∪ (G j ∪ S.biUnion G)=(F ∪ S.biUnion G) ∪ G j := by
      ext x
      simp only [Finset.mem_union]
      tauto
    rw [he]
    linarith

theorem regular_group_increment {I : Type*} [DecidableEq I]
    (K : ℝ) (L : Finset Point → ℝ) (hL : Regular K L)
    (F : Finset Point) (S : Finset I) (G : I → Finset Point)
    (level : I → ℕ) (cell : ∀ j, Grid (level j))
    (hle : ∀ j ∈ S, 1 ≤ level j)
    (hinside : ∀ j ∈ S, ∀ x ∈ G j, x ∈ dyadicSquare (level j) (cell j))
    (hnear : ∀ j ∈ S, ∃ x ∈ F, ∃ y ∈ dyadicSquare (level j) (cell j),
      edist x y ≤ (2:ℝ)^(-(level j:ℤ)+2)) :
    L (F ∪ S.biUnion G) ≤ L F+
      K*∑ j ∈ S, (2:ℝ)^(-(level j:ℤ))*Real.sqrt (G j).card := by
  classical
  rw [Finset.mul_sum]
  apply finite_union_increment
  intro j hj H hFH
  obtain ⟨x,hx,y,hy,hxy⟩ := hnear j hj
  have h := (hL (level j) (hle j hj) H (G j) (cell j) (hinside j hj)
    ⟨x,hFH hx,y,hy,hxy⟩).2
  simpa only [mul_assoc] using h

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_GroupInsertion
-- END TCProof.GroupInsertion

-- BEGIN TCProof.SelectedCells
section Assembled_TCProof_SelectedCells

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

noncomputable def selectedLevel (F : Finset Point) (k₀ : ℕ) (x : Point) : ℕ :=
  Nat.find (show ∃ k, k=k₀ ∨ ∀ y ∈ F, squareIndex k y ≠ squareIndex k x from
    ⟨k₀,Or.inl rfl⟩)

theorem selectedLevel_spec (F : Finset Point) (k₀ : ℕ) (x : Point) :
    selectedLevel F k₀ x=k₀ ∨
      ∀ y ∈ F, squareIndex (selectedLevel F k₀ x) y ≠ squareIndex (selectedLevel F k₀ x) x :=
  by
    classical
    exact Nat.find_spec (show ∃ k, k=k₀ ∨ ∀ y ∈ F, squareIndex k y ≠ squareIndex k x from
      ⟨k₀,Or.inl rfl⟩)

theorem selectedLevel_le (F : Finset Point) (k₀ : ℕ) (x : Point) :
    selectedLevel F k₀ x ≤ k₀ := Nat.find_min' _ (Or.inl rfl)

theorem selectedLevel_before (F : Finset Point) (k₀ : ℕ) (x : Point)
    (j : ℕ) (hj : j < selectedLevel F k₀ x) :
    ∃ y ∈ F, squareIndex j y=squareIndex j x := by
  classical
  have h := Nat.find_min (show ∃ k, k=k₀ ∨ ∀ y ∈ F, squareIndex k y ≠ squareIndex k x from
    ⟨k₀,Or.inl rfl⟩) hj
  push Not at h
  exact h.2

theorem selectedLevel_pos (F : Finset Point) (hF : F.Nonempty) (k₀ : ℕ)
    (hk₀ : 0 < k₀) (x : Point) : 0 < selectedLevel F k₀ x := by
  by_contra hn
  have he : selectedLevel F k₀ x=0 := by omega
  rcases selectedLevel_spec F k₀ x with h|h
  · omega
  · obtain ⟨y,hy⟩ := hF
    have hz := h y hy
    rw [he] at hz
    apply hz
    funext i
    apply Fin.ext
    have hx := (squareIndex 0 x i).isLt
    have hy := (squareIndex 0 y i).isLt
    norm_num at hx hy
    omega

theorem selectedLevel_near (F : Finset Point) (hF : F.Nonempty) (k₀ : ℕ)
    (hk₀ : 0 < k₀) (x : Point) :
    ∃ y ∈ F, edist y x ≤ (2:ℝ)^(-(selectedLevel F k₀ x:ℤ)+2) := by
  have hk := selectedLevel_pos F hF k₀ hk₀ x
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hlt : j < selectedLevel F k₀ x := by omega
  obtain ⟨y,hy,he⟩ := selectedLevel_before F k₀ x j hlt
  refine ⟨y,hy,?_⟩
  have hx := mem_dyadicSquare_index j x
  have hy' := mem_dyadicSquare_index j y
  rw [he] at hy'
  have hd := edist_same_cell hy' hx
  have hp : (2:ℝ)^(-(selectedLevel F k₀ x:ℤ)+2)=2*(2:ℝ)^(-(j:ℤ)) := by
    rw [hj]
    push_cast
    have hh : -((j:ℤ)+1)+2=-(j:ℤ)+1 := by omega
    rw [hh,zpow_add₀ (by norm_num)]
    norm_num
    ring
  rw [hp]
  exact hd

noncomputable def selectedLabel (F : Finset Point) (k₀ : ℕ) (x : Point) :
    Sigma Grid := ⟨selectedLevel F k₀ x,squareIndex (selectedLevel F k₀ x) x⟩

noncomputable def selectedLabels (F G : Finset Point) (k₀ : ℕ) : Finset (Sigma Grid) :=
  by classical exact G.image (selectedLabel F k₀)

noncomputable def selectedGroup (F G : Finset Point) (k₀ : ℕ) (c : Sigma Grid) : Finset Point :=
  by classical exact G.filter (fun x => selectedLabel F k₀ x=c)

theorem selectedGroup_inside (F G : Finset Point) (k₀ : ℕ) (c : Sigma Grid) :
    ∀ x ∈ selectedGroup F G k₀ c, x ∈ dyadicSquare c.1 c.2 := by
  classical
  intro x hx
  have he : selectedLabel F k₀ x=c := (Finset.mem_filter.mp hx).2
  subst c
  exact mem_dyadicSquare_index (selectedLevel F k₀ x) x

theorem biUnion_selectedGroup (F G : Finset Point) (k₀ : ℕ) :
    (selectedLabels F G k₀).biUnion (selectedGroup F G k₀)=G := by
  classical
  ext x
  simp only [Finset.mem_biUnion,selectedGroup,Finset.mem_filter]
  constructor
  · rintro ⟨c,hc,hx,he⟩
    exact hx
  · intro hx
    exact ⟨selectedLabel F k₀ x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,hx,rfl⟩

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_SelectedCells
-- END TCProof.SelectedCells

-- BEGIN TCProof.PrefixFree
section Assembled_TCProof_PrefixFree

namespace TalagrandConc.TSP.TCFresh

theorem selectedLevel_le_of_same (F : Finset Point) (k₀ : ℕ) (x y : Point)
    (h : squareIndex (selectedLevel F k₀ x) y=squareIndex (selectedLevel F k₀ x) x) :
    selectedLevel F k₀ y ≤ selectedLevel F k₀ x := by
  apply Nat.find_min'
  rcases selectedLevel_spec F k₀ x with ht|he
  · exact Or.inl ht
  · exact Or.inr (by intro z hz; rw [h]; exact he z hz)

theorem selectedLevel_eq_of_same (F : Finset Point) (k₀ : ℕ) (x y : Point)
    (h : squareIndex (selectedLevel F k₀ x) y=squareIndex (selectedLevel F k₀ x) x) :
    selectedLevel F k₀ y=selectedLevel F k₀ x := by
  have hle := selectedLevel_le_of_same F k₀ x y h
  apply le_antisymm hle
  apply selectedLevel_le_of_same F k₀ y x
  exact (squareIndex_same_ancestor hle h).symm

theorem selectedLabel_eq_of_same (F : Finset Point) (k₀ : ℕ) (x y : Point)
    (h : squareIndex (selectedLevel F k₀ x) y=squareIndex (selectedLevel F k₀ x) x) :
    selectedLabel F k₀ y=selectedLabel F k₀ x := by
  have he := selectedLevel_eq_of_same F k₀ x y h
  change (⟨selectedLevel F k₀ y,squareIndex (selectedLevel F k₀ y) y⟩ : Sigma Grid)=
    ⟨selectedLevel F k₀ x,squareIndex (selectedLevel F k₀ x) x⟩
  rw [he,h]

theorem selected_prefix_free (F : Finset Point) (k₀ : ℕ) (x y : Point)
    (hne : selectedLabel F k₀ x ≠ selectedLabel F k₀ y) :
    squareIndex (selectedLevel F k₀ x) x ≠ squareIndex (selectedLevel F k₀ x) y := by
  intro he
  exact hne (selectedLabel_eq_of_same F k₀ x y he.symm).symm

theorem selectedGroup_eq_cell_filter (F G : Finset Point) (k₀ : ℕ) (x : Point) :
    selectedGroup F G k₀ (selectedLabel F k₀ x)=
      G.filter (fun y => squareIndex (selectedLevel F k₀ x) y=
        squareIndex (selectedLevel F k₀ x) x) := by
  classical
  ext y
  simp only [selectedGroup,Finset.mem_filter]
  constructor
  · rintro ⟨hy,he⟩
    refine ⟨hy,?_⟩
    have hk := congrArg Sigma.fst he
    change selectedLevel F k₀ y=selectedLevel F k₀ x at hk
    have hh : (⟨selectedLevel F k₀ x,squareIndex (selectedLevel F k₀ x) y⟩ : Sigma Grid)=
        ⟨selectedLevel F k₀ x,squareIndex (selectedLevel F k₀ x) x⟩ := by
      change (⟨selectedLevel F k₀ y,squareIndex (selectedLevel F k₀ y) y⟩ : Sigma Grid)=
        ⟨selectedLevel F k₀ x,squareIndex (selectedLevel F k₀ x) x⟩ at he
      rw [hk] at he
      exact he
    exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  · rintro ⟨hy,he⟩
    exact ⟨hy,selectedLabel_eq_of_same F k₀ x y he⟩

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_PrefixFree
-- END TCProof.PrefixFree

-- BEGIN TCProof.CoordinateGroups
section Assembled_TCProof_CoordinateGroups

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

noncomputable def coordinateGroup {N : ℕ} (F : Finset Point) (k₀ : ℕ)
    (x : Fin N → Point) (I : Finset (Fin N)) (c : Sigma Grid) : Finset (Fin N) :=
  by classical exact I.filter (fun i => selectedLabel F k₀ (x i)=c)

theorem selectedGroup_image {N : ℕ} (F : Finset Point) (k₀ : ℕ)
    (x : Fin N → Point) (I : Finset (Fin N)) (c : Sigma Grid) :
    selectedGroup F (I.image x) k₀ c=(coordinateGroup F k₀ x I c).image x := by
  classical
  ext y
  simp only [selectedGroup,coordinateGroup,Finset.mem_filter,Finset.mem_image]
  aesop

theorem selectedGroup_card_le {N : ℕ} (F : Finset Point) (k₀ : ℕ)
    (x : Fin N → Point) (I : Finset (Fin N)) (c : Sigma Grid) :
    (selectedGroup F (I.image x) k₀ c).card ≤ (coordinateGroup F k₀ x I c).card := by
  classical
  rw [selectedGroup_image]
  exact Finset.card_image_le

theorem coordinateGroup_sum {N : ℕ} (F : Finset Point) (k₀ : ℕ)
    (x : Fin N → Point) (I : Finset (Fin N)) (a : Fin N → ℝ) :
    (∑ c ∈ selectedLabels F (I.image x) k₀, ∑ i ∈ coordinateGroup F k₀ x I c, a i)=
      ∑ i ∈ I, a i := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (by
    intro i hi
    exact Finset.mem_image.mpr ⟨x i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,rfl⟩) a

theorem coordinateGroup_card_sum {N : ℕ} (F : Finset Point) (k₀ : ℕ)
    (x : Fin N → Point) (I : Finset (Fin N)) :
    (∑ c ∈ selectedLabels F (I.image x) k₀, ((coordinateGroup F k₀ x I c).card:ℝ))=I.card := by
  classical
  simpa only [Finset.sum_const,one_mul,nsmul_eq_mul,mul_one] using
    coordinateGroup_sum F k₀ x I (fun _ => (1:ℝ))

theorem coordinateGroup_nonempty {N : ℕ} (F : Finset Point) (k₀ : ℕ)
    (x : Fin N → Point) (I : Finset (Fin N)) (c : Sigma Grid)
    (hc : c ∈ selectedLabels F (I.image x) k₀) :
    (coordinateGroup F k₀ x I c).Nonempty := by
  classical
  obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hc
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
  exact ⟨i,Finset.mem_filter.mpr ⟨hi,he⟩⟩

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CoordinateGroups
-- END TCProof.CoordinateGroups

-- BEGIN TCProof.CoordinateOccupancy
section Assembled_TCProof_CoordinateOccupancy

namespace TalagrandConc.TSP.TCFresh

theorem selectedLabel_eq_iff (F : Finset Point) (k₀ : ℕ) (y z : Point) :
    selectedLabel F k₀ y=selectedLabel F k₀ z ↔
      squareIndex (selectedLevel F k₀ z) y=squareIndex (selectedLevel F k₀ z) z := by
  classical
  have h := congrArg (fun S : Finset Point => y ∈ S) (selectedGroup_eq_cell_filter F {y} k₀ z)
  simpa only [selectedGroup,Finset.mem_filter,Finset.mem_singleton,true_and] using Iff.of_eq h

theorem coordinateGroup_eq_full_cell {N : ℕ} (x : Fin N → Point)
    (I : Finset (Fin N)) (k₀ : ℕ) (z : Point)
    (hlevel : selectedLevel ((Finset.univ \ I).image x) k₀ z < k₀) :
    coordinateGroup ((Finset.univ \ I).image x) k₀ x I
      (selectedLabel ((Finset.univ \ I).image x) k₀ z)=
    Finset.univ.filter (fun i => squareIndex (selectedLevel ((Finset.univ \ I).image x) k₀ z) (x i)=
      squareIndex (selectedLevel ((Finset.univ \ I).image x) k₀ z) z) := by
  classical
  let F := (Finset.univ \ I).image x
  change selectedLevel F k₀ z < k₀ at hlevel
  have hempty : ∀ y ∈ F, squareIndex (selectedLevel F k₀ z) y ≠ squareIndex (selectedLevel F k₀ z) z := by
    rcases selectedLevel_spec F k₀ z with he|he
    · omega
    · exact he
  ext i
  simp only [coordinateGroup,Finset.mem_filter,Finset.mem_univ,true_and,selectedLabel_eq_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_,h⟩
    by_contra hi
    have hx : x i ∈ F := Finset.mem_image.mpr ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
    exact hempty (x i) hx h

theorem coordinateGroup_card_full {N : ℕ} (x : Fin N → Point)
    (I : Finset (Fin N)) (k₀ : ℕ) (z : Point)
    (hlevel : selectedLevel ((Finset.univ \ I).image x) k₀ z < k₀) :
    (coordinateGroup ((Finset.univ \ I).image x) k₀ x I
      (selectedLabel ((Finset.univ \ I).image x) k₀ z)).card=
    cellCount (sampleGrid N (selectedLevel ((Finset.univ \ I).image x) k₀ z) x)
      (squareIndex (selectedLevel ((Finset.univ \ I).image x) k₀ z) z) := by
  rw [coordinateGroup_eq_full_cell x I k₀ z hlevel]
  rfl

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CoordinateOccupancy
-- END TCProof.CoordinateOccupancy

-- BEGIN TCProof.EnergyBaseline
section Assembled_TCProof_EnergyBaseline

namespace TalagrandConc.TSP.TCFresh

theorem sqrt_gridArea (k : ℕ) : Real.sqrt (gridArea k)=(2:ℝ)^(-(k:ℤ)) := by
  rw [gridArea,dyadicSide_eq_inv,Real.sqrt_inv]
  congr 1
  have he : (4:ℝ)^k=((2:ℝ)^k)^2 := by
    rw [← pow_mul, Nat.mul_comm k 2,pow_mul]
    norm_num
  rw [he,Real.sqrt_sq (by positivity)]

theorem sampleAlpha_lower {N : ℕ} (hN : 0 < N) (x : Fin N → Point)
    (k₁ : ℕ) (i : Fin N) :
    1/Real.sqrt (N:ℝ) ≤ sampleAlpha x (terminalLevel N) k₁ i := by
  have h := (terminalLevel_bounds N hN).1
  have hi : (N:ℝ)⁻¹ ≤ gridArea (terminalLevel N) :=
    inv_anti₀ (by positivity) h
  have hs := Real.sqrt_le_sqrt hi
  rw [Real.sqrt_inv] at hs
  have hs' : 1/Real.sqrt (N:ℝ) ≤ Real.sqrt (gridArea (terminalLevel N)) := by
    simpa only [one_div] using hs
  exact hs'.trans (sampleAlpha_baseline x _ k₁ i)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_EnergyBaseline
-- END TCProof.EnergyBaseline

-- BEGIN TCProof.InsertionCosts
section Assembled_TCProof_InsertionCosts

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

theorem dense_cell_cost (s n g : ℝ) (hs : 0 ≤ s) (hn : 0 < n) (hg : 0 ≤ g)
    (hd : n*s^2 ≤ 128*g) : s*Real.sqrt g ≤ 12*g/Real.sqrt n := by
  have hsn := Real.sqrt_pos.mpr hn
  have hsg := Real.sqrt_nonneg g
  have hqg := Real.sq_sqrt hg
  have hqn := Real.sq_sqrt hn.le
  apply (le_div_iff₀ hsn).mpr
  have hmul := mul_le_mul_of_nonneg_right hd hg
  have hsq : (s*Real.sqrt g*Real.sqrt n)^2 ≤ (12*g)^2 := by
    calc
      _ = n*s^2*g := by rw [mul_pow,mul_pow,hqg,hqn]; ring
      _ ≤ 128*g^2 := by nlinarith
      _ ≤ (12*g)^2 := by nlinarith [sq_nonneg g]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

theorem sparse_cell_cost (s : ℝ) (hs : 0 ≤ s) (g : ℕ) :
    s*Real.sqrt g ≤ s*g := by
  apply mul_le_mul_of_nonneg_left _ hs
  by_cases hg : g=0
  · simp only [hg,Nat.cast_zero,Real.sqrt_zero,le_refl]
  · have hg1 : (1:ℝ) ≤ g := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hg
    have hq := Real.sq_sqrt (Nat.cast_nonneg g)
    have hnon := Real.sqrt_nonneg (g:ℝ)
    nlinarith

theorem coarse_cells_cost {I : Type*} (S : Finset I) (s g : I → ℝ)
    (hg : ∀ i ∈ S, 0 ≤ g i) :
    (∑ i ∈ S, s i*Real.sqrt (g i))^2 ≤
      (∑ i ∈ S, (s i)^2)*(∑ i ∈ S, g i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S s (fun i => Real.sqrt (g i))
  have he : (∑ i ∈ S, (Real.sqrt (g i))^2)=∑ i ∈ S, g i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hg i hi))
  rwa [he] at h

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_InsertionCosts
-- END TCProof.InsertionCosts

-- BEGIN TCProof.CoordinateCharge
section Assembled_TCProof_CoordinateCharge

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

theorem coordinateGroup_mem_cell {N : ℕ} (F : Finset Point) (k₀ : ℕ)
    (x : Fin N → Point) (I : Finset (Fin N)) (c : Sigma Grid) (i : Fin N)
    (hi : i ∈ coordinateGroup F k₀ x I c) : squareIndex c.1 (x i)=c.2 := by
  classical
  have he := (Finset.mem_filter.mp hi).2
  change selectedLabel F k₀ (x i)=c at he
  subst c
  rfl

theorem coordinateGroup_full_count {N : ℕ} (x : Fin N → Point) (I : Finset (Fin N))
    (k₀ : ℕ) (c : Sigma Grid)
    (hc : c ∈ selectedLabels ((Finset.univ \ I).image x) (I.image x) k₀)
    (hlt : c.1 < k₀) :
    (coordinateGroup ((Finset.univ \ I).image x) k₀ x I c).card=
      cellCount (sampleGrid N c.1 x) c.2 := by
  classical
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
  exact coordinateGroup_card_full x I k₀ z hlt

theorem coordinateGroup_level_le {N : ℕ} (F : Finset Point) (x : Fin N → Point)
    (I : Finset (Fin N)) (k₀ : ℕ) (c : Sigma Grid)
    (hc : c ∈ selectedLabels F (I.image x) k₀) : c.1 ≤ k₀ := by
  classical
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
  exact selectedLevel_le F k₀ z

theorem coordinate_dense_charge {N : ℕ} (hN : 0 < N) (F : Finset Point)
    (x : Fin N → Point) (I : Finset (Fin N)) (k₁ : ℕ) (c : Sigma Grid)
    (hd : (N:ℝ)*gridArea c.1 ≤
      128*(coordinateGroup F (terminalLevel N) x I c).card) :
    Real.sqrt (gridArea c.1)*Real.sqrt (coordinateGroup F (terminalLevel N) x I c).card ≤
      12*∑ i ∈ coordinateGroup F (terminalLevel N) x I c,
        sampleAlpha x (terminalLevel N) k₁ i := by
  have hbase : ((coordinateGroup F (terminalLevel N) x I c).card:ℝ)/Real.sqrt N ≤
      ∑ i ∈ coordinateGroup F (terminalLevel N) x I c, sampleAlpha x (terminalLevel N) k₁ i := by
    calc
      _ = ∑ _i ∈ coordinateGroup F (terminalLevel N) x I c, 1/Real.sqrt N := by
        simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun i hi => sampleAlpha_lower hN x k₁ i)
  have hd' := dense_cell_cost (Real.sqrt (gridArea c.1)) (N:ℝ)
    (coordinateGroup F (terminalLevel N) x I c).card (Real.sqrt_nonneg _)
    (by exact_mod_cast hN) (Nat.cast_nonneg _) (by rwa [Real.sq_sqrt (gridArea_pos c.1).le])
  calc
    _ ≤ 12*(coordinateGroup F (terminalLevel N) x I c).card/Real.sqrt N := hd'
    _ = 12*(((coordinateGroup F (terminalLevel N) x I c).card:ℝ)/Real.sqrt N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by norm_num)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CoordinateCharge
-- END TCProof.CoordinateCharge

-- BEGIN TCProof.SparseCharge
section Assembled_TCProof_SparseCharge

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

theorem coordinate_terminal_dense {N : ℕ} (hN : 0 < N) (F : Finset Point)
    (x : Fin N → Point) (I : Finset (Fin N)) (c : Sigma Grid)
    (hc : c ∈ selectedLabels F (I.image x) (terminalLevel N))
    (he : c.1=terminalLevel N) :
    (N:ℝ)*gridArea c.1 ≤ 128*(coordinateGroup F (terminalLevel N) x I c).card := by
  have hn := Finset.card_pos.mpr (coordinateGroup_nonempty F (terminalLevel N) x I c hc)
  have hn' : (1:ℝ) ≤ (coordinateGroup F (terminalLevel N) x I c).card := by exact_mod_cast hn
  have ht := (expectedCount_terminal N hN).2
  rw [expectedCount_eq_area,← he] at ht
  linarith

theorem coordinate_sparse_charge {N : ℕ} (hN : 0 < N)
    (x : Fin N → Point) (I : Finset (Fin N)) (k₁ : ℕ) (c : Sigma Grid)
    (hc : c ∈ selectedLabels ((Finset.univ \ I).image x) (I.image x) (terminalLevel N))
    (hk₁ : k₁ ≤ c.1)
    (hsparse : 128*(coordinateGroup ((Finset.univ \ I).image x) (terminalLevel N) x I c).card <
      (N:ℝ)*gridArea c.1) :
    Real.sqrt (gridArea c.1)*
      Real.sqrt (coordinateGroup ((Finset.univ \ I).image x) (terminalLevel N) x I c).card ≤
    ∑ i ∈ coordinateGroup ((Finset.univ \ I).image x) (terminalLevel N) x I c,
      sampleAlpha x (terminalLevel N) k₁ i := by
  classical
  let F := (Finset.univ \ I).image x
  have hle := coordinateGroup_level_le F x I (terminalLevel N) c hc
  have hlt : c.1 < terminalLevel N := by
    by_contra hh
    have he : c.1=terminalLevel N := by omega
    have hd := coordinate_terminal_dense hN F x I c hc he
    linarith
  have hfull := coordinateGroup_full_count x I (terminalLevel N) c hc hlt
  have hcell : c.2 ∈ sparseGridCells x c.1 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (cellCount (sampleGrid N c.1 x) c.2:ℝ) ≤ ((N:ℝ)*gridArea c.1/2)/64
    rw [← hfull]
    linarith
  have halpha : ∀ i ∈ coordinateGroup F (terminalLevel N) x I c,
      Real.sqrt (gridArea c.1) ≤ sampleAlpha x (terminalLevel N) k₁ i := by
    intro i hi
    apply sampleAlpha_sparse x (terminalLevel N) k₁ c.1 (Finset.mem_Icc.mpr ⟨hk₁,hle⟩) i
    rw [coordinateGroup_mem_cell F (terminalLevel N) x I c i hi]
    exact hcell
  calc
    _ ≤ Real.sqrt (gridArea c.1)*(coordinateGroup F (terminalLevel N) x I c).card :=
      sparse_cell_cost _ (Real.sqrt_nonneg _) _
    _ = ∑ _i ∈ coordinateGroup F (terminalLevel N) x I c, Real.sqrt (gridArea c.1) := by
      simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum halpha

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_SparseCharge
-- END TCProof.SparseCharge

-- BEGIN TCProof.GridAncestor
section Assembled_TCProof_GridAncestor

open MeasureTheory
open scoped ENNReal
namespace TalagrandConc.TSP.TCFresh

theorem squareIndex_surjective (k : ℕ) : Function.Surjective (squareIndex k) := by
  intro c
  have hm := pointLaw_grid_atom k c
  have hn : ({x : Point | squareIndex k x=c} : Set Point).Nonempty := by
    by_contra h
    have he : {x : Point | squareIndex k x=c}=∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he,measure_empty] at hm
    have hp : (Fintype.card (Grid k):ℝ≥0∞)⁻¹ ≠ 0 := by simp
    exact hp hm.symm
  exact hn

noncomputable def gridRepresentative (k : ℕ) (c : Grid k) : Point :=
  Classical.choose (squareIndex_surjective k c)

theorem squareIndex_representative (k : ℕ) (c : Grid k) :
    squareIndex k (gridRepresentative k c)=c :=
  Classical.choose_spec (squareIndex_surjective k c)

noncomputable def ancestorCell (k m : ℕ) (c : Grid m) : Grid k :=
  squareIndex k (gridRepresentative m c)

theorem ancestorCell_squareIndex (k m : ℕ) (hkm : k ≤ m) (x : Point) :
    ancestorCell k m (squareIndex m x)=squareIndex k x := by
  apply squareIndex_same_ancestor hkm
  exact squareIndex_representative m (squareIndex m x)

theorem ancestorCell_comp (k l m : ℕ) (hkl : k ≤ l) (c : Grid m) :
    ancestorCell k l (ancestorCell l m c)=ancestorCell k m c :=
  ancestorCell_squareIndex k l hkl (gridRepresentative m c)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_GridAncestor
-- END TCProof.GridAncestor

-- BEGIN TCProof.AncestorVolume
section Assembled_TCProof_AncestorVolume

open MeasureTheory
open scoped BigOperators ENNReal
namespace TalagrandConc.TSP.TCFresh

theorem pointLaw_grid_set (k : ℕ) (C : Finset (Grid k)) :
    pointLaw {x | squareIndex k x ∈ C}=C.card*(Fintype.card (Grid k):ℝ≥0∞)⁻¹ := by
  classical
  have h := sum_measure_preimage_singleton (μ := pointLaw) C (f := squareIndex k)
    (fun c _ => (measurable_squareIndex k) (measurableSet_singleton c))
  change pointLaw (squareIndex k ⁻¹' (C : Set (Grid k)))=_
  rw [← h]
  change (∑ c ∈ C, pointLaw {x | squareIndex k x=c})=_
  simp only [pointLaw_grid_atom,Finset.sum_const,nsmul_eq_mul]

noncomputable def descendants (k m : ℕ) (c : Grid k) : Finset (Grid m) :=
  by classical exact Finset.univ.filter (fun d => ancestorCell k m d=c)

theorem descendants_volume (k m : ℕ) (hkm : k ≤ m) (c : Grid k) :
    ((descendants k m c).card:ℝ)/(Fintype.card (Grid m):ℝ)=
      (Fintype.card (Grid k):ℝ)⁻¹ := by
  classical
  have he : {x | squareIndex m x ∈ descendants k m c}={x | squareIndex k x=c} := by
    ext x
    simp only [Set.mem_ofPred_eq,descendants,Finset.mem_filter,Finset.mem_univ,true_and,
      ancestorCell_squareIndex k m hkm]
  have h := pointLaw_grid_set m (descendants k m c)
  rw [he,pointLaw_grid_atom] at h
  have hr := congrArg ENNReal.toReal h.symm
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_inv,div_eq_mul_inv] using hr

theorem descendants_disjoint {k l m : ℕ}
    {c : Grid k} {d : Grid l}
    (h : ∀ x : Point, ¬ (squareIndex k x=c ∧ squareIndex l x=d)) :
    Disjoint (descendants k m c) (descendants l m d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hd
  have he' := (Finset.mem_filter.mp he).2
  have hd' := (Finset.mem_filter.mp hd).2
  exact h (gridRepresentative m e) ⟨he',hd'⟩

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_AncestorVolume
-- END TCProof.AncestorVolume

-- BEGIN TCProof.OccupancyRefinement
section Assembled_TCProof_OccupancyRefinement

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

theorem hitSum_descendants {N : ℕ} (x : Fin N → Point) (k m : ℕ) (hkm : k ≤ m)
    (c : Grid k) : hitSum (descendants k m c) (sampleGrid N m x)=
      (cellCount (sampleGrid N k x) c:ℝ) := by
  classical
  simp only [hitSum,descendants,sampleGrid,Finset.mem_filter,Finset.mem_univ,true_and,
    ancestorCell_squareIndex k m hkm,cellCount,Finset.card_eq_sum_ones,
    Nat.cast_sum]
  simp only [Nat.cast_one]
  exact (Finset.sum_filter (fun i : Fin N => squareIndex k (x i)=c) (fun _ => (1:ℝ))).symm

theorem selected_cells_disjoint (F : Finset Point) (k₀ : ℕ) (x y : Point)
    (hne : selectedLabel F k₀ x ≠ selectedLabel F k₀ y) (z : Point) :
    ¬ (squareIndex (selectedLevel F k₀ x) z=squareIndex (selectedLevel F k₀ x) x ∧
      squareIndex (selectedLevel F k₀ y) z=squareIndex (selectedLevel F k₀ y) y) := by
  rintro ⟨hx,hy⟩
  rcases le_total (selectedLevel F k₀ x) (selectedLevel F k₀ y) with hle|hle
  · have hh := squareIndex_same_ancestor hle hy
    exact selected_prefix_free F k₀ x y hne (hx.symm.trans hh)
  · have hh := squareIndex_same_ancestor hle hx
    exact selected_prefix_free F k₀ y x (Ne.symm hne) (hy.symm.trans hh)

theorem selected_descendants_disjoint (F G : Finset Point) (k₀ m : ℕ)
    (c d : Sigma Grid) (hc : c ∈ selectedLabels F G k₀)
    (hd : d ∈ selectedLabels F G k₀) (hne : c ≠ d) :
    Disjoint (descendants c.1 m c.2) (descendants d.1 m d.2) := by
  classical
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hd
  exact descendants_disjoint (selected_cells_disjoint F k₀ x y hne)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_OccupancyRefinement
-- END TCProof.OccupancyRefinement

-- BEGIN TCProof.LowAreaTransfer
section Assembled_TCProof_LowAreaTransfer

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

theorem sparse_union_card_le_low {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (x : Fin N → α) (lam : ℝ) (hlam : 0 < lam) (U : Finset α)
    (hU : hitSum U x ≤ (U.card:ℝ)*lam/128) :
    (U.card:ℝ) ≤ 2*(lowCells x lam).card := by
  classical
  let H := U \ lowCells x lam
  have hcount : (H.card:ℝ)*lam/64 ≤ hitSum U x := by
    rw [hitSum_eq_sum_cellCount]
    calc
      _ = ∑ _a ∈ H, lam/64 := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ ∑ a ∈ H, (cellCount x a:ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        have hn := (Finset.mem_sdiff.mp ha).2
        have hh : ¬ (cellCount x a:ℝ) ≤ lam/64 := by
          intro hh
          apply hn
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
        exact (lt_of_not_ge hh).le
      _ ≤ ∑ a ∈ U, (cellCount x a:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (by intro a ha hb; positivity)
  have hhigh : (H.card:ℝ)*2 ≤ U.card := by
    have h := hcount.trans hU
    apply (mul_le_mul_iff_left₀ hlam).mp
    linarith
  have hcards := Finset.card_sdiff_add_card_inter U (lowCells x lam)
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := U) (s₂ := lowCells x lam))
  have hc : (H.card:ℝ)+(U ∩ lowCells x lam).card=U.card := by exact_mod_cast hcards
  have hl' : ((U ∩ lowCells x lam).card:ℝ) ≤ (lowCells x lam).card := by exact_mod_cast hl
  linarith


theorem hitSum_biUnion {α I : Type*} [DecidableEq α] [DecidableEq I]
    {N : ℕ} (x : Fin N → α) (S : Finset I) (D : I → Finset α)
    (hD : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (D i) (D j)) :
    hitSum (S.biUnion D) x=∑ i ∈ S, hitSum (D i) x := by
  classical
  simp only [hitSum_eq_sum_cellCount]
  exact Finset.sum_biUnion hD

theorem sparse_disjoint_union_card_le_low {α I : Type*}
    [Fintype α] [DecidableEq α] [DecidableEq I]
    {N : ℕ} (x : Fin N → α) (lam : ℝ) (hlam : 0 < lam)
    (S : Finset I) (D : I → Finset α)
    (hD : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (D i) (D j))
    (hsmall : ∀ i ∈ S, hitSum (D i) x ≤ ((D i).card:ℝ)*lam/128) :
    (∑ i ∈ S, ((D i).card:ℝ)) ≤ 2*(lowCells x lam).card := by
  classical
  have hcard : ((S.biUnion D).card:ℝ)=∑ i ∈ S, ((D i).card:ℝ) := by
    rw [Finset.card_biUnion hD,Nat.cast_sum]
  rw [← hcard]
  apply sparse_union_card_le_low x lam hlam
  rw [hitSum_biUnion x S D hD,hcard]
  calc
    _ ≤ ∑ i ∈ S, ((D i).card:ℝ)*lam/128 := Finset.sum_le_sum hsmall
    _ = _ := by rw [← Finset.sum_div,← Finset.sum_mul]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_LowAreaTransfer
-- END TCProof.LowAreaTransfer

-- BEGIN TCProof.CoarseArea
section Assembled_TCProof_CoarseArea

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

theorem selected_coarse_area {N : ℕ} (hN : 0 < N) (x : Fin N → Point)
    (F G : Finset Point) (k₀ m : ℕ) (S : Finset (Sigma Grid))
    (hS : S ⊆ selectedLabels F G k₀)
    (hlevel : ∀ c ∈ S, c.1 ≤ m)
    (hsmall : ∀ c ∈ S, (cellCount (sampleGrid N c.1 x) c.2:ℝ) ≤
      (N:ℝ)/(128*Fintype.card (Grid c.1))) :
    (∑ c ∈ S, (Fintype.card (Grid c.1):ℝ)⁻¹) ≤
      2*(lowCells (sampleGrid N m x) ((N:ℝ)/Fintype.card (Grid m))).card/
        Fintype.card (Grid m) := by
  classical
  let M : ℝ := Fintype.card (Grid m)
  have hM : 0 < M := by dsimp [M]; exact_mod_cast Fintype.card_pos
  let D := fun c : Sigma Grid => descendants c.1 m c.2
  have hD : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → Disjoint (D c) (D d) := by
    intro c hc d hd hne
    exact selected_descendants_disjoint F G k₀ m c d (hS hc) (hS hd) hne
  have hsmall' : ∀ c ∈ S, hitSum (D c) (sampleGrid N m x) ≤ ((D c).card:ℝ)*((N:ℝ)/M)/128 := by
    intro c hc
    rw [hitSum_descendants x c.1 m (hlevel c hc)]
    have hv := descendants_volume c.1 m (hlevel c hc) c.2
    have he : ((D c).card:ℝ)*((N:ℝ)/M)/128=(N:ℝ)/(128*Fintype.card (Grid c.1)) := by
      calc
        _ = ((D c).card/M)*(N:ℝ)/128 := by ring
        _ = _ := by rw [hv]; ring
    rw [he]
    exact hsmall c hc
  have hb := sparse_disjoint_union_card_le_low (sampleGrid N m x) ((N:ℝ)/M)
    (div_pos (by exact_mod_cast hN) hM) S D hD hsmall'
  have hm := div_le_div_of_nonneg_right hb hM.le
  have he : (∑ c ∈ S, ((D c).card:ℝ))/M=∑ c ∈ S, (Fintype.card (Grid c.1):ℝ)⁻¹ := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun c hc => descendants_volume c.1 m (hlevel c hc) c.2)
  rw [he] at hm
  exact hm

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CoarseArea
-- END TCProof.CoarseArea

-- BEGIN TCProof.CostAssembly
section Assembled_TCProof_CostAssembly

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

theorem insertion_cost_sum {I : Type*} [DecidableEq I]
    (S C : Finset I) (hCS : C ⊆ S) (s g w : I → ℝ)
    (hs : ∀ c ∈ S, 0 ≤ s c) (hg : ∀ c ∈ S, 0 ≤ g c)
    (hw : ∀ c ∈ S, 0 ≤ w c)
    (N t : ℝ) (hN : 0 < N) (ht : 0 ≤ t)
    (hcount : (∑ c ∈ S, g c) ≤ N)
    (harea : (∑ c ∈ C, (s c)^2) ≤ 54*t^2/N)
    (hcharge : ∀ c ∈ S \ C, s c*Real.sqrt (g c) ≤ 12*w c)
    (hcost : (∑ c ∈ S, w c) ≤ 128*t) :
    (∑ c ∈ S, s c*Real.sqrt (g c)) ≤ 2048*t := by
  have hcg : (∑ c ∈ C, g c) ≤ N :=
    (Finset.sum_le_sum_of_subset_of_nonneg hCS (fun c hc hn => hg c hc)).trans hcount
  have hcn : 0 ≤ ∑ c ∈ C, g c := Finset.sum_nonneg (fun c hc => hg c (hCS hc))
  have hcoarse : (∑ c ∈ C, s c*Real.sqrt (g c)) ≤ 8*t := by
    have hc := coarse_cells_cost C s g (fun c hc => hg c (hCS hc))
    have hm := mul_le_mul harea hcg hcn (show 0 ≤ 54*t^2/N by positivity)
    have hb : (54*t^2/N)*N=54*t^2 := by field_simp
    rw [hb] at hm
    have hpositive : 0 ≤ ∑ c ∈ C, s c*Real.sqrt (g c) :=
      Finset.sum_nonneg (fun c hc => mul_nonneg (hs c (hCS hc)) (Real.sqrt_nonneg _))
    nlinarith [sq_nonneg t]
  have hrest : (∑ c ∈ S \ C, s c*Real.sqrt (g c)) ≤ 12*(128*t) := by
    calc
      _ ≤ ∑ c ∈ S \ C, 12*w c := Finset.sum_le_sum hcharge
      _ = 12*∑ c ∈ S \ C, w c := (Finset.mul_sum _ _ _).symm
      _ ≤ 12*∑ c ∈ S, w c := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun c hc hn => hw c hc)) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hcost (by norm_num)
  have he := Finset.sum_sdiff hCS (f := fun c => s c*Real.sqrt (g c))
  linarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CostAssembly
-- END TCProof.CostAssembly

-- BEGIN TCProof.PrefixInsertion
section Assembled_TCProof_PrefixInsertion

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

theorem regular_selected_increment (K : ℝ) (L : Finset Point → ℝ)
    (hL : Regular K L) (F G : Finset Point) (hF : F.Nonempty)
    (k₀ : ℕ) (hk₀ : 0 < k₀) :
    L (F ∪ G) ≤ L F+K*∑ c ∈ selectedLabels F G k₀,
      (2:ℝ)^(-(c.1:ℤ))*Real.sqrt (selectedGroup F G k₀ c).card := by
  classical
  have h := regular_group_increment K L hL F (selectedLabels F G k₀)
    (selectedGroup F G k₀) Sigma.fst Sigma.snd (by
      intro c hc
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
      exact selectedLevel_pos F hF k₀ hk₀ x)
    (fun c _ => selectedGroup_inside F G k₀ c) (by
      intro c hc
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨y,hy,hd⟩ := selectedLevel_near F hF k₀ hk₀ x
      exact ⟨y,hy,x,mem_dyadicSquare_index _ x,hd⟩)
  simpa only [biUnion_selectedGroup] using h

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_PrefixInsertion
-- END TCProof.PrefixInsertion

-- BEGIN TCProof.SampleInsertion
section Assembled_TCProof_SampleInsertion

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

theorem gridArea_card (k : ℕ) : gridArea k=(Fintype.card (Grid k):ℝ)⁻¹ := by
  rw [grid_card]
  simp only [gridArea,Nat.cast_pow,Nat.cast_ofNat]

theorem sample_insertion_cost {N : ℕ} (hN : 0 < N) (x : Fin N → Point)
    (I : Finset (Fin N)) (k₁ : ℕ) (hkk : k₁ ≤ terminalLevel N)
    (t : ℝ) (ht : 0 ≤ t)
    (hcost : (∑ i ∈ I, sampleAlpha x (terminalLevel N) k₁ i) ≤ 128*t)
    (harea : 2*(lowCells (sampleGrid N (k₁-1) x)
      ((N:ℝ)/Fintype.card (Grid (k₁-1)))).card/Fintype.card (Grid (k₁-1)) ≤ 54*t^2/N) :
    (∑ c ∈ selectedLabels ((Finset.univ \ I).image x) (I.image x) (terminalLevel N),
      (2:ℝ)^(-(c.1:ℤ))*Real.sqrt
        (selectedGroup ((Finset.univ \ I).image x) (I.image x) (terminalLevel N) c).card) ≤ 2048*t := by
  classical
  let F := (Finset.univ \ I).image x
  let k₀ := terminalLevel N
  let S := selectedLabels F (I.image x) k₀
  let g := fun c => (coordinateGroup F k₀ x I c).card
  let s := fun c : Sigma Grid => Real.sqrt (gridArea c.1)
  let w := fun c => ∑ i ∈ coordinateGroup F k₀ x I c, sampleAlpha x k₀ k₁ i
  let C := S.filter (fun c => c.1 < k₁ ∧ (128:ℝ)*g c < (N:ℝ)*gridArea c.1)
  have hCS : C ⊆ S := Finset.filter_subset _ _
  have hw : ∀ c ∈ S, 0 ≤ w c := by
    intro c hc
    exact Finset.sum_nonneg (fun i hi => sampleAlpha_nonneg x k₀ k₁ i)
  have hClevel : ∀ c ∈ C, c.1 ≤ k₁-1 := by
    intro c hc
    have hh := (Finset.mem_filter.mp hc).2.1
    omega
  have hCsmall : ∀ c ∈ C, (cellCount (sampleGrid N c.1 x) c.2:ℝ) ≤
      (N:ℝ)/(128*Fintype.card (Grid c.1)) := by
    intro c hc
    have hh := (Finset.mem_filter.mp hc).2
    have hfull := coordinateGroup_full_count x I k₀ c (hCS hc) (by dsimp [k₀]; omega)
    have he : (N:ℝ)/(128*Fintype.card (Grid c.1))=(N:ℝ)*gridArea c.1/128 := by
      rw [gridArea_card]
      ring
    rw [he,← hfull]
    change (g c:ℝ) ≤ (N:ℝ)*gridArea c.1/128
    linarith
  have hCarea : (∑ c ∈ C, (s c)^2) ≤ 54*t^2/N := by
    have h := selected_coarse_area hN x F (I.image x) k₀ (k₁-1) C hCS hClevel hCsmall
    have he : (∑ c ∈ C, (s c)^2)=(∑ c ∈ C, (Fintype.card (Grid c.1):ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (Real.sq_sqrt (gridArea_pos c.1).le).trans (gridArea_card c.1)
    rw [he]
    exact h.trans harea
  have hcharge : ∀ c ∈ S \ C, s c*Real.sqrt (g c) ≤ 12*w c := by
    intro c hc
    have hcS := (Finset.mem_sdiff.mp hc).1
    have hcC := (Finset.mem_sdiff.mp hc).2
    by_cases hd : (N:ℝ)*gridArea c.1 ≤ 128*g c
    · exact coordinate_dense_charge hN F x I k₁ c hd
    · have hd' : (128:ℝ)*g c < (N:ℝ)*gridArea c.1 := lt_of_not_ge hd
      have hk : k₁ ≤ c.1 := by
        by_contra hh
        exact hcC (Finset.mem_filter.mpr ⟨hcS,by omega,hd'⟩)
      have hh := coordinate_sparse_charge hN x I k₁ c hcS hk hd'
      have hwc := hw c hcS
      change s c*Real.sqrt (g c) ≤ w c at hh
      linarith
  have hcount : (∑ c ∈ S, (g c:ℝ)) ≤ N := by
    rw [coordinateGroup_card_sum]
    have hh := Finset.card_le_card (Finset.subset_univ I)
    simp only [Finset.card_univ,Fintype.card_fin] at hh
    exact_mod_cast hh
  have hcost' : (∑ c ∈ S, w c) ≤ 128*t := by
    rw [coordinateGroup_sum]
    exact hcost
  have htotal := insertion_cost_sum S C hCS s (fun c => (g c:ℝ)) w
    (fun c hc => Real.sqrt_nonneg _) (fun c hc => Nat.cast_nonneg _) hw
    (N:ℝ) t (by exact_mod_cast hN) ht hcount hCarea hcharge hcost'
  apply le_trans _ htotal
  apply Finset.sum_le_sum
  intro c hc
  rw [← sqrt_gridArea]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt (by exact_mod_cast selectedGroup_card_le F k₀ x I c)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_SampleInsertion
-- END TCProof.SampleInsertion

-- BEGIN TCProof.RetainedInsertion
section Assembled_TCProof_RetainedInsertion

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

theorem regular_retained_increment {N : ℕ} (hN : 0 < N) (K : ℝ) (hK : 0 ≤ K)
    (L : Finset Point → ℝ) (hL : Regular K L) (x : Fin N → Point)
    (J : Finset (Fin N)) (hJ : J.Nonempty) (k₁ : ℕ) (hk₁ : 1 ≤ k₁)
    (hkk : k₁ ≤ terminalLevel N) (t : ℝ) (ht : 0 ≤ t)
    (hcost : (∑ i ∈ Finset.univ \ J, sampleAlpha x (terminalLevel N) k₁ i) ≤ 128*t)
    (harea : 2*(lowCells (sampleGrid N (k₁-1) x)
      ((N:ℝ)/Fintype.card (Grid (k₁-1)))).card/Fintype.card (Grid (k₁-1)) ≤ 54*t^2/N) :
    L (sampleSet x) ≤ L (J.image x)+2048*K*t := by
  classical
  let I := Finset.univ \ J
  have he : Finset.univ \ I=J := by
    ext i
    simp only [I,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not]
  have hbound := sample_insertion_cost hN x I k₁ hkk t ht hcost harea
  rw [he] at hbound
  have hne : (J.image x).Nonempty := hJ.image x
  have hinc := regular_selected_increment K L hL (J.image x) (I.image x) hne
    (terminalLevel N) (by omega)
  have hunion : J.image x ∪ I.image x=sampleSet x := by
    rw [← Finset.image_union]
    have hJI : J ∪ I=Finset.univ := by ext i; simp [I]
    rw [hJI]
    rfl
  rw [hunion] at hinc
  have hm := mul_le_mul_of_nonneg_left hbound hK
  nlinarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_RetainedInsertion
-- END TCProof.RetainedInsertion

-- BEGIN TCProof.MatchingInsertion
section Assembled_TCProof_MatchingInsertion

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

theorem regular_matching_increment {N : ℕ} (hN : 0 < N) (K : ℝ) (hK : 0 ≤ K)
    (L : Finset Point → ℝ) (hL : Regular K L) (x y : Fin N → Point)
    (hmatch : ∃ i, x i=y i) (k₁ : ℕ) (hk₁ : 1 ≤ k₁)
    (hkk : k₁ ≤ terminalLevel N) (t : ℝ) (ht : 0 ≤ t)
    (hcost : (∑ i, if x i=y i then 0 else sampleAlpha x (terminalLevel N) k₁ i) ≤ 128*t)
    (harea : 2*(lowCells (sampleGrid N (k₁-1) x)
      ((N:ℝ)/Fintype.card (Grid (k₁-1)))).card/Fintype.card (Grid (k₁-1)) ≤ 54*t^2/N) :
    L (sampleSet x) ≤ L (sampleSet y)+2048*K*t := by
  classical
  let J := Finset.univ.filter (fun i => x i=y i)
  have hJ : J.Nonempty := by
    obtain ⟨i,hi⟩ := hmatch
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  have hcost' : (∑ i ∈ Finset.univ \ J, sampleAlpha x (terminalLevel N) k₁ i) ≤ 128*t := by
    have he : Finset.univ \ J=Finset.univ.filter (fun i => x i ≠ y i) := by
      ext i
      simp [J]
    rw [he,Finset.sum_filter]
    simpa only [ite_not] using hcost
  have hi := regular_retained_increment hN K hK L hL x J hJ k₁ hk₁ hkk t ht hcost' harea
  have hsub : J.image x ⊆ sampleSet y := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have he := (Finset.mem_filter.mp hi).2
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩
  have hm := regular_mono_nonempty K L hL (hJ.image x) hsub
  linarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_MatchingInsertion
-- END TCProof.MatchingInsertion

-- BEGIN TCProof.PatternHull
section Assembled_TCProof_PatternHull

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

abbrev Pattern (n : ℕ) := Fin n → Bool

def bitVector {n : ℕ} (u : Pattern n) : Fin n → ℝ := fun i => if u i then 1 else 0

noncomputable def sqNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, v i ^ 2

lemma sqNorm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun i _ => sq_nonneg (v i)

lemma continuous_sqNorm (n : ℕ) : Continuous (sqNorm (n := n)) := by
  unfold sqNorm
  fun_prop

noncomputable def patternHull {n : ℕ} (U : Finset (Pattern n)) : Set (Fin n → ℝ) :=
  convexHull ℝ (bitVector '' (U : Set (Pattern n)))

lemma patternHull_compact {n : ℕ} (U : Finset (Pattern n)) : IsCompact (patternHull U) :=
  (U.finite_toSet.image bitVector).isCompact_convexHull (𝕜 := ℝ)

lemma patternHull_nonempty {n : ℕ} {U : Finset (Pattern n)} (hU : U.Nonempty) :
    (patternHull U).Nonempty := by
  obtain ⟨u, hu⟩ := hU
  exact ⟨bitVector u, subset_convexHull ℝ _ ⟨u, hu, rfl⟩⟩

lemma exists_patternMin {n : ℕ} {U : Finset (Pattern n)} (hU : U.Nonempty) :
    ∃ v ∈ patternHull U, ∀ w ∈ patternHull U, sqNorm v ≤ sqNorm w := by
  exact (patternHull_compact U).exists_isMinOn (patternHull_nonempty hU)
    (continuous_sqNorm n).continuousOn

noncomputable def patternMin {n : ℕ} (U : Finset (Pattern n)) (hU : U.Nonempty) : Fin n → ℝ :=
  Classical.choose (exists_patternMin hU)

lemma patternMin_spec {n : ℕ} (U : Finset (Pattern n)) (hU : U.Nonempty) :
    patternMin U hU ∈ patternHull U ∧
      ∀ w ∈ patternHull U, sqNorm (patternMin U hU) ≤ sqNorm w :=
  Classical.choose_spec (exists_patternMin hU)

noncomputable def patternDistance {n : ℕ} (U : Finset (Pattern n)) : ℝ :=
  if hU : U.Nonempty then sqNorm (patternMin U hU) else n

lemma patternDistance_eq {n : ℕ} {U : Finset (Pattern n)} (hU : U.Nonempty) :
    patternDistance U = sqNorm (patternMin U hU) := by simp [patternDistance, hU]

lemma patternDistance_nonneg {n : ℕ} (U : Finset (Pattern n)) : 0 ≤ patternDistance U := by
  unfold patternDistance
  split_ifs
  · exact sqNorm_nonneg _
  · positivity

lemma patternDistance_le {n : ℕ} {U : Finset (Pattern n)} (hU : U.Nonempty)
    {v : Fin n → ℝ} (hv : v ∈ patternHull U) : patternDistance U ≤ sqNorm v := by
  rw [patternDistance_eq hU]
  exact (patternMin_spec U hU).2 v hv

lemma patternDistance_antitone {n : ℕ} {U V : Finset (Pattern n)}
    (hU : U.Nonempty) (hUV : U ⊆ V) : patternDistance V ≤ patternDistance U := by
  have hV := hU.mono hUV
  rw [patternDistance_eq hU]
  apply patternDistance_le hV
  exact convexHull_mono (Set.image_mono hUV) (patternMin_spec U hU).1

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_PatternHull
-- END TCProof.PatternHull

-- BEGIN TCProof.PatternWitness
section Assembled_TCProof_PatternWitness

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

lemma patternDistance_le_dimension {n : ℕ} (U : Finset (Pattern n)) :
    patternDistance U ≤ n := by
  by_cases hU : U.Nonempty
  · have hUne := hU
    obtain ⟨u, hu⟩ := hU
    apply (patternDistance_le hUne (subset_convexHull ℝ _ ⟨u, hu, rfl⟩)).trans
    calc
      sqNorm (bitVector u) ≤ ∑ _i : Fin n, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [bitVector]
        split_ifs <;> norm_num
      _ = n := by simp
  · simp [patternDistance, hU]

lemma convex_dot_superlevel {n : ℕ} (a : Fin n → ℝ) (c : ℝ) :
    Convex ℝ {v : Fin n → ℝ | c ≤ ∑ i, a i*v i} := by
  intro x hx y hy s t hs ht hst
  change c ≤ ∑ i, a i*(s*x i+t*y i)
  have he : (∑ i, a i*(s*x i+t*y i)) = s*(∑ i,a i*x i)+t*(∑ i,a i*y i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  change c ≤ ∑ i, a i*x i at hx
  change c ≤ ∑ i, a i*y i at hy
  have hc : s*c+t*c=c := by rw [← add_mul,hst,one_mul]
  linarith [mul_le_mul_of_nonneg_left hx hs,mul_le_mul_of_nonneg_left hy ht]

lemma pattern_weight_witness {n : ℕ} {U : Finset (Pattern n)} (hU : U.Nonempty)
    (a : Fin n → ℝ) : ∃ u ∈ U,
      (∑ i, a i*bitVector u i) ≤ Real.sqrt (sqNorm a)*Real.sqrt (patternDistance U) := by
  obtain ⟨u, hu, hmin⟩ := U.exists_min_image (fun u => ∑ i, a i*bitVector u i) hU
  refine ⟨u, hu, ?_⟩
  have hh : patternHull U ⊆ {v | (∑ i,a i*bitVector u i) ≤ ∑ i,a i*v i} := by
    apply convexHull_min
    · rintro _ ⟨v,hv,rfl⟩
      exact hmin v hv
    · exact convex_dot_superlevel _ _
  have h := hh (patternMin_spec U hU).1
  apply h.trans
  rw [patternDistance_eq hU]
  exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a (patternMin U hU)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_PatternWitness
-- END TCProof.PatternWitness

-- BEGIN TCProof.MismatchPatterns
section Assembled_TCProof_MismatchPatterns

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

noncomputable def mismatchPatterns {α : Type*} {n : ℕ}
    (A : Set (Fin n → α)) (x : Fin n → α) : Finset (Pattern n) := by
  classical
  exact Finset.univ.filter fun u => ∃ y ∈ A, ∀ i, u i = false → x i = y i

lemma mem_mismatchPatterns {α : Type*} {n : ℕ} {A : Set (Fin n → α)}
    {x : Fin n → α} {u : Pattern n} :
    u ∈ mismatchPatterns A x ↔ ∃ y ∈ A, ∀ i, u i = false → x i = y i := by
  classical
  simp [mismatchPatterns]

lemma mismatchPatterns_nonempty {α : Type*} {n : ℕ} {A : Set (Fin n → α)}
    (hA : A.Nonempty) (x : Fin n → α) : (mismatchPatterns A x).Nonempty := by
  obtain ⟨y,hy⟩ := hA
  exact ⟨fun _ => true, mem_mismatchPatterns.mpr ⟨y,hy,by simp⟩⟩

lemma mismatchPatterns_mono {α : Type*} {n : ℕ} {A B : Set (Fin n → α)}
    (hAB : A ⊆ B) (x : Fin n → α) : mismatchPatterns A x ⊆ mismatchPatterns B x := by
  intro u hu
  obtain ⟨y,hy,hm⟩ := mem_mismatchPatterns.mp hu
  exact mem_mismatchPatterns.mpr ⟨y,hAB hy,hm⟩

noncomputable def convexDistanceSq {α : Type*} {n : ℕ}
    (A : Set (Fin n → α)) (x : Fin n → α) : ℝ := patternDistance (mismatchPatterns A x)

lemma convexDistanceSq_nonneg {α : Type*} {n : ℕ} (A : Set (Fin n → α)) (x : Fin n → α) :
    0 ≤ convexDistanceSq A x := patternDistance_nonneg _

lemma convexDistanceSq_le_dimension {α : Type*} {n : ℕ} (A : Set (Fin n → α)) (x : Fin n → α) :
    convexDistanceSq A x ≤ n := patternDistance_le_dimension _

lemma convexDistanceSq_zero {α : Type*} {n : ℕ} {A : Set (Fin n → α)}
    {x : Fin n → α} (hx : x ∈ A) : convexDistanceSq A x = 0 := by
  have hu : (fun _ => false) ∈ mismatchPatterns A x :=
    mem_mismatchPatterns.mpr ⟨x,hx,by simp⟩
  have hd := patternDistance_le (mismatchPatterns_nonempty ⟨x,hx⟩ x)
    (subset_convexHull ℝ _ ⟨fun _ => false,hu,rfl⟩)
  have he : sqNorm (bitVector (fun _ : Fin n => false)) = 0 := by simp [sqNorm,bitVector]
  rw [he] at hd
  exact le_antisymm hd (convexDistanceSq_nonneg _ _)

lemma convexDistance_weight_witness {α : Type*} [DecidableEq α] {n : ℕ} {A : Set (Fin n → α)}
    (hA : A.Nonempty) (x : Fin n → α) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ y ∈ A, (∑ i, if x i = y i then 0 else a i) ≤
      Real.sqrt (sqNorm a)*Real.sqrt (convexDistanceSq A x) := by
  classical
  obtain ⟨u,hu,hw⟩ := pattern_weight_witness (mismatchPatterns_nonempty hA x) a
  obtain ⟨y,hy,hm⟩ := mem_mismatchPatterns.mp hu
  refine ⟨y,hy,le_trans ?_ hw⟩
  apply Finset.sum_le_sum
  intro i _
  by_cases he : x i = y i
  · simp only [he,ite_true]
    exact mul_nonneg (ha i) (by cases h : u i <;> simp [bitVector,h])
  · have hb : u i = true := by cases h : u i <;> simp_all
    simp [he,bitVector,hb]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_MismatchPatterns
-- END TCProof.MismatchPatterns

-- BEGIN TCProof.RetainedWitness
section Assembled_TCProof_RetainedWitness

open scoped BigOperators
namespace TalagrandConc.TSP.TCFresh

lemma retained_matching_witness {X : Type*} [DecidableEq X] {N : ℕ}
    {A : Set (Fin N → X)} (hA : A.Nonempty) (x : Fin N → X)
    (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hbase : ∀ i, 1/Real.sqrt N ≤ a i) (henergy : sqNorm a ≤ 1024)
    (s : ℝ) (hs : 1 ≤ s) (hN : (1048576:ℝ)*s^2 ≤ N)
    (hd : convexDistanceSq A x ≤ 16*s^2) :
    ∃ y ∈ A, (∑ i, if x i = y i then 0 else a i) ≤ 128*s ∧ ∃ i, x i=y i := by
  obtain ⟨y,hy,hw⟩ := convexDistance_weight_witness hA x a ha
  have hs0 : 0 < s := by linarith
  have he : Real.sqrt (sqNorm a) ≤ 32 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num,by norm_num; exact henergy⟩
  have hdist : Real.sqrt (convexDistanceSq A x) ≤ 4*s := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity,by nlinarith⟩
  have hcost : (∑ i, if x i = y i then 0 else a i) ≤ 128*s := by
    have hh := mul_le_mul he hdist (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 32)
    nlinarith
  refine ⟨y,hy,hcost,?_⟩
  by_contra hn
  have hne : ∀ i, x i ≠ y i := by simpa only [not_exists] using hn
  simp only [hne,ite_false] at hcost
  have hNp : (0:ℝ) < N := by nlinarith [sq_nonneg (s-1)]
  have hsqrt := Real.sqrt_pos.mpr hNp
  have hsq := Real.sq_sqrt hNp.le
  have hsum : (N:ℝ)/Real.sqrt N ≤ ∑ i, a i := by
    calc
      _ = ∑ _i : Fin N, 1/Real.sqrt N := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hbase i)
  have hdiv := (div_le_iff₀ hsqrt).mp (hsum.trans hcost)
  have hlower : 1024*s ≤ Real.sqrt N := by
    apply (Real.le_sqrt (by positivity) hNp.le).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hlower hsqrt.le
  nlinarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_RetainedWitness
-- END TCProof.RetainedWitness

-- BEGIN TCProof.GeometryBridge
section Assembled_TCProof_GeometryBridge

open MeasureTheory
namespace TalagrandConc.TSP.TCFresh

lemma regular_geometry_bridge (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : 0 < N)
    (L : Finset Point → ℝ) (hL : Regular K L)
    (t : ℝ) (ht : 1 ≤ t) (hdim : (1048576:ℝ)*t^2 ≤ N) :
    ∃ E : Set (Fin N → Point),
      sampleLaw N E ≤ ENNReal.ofReal (2*Real.exp (-(t^2))) ∧
      ∀ x, x ∉ E → ∀ A : Set (Fin N → Point), A.Nonempty →
        convexDistanceSq A x ≤ 16*t^2 →
          ∃ y ∈ A, L (sampleSet x) ≤ L (sampleSet y)+2048*K*t := by
  classical
  let r : ℝ := (N:ℝ)/t^2
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t^2 := sq_pos_of_pos ht0
  have hr : (2:ℝ)^20 ≤ r := by
    apply (le_div_iff₀ ht2).mpr
    norm_num
    exact hdim
  have hr0 : 0 < r := by norm_num at hr; linarith
  have hrel : r*t^2=(N:ℝ) := div_mul_cancel₀ _ ht2.ne'
  let hT := logarithmic_threshold_ge_four r hr
  let k₁ := cutoffLevel N hN (128*Real.log r) hT
  have hkpos : 0 < k₁ := cutoffLevel_pos N hN (128*Real.log r) hT
    (cutoff_threshold_lt_count N t r ht hr hrel)
  have hkk : k₁ ≤ terminalLevel N := (cutoffLevel_spec N hN (128*Real.log r) hT).1
  let E := occupancyBadEvent N (k₁-1) (terminalLevel N) t
  refine ⟨E,occupancyBadEvent_bound N hN _ _ t,?_⟩
  intro x hx A hA hd
  have hscale : t^2*gridArea k₁ ≤ 128 := cutoff_energy_scale N hN t r hr0 hrel hT
  have henergy := good_event_alpha_energy hN x k₁ hkpos t ht hscale hx
  have hbase := sampleAlpha_lower hN x k₁
  obtain ⟨y,hy,hcost,hmatch⟩ := retained_matching_witness hA x
    (sampleAlpha x (terminalLevel N) k₁) (sampleAlpha_nonneg x _ k₁) hbase henergy t ht hdim hd
  refine ⟨y,hy,?_⟩
  apply regular_matching_increment hN K hK L hL x y hmatch k₁ hkpos hkk t ht0.le hcost
  exact good_coarse_low_area hN x t r ht hr hrel hx

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_GeometryBridge
-- END TCProof.GeometryBridge

-- BEGIN TCProof.CellGroups
section Assembled_TCProof_CellGroups

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

noncomputable def cellGroup (F : Finset Point) (k : ℕ) (c : Grid k) : Finset Point :=
  by classical exact F.filter (fun x => squareIndex k x=c)

theorem cellGroup_inside (F : Finset Point) (k : ℕ) (c : Grid k) :
    ∀ x ∈ cellGroup F k c, x ∈ dyadicSquare k c := by
  classical
  intro x hx
  have he := (Finset.mem_filter.mp hx).2
  rw [← he]
  exact mem_dyadicSquare_index k x

theorem biUnion_cellGroup (F : Finset Point) (k : ℕ) :
    Finset.univ.biUnion (cellGroup F k)=F := by
  classical
  ext x
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,cellGroup,Finset.mem_filter]
  exact ⟨fun ⟨_,hx,_⟩ => hx,fun hx => ⟨squareIndex k x,hx,rfl⟩⟩

theorem sum_card_cellGroup (F : Finset Point) (k : ℕ) :
    ∑ c : Grid k, (cellGroup F k c).card=F.card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise (f := squareIndex k)
    (t := Finset.univ) (s := F) (by intro x hx; exact Finset.mem_univ _)).symm

theorem sqrt_sum_cellGroup (F : Finset Point) (k : ℕ) :
    (∑ c : Grid k, Real.sqrt (cellGroup F k c).card)^2 ≤
      (Fintype.card (Grid k):ℝ)*F.card := by
  classical
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Grid k))
    (fun _ => (1:ℝ)) (fun c => Real.sqrt (cellGroup F k c).card)
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    Real.sq_sqrt (Nat.cast_nonneg _),← Nat.cast_sum,sum_card_cellGroup] using h

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CellGroups
-- END TCProof.CellGroups

-- BEGIN TCProof.GlobalInsertion
section Assembled_TCProof_GlobalInsertion

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

theorem regular_global_increment (K : ℝ) (hK : 0 ≤ K) (L : Finset Point → ℝ)
    (hL : Regular K L) (F G : Finset Point) (hF : F.Nonempty) :
    L (F ∪ G) ≤ L F+K*Real.sqrt G.card := by
  classical
  obtain ⟨x,hx⟩ := hF
  have h := regular_group_increment K L hL F Finset.univ (cellGroup G 1)
    (fun _ => 1) (fun c => c) (by intro c hc; omega)
    (by intro c hc; exact cellGroup_inside G 1 c) (by
      intro c hc
      let y : Point := fun i => cellLower 1 (c i)
      have hy : y ∈ dyadicSquare 1 c := by
        rw [dyadicSquare_eq_pi]
        intro i hi
        constructor
        · exact le_rfl
        · change (c i).val/(2:ℝ)^1 ≤ ((c i).val+1)/(2:ℝ)^1
          norm_num
          linarith
      exact ⟨x,hx,y,hy,by simpa using edist_le_two x y⟩)
  rw [biUnion_cellGroup] at h
  have hs := sqrt_sum_cellGroup G 1
  rw [grid_card] at hs
  norm_num at hs
  have hq := Real.sq_sqrt (Nat.cast_nonneg G.card)
  have hnon := Real.sqrt_nonneg (G.card:ℝ)
  have hsum : ∑ c : Grid 1, Real.sqrt (cellGroup G 1 c).card ≤ 2*Real.sqrt G.card := by
    nlinarith [sq_nonneg ((∑ c : Grid 1, Real.sqrt (cellGroup G 1 c).card)+2*Real.sqrt G.card)]
  have hcost : ∑ c : Grid 1, (2:ℝ)^(-(1:ℤ))*Real.sqrt (cellGroup G 1 c).card ≤ Real.sqrt G.card := by
    rw [← Finset.mul_sum]
    norm_num
    linarith
  have hm := mul_le_mul_of_nonneg_left hcost hK
  norm_num only [Nat.cast_one] at h
  norm_num at hm
  linarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_GlobalInsertion
-- END TCProof.GlobalInsertion

-- BEGIN TCProof.GlobalRange
section Assembled_TCProof_GlobalRange

namespace TalagrandConc.TSP.TCFresh

theorem regular_range_anchor (K : ℝ) (hK : 0 ≤ K) (L : Finset Point → ℝ)
    (hL : Regular K L) (a : Point) (F : Finset Point) (hF : F.Nonempty) :
    L {a}-K/2 ≤ L F ∧ L F ≤ L {a}+K*Real.sqrt F.card := by
  classical
  obtain ⟨x,hx⟩ := hF
  have hmono := regular_mono_nonempty K L hL (Finset.singleton_nonempty x)
    (Finset.singleton_subset_iff.mpr hx)
  have hsingle := regular_singleton_oscillation K L hL a x
  have hlower := (abs_le.mp hsingle).2
  have hupper := regular_global_increment K hK L hL {a} F (Finset.singleton_nonempty a)
  have hmono' := regular_mono_nonempty K L hL ⟨x,hx⟩
    (show F ⊆ {a} ∪ F from Finset.subset_union_right)
  exact ⟨by linarith, hmono'.trans hupper⟩

theorem regular_pair_oscillation (K : ℝ) (hK : 0 ≤ K) (L : Finset Point → ℝ)
    (hL : Regular K L) (F G : Finset Point) (hF : F.Nonempty) (hG : G.Nonempty)
    (N : ℕ) (hN : 0 < N) (hFN : F.card ≤ N) (hGN : G.card ≤ N) :
    |L F-L G| ≤ 2*K*Real.sqrt N := by
  obtain ⟨a,ha⟩ := hF
  have hf := regular_range_anchor K hK L hL a F ⟨a,ha⟩
  have hg := regular_range_anchor K hK L hL a G hG
  have hsF := Real.sqrt_le_sqrt (show (F.card:ℝ) ≤ N by exact_mod_cast hFN)
  have hsG := Real.sqrt_le_sqrt (show (G.card:ℝ) ≤ N by exact_mod_cast hGN)
  have hmF := mul_le_mul_of_nonneg_left hsF hK
  have hmG := mul_le_mul_of_nonneg_left hsG hK
  have hsN : (1:ℝ) ≤ Real.sqrt N := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by exact_mod_cast hN)
  have hmN := mul_le_mul_of_nonneg_left hsN hK
  rw [abs_le]
  constructor <;> nlinarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_GlobalRange
-- END TCProof.GlobalRange

-- BEGIN TCProof.MatchError
section Assembled_TCProof_MatchError

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

noncomputable def matchError {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (x : Fin n → X) (u : Pattern n) (y : Fin n → X) : ℝ :=
  ∑ i, if u i = false then dist (x i) (y i) else 0

lemma matchError_nonneg {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (x : Fin n → X) (u : Pattern n) (y : Fin n → X) : 0 ≤ matchError x u y := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

lemma continuous_matchError {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (x : Fin n → X) (u : Pattern n) : Continuous (matchError x u) := by
  unfold matchError
  apply continuous_finsetSum
  intro i _
  by_cases h : u i = false
  · simp only [h,ite_true]
    fun_prop
  · have ht : u i = true := Bool.eq_true_of_not_eq_false h
    simp only [ht, Bool.true_eq_false, ↓reduceIte]
    exact continuous_const

lemma matchError_zero_iff {X : Type*} [MetricSpace X] {n : ℕ}
    (x : Fin n → X) (u : Pattern n) (y : Fin n → X) :
    matchError x u y = 0 ↔ ∀ i, u i = false → x i = y i := by
  constructor
  · intro h i hi
    have hb : dist (x i) (y i) ≤ matchError x u y := by
      have hs := Finset.single_le_sum (f := fun j => if u j = false then dist (x j) (y j) else 0)
        (s := Finset.univ) (a := i) (by intro j _; split_ifs <;> positivity) (Finset.mem_univ i)
      change dist (x i) (y i) ≤ ∑ j, if u j = false then dist (x j) (y j) else 0
      simpa only [hi,ite_true] using hs
    rw [h] at hb
    exact dist_le_zero.mp hb
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · simp [h i hi]
    · rfl

lemma matchError_quantized_bound {X Y : Type*} [PseudoMetricSpace X] {n : ℕ}
    (q : X → Y) (δ : ℝ) (hδ : 0 ≤ δ)
    (hq : ∀ x y, q x=q y → dist x y ≤ δ)
    (x y : Fin n → X) (u : Pattern n) (hu : ∀ i, u i=false → q (x i)=q (y i)) :
    matchError x u y ≤ n*δ := by
  calc
    matchError x u y ≤ ∑ _i : Fin n, δ := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact hq _ _ (hu i hi)
      · exact hδ
    _ = n*δ := by simp

lemma compact_matchError_positive {X : Type*} [MetricSpace X] {n : ℕ}
    {A : Set (Fin n → X)} (hA : IsCompact A) (hne : A.Nonempty)
    (x : Fin n → X) (u : Pattern n) (hu : u ∉ mismatchPatterns A x) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ A, c ≤ matchError x u y := by
  obtain ⟨y,hy,hm⟩ := hA.exists_isMinOn hne (continuous_matchError x u).continuousOn
  refine ⟨matchError x u y,?_,hm⟩
  apply lt_of_le_of_ne (matchError_nonneg x u y)
  intro he
  apply hu
  exact mem_mismatchPatterns.mpr ⟨y,hy,(matchError_zero_iff x u y).mp he.symm⟩

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_MatchError
-- END TCProof.MatchError

-- BEGIN TCProof.CompactPatterns
section Assembled_TCProof_CompactPatterns

open Filter
open scoped Topology

namespace TalagrandConc.TSP.TCFresh

def quantizedPoint {X Y : Type*} {n : ℕ} (q : X → Y) (x : Fin n → X) : Fin n → Y :=
  fun i => q (x i)

def quantizedSet {X Y : Type*} {n : ℕ} (q : X → Y) (A : Set (Fin n → X)) :
    Set (Fin n → Y) := quantizedPoint q '' A

lemma exact_pattern_quantized {X Y : Type*} {n : ℕ} (q : X → Y)
    {A : Set (Fin n → X)} {x : Fin n → X} {u : Pattern n}
    (hu : u ∈ mismatchPatterns A x) :
    u ∈ mismatchPatterns (quantizedSet q A) (quantizedPoint q x) := by
  obtain ⟨y,hy,hm⟩ := mem_mismatchPatterns.mp hu
  exact mem_mismatchPatterns.mpr ⟨quantizedPoint q y,⟨y,hy,rfl⟩,
    fun i hi => congrArg q (hm i hi)⟩

lemma quantized_pattern_error {X Y : Type*} [PseudoMetricSpace X] {n : ℕ}
    (q : X → Y) {δ : ℝ} (hδ : 0 ≤ δ) (hq : ∀ x y, q x=q y → dist x y ≤ δ)
    {A : Set (Fin n → X)} {x : Fin n → X} {u : Pattern n}
    (hu : u ∈ mismatchPatterns (quantizedSet q A) (quantizedPoint q x)) :
    ∃ y ∈ A, matchError x u y ≤ n*δ := by
  obtain ⟨z,⟨y,hy,rfl⟩,hm⟩ := mem_mismatchPatterns.mp hu
  exact ⟨y,hy,matchError_quantized_bound q δ hδ hq x y u hm⟩

lemma compact_patterns_eventually_equal {X : Type*} [MetricSpace X] {Y : ℕ → Type*}
    {n : ℕ} {A : Set (Fin n → X)} (hA : IsCompact A) (hne : A.Nonempty)
    (q : (m : ℕ) → X → Y m) (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m)
    (hq : ∀ m x y, q m x=q m y → dist x y ≤ δ m)
    (hlim : Tendsto δ atTop (𝓝 0)) (x : Fin n → X) :
    ∀ᶠ m in atTop, mismatchPatterns (quantizedSet (q m) A) (quantizedPoint (q m) x) =
      mismatchPatterns A x := by
  classical
  have hu (u : Pattern n) : ∀ᶠ m in atTop,
      (u ∈ mismatchPatterns (quantizedSet (q m) A) (quantizedPoint (q m) x) ↔
        u ∈ mismatchPatterns A x) := by
    by_cases hex : u ∈ mismatchPatterns A x
    · exact Filter.Eventually.of_forall fun m => ⟨fun _ => hex,fun _ => exact_pattern_quantized (q m) hex⟩
    · obtain ⟨c,hc,hmin⟩ := compact_matchError_positive hA hne x u hex
      have ht : Tendsto (fun m => (n:ℝ)*δ m) atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.mul hlim
      have hev := ht.eventually_lt_const hc
      filter_upwards [hev] with m hm
      constructor
      · intro hmem
        obtain ⟨y,hy,hb⟩ := quantized_pattern_error (q m) (hδ m) (hq m) hmem
        exact False.elim ((not_lt_of_ge ((hmin y hy).trans hb)) hm)
      · exact fun he => False.elim (hex he)
  have hall : ∀ᶠ m in atTop, ∀ u : Pattern n,
      (u ∈ mismatchPatterns (quantizedSet (q m) A) (quantizedPoint (q m) x) ↔
        u ∈ mismatchPatterns A x) := Filter.eventually_all.mpr hu
  filter_upwards [hall] with m hm
  exact Finset.ext hm

lemma compact_distance_eventually_equal {X : Type*} [MetricSpace X] {Y : ℕ → Type*}
    {n : ℕ} {A : Set (Fin n → X)} (hA : IsCompact A) (hne : A.Nonempty)
    (q : (m : ℕ) → X → Y m) (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m)
    (hq : ∀ m x y, q m x=q m y → dist x y ≤ δ m)
    (hlim : Tendsto δ atTop (𝓝 0)) (x : Fin n → X) :
    ∀ᶠ m in atTop, convexDistanceSq (quantizedSet (q m) A) (quantizedPoint (q m) x) =
      convexDistanceSq A x := by
  filter_upwards [compact_patterns_eventually_equal hA hne q δ hδ hq hlim x] with m hm
  exact congrArg patternDistance hm

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CompactPatterns
-- END TCProof.CompactPatterns

-- BEGIN TCProof.SnocHull
section Assembled_TCProof_SnocHull

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

lemma snoc_real_mix {n : ℕ} (x y : Fin n → ℝ) (b s t : ℝ) (hst : s+t=1) :
    Fin.snoc (s • x+t • y) b = s • Fin.snoc x b+t • Fin.snoc y b := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun z : ℝ => z*b) hst]
  · simp

lemma bitVector_snoc {n : ℕ} (u : Pattern n) (b : Bool) :
    bitVector (Fin.snoc u b) = Fin.snoc (bitVector u) (if b then 1 else 0) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [bitVector]

lemma snoc_mem_patternHull {n : ℕ} {U : Finset (Pattern n)}
    {V : Finset (Pattern (n+1))} (b : Bool)
    (hUV : ∀ u ∈ U, Fin.snoc u b ∈ V) {v : Fin n → ℝ} (hv : v ∈ patternHull U) :
    Fin.snoc v (if b then 1 else 0) ∈ patternHull V := by
  have hc : Convex ℝ {w : Fin n → ℝ | Fin.snoc w (if b then 1 else 0) ∈ patternHull V} := by
    intro x hx y hy s t hs ht hst
    change Fin.snoc (s • x+t • y) (if b then 1 else 0) ∈ patternHull V
    rw [snoc_real_mix _ _ _ _ _ hst]
    exact (convex_convexHull ℝ _) hx hy hs ht hst
  apply (convexHull_min ?_ hc) hv
  rintro _ ⟨u,hu,rfl⟩
  change Fin.snoc (bitVector u) (if b then 1 else 0) ∈ patternHull V
  rw [← bitVector_snoc]
  exact subset_convexHull ℝ _ ⟨Fin.snoc u b,hUV u hu,rfl⟩

lemma sqNorm_snoc {n : ℕ} (v : Fin n → ℝ) (b : ℝ) :
    sqNorm (Fin.snoc v b) = sqNorm v+b^2 := by
  simp [sqNorm,Fin.sum_univ_castSucc]

lemma sqNorm_mix_le {n : ℕ} (x y : Fin n → ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1) :
    sqNorm (s • x+t • y) ≤ s*sqNorm x+t*sqNorm y := by
  simp only [sqNorm,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have he : s*(x i)^2+t*(y i)^2-(s*x i+t*y i)^2 = s*t*(x i-y i)^2 := by
    have ht' : t=1-s := by linarith
    rw [ht']
    ring
  have hpos := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x i-y i))
  linarith

lemma patternDistance_snoc_mix {n : ℕ} {U W : Finset (Pattern n)}
    {V : Finset (Pattern (n+1))} (hU : U.Nonempty) (hW : W.Nonempty)
    (h0 : ∀ u ∈ U, Fin.snoc u false ∈ V) (h1 : ∀ u ∈ W, Fin.snoc u true ∈ V)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    patternDistance V ≤ (1-t)^2+t*patternDistance U+(1-t)*patternDistance W := by
  let x := patternMin U hU
  let y := patternMin W hW
  have hx := snoc_mem_patternHull false h0 (patternMin_spec U hU).1
  have hy := snoc_mem_patternHull true h1 (patternMin_spec W hW).1
  simp only [Bool.false_eq_true,ite_false,ite_true] at hx hy
  have hv : V.Nonempty := by
    obtain ⟨u,hu⟩ := hU
    exact ⟨Fin.snoc u false,h0 u hu⟩
  have hm := (convex_convexHull ℝ (bitVector '' (V : Set (Pattern (n+1)))))
    hx hy ht (sub_nonneg.mpr ht1) (by ring)
  have he : t • Fin.snoc x 0+(1-t) • Fin.snoc y 1 = Fin.snoc (t • x+(1-t) • y) (1-t) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  change t • Fin.snoc x 0+(1-t) • Fin.snoc y 1 ∈ patternHull V at hm
  rw [he] at hm
  have hb := patternDistance_le hv hm
  rw [sqNorm_snoc] at hb
  have hc := sqNorm_mix_le x y ht (sub_nonneg.mpr ht1) (by ring)
  rw [patternDistance_eq hU,patternDistance_eq hW]
  dsimp [x,y] at hb hc
  linarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_SnocHull
-- END TCProof.SnocHull

-- BEGIN TCProof.FiberPatterns
section Assembled_TCProof_FiberPatterns

namespace TalagrandConc.TSP.TCFresh

def lastFiber {α : Type*} {n : ℕ} (A : Set (Fin (n+1) → α)) (a : α) : Set (Fin n → α) :=
  {x | Fin.snoc x a ∈ A}

def lastProjection {α : Type*} {n : ℕ} (A : Set (Fin (n+1) → α)) : Set (Fin n → α) :=
  {x | ∃ a, Fin.snoc x a ∈ A}

lemma lastFiber_subset {α : Type*} {n : ℕ} (A : Set (Fin (n+1) → α)) (a : α) :
    lastFiber A a ⊆ lastProjection A := fun _ hx => ⟨a,hx⟩

lemma lastProjection_nonempty {α : Type*} {n : ℕ} {A : Set (Fin (n+1) → α)}
    (hA : A.Nonempty) : (lastProjection A).Nonempty := by
  obtain ⟨x,hx⟩ := hA
  refine ⟨Fin.init x,x (Fin.last n),?_⟩
  simpa using hx

lemma fiber_pattern_snoc {α : Type*} {n : ℕ} {A : Set (Fin (n+1) → α)}
    (a : α) (x : Fin n → α) {u : Pattern n} (hu : u ∈ mismatchPatterns (lastFiber A a) x) :
    Fin.snoc u false ∈ mismatchPatterns A (Fin.snoc x a) := by
  obtain ⟨y,hy,hm⟩ := mem_mismatchPatterns.mp hu
  apply mem_mismatchPatterns.mpr
  refine ⟨Fin.snoc y a,hy,?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa using hm j

lemma projection_pattern_snoc {α : Type*} {n : ℕ} {A : Set (Fin (n+1) → α)}
    (a : α) (x : Fin n → α) {u : Pattern n} (hu : u ∈ mismatchPatterns (lastProjection A) x) :
    Fin.snoc u true ∈ mismatchPatterns A (Fin.snoc x a) := by
  obtain ⟨y,⟨b,hy⟩,hm⟩ := mem_mismatchPatterns.mp hu
  apply mem_mismatchPatterns.mpr
  refine ⟨Fin.snoc y b,hy,?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa using hm j

lemma convexDistanceSq_snoc_mix {α : Type*} {n : ℕ} {A : Set (Fin (n+1) → α)}
    (a : α) (x : Fin n → α) (hf : (lastFiber A a).Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    convexDistanceSq A (Fin.snoc x a) ≤ (1-t)^2+t*convexDistanceSq (lastFiber A a) x+
      (1-t)*convexDistanceSq (lastProjection A) x := by
  exact patternDistance_snoc_mix (mismatchPatterns_nonempty hf x)
    (mismatchPatterns_nonempty (hf.mono (lastFiber_subset A a)) x)
    (fun u hu => fiber_pattern_snoc a x hu) (fun u hu => projection_pattern_snoc a x hu) ht ht1

lemma convexDistanceSq_snoc_projection {α : Type*} {n : ℕ} {A : Set (Fin (n+1) → α)}
    (hA : A.Nonempty) (a : α) (x : Fin n → α) :
    convexDistanceSq A (Fin.snoc x a) ≤ 1+convexDistanceSq (lastProjection A) x := by
  let W := mismatchPatterns (lastProjection A) x
  have hW : W.Nonempty := mismatchPatterns_nonempty (lastProjection_nonempty hA) x
  have hm := snoc_mem_patternHull true (fun u hu => projection_pattern_snoc a x hu)
    (patternMin_spec W hW).1
  simp only [ite_true] at hm
  have hb := patternDistance_le (mismatchPatterns_nonempty hA (Fin.snoc x a)) hm
  rw [sqNorm_snoc,one_pow] at hb
  change patternDistance _ ≤ 1+patternDistance W
  rw [patternDistance_eq hW]
  linarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_FiberPatterns
-- END TCProof.FiberPatterns

-- BEGIN TCProof.ProductMassFiber
section Assembled_TCProof_ProductMassFiber

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

lemma productMass_empty {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ) :
    productMass p n ∅ = 0 := by
  simp [productMass,productMean,finiteMean]

lemma productMass_pos_nonempty {α : Type*} [Fintype α] {p : α → ℝ}
    {n : ℕ} {A : Set (Fin n → α)} (h : 0 < productMass p n A) : A.Nonempty := by
  by_contra hn
  have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  rw [he,productMass_empty] at h
  exact (lt_irrefl 0) h

lemma productMass_le_one {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (n : ℕ) (A : Set (Fin n → α)) :
    productMass p n A ≤ 1 := by
  classical
  calc
    productMass p n A ≤ finiteMean (productWeight p n) (fun _ => 1) := by
      apply finiteMean_mono (productWeight_nonneg hp n)
      intro x
      split_ifs <;> norm_num
    _ = 1 := finiteMean_const (productWeight_sum hs n) 1

lemma productMass_succ {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ)
    (A : Set (Fin (n+1) → α)) :
    productMass p (n+1) A = finiteMean p (fun a => productMass p n (lastFiber A a)) := by
  classical
  simp only [productMass,productMean_succ,lastFiber,Set.mem_ofPred_eq]
  rfl

lemma productMass_le_projection {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) {n : ℕ} (A : Set (Fin (n+1) → α)) :
    productMass p (n+1) A ≤ productMass p n (lastProjection A) := by
  rw [productMass_succ]
  calc
    finiteMean p (fun a => productMass p n (lastFiber A a)) ≤
        finiteMean p (fun _ => productMass p n (lastProjection A)) :=
      finiteMean_mono hp (fun a => productMass_mono hp (lastFiber_subset A a))
    _ = _ := finiteMean_const hs _

lemma productMean_const {α : Type*} [Fintype α] {p : α → ℝ}
    (hs : ∑ a, p a = 1) (n : ℕ) (c : ℝ) : productMean p n (fun _ => c) = c :=
  finiteMean_const (productWeight_sum hs n) c

lemma productMean_mul_const {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ)
    (f : (Fin n → α) → ℝ) (c : ℝ) :
    productMean p n (fun x => f x*c) = productMean p n f*c :=
  finiteMean_mul_const _ _ _

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_ProductMassFiber
-- END TCProof.ProductMassFiber

-- BEGIN TCProof.ExponentialMix
section Assembled_TCProof_ExponentialMix

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

lemma exp_mix_le (a b t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (t*a+(1-t)*b) ≤ t*Real.exp a+(1-t)*Real.exp b := by
  simpa only [smul_eq_mul] using convexOn_exp.2
    (Set.mem_univ a) (Set.mem_univ b) ht (sub_nonneg.mpr ht1) (by ring)

lemma finiteMean_exp_sub {Ω : Type*} [Fintype Ω] (w f : Ω → ℝ) (c : ℝ) :
    finiteMean w (fun a => Real.exp (f a-c)) =
      finiteMean w (fun a => Real.exp (f a)) / Real.exp c := by
  simp only [Real.exp_sub, div_eq_mul_inv]
  exact finiteMean_mul_const _ _ _

lemma finiteMean_exp_mix {Ω : Type*} [Fintype Ω] {w f g : Ω → ℝ}
    (hw : ∀ a, 0 ≤ w a) {A B t : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hf : finiteMean w (fun a => Real.exp (f a)) ≤ A)
    (hg : finiteMean w (fun a => Real.exp (g a)) ≤ B)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    finiteMean w (fun a => Real.exp (t*f a+(1-t)*g a)) ≤
      Real.exp (t*Real.log A+(1-t)*Real.log B) := by
  let c := t*Real.log A+(1-t)*Real.log B
  have hnormf : finiteMean w (fun a => Real.exp (f a-Real.log A)) ≤ 1 := by
    rw [finiteMean_exp_sub, Real.exp_log hA]
    exact (div_le_one hA).mpr hf
  have hnormg : finiteMean w (fun a => Real.exp (g a-Real.log B)) ≤ 1 := by
    rw [finiteMean_exp_sub, Real.exp_log hB]
    exact (div_le_one hB).mpr hg
  have hpoint (a : Ω) : Real.exp ((t*f a+(1-t)*g a)-c) ≤
      t*Real.exp (f a-Real.log A)+(1-t)*Real.exp (g a-Real.log B) := by
    convert exp_mix_le (f a-Real.log A) (g a-Real.log B) t ht ht1 using 1
    congr 1
    dsimp [c]
    ring
  have hm := finiteMean_mono hw hpoint
  rw [finiteMean_exp_sub] at hm
  have hid : finiteMean w (fun a => t*Real.exp (f a-Real.log A)+(1-t)*Real.exp (g a-Real.log B)) =
      t*finiteMean w (fun a => Real.exp (f a-Real.log A))+
      (1-t)*finiteMean w (fun a => Real.exp (g a-Real.log B)) := by
    simp only [finiteMean, mul_add, Finset.sum_add_distrib]
    congr 1 <;> rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [hid] at hm
  have hb : t*finiteMean w (fun a => Real.exp (f a-Real.log A))+
      (1-t)*finiteMean w (fun a => Real.exp (g a-Real.log B)) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hnormf ht,
      mul_le_mul_of_nonneg_left hnormg (sub_nonneg.mpr ht1)]
  exact (div_le_one (Real.exp_pos c)).mp (hm.trans hb)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_ExponentialMix
-- END TCProof.ExponentialMix

-- BEGIN TCProof.MixingScalar
section Assembled_TCProof_MixingScalar

namespace TalagrandConc.TSP.TCFresh

noncomputable def mixingLog (s : ℝ) : ℝ :=
  Real.log (1+s)+(1-2*s)*Real.log (1-s)-s^2

lemma mixingLog_deriv {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) (1/2)) :
    HasDerivAt mixingLog (1/(1+s)-2*Real.log (1-s)-(1-2*s)/(1-s)-2*s) s := by
  have hp : 0 < 1+s := by linarith [hs.1]
  have hm : 0 < 1-s := by linarith [hs.2]
  have h1 := ((hasDerivAt_const s (1:ℝ)).add (hasDerivAt_id s)).log hp.ne'
  have h2 := ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).log hm.ne'
  have h3 := ((hasDerivAt_const s (1:ℝ)).sub ((hasDerivAt_id s).const_mul 2)).mul h2
  apply ((h1.add h3).sub ((hasDerivAt_id s).pow 2)).congr_deriv
  dsimp
  ring

lemma mixingLog_nonneg {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) (1/2)) :
    0 ≤ mixingLog s := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/2)) := mixingLog_deriv hx
  have hc : ContinuousOn mixingLog (Set.Icc (0:ℝ) (1/2)) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hm : MonotoneOn mixingLog (Set.Icc (0:ℝ) (1/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hd x hx').deriv]
      have hpos : 0 < 1-x := by linarith [hx'.2]
      have hp : 0 < 1+x := by linarith [hx'.1]
      have hl := Real.log_le_sub_one_of_pos hpos
      have hr : 0 ≤ 1/(1+x)-(1-2*x)/(1-x) := by
        apply (sub_nonneg.mpr ?_)
        apply (div_le_div_iff₀ hpos hp).mpr
        nlinarith [sq_nonneg x]
      linarith
  have h := hm (by norm_num) hs hs.1
  simpa [mixingLog] using h

lemma exp_quarter_le : Real.exp (1/4:ℝ) ≤ 3/2 := by
  have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1/4:ℝ) < 1)
  norm_num at h ⊢
  linarith

lemma mixing_scalar {r : ℝ} (_hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      Real.exp ((1-t)^2/4-t*Real.log r) ≤ 2-r := by
  by_cases h : r ≤ 1/2
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    simp only [sub_zero, one_pow, zero_mul]
    exact exp_quarter_le.trans (by linarith)
  · have hs : 1-r ∈ Set.Icc (0:ℝ) (1/2) := ⟨by linarith, by linarith⟩
    have hm := mixingLog_nonneg hs
    have hlog : ((1-(2*r-1))^2/4-(2*r-1)*Real.log r) ≤ Real.log (2-r) := by
      dsimp [mixingLog] at hm
      have h1 : 1+(1-r)=2-r := by ring
      have h2 : 1-(1-r)=r := by ring
      rw [h1,h2] at hm
      nlinarith
    refine ⟨2*r-1, by linarith, by linarith, ?_⟩
    exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log (by linarith))

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_MixingScalar
-- END TCProof.MixingScalar

-- BEGIN TCProof.ExponentialFiber
section Assembled_TCProof_ExponentialFiber

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

lemma reciprocal_mix_identity {c b : ℝ} (hc : 0 < c) (hb : 0 < b) (t : ℝ) :
    Real.exp (t*Real.log (1/c)+(1-t)*Real.log (1/b))*Real.exp ((1-t)^2/4) =
      Real.exp ((1-t)^2/4-t*Real.log (c/b))/b := by
  calc
    _ = Real.exp (t*Real.log (1/c)+(1-t)*Real.log (1/b)+(1-t)^2/4) := (Real.exp_add _ _).symm
    _ = Real.exp ((1-t)^2/4-t*Real.log (c/b)-Real.log b) := by
      congr 1
      rw [Real.log_div hc.ne' hb.ne',one_div,one_div,Real.log_inv,Real.log_inv]
      ring
    _ = _ := by rw [Real.exp_sub,Real.exp_log hb]


lemma exponential_fiber_bound {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (n : ℕ)
    (ih : ∀ B : Set (Fin n → α), 0 < productMass p n B →
      productMean p n (fun x => Real.exp (convexDistanceSq B x/4)) ≤ 1/productMass p n B)
    (A : Set (Fin (n+1) → α)) (hA : 0 < productMass p (n+1) A) (a : α) :
    productMean p n (fun x => Real.exp (convexDistanceSq A (Fin.snoc x a)/4)) ≤
      (2-productMass p n (lastFiber A a)/productMass p n (lastProjection A))/
        productMass p n (lastProjection A) := by
  let b := productMass p n (lastProjection A)
  let c := productMass p n (lastFiber A a)
  have hb : 0 < b := lt_of_lt_of_le hA (productMass_le_projection hp hs A)
  have hc0 : 0 ≤ c := productMass_nonneg hp n _
  have hcb : c ≤ b := productMass_mono hp (lastFiber_subset A a)
  have hbase := ih (lastProjection A) hb
  have hne := productMass_pos_nonempty hA
  by_cases hc : 0 < c
  · obtain ⟨t,ht,ht1,hmix⟩ := mixing_scalar (div_pos hc hb) ((div_le_one hb).mpr hcb)
    have hf := ih (lastFiber A a) hc
    have hfn := productMass_pos_nonempty hc
    have hpoint (x : Fin n → α) : Real.exp (convexDistanceSq A (Fin.snoc x a)/4) ≤
        Real.exp (t*(convexDistanceSq (lastFiber A a) x/4)+(1-t)*(convexDistanceSq (lastProjection A) x/4))*
          Real.exp ((1-t)^2/4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hd := convexDistanceSq_snoc_mix a x hfn ht ht1
      nlinarith
    have havg := finiteMean_exp_mix (productWeight_nonneg hp n) (one_div_pos.mpr hc)
      (one_div_pos.mpr hb) hf hbase ht ht1
    calc
      productMean p n (fun x => Real.exp (convexDistanceSq A (Fin.snoc x a)/4)) ≤
          productMean p n (fun x => Real.exp (t*(convexDistanceSq (lastFiber A a) x/4)+
            (1-t)*(convexDistanceSq (lastProjection A) x/4))*Real.exp ((1-t)^2/4)) :=
        finiteMean_mono (productWeight_nonneg hp n) hpoint
      _ = productMean p n (fun x => Real.exp (t*(convexDistanceSq (lastFiber A a) x/4)+
            (1-t)*(convexDistanceSq (lastProjection A) x/4)))*Real.exp ((1-t)^2/4) :=
        productMean_mul_const _ _ _ _
      _ ≤ Real.exp (t*Real.log (1/c)+(1-t)*Real.log (1/b))*Real.exp ((1-t)^2/4) :=
        mul_le_mul_of_nonneg_right havg (Real.exp_pos _).le
      _ = Real.exp ((1-t)^2/4-t*Real.log (c/b))/b := reciprocal_mix_identity hc hb t
      _ ≤ (2-c/b)/b := div_le_div_of_nonneg_right hmix hb.le
  · have hcz : c=0 := le_antisymm (not_lt.mp hc) hc0
    have hpoint (x : Fin n → α) : Real.exp (convexDistanceSq A (Fin.snoc x a)/4) ≤
        Real.exp (convexDistanceSq (lastProjection A) x/4)*Real.exp (1/4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [convexDistanceSq_snoc_projection hne a x]
    have hm := finiteMean_mono (productWeight_nonneg hp n) hpoint
    change productMean p n _ ≤ productMean p n _ at hm
    rw [productMean_mul_const] at hm
    have he : Real.exp (1/4:ℝ) ≤ 2 := exp_quarter_le.trans (by norm_num)
    change _ ≤ (2-c/b)/b
    rw [hcz,zero_div,sub_zero]
    calc
      _ ≤ (1/b)*Real.exp (1/4) := hm.trans (mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le)
      _ ≤ (1/b)*2 := mul_le_mul_of_nonneg_left he (one_div_pos.mpr hb).le
      _ = 2/b := by ring

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_ExponentialFiber
-- END TCProof.ExponentialFiber

-- BEGIN TCProof.FiniteConcentration
section Assembled_TCProof_FiniteConcentration

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

lemma finiteMean_fiber_expression {α : Type*} [Fintype α] {p : α → ℝ}
    (hs : ∑ a, p a = 1) (c : α → ℝ) (b : ℝ) :
    finiteMean p (fun a => (2-c a/b)/b) = (2-finiteMean p c/b)/b := by
  unfold finiteMean
  calc
    _ = ∑ a, (p a*2/b-(p a*c a)/(b*b)) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (∑ a,p a)*2/b-(∑ a,p a*c a)/(b*b) := by
      simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    _ = _ := by rw [hs]; ring


lemma reciprocal_fiber_average {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (2-a/b)/b ≤ 1/a := by
  apply (div_le_div_iff₀ hb ha).mpr
  apply (mul_le_mul_iff_right₀ hb).mp
  have hba : a/b*b=a := div_mul_cancel₀ a hb.ne'
  have he : ((2-a/b)*a)*b = 2*a*b-a^2 := by
    calc
      _ = 2*a*b-a*(a/b*b) := by ring
      _ = _ := by rw [hba]; ring
  rw [mul_comm b ((2-a/b)*a), he]
  nlinarith [sq_nonneg (b-a)]

lemma finite_convex_distance_exponential {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (n : ℕ)
    (A : Set (Fin n → α)) (hA : 0 < productMass p n A) :
    productMean p n (fun x => Real.exp (convexDistanceSq A x/4)) ≤ 1/productMass p n A := by
  induction n with
  | zero =>
      have hne := productMass_pos_nonempty hA
      obtain ⟨x,hx⟩ := hne
      have he : x=Fin.elim0 := Subsingleton.elim _ _
      subst x
      have hm : productMass p 0 A=1 := by
        classical
        unfold productMass
        rw [productMean_zero]
        simp [hx]
      rw [productMean_zero,convexDistanceSq_zero hx,zero_div,Real.exp_zero,hm]
      norm_num
  | succ n ih =>
      have hb : 0 < productMass p n (lastProjection A) :=
        lt_of_lt_of_le hA (productMass_le_projection hp hs A)
      rw [productMean_succ]
      calc
        finiteMean p (fun a => productMean p n (fun x => Real.exp (convexDistanceSq A (Fin.snoc x a)/4))) ≤
            finiteMean p (fun a => (2-productMass p n (lastFiber A a)/productMass p n (lastProjection A))/
              productMass p n (lastProjection A)) :=
          finiteMean_mono hp (fun a => exponential_fiber_bound hp hs n ih A hA a)
        _ = (2-productMass p (n+1) A/productMass p n (lastProjection A))/
              productMass p n (lastProjection A) := by
          rw [finiteMean_fiber_expression hs,← productMass_succ]
        _ ≤ 1/productMass p (n+1) A := reciprocal_fiber_average hA hb

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_FiniteConcentration
-- END TCProof.FiniteConcentration

-- BEGIN TCProof.FiniteTail
section Assembled_TCProof_FiniteTail

open scoped BigOperators

namespace TalagrandConc.TSP.TCFresh

lemma finite_convex_distance_tail {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (n : ℕ)
    (A : Set (Fin n → α)) (hA : 0 < productMass p n A) (r : ℝ) :
    productMass p n {x | r ≤ convexDistanceSq A x} ≤
      Real.exp (-r/4) / productMass p n A := by
  classical
  have hmark : productMass p n {x | r ≤ convexDistanceSq A x} * Real.exp (r/4) ≤
      productMean p n (fun x => Real.exp (convexDistanceSq A x/4)) := by
    unfold productMass productMean
    rw [← finiteMean_mul_const]
    apply finiteMean_mono (productWeight_nonneg hp n)
    intro x
    split_ifs with hx
    · simp only [one_mul]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hx (by norm_num))
    · simp only [zero_mul]
      exact (Real.exp_pos _).le
  have h := hmark.trans (finite_convex_distance_exponential hp hs n A hA)
  have heq : (Real.exp (-r/4) / productMass p n A) * Real.exp (r/4) =
      1/productMass p n A := by
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    have he : -r/4+r/4=0 := by ring
    rw [he,Real.exp_zero]
  nlinarith [Real.exp_pos (r/4)]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_FiniteTail
-- END TCProof.FiniteTail

-- BEGIN TCProof.CompactTail
section Assembled_TCProof_CompactTail

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace TalagrandConc.TSP.TCFresh

lemma measure_le_of_eventually_mem {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) (S : ℕ → Set X) (c : ℝ≥0∞)
    (h : ∀ x ∈ E, ∀ᶠ m in atTop, x ∈ S m) (hb : ∀ m, μ (S m) ≤ c) :
    μ E ≤ c := by
  let T : ℕ → Set X := fun k => ⋂ m ≥ k, S m
  have hT : Monotone T := by
    intro k l hkl x hx
    simp only [T, Set.mem_iInter] at hx ⊢
    exact fun m hlm => hx m (hkl.trans hlm)
  have hsub : E ⊆ ⋃ k, T k := by
    intro x hx
    obtain ⟨k,hk⟩ := eventually_atTop.mp (h x hx)
    exact Set.mem_iUnion.mpr ⟨k,by simpa only [T,Set.mem_iInter] using hk⟩
  calc
    μ E ≤ μ (⋃ k, T k) := measure_mono hsub
    _ = ⨆ k, μ (T k) := hT.measure_iUnion
    _ ≤ c := iSup_le fun k => (measure_mono (by
      intro x hx
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hx k) le_rfl)).trans (hb k)

lemma compact_convex_distance_tail {X : Type*} [MetricSpace X] [MeasurableSpace X]
    {Y : ℕ → Type*} [∀ m, Fintype (Y m)] {n : ℕ}
    (μ : Measure (Fin n → X)) {A : Set (Fin n → X)}
    (hA : IsCompact A) (hne : A.Nonempty)
    (q : (m : ℕ) → X → Y m) (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m)
    (hq : ∀ m x y, q m x=q m y → dist x y ≤ δ m)
    (hlim : Tendsto δ atTop (𝓝 0))
    (p : (m : ℕ) → Y m → ℝ) (hp : ∀ m a, 0 ≤ p m a)
    (hs : ∀ m, ∑ a, p m a = 1)
    (hlaw : ∀ m (B : Set (Fin n → Y m)),
      μ (quantizedPoint (q m) ⁻¹' B) = ENNReal.ofReal (productMass (p m) n B))
    (a : ℝ) (ha : 0 < a) (hμA : ENNReal.ofReal a ≤ μ A) (r : ℝ) :
    μ {x | r ≤ convexDistanceSq A x} ≤ ENNReal.ofReal (Real.exp (-r/4)/a) := by
  apply measure_le_of_eventually_mem μ _
    (fun m => {x | r ≤ convexDistanceSq (quantizedSet (q m) A) (quantizedPoint (q m) x)})
  · intro x hx
    filter_upwards [compact_distance_eventually_equal hA hne q δ hδ hq hlim x] with m hm
    simpa only [Set.mem_ofPred_eq,hm] using hx
  · intro m
    have hmass : a ≤ productMass (p m) n (quantizedSet (q m) A) := by
      apply (ENNReal.ofReal_le_ofReal_iff (productMass_nonneg (hp m) n _)).mp
      apply hμA.trans
      rw [← hlaw]
      exact measure_mono (fun x hx => ⟨x,hx,rfl⟩)
    rw [show {x | r ≤ convexDistanceSq (quantizedSet (q m) A) (quantizedPoint (q m) x)} =
      quantizedPoint (q m) ⁻¹' {z | r ≤ convexDistanceSq (quantizedSet (q m) A) z} from rfl,hlaw]
    apply ENNReal.ofReal_le_ofReal
    exact (finite_convex_distance_tail (hp m) (hs m) n _ (ha.trans_le hmass) r).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le ha hmass)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_CompactTail
-- END TCProof.CompactTail

-- BEGIN TCProof.NativeCompactTail
section Assembled_TCProof_NativeCompactTail

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace TalagrandConc.TSP.TCFresh

lemma dyadicSide_tendsto : Tendsto (fun k : ℕ => (2:ℝ)^(-(k:ℤ))) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 < 1)
  simpa only [zpow_neg,zpow_natCast,inv_pow,one_div] using h

lemma native_compact_convex_tail {N : ℕ} {A : Set (Fin N → Point)}
    (hA : IsCompact A) (hne : A.Nonempty) (a : ℝ) (ha : 0 < a)
    (hμA : ENNReal.ofReal a ≤ sampleLaw N A) (r : ℝ) :
    sampleLaw N {x | r ≤ convexDistanceSq A x} ≤ ENNReal.ofReal (Real.exp (-r/4)/a) := by
  apply compact_convex_distance_tail (sampleLaw N) hA hne squareIndex
    (fun k => (2:ℝ)^(-(k:ℤ))) (fun k => (dyadicSide_pos k).le)
    (fun _ _ _ h => dist_same_squareIndex h) dyadicSide_tendsto
    (fun k _ => 1/(Fintype.card (Grid k):ℝ))
  · intro m a
    positivity
  · intro m
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hp : (Fintype.card (Grid m):ℝ) ≠ 0 := by positivity
    exact mul_one_div_cancel hp
  · exact fun m B => sampleLaw_grid_productMass N m B
  · exact ha
  · exact hμA

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_NativeCompactTail
-- END TCProof.NativeCompactTail

-- BEGIN TCProof.NativeMeasurableTail
section Assembled_TCProof_NativeMeasurableTail

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.TSP.TCFresh

instance sampleLaw_probability (N : ℕ) : IsProbabilityMeasure (sampleLaw N) := by
  unfold sampleLaw
  infer_instance

lemma convexDistanceSq_antitone {X : Type*} {N : ℕ} {A B : Set (Fin N → X)}
    (hA : A.Nonempty) (hAB : A ⊆ B) (x : Fin N → X) :
    convexDistanceSq B x ≤ convexDistanceSq A x :=
  patternDistance_antitone (mismatchPatterns_nonempty hA x) (mismatchPatterns_mono hAB x)

lemma native_measurable_convex_tail {N : ℕ} {A : Set (Fin N → Point)}
    (hA : MeasurableSet A) (a : ℝ) (ha : 0 < a)
    (hμA : ENNReal.ofReal a < sampleLaw N A) (r : ℝ) :
    sampleLaw N {x | r ≤ convexDistanceSq A x} ≤ ENNReal.ofReal (Real.exp (-r/4)/a) := by
  obtain ⟨K,hKA,hK,hμK⟩ := hA.exists_lt_isCompact_of_ne_top (measure_ne_top _ _) hμA
  have hne : K.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he,measure_empty] at hμK
    exact not_lt_of_ge (zero_le) hμK
  apply le_trans (measure_mono ?_) (native_compact_convex_tail hK hne a ha hμK.le r)
  intro x hx
  exact hx.trans (convexDistanceSq_antitone hne hKA x)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_NativeMeasurableTail
-- END TCProof.NativeMeasurableTail

-- BEGIN TCProof.MedianRange
section Assembled_TCProof_MedianRange

open MeasureTheory
open scoped ENNReal
namespace TalagrandConc.TSP.TCFresh

lemma median_range_of_pair_bound {N : ℕ} (L : Finset Point → ℝ) (M D : ℝ)
    (hM : IsMedian (N := N) L M)
    (hpair : ∀ x y : Fin N → Point, |L (sampleSet x)-L (sampleSet y)| ≤ D)
    (x : Fin N → Point) : |L (sampleSet x)-M| ≤ D := by
  have hlo : ({y : Fin N → Point | L (sampleSet y) ≤ M} : Set _).Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞) < 1/2) hM.1)
  have hhi : ({y : Fin N → Point | M ≤ L (sampleSet y)} : Set _).Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞) < 1/2) hM.2)
  obtain ⟨y,hy⟩ := hlo
  obtain ⟨z,hz⟩ := hhi
  change L (sampleSet y) ≤ M at hy
  change M ≤ L (sampleSet z) at hz
  have hl := (abs_le.mp (hpair x y)).2
  have hu := (abs_le.mp (hpair x z)).1
  rw [abs_le]
  exact ⟨by linarith,by linarith⟩

lemma regular_median_range (K : ℝ) (hK : 0 ≤ K) (L : Finset Point → ℝ)
    (hL : Regular K L) (N : ℕ) (hN : 0 < N) (M : ℝ)
    (hM : IsMedian (N := N) L M) (x : Fin N → Point) :
    |L (sampleSet x)-M| ≤ 2*K*Real.sqrt N := by
  classical
  apply median_range_of_pair_bound L M _ hM _ x
  intro y z
  have hsample (w : Fin N → Point) : (sampleSet w).Nonempty := by
    exact ⟨w ⟨0,hN⟩,Finset.mem_image.mpr ⟨⟨0,hN⟩,Finset.mem_univ _,rfl⟩⟩
  have hcard (w : Fin N → Point) : (sampleSet w).card ≤ N := by
    exact (Finset.card_image_le).trans (by simp)
  exact regular_pair_oscillation K hK L hL _ _ (hsample y) (hsample z) N hN (hcard y) (hcard z)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_MedianRange
-- END TCProof.MedianRange

-- BEGIN TCProof.SmallDimension
section Assembled_TCProof_SmallDimension

open MeasureTheory
namespace TalagrandConc.TSP.TCFresh

lemma regular_small_dimension_tail (K : ℝ) (hK : 0 ≤ K) (L : Finset Point → ℝ)
    (hL : Regular K L) (N : ℕ) (hN : 0 < N) (M : ℝ)
    (hM : IsMedian (N := N) L M) (t : ℝ) (ht : 0 ≤ t)
    (hdim : (N:ℝ) ≤ 4194304*t^2) :
    sampleLaw N {x | (4096*max 1 K)*t < |L (sampleSet x)-M|} = 0 := by
  have hs : Real.sqrt N ≤ 2048*t := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have hm : K ≤ max 1 K := le_max_right _ _
  have hbound (x : Fin N → Point) : |L (sampleSet x)-M| ≤ (4096*max 1 K)*t := by
    have h := regular_median_range K hK L hL N hN M hM x
    have hb := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*K)
    have hc := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 4096*t)
    nlinarith
  have he : {x : Fin N → Point | (4096*max 1 K)*t < |L (sampleSet x)-M|} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact not_lt_of_ge (hbound x) hx
  rw [he,measure_empty]

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_SmallDimension
-- END TCProof.SmallDimension

-- BEGIN TCProof.Separation
section Assembled_TCProof_Separation

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.TSP.TCFresh

lemma native_separated_mass_bound {N : ℕ} {A B E : Set (Fin N → Point)}
    (hA : MeasurableSet A) (a : ℝ) (ha : 0 < a)
    (hμA : ENNReal.ofReal a < sampleLaw N A) (r b : ℝ) (hb : 0 ≤ b)
    (hE : sampleLaw N E ≤ ENNReal.ofReal b)
    (hsep : ∀ x ∈ B, x ∉ E → r ≤ convexDistanceSq A x) :
    sampleLaw N B ≤ ENNReal.ofReal (b+Real.exp (-r/4)/a) := by
  have hsub : B ⊆ E ∪ {x | r ≤ convexDistanceSq A x} := by
    intro x hx
    by_cases he : x ∈ E
    · exact Or.inl he
    · exact Or.inr (hsep x hx he)
  calc
    sampleLaw N B ≤ sampleLaw N (E ∪ {x | r ≤ convexDistanceSq A x}) := measure_mono hsub
    _ ≤ sampleLaw N E + sampleLaw N {x | r ≤ convexDistanceSq A x} := measure_union_le _ _
    _ ≤ ENNReal.ofReal b + ENNReal.ofReal (Real.exp (-r/4)/a) :=
      add_le_add hE (native_measurable_convex_tail hA a ha hμA r)
    _ = _ := (ENNReal.ofReal_add hb (by positivity)).symm

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_Separation
-- END TCProof.Separation

-- BEGIN TCProof.MedianScalar
section Assembled_TCProof_MedianScalar
namespace TalagrandConc.TSP.TCFresh

lemma median_tail_scalar (t : ℝ) (ht : 1 ≤ t) :
    8*Real.exp (-(16*t^2))+2*Real.exp (-(4*t^2)) ≤
      4*Real.exp (-(t^2)) := by
  have hx : 1 ≤ t^2 := by nlinarith
  have h3 : 4 ≤ Real.exp (3*t^2) := by
    linarith [Real.add_one_le_exp (3*t^2)]
  have hprod : Real.exp (3*t^2)*Real.exp (-(4*t^2)) = Real.exp (-(t^2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfour : 4*Real.exp (-(4*t^2)) ≤ Real.exp (-(t^2)) := by
    rw [← hprod]
    exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  have h16 : Real.exp (-(16*t^2)) ≤ Real.exp (-(4*t^2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg t]
  nlinarith [Real.exp_pos (-(4*t^2))]

lemma median_bad_scalar (t : ℝ) (ht : 1 ≤ t) :
    2*Real.exp (-(4*t^2)) < 1/4 := by
  have hx : 1 ≤ t^2 := by nlinarith
  have h2 : 3 ≤ Real.exp (2*t^2) := by
    linarith [Real.add_one_le_exp (2*t^2)]
  have hprod : Real.exp (4*t^2) = Real.exp (2*t^2)^2 := by
    calc
      _ = Real.exp (2*t^2)*Real.exp (2*t^2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = _ := (pow_two _).symm
  have h4 : 9 ≤ Real.exp (4*t^2) := by rw [hprod]; nlinarith
  have hinv : Real.exp (4*t^2)*Real.exp (-(4*t^2)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hmul : 9*Real.exp (-(4*t^2)) ≤ 1 := by
    rw [← hinv]
    exact mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
  linarith

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_MedianScalar
-- END TCProof.MedianScalar

-- BEGIN TCProof.MedianAssembly
section Assembled_TCProof_MedianAssembly

open MeasureTheory
namespace TalagrandConc.TSP.TCFresh

lemma median_single_scale {N : ℕ} (f : (Fin N → Point) → ℝ)
    (hf : Measurable f) (M D r b : ℝ) (E : Set (Fin N → Point))
    (hb : 0 ≤ b) (hbsmall : b < 1/4)
    (hE : sampleLaw N E ≤ ENNReal.ofReal b)
    (hmedlo : (1/2 : ENNReal) ≤ sampleLaw N {x | f x ≤ M})
    (hmedhi : (1/2 : ENNReal) ≤ sampleLaw N {x | M ≤ f x})
    (hgeom : ∀ x, x ∉ E → ∀ A : Set (Fin N → Point), A.Nonempty →
      convexDistanceSq A x ≤ r → ∃ y ∈ A, f x ≤ f y+D) :
    sampleLaw N {x | M+D < f x} ≤ ENNReal.ofReal (b+4*Real.exp (-r/4)) ∧
    sampleLaw N {x | f x < M-D} ≤ ENNReal.ofReal (4*Real.exp (-r/4)) := by
  have hquarter : (ENNReal.ofReal (1/4 : ℝ)) < (1/2 : ENNReal) := by
    have hh : ENNReal.ofReal (1/4 : ℝ) < ENNReal.ofReal (1/2 : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
    simpa using hh
  have hne {A : Set (Fin N → Point)} {a : ℝ}
      (hm : ENNReal.ofReal a < sampleLaw N A) : A.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty] at hm
    exact not_lt_of_ge zero_le hm
  constructor
  · have hmass := hquarter.trans_le hmedlo
    have hbound := native_separated_mass_bound
      (A := {x | f x ≤ M}) (B := {x | M+D < f x}) (E := E)
      (measurableSet_le hf measurable_const) (1/4) (by norm_num)
      hmass r b hb hE (by
        intro x hx hxE
        by_contra hd
        have hd' : convexDistanceSq {x | f x ≤ M} x ≤ r := (lt_of_not_ge hd).le
        obtain ⟨y,hy,hxy⟩ := hgeom x hxE _ (hne hmass) hd'
        change f y ≤ M at hy
        change M+D < f x at hx
        linarith)
    convert hbound using 1
    congr 1
    ring
  · by_contra hnot
    have hmass : ENNReal.ofReal (4*Real.exp (-r/4)) <
        sampleLaw N {x | f x < M-D} := lt_of_not_ge hnot
    have hbound := native_separated_mass_bound
      (A := {x | f x < M-D}) (B := {x | M ≤ f x}) (E := E)
      (measurableSet_lt hf measurable_const) (4*Real.exp (-r/4)) (by positivity)
      hmass r b hb hE (by
        intro x hx hxE
        by_contra hd
        have hd' : convexDistanceSq {x | f x < M-D} x ≤ r := (lt_of_not_ge hd).le
        obtain ⟨y,hy,hxy⟩ := hgeom x hxE _ (hne hmass) hd'
        change f y < M-D at hy
        change M ≤ f x at hx
        linarith)
    have heq : Real.exp (-r/4)/(4*Real.exp (-r/4)) = 1/4 := by
      field_simp
    rw [heq] at hbound
    have hlt : ENNReal.ofReal (b+1/4) < (1/2 : ENNReal) := by
      have hh : ENNReal.ofReal (b+1/4) < ENNReal.ofReal (1/2 : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by linarith)
      simpa using hh
    exact (not_lt_of_ge hmedhi) (hbound.trans_lt hlt)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_MedianAssembly
-- END TCProof.MedianAssembly

-- BEGIN TCProof.TailRescale
section Assembled_TCProof_TailRescale

open MeasureTheory
namespace TalagrandConc.TSP.TCFresh

lemma closed_tail_rescale {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (M A : ℝ)
    (hA : 1 ≤ A)
    (h : ∀ s : ℝ, 1 ≤ s → μ {x | A*s < |f x-M|} ≤
      ENNReal.ofReal (4 * Real.exp (-(s^2)))) :
    ∀ t : ℝ, 0 ≤ t → μ {x | t ≤ |f x-M|} ≤
      ENNReal.ofReal ((8*A^2)*Real.exp (-(t^2)/(8*A^2))) := by
  intro t ht
  have hAp : 0 < A := by linarith
  have hA2 : 1 ≤ A^2 := by nlinarith
  have hden : 0 < 8*A^2 := by positivity
  by_cases hlarge : 2*A ≤ t
  · have hs : 1 ≤ t/(2*A) := (le_div_iff₀ (by positivity)).2 (by linarith)
    have heq : A*(t/(2*A)) = t/2 := by field_simp
    have hsub : {x | t ≤ |f x-M|} ⊆ {x | A*(t/(2*A)) < |f x-M|} := by
      intro x hx
      change t ≤ |f x-M| at hx
      change A*(t/(2*A)) < |f x-M|
      rw [heq]
      linarith
    apply (measure_mono hsub).trans ((h _ hs).trans (ENNReal.ofReal_le_ofReal ?_))
    have hexp : -(t/(2*A))^2 ≤ -(t^2)/(8*A^2) := by
      field_simp
      nlinarith [sq_nonneg t]
    calc
      4*Real.exp (-(t/(2*A))^2) ≤ 4*Real.exp (-(t^2)/(8*A^2)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
      _ ≤ (8*A^2)*Real.exp (-(t^2)/(8*A^2)) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le
  · have hsmall : t < 2*A := lt_of_not_ge hlarge
    have hsq : t^2 ≤ 4*A^2 := by nlinarith
    have hratio : t^2/(8*A^2) ≤ 1/2 :=
      (div_le_iff₀ hden).2 (by nlinarith)
    have he : 1/2 ≤ Real.exp (-(t^2)/(8*A^2)) := by
      have hb := Real.add_one_le_exp (-(t^2)/(8*A^2))
      rw [neg_div] at hb ⊢
      linarith
    have hone : (1:ℝ) ≤ (8*A^2)*Real.exp (-(t^2)/(8*A^2)) := by
      nlinarith
    calc
      μ {x | t ≤ |f x-M|} ≤ 1 := by
        calc
          _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal ((8*A^2)*Real.exp (-(t^2)/(8*A^2))) := by
        exact_mod_cast ENNReal.ofReal_le_ofReal hone

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_TailRescale
-- END TCProof.TailRescale

-- BEGIN TCProof.BridgeAssembly
section Assembled_TCProof_BridgeAssembly

open MeasureTheory
namespace TalagrandConc.TSP.TCFresh

lemma regular_tail_from_bridge (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : 0 < N)
    (L : Finset Point → ℝ) (hL : Regular K L)
    (hf : Measurable (fun x : Fin N → Point => L (sampleSet x)))
    (M : ℝ) (hM : IsMedian (N := N) L M)
    (hbridge : ∀ s : ℝ, 1 ≤ s → (1048576:ℝ)*s^2 ≤ N →
      ∃ E : Set (Fin N → Point),
        sampleLaw N E ≤ ENNReal.ofReal (2*Real.exp (-(s^2))) ∧
        ∀ x, x ∉ E → ∀ A : Set (Fin N → Point), A.Nonempty →
          convexDistanceSq A x ≤ 16*s^2 →
            ∃ y ∈ A, L (sampleSet x) ≤ L (sampleSet y)+2048*K*s) :
    ∀ t : ℝ, 1 ≤ t →
      sampleLaw N {x | (4096*max 1 K)*t < |L (sampleSet x)-M|} ≤
        ENNReal.ofReal (4*Real.exp (-(t^2))) := by
  intro t ht
  have ht0 : 0 ≤ t := by linarith
  by_cases hsmall : (N:ℝ) ≤ 4194304*t^2
  · rw [regular_small_dimension_tail K hK L hL N hN M hM t ht0 hsmall]
    exact zero_le
  · have hdim : (1048576:ℝ)*(2*t)^2 ≤ N := by nlinarith
    obtain ⟨E,hE,hgeom⟩ := hbridge (2*t) (by linarith) hdim
    have hb : 2*Real.exp (-((2*t)^2)) < 1/4 := by
      convert median_bad_scalar t ht using 1
      congr 2
      ring
    have h := median_single_scale (fun x : Fin N → Point => L (sampleSet x)) hf
      M (2048*K*(2*t)) (16*(2*t)^2) (2*Real.exp (-((2*t)^2))) E
      (by positivity) hb hE hM.1 hM.2 hgeom
    have hsub : {x : Fin N → Point | (4096*max 1 K)*t < |L (sampleSet x)-M|} ⊆
        {x | M+2048*K*(2*t) < L (sampleSet x)} ∪
        {x | L (sampleSet x) < M-2048*K*(2*t)} := by
      intro x hx
      have hbnd : 2048*K*(2*t) ≤ (4096*max 1 K)*t := by
        have hh := mul_le_mul_of_nonneg_right (le_max_right 1 K) ht0
        nlinarith
      have ha := lt_of_le_of_lt hbnd hx
      rcases lt_abs.mp ha with hp | hn
      · exact Or.inl (by change M+2048*K*(2*t) < L (sampleSet x); linarith)
      · exact Or.inr (by change L (sampleSet x) < M-2048*K*(2*t); linarith)
    calc
      _ ≤ sampleLaw N ({x | M+2048*K*(2*t) < L (sampleSet x)} ∪
          {x | L (sampleSet x) < M-2048*K*(2*t)}) := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (2*Real.exp (-((2*t)^2))+4*Real.exp (-(16*(2*t)^2)/4)) +
          ENNReal.ofReal (4*Real.exp (-(16*(2*t)^2)/4)) := add_le_add h.1 h.2
      _ = ENNReal.ofReal (8*Real.exp (-(16*t^2))+2*Real.exp (-(4*t^2))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have he : -(16*(2*t)^2)/4=-(16*t^2) := by ring
        have he' : -((2*t)^2)=-(4*t^2) := by ring
        rw [he,he']
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (median_tail_scalar t ht)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_BridgeAssembly
-- END TCProof.BridgeAssembly

-- BEGIN TCProof.ClosedAssembly
section Assembled_TCProof_ClosedAssembly

open MeasureTheory
namespace TalagrandConc.TSP.TCFresh

lemma regular_closed_tail_from_bridge (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : 0 < N)
    (L : Finset Point → ℝ) (hL : Regular K L)
    (hf : Measurable (fun x : Fin N → Point => L (sampleSet x)))
    (M : ℝ) (hM : IsMedian (N := N) L M)
    (hbridge : ∀ s : ℝ, 1 ≤ s → (1048576:ℝ)*s^2 ≤ N →
      ∃ E : Set (Fin N → Point),
        sampleLaw N E ≤ ENNReal.ofReal (2*Real.exp (-(s^2))) ∧
        ∀ x, x ∉ E → ∀ A : Set (Fin N → Point), A.Nonempty →
          convexDistanceSq A x ≤ 16*s^2 →
            ∃ y ∈ A, L (sampleSet x) ≤ L (sampleSet y)+2048*K*s) :
    ∀ t : ℝ, 0 ≤ t →
      sampleLaw N {x | t ≤ |L (sampleSet x)-M|} ≤
        ENNReal.ofReal ((8*(4096*max 1 K)^2)*Real.exp (-(t^2)/(8*(4096*max 1 K)^2))) := by
  have hA : 1 ≤ 4096*max 1 K := by
    have h := le_max_left (1:ℝ) K
    linarith
  exact closed_tail_rescale (sampleLaw N) (fun x : Fin N → Point => L (sampleSet x))
    M (4096*max 1 K) hA (regular_tail_from_bridge K hK N hN L hL hf M hM hbridge)

end TalagrandConc.TSP.TCFresh
end Assembled_TCProof_ClosedAssembly
-- END TCProof.ClosedAssembly

-- BEGIN TCProof.NativeProof
section Assembled_TCProof_NativeProof

namespace TalagrandConc.TSP

open MeasureTheory

/-- Talagrand (1995), Theorem 11.2.2, p. 175. The constant is uniform in
the sample size and the functional, for each fixed regularity constant. -/
theorem gaussian_concentration (K₀ : ℝ) (hK₀ : 0 < K₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (_ : 0 < N) (L : Finset Point → ℝ),
      Regular K₀ L → Measurable (fun x : Fin N → Point => L (sampleSet x)) →
      ∀ (M : ℝ), IsMedian (N := N) L M → ∀ (t : ℝ), 0 ≤ t →
        sampleLaw N {x | t ≤ |L (sampleSet x) - M|} ≤
          ENNReal.ofReal (K * Real.exp (-(t ^ 2) / K)) := by
  refine ⟨8*(4096*max 1 K₀)^2, by positivity, ?_⟩
  intro N hN L hL hf M hM t ht
  exact TCFresh.regular_closed_tail_from_bridge K₀ hK₀.le N hN L hL hf M hM
    (fun s hs hdim => TCFresh.regular_geometry_bridge K₀ hK₀.le N hN L hL s hs hdim) t ht

end TalagrandConc.TSP
end Assembled_TCProof_NativeProof
-- END TCProof.NativeProof


open TalagrandConc.TSP

open MeasureTheory

/-- Talagrand (1995), Theorem 11.2.2, p. 175. The constant is uniform in
the sample size and the functional, for each fixed regularity constant. -/
theorem solution (K₀ : ℝ) (hK₀ : 0 < K₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (_ : 0 < N) (L : Finset Point → ℝ),
      Regular K₀ L → Measurable (fun x : Fin N → Point => L (sampleSet x)) →
      ∀ (M : ℝ), IsMedian (N := N) L M → ∀ (t : ℝ), 0 ≤ t →
        sampleLaw N {x | t ≤ |L (sampleSet x) - M|} ≤
          ENNReal.ofReal (K * Real.exp (-(t ^ 2) / K)) := by
  exact TalagrandConc.TSP.gaussian_concentration K₀ hK₀


