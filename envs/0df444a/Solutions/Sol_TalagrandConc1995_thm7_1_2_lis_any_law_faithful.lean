-- Prove2me | solution 1 for TalagrandConc1995.thm7_1_2_lis_any_law_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:21:07.811959+00:00
-- url     : https://prove2.me/submissions/af02991b-555b-40f2-8d2f-66c5395b660a

-- Complete checked reconstruction of the full native longest-increasing-subsequence concentration theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_TalagrandConc_ConvexHull_Basic
import Definitions.Def_TalagrandConc_Subsequences_Basic
import Mathlib


-- Begin FiniteQuadrature
section ModuleScope_FiniteQuadrature

open MeasureTheory Set
open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

lemma finite_quadrature {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : J → Ω → ℝ)
    (hf : ∀ j,Integrable (f j) μ) (G : Set Ω) (hG : ∀ᵐ x ∂μ,x∈G)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : Type) (_ : Fintype K) (p : K → ℝ) (v : K → Ω),
      (∀ k,0 ≤ p k) ∧ (∑ k,p k)=1 ∧ (∀ k,v k∈G) ∧
      ∀ j,|(∑ k,p k*f j (v k)) - ∫ x,f j x ∂μ| < ε := by
  classical
  let F : Ω → J → ℝ := fun x j => f j x
  let S : Set (J → ℝ) := F '' G
  have hfi : Integrable F μ := integrable_pi_iff.mpr hf
  have hm : (∫ x,F x ∂μ) ∈ closure (convexHull ℝ S) := by
    apply (convex_convexHull ℝ S).closure.integral_mem isClosed_closure _ hfi
    filter_upwards [hG] with x hx
    exact subset_closure (subset_convexHull ℝ S ⟨x,hx,rfl⟩)
  obtain ⟨z,hz,hclose⟩ := Metric.mem_closure_iff.mp hm ε hε
  obtain ⟨K,hK,p,a,hp0,hp1,ha,he⟩ := mem_convexHull_iff_exists_fintype.mp hz
  have hval : ∀ k,∃ v∈G,F v=a k := ha
  choose v hv heq using hval
  refine ⟨K,hK,p,v,hp0,hp1,hv,?_⟩
  intro j
  have hj := norm_le_pi_norm ( (∫ x,F x ∂μ)-z) j
  have hzj : z j=∑ k,p k*f j (v k) := by
    rw [← he]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [← heq k]
  have hfj : (∫ x,F x ∂μ) j=∫ x,f j x ∂μ := eval_integral hf j
  rw [dist_eq_norm] at hclose
  have hlt := hj.trans_lt hclose
  simpa only [Pi.sub_apply,hfj,hzj,Real.norm_eq_abs,abs_sub_comm] using hlt

end TalagrandConc.Subsequences.Proof
end ModuleScope_FiniteQuadrature
-- End FiniteQuadrature

-- Begin FiniteLaw
section ModuleScope_FiniteLaw

open Set
open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

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

end TalagrandConc.Subsequences.Proof
end ModuleScope_FiniteLaw
-- End FiniteLaw

-- Begin Canonical
section ModuleScope_Canonical

open MeasureTheory
open scoped ENNReal
end ModuleScope_Canonical
-- End Canonical

-- Begin MaskSetting
section ModuleScope_MaskSetting

namespace TalagrandConc.Subsequences.Proof

def maskSet {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) : Set (Fin N → ℝ) :=
  {s | (∀ i, s i = 0 ∨ s i = 1) ∧ ∃ y ∈ A, ∀ i, s i = 0 → x i = y i}

def maskHull {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) : Set (Fin N → ℝ) :=
  convexHull ℝ (maskSet A x)

end TalagrandConc.Subsequences.Proof
end ModuleScope_MaskSetting
-- End MaskSetting

-- Begin FiniteDistance
section ModuleScope_FiniteDistance

open Set
open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

noncomputable def sqNorm {N : ℕ} (s : Fin N → ℝ) : ℝ := ∑ i,s i^2
lemma sqNorm_nonneg {N : ℕ} (s : Fin N → ℝ) : 0 ≤ sqNorm s := Finset.sum_nonneg (fun i _ => sq_nonneg (s i))
lemma continuous_sqNorm (N : ℕ) : Continuous (sqNorm (N := N)) := by unfold sqNorm; fun_prop

lemma masks_finite {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) :
    (maskSet A x).Finite := by
  classical
  let f : (Fin N → Bool) → (Fin N → ℝ) := fun b i => if b i then 1 else 0
  apply (Set.finite_range f).subset
  intro s hs
  refine ⟨fun i => decide (s i=1),?_⟩
  funext i
  rcases hs.1 i with hi | hi <;> simp [f,hi]

lemma masks_nonempty {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    (maskSet A x).Nonempty := by
  obtain ⟨y,hy⟩ := hA
  refine ⟨fun _ => 1,?_,y,hy,?_⟩
  · intro i; exact Or.inr rfl
  · intro i hi; norm_num at hi

lemma hull_compact {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) :
    IsCompact (maskHull A x) := (masks_finite A x).isCompact_convexHull ℝ

lemma hull_nonempty {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    (maskHull A x).Nonempty := (masks_nonempty hA x).mono (subset_convexHull ℝ _)

lemma exists_min_mask {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    ∃ s ∈ maskHull A x, ∀ t ∈ maskHull A x,sqNorm s ≤ sqNorm t :=
  (hull_compact A x).exists_isMinOn (hull_nonempty hA x) (continuous_sqNorm N).continuousOn

noncomputable def minMask {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) : Fin N → ℝ :=
  by
    classical
    exact if hA : A.Nonempty then Classical.choose (exists_min_mask hA x) else 0

noncomputable def distSq {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) : ℝ := sqNorm (minMask A x)

lemma minMask_mem {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    minMask A x ∈ maskHull A x := by
  rw [minMask,dif_pos hA]
  exact (Classical.choose_spec (exists_min_mask hA x)).1

lemma distSq_le {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K)
    {s : Fin N → ℝ} (hs : s ∈ maskHull A x) : distSq A x ≤ sqNorm s := by
  rw [distSq,minMask,dif_pos hA]
  exact (Classical.choose_spec (exists_min_mask hA x)).2 s hs

lemma distSq_nonneg {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) : 0 ≤ distSq A x :=
  sqNorm_nonneg _

lemma sqNorm_cons {N : ℕ} (a : ℝ) (s : Fin N → ℝ) : sqNorm (Fin.cons a s)=a^2+sqNorm s := by
  simp [sqNorm,Fin.sum_univ_succ]

lemma distSq_zero_dim {K : Type*} (A : Set (Fin 0 → K)) (x : Fin 0 → K) : distSq A x=0 := by
  simp [distSq,sqNorm]

end TalagrandConc.Subsequences.Proof
end ModuleScope_FiniteDistance
-- End FiniteDistance

-- Begin DistanceLift
section ModuleScope_DistanceLift

open Set
open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

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
    {s : Fin N → ℝ} (hs : s ∈ maskSet (fiber A z) x) :
    liftMask 0 s ∈ maskSet A (Fin.cons z x) := by
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
    {s : Fin N → ℝ} (hs : s ∈ maskSet (projection A) x) :
    liftMask 1 s ∈ maskSet A (Fin.cons z x) := by
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
    (h : ∀ s ∈ maskSet B x,liftMask b s ∈ maskSet A (Fin.cons z x))
    {s : Fin N → ℝ} (hs : s ∈ maskHull B x) :
    liftMask b s ∈ maskHull A (Fin.cons z x) := by
  have hi : liftMask b '' maskSet B x ⊆ maskSet A (Fin.cons z x) := by
    rintro _ ⟨s,hs,rfl⟩; exact h s hs
  apply convexHull_mono hi
  rw [← AffineMap.image_convexHull]
  exact ⟨s,hs,rfl⟩

lemma distSq_projection {K : Type*} {N : ℕ} {A : Set (Fin (N+1) → K)} (hA : A.Nonempty)
    (x : Fin N → K) (z : K) : distSq A (Fin.cons z x) ≤ 1+distSq (projection A) x := by
  have hm := lift_hull (fun s hs => lift_projection_mask A x z hs) (minMask_mem (projection_nonempty hA) x)
  have hd := distSq_le hA (Fin.cons z x) hm
  simpa only [liftMask,AffineMap.coe_mk,sqNorm_cons,one_pow,distSq] using hd

end TalagrandConc.Subsequences.Proof
end ModuleScope_DistanceLift
-- End DistanceLift

-- Begin FiniteProduct
section ModuleScope_FiniteProduct

open Set
open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

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

end TalagrandConc.Subsequences.Proof
end ModuleScope_FiniteProduct
-- End FiniteProduct

-- Begin FinitePairLaw
section ModuleScope_FinitePairLaw

open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

lemma pair_weight_sum {H K : Type*} [Fintype H] [Fintype K] (a : H → ℝ) (b : K → ℝ)
    (ha : ∑ h,a h=1) (hb : ∑ k,b k=1) : (∑ z : H×K,a z.1*b z.2)=1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum,hb,mul_one]
  exact ha

lemma finiteExpect_pair_snd {H K : Type*} [Fintype H] [Fintype K]
    (a : H → ℝ) (b : K → ℝ) (ha : ∑ h,a h=1) (N : ℕ)
    (f : (Fin N → K) → ℝ) :
    finiteExpect (fun z : H×K => a z.1*b z.2) (fun x => f (fun i => (x i).2))=
      finiteExpect b f := by
  induction N with
  | zero =>
    simp only [finiteExpect,configWeight,Fin.prod_univ_zero,one_mul,Fintype.sum_unique]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ N ih =>
    rw [finiteExpect_succ,finiteExpect_succ,Fintype.sum_prod_type]
    have he (z : H×K) :
        finiteExpect (fun z : H×K => a z.1*b z.2)
          (fun x : Fin N → H×K => f (fun i => ((Fin.cons z x : Fin (N+1) → H×K) i).2))=
        finiteExpect b (fun y => f (Fin.cons z.2 y)) := by
      convert ih (fun y => f (Fin.cons z.2 y)) using 1
      congr 1
      funext x
      congr 1
      funext i
      refine Fin.cases rfl (fun j => rfl) i
    simp_rw [he]
    calc
      _ = ∑ h,a h*(∑ k,b k*finiteExpect b (fun y => f (Fin.cons k y))) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [← Finset.sum_mul,ha,one_mul]

lemma finiteExpect_pair_cons {Ω H K : Type*} [Fintype H] [Fintype K]
    (a : H → ℝ) (b : K → ℝ) (ha : ∑ h,a h=1) (hb : ∑ k,b k=1)
    {N : ℕ} (v : H → Ω) (w : Fin N → K → Ω) (f : (Fin (N+1) → Ω) → ℝ) :
    finiteExpect (fun z : H×K => a z.1*b z.2)
      (fun x => f (Fin.cons (v (x 0).1) (fun i => w i (x i.succ).2)))=
      ∑ h,a h*finiteExpect b (fun x => f (Fin.cons (v h) (fun i => w i (x i)))) := by
  rw [finiteExpect_succ,Fintype.sum_prod_type]
  simp only [Fin.cons_zero,Fin.cons_succ]
  have hs (h : H) := finiteExpect_pair_snd a b ha N
    (fun y => f (Fin.cons (v h) (fun i => w i (y i))))
  simp only at hs
  simp_rw [hs]
  apply Finset.sum_congr rfl
  intro h _
  calc
    _ = a h*(∑ k,b k)*finiteExpect b (fun x => f (Fin.cons (v h) (fun i => w i (x i)))) := by
      rw [Finset.mul_sum,Finset.sum_mul]
    _ = _ := by rw [hb,mul_one]

end TalagrandConc.Subsequences.Proof
end ModuleScope_FinitePairLaw
-- End FinitePairLaw

-- Begin ProductSlices
section ModuleScope_ProductSlices

open MeasureTheory
namespace TalagrandConc.Subsequences.Proof

lemma integrable_cons {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Fin (N+1) → Measure Ω) [∀ i,IsProbabilityMeasure (μ i)]
    {f : (Fin (N+1) → Ω) → ℝ} (hf : Integrable f (Measure.pi μ)) :
    Integrable (fun z : Ω×(Fin N → Ω) => f (Fin.cons z.1 z.2))
      ((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
  have hm := (measurePreserving_piFinSuccAbove μ 0).symm
  have hh := hm.integrable_comp_of_integrable hf
  simpa [Function.comp_def,MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv,Fin.insertNth_zero,Fin.zero_succAbove] using hh

lemma integral_cons {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Fin (N+1) → Measure Ω) [∀ i,IsProbabilityMeasure (μ i)]
    {f : (Fin (N+1) → Ω) → ℝ} (hf : Integrable f (Measure.pi μ)) :
    (∫ x,f x ∂Measure.pi μ)=
      ∫ a,∫ y,f (Fin.cons a y) ∂Measure.pi (fun i => μ i.succ) ∂μ 0 := by
  have hm := (measurePreserving_piFinSuccAbove μ 0).symm
  have he := hm.integral_comp' f
  have he' : (∫ z : Ω×(Fin N → Ω),f (Fin.cons z.1 z.2)
      ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))))=∫ x,f x ∂Measure.pi μ := by
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
      Fin.insertNth_zero,Fin.zero_succAbove] using he
  rw [← he',integral_prod _ (integrable_cons μ hf)]

end TalagrandConc.Subsequences.Proof
end ModuleScope_ProductSlices
-- End ProductSlices

-- Begin ProductQuadrature
section ModuleScope_ProductQuadrature

open MeasureTheory Set
open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

lemma weighted_error {H : Type*} [Fintype H] (a f g : H → ℝ)
    (ha0 : ∀ h,0 ≤ a h) (ha : ∑ h,a h=1) {ε : ℝ}
    (he : ∀ h,|f h-g h| ≤ ε) : |(∑ h,a h*f h)-(∑ h,a h*g h)| ≤ ε := by
  calc
    _ = |∑ h,a h*(f h-g h)| := by congr 1; simp only [mul_sub,Finset.sum_sub_distrib]
    _ ≤ ∑ h,|a h*(f h-g h)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ h,a h*|f h-g h| := by simp_rw [abs_mul,abs_of_nonneg (ha0 _)]
    _ ≤ ∑ h,a h*ε := Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (he h) (ha0 h))
    _ = ε := by rw [← Finset.sum_mul,ha,one_mul]

lemma product_quadrature {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) :
    ∀ (μ : Fin N → Measure Ω) [∀ i,IsProbabilityMeasure (μ i)]
      {J : Type*} [Fintype J] (f : J → (Fin N → Ω) → ℝ),
      (∀ j,Integrable (f j) (Measure.pi μ)) →
      ∀ ε : ℝ,0 < ε →
      ∃ (K : Type) (_ : Fintype K) (p : K → ℝ) (v : Fin N → K → Ω),
        (∀ k,0 ≤ p k) ∧ (∑ k,p k)=1 ∧
        ∀ j,|finiteExpect p (fun x => f j (fun i => v i (x i)))-∫ x,f j x ∂Measure.pi μ| < ε := by
  classical
  induction N with
  | zero =>
    intro μ _ J _ f hf ε hε
    refine ⟨PUnit,inferInstance,fun _ => 1,fun i => Fin.elim0 i,fun _ => zero_le_one,by simp,?_⟩
    intro j
    have he : f j=fun _ => f j (fun i => Fin.elim0 i) := by
      funext x
      congr 1
      funext i
      exact Fin.elim0 i
    rw [he]
    simpa [finiteExpect,configWeight] using hε
  | succ N ih =>
    intro μ _ J _ f hf ε hε
    let ν := Measure.pi (fun i : Fin N => μ i.succ)
    let g : J → Ω → ℝ := fun j a => ∫ y,f j (Fin.cons a y) ∂ν
    let G : Set Ω := {a | ∀ j,Integrable (fun y => f j (Fin.cons a y)) ν}
    have hprod (j : J) := integrable_cons μ (hf j)
    have hg : ∀ j,Integrable (g j) (μ 0) := fun j => (hprod j).integral_prod_left
    have hG : ∀ᵐ a ∂μ 0,a∈G := by
      exact ae_all_iff.mpr (fun j => (hprod j).prod_right_ae)
    obtain ⟨H,hH,a,v,ha0,ha,hv,hhead⟩ := finite_quadrature (μ 0) g hg G hG (ε/2) (by linarith)
    let F : H×J → (Fin N → Ω) → ℝ := fun z y => f z.2 (Fin.cons (v z.1) y)
    have hF : ∀ z,Integrable (F z) ν := fun z => hv z.1 z.2
    obtain ⟨K,hK,b,w,hb0,hb,htail⟩ := ih (fun i => μ i.succ) F hF (ε/2) (by linarith)
    let V : Fin (N+1) → (H×K) → Ω := fun i => Fin.cases (fun z => v z.1) (fun j z => w j z.2) i
    refine ⟨H×K,inferInstance,fun z => a z.1*b z.2,V,
      fun z => mul_nonneg (ha0 z.1) (hb0 z.2),pair_weight_sum a b ha hb,?_⟩
    intro j
    have he : finiteExpect (fun z : H×K => a z.1*b z.2) (fun x => f j (fun i => V i (x i)))=
        ∑ h,a h*finiteExpect b (fun y => f j (Fin.cons (v h) (fun i => w i (y i)))) := by
      have hid (x : Fin (N+1) → H×K) : (fun i => V i (x i))=
          Fin.cons (v (x 0).1) (fun i => w i (x i.succ).2) := by
        funext i
        refine Fin.cases rfl (fun i => rfl) i
      simp_rw [hid]
      exact finiteExpect_pair_cons a b ha hb v w (f j)
    rw [he,integral_cons μ (hf j)]
    have herr := weighted_error a
      (fun h => finiteExpect b (fun y => f j (Fin.cons (v h) (fun i => w i (y i)))) )
      (fun h => g j (v h)) ha0 ha (fun h => (htail (h,j)).le)
    have hh := hhead j
    have ht := abs_add_le ((∑ h,a h*finiteExpect b
      (fun y => f j (Fin.cons (v h) (fun i => w i (y i)))))-(∑ h,a h*g j (v h)))
      ((∑ h,a h*g j (v h))-∫ x,g j x ∂μ 0)
    simp only [sub_add_sub_cancel] at ht
    exact ht.trans_lt (by linarith)

end TalagrandConc.Subsequences.Proof
end ModuleScope_ProductQuadrature
-- End ProductQuadrature

-- Begin TwoEventTransfer
section ModuleScope_TwoEventTransfer

namespace TalagrandConc.Subsequences.Proof
open MeasureTheory

lemma two_event_product_transfer {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Fin N → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : Set (Fin N → Ω)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (C : ℝ)
    (hfinite : ∀ (K : Type) [Fintype K] (p : K → ℝ), (∀ k, 0 ≤ p k) →
      (∑ k, p k) = 1 → ∀ v : Fin N → K → Ω,
      finiteMass p {x | (fun i => v i (x i)) ∈ A} *
        finiteMass p {x | (fun i => v i (x i)) ∈ B} ≤ C) :
    (Measure.pi μ).real A * (Measure.pi μ).real B ≤ C := by
  classical
  let P := Measure.pi μ
  let f : Fin 2 → (Fin N → Ω) → ℝ :=
    ![A.indicator (fun _ => 1), B.indicator (fun _ => 1)]
  have hf : ∀ j, Integrable (f j) P := by
    intro j
    fin_cases j
    · exact (integrable_const 1).indicator hA
    · exact (integrable_const 1).indicator hB
  have hIA : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂P) = P.real A := by
    rw [integral_indicator hA]; simp
  have hIB : (∫ x, B.indicator (fun _ => (1 : ℝ)) x ∂P) = P.real B := by
    rw [integral_indicator hB]; simp
  by_contra hn
  have hpos : 0 < (P.real A * P.real B - C) / 4 := by
    have := lt_of_not_ge hn
    dsimp [P] at *
    linarith
  let ε := (P.real A * P.real B - C) / 4
  obtain ⟨K, hK, p, v, hp0, hp, herr⟩ := product_quadrature N μ f hf ε hpos
  let a := finiteMass p {x | (fun i => v i (x i)) ∈ A}
  let b := finiteMass p {x | (fun i => v i (x i)) ∈ B}
  have ha : |a - P.real A| < ε := by
    have he := herr 0
    change |finiteExpect p (fun x => A.indicator (fun _ => 1) (fun i => v i (x i))) -
      ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂P| < ε at he
    rw [hIA] at he
    simpa only [a, finiteMass, finiteExpect, Set.indicator, Set.mem_ofPred_eq] using he
  have hb : |b - P.real B| < ε := by
    have he := herr 1
    change |finiteExpect p (fun x => B.indicator (fun _ => 1) (fun i => v i (x i))) -
      ∫ x, B.indicator (fun _ => (1 : ℝ)) x ∂P| < ε at he
    rw [hIB] at he
    simpa only [b, finiteMass, finiteExpect, Set.indicator, Set.mem_ofPred_eq] using he
  have ha0 : 0 ≤ a := finiteMass_nonneg hp0 _
  have ha1 : a ≤ 1 := finiteMass_le_one hp0 hp _
  have hB0 : 0 ≤ P.real B := measureReal_nonneg
  have hB1 : P.real B ≤ 1 := measureReal_le_one
  have h1 : (P.real A - a) * P.real B ≤ ε := by
    calc
      _ ≤ ε * P.real B := mul_le_mul_of_nonneg_right (by linarith [(abs_lt.mp ha).1]) hB0
      _ ≤ ε := mul_le_of_le_one_right hpos.le hB1
  have h2 : a * (P.real B - b) ≤ ε := by
    calc
      _ ≤ a * ε := mul_le_mul_of_nonneg_left (by linarith [(abs_lt.mp hb).1]) ha0
      _ ≤ ε := mul_le_of_le_one_left hpos.le ha1
  have hbound : a * b ≤ C := hfinite K p hp0 hp v
  dsimp [ε] at h1 h2
  nlinarith

end TalagrandConc.Subsequences.Proof
end ModuleScope_TwoEventTransfer
-- End TwoEventTransfer

-- Begin ConfigurationTransfer
section ModuleScope_ConfigurationTransfer

namespace TalagrandConc.Subsequences.Proof

lemma configuration_comp {Ω K : Type*} {N : ℕ} {L : (Fin N → Ω) → ℕ}
    (hL : IsConfigurationFunction L) (v : Fin N → K → Ω) :
    IsConfigurationFunction (fun x : Fin N → K => L (fun i => v i (x i))) := by
  classical
  intro x
  obtain ⟨J, hJ, hcert⟩ := hL (fun i => v i (x i))
  refine ⟨J, hJ, fun y => ?_⟩
  apply le_trans _ (hcert (fun i => v i (y i)))
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, congrArg (v i) he⟩

end TalagrandConc.Subsequences.Proof
end ModuleScope_ConfigurationTransfer
-- End ConfigurationTransfer

-- Begin ConfigurationDistance
section ModuleScope_ConfigurationDistance

open scoped BigOperators
open Classical
namespace TalagrandConc.Subsequences.Proof

lemma configuration_mask_bound {K : Type*} {N : ℕ} (L : (Fin N → K) → ℕ)
    (x : Fin N → K) (J : Finset (Fin N)) (hJ : J.card = L x)
    (hcert : ∀ y, (J.filter (fun i => y i=x i)).card ≤ L y)
    (a : ℝ) {s : Fin N → ℝ} (hs : s ∈ maskSet {y | (L y:ℝ)≤a} x) :
    (L x:ℝ)-a ≤ ∑ i ∈ J,s i := by
  classical
  obtain ⟨hs,y,hy,he⟩ := hs
  change (L y:ℝ) ≤ a at hy
  have hi : ∀ i ∈ J, (1:ℝ) ≤ (if y i=x i then 1 else 0)+s i := by
    intro i _
    rcases hs i with h | h
    · have hxy := (he i h).symm
      simp [h,hxy]
    · by_cases hxy : y i=x i <;> simp [h,hxy]
  have hh := Finset.sum_le_sum hi
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Finset.sum_filter, Finset.sum_const] at hh
  have hc : ((J.filter (fun i => y i=x i)).card:ℝ) ≤ (L y:ℝ) := by
    exact_mod_cast hcert y
  rw [hJ] at hh
  linarith

lemma configuration_hull_bound {K : Type*} {N : ℕ} (L : (Fin N → K) → ℕ)
    (x : Fin N → K) (J : Finset (Fin N)) (hJ : J.card = L x)
    (hcert : ∀ y, (J.filter (fun i => y i=x i)).card ≤ L y)
    (a : ℝ) {s : Fin N → ℝ} (hs : s ∈ maskHull {y | (L y:ℝ)≤a} x) :
    (L x:ℝ)-a ≤ ∑ i ∈ J,s i := by
  let f : (Fin N → ℝ) → ℝ := fun s => ∑ i ∈ J,s i
  have hf : IsLinearMap ℝ f := by
    constructor
    · intro s t; simp [f,Finset.sum_add_distrib]
    · intro c s; simp [f,Finset.mul_sum]
  exact convexHull_min (fun s hs => configuration_mask_bound L x J hJ hcert a hs)
    (convex_halfSpace_ge hf _) hs

lemma configuration_distance_bound {K : Type*} {N : ℕ} (L : (Fin N → K) → ℕ)
    (hL : IsConfigurationFunction L) (a b : ℝ) (ha : 0≤a) (hab : a<b)
    (hA : ({y | (L y:ℝ)≤a} : Set (Fin N → K)).Nonempty)
    (x : Fin N → K) (hx : b≤(L x:ℝ)) :
    (b-a)^2/b ≤ distSq {y | (L y:ℝ)≤a} x := by
  classical
  obtain ⟨J,hJ,hcert⟩ := hL x
  let s := minMask {y | (L y:ℝ)≤a} x
  have hh := configuration_hull_bound L x J hJ hcert a (minMask_mem hA x)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1:ℝ)) s
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,hJ] at hc
  have hs : (∑ i ∈ J,(s i)^2) ≤ distSq {y | (L y:ℝ)≤a} x := by
    exact Finset.sum_le_univ_sum_of_nonneg (fun i => sq_nonneg (s i))
  have hl : 0 ≤ (L x:ℝ) := Nat.cast_nonneg _
  have hb : 0<b := lt_of_le_of_lt ha hab
  have hp : 0<(L x:ℝ) := lt_of_lt_of_le hb hx
  have hsq : ((L x:ℝ)-a)^2 ≤ (L x:ℝ)*distSq {y | (L y:ℝ)≤a} x := by
    have hmul := mul_le_mul_of_nonneg_left hs hl
    have hh' : (L x:ℝ)-a ≤ ∑ i ∈ J,s i := hh
    nlinarith
  have halg : (L x:ℝ)*(b-a)^2 ≤ b*((L x:ℝ)-a)^2 := by
    have h1 : 0 ≤ ((L x:ℝ)-b)*((L x:ℝ)*b-a^2) :=
      mul_nonneg (sub_nonneg.mpr hx) (by nlinarith)
    nlinarith
  apply (div_le_iff₀ hb).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq hb.le]

end TalagrandConc.Subsequences.Proof
end ModuleScope_ConfigurationDistance
-- End ConfigurationDistance

-- Begin DistanceInterpolation
section ModuleScope_DistanceInterpolation

open Set
open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

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
  have hm : a • liftMask 0 s+(1-a) • liftMask 1 t ∈ maskHull A (Fin.cons z x) :=
    (convex_convexHull ℝ _) hs ht ha (sub_nonneg.mpr ha1) (by ring)
  exact (distSq_le hA (Fin.cons z x) hm).trans (sqNorm_interpolate s t ha ha1)

end TalagrandConc.Subsequences.Proof
end ModuleScope_DistanceInterpolation
-- End DistanceInterpolation

-- Begin FiniteHolder
section ModuleScope_FiniteHolder

open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

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

end TalagrandConc.Subsequences.Proof
end ModuleScope_FiniteHolder
-- End FiniteHolder

-- Begin ScalarInterpolation
section ModuleScope_ScalarInterpolation

open Set
namespace TalagrandConc.Subsequences.Proof

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

end TalagrandConc.Subsequences.Proof
end ModuleScope_ScalarInterpolation
-- End ScalarInterpolation

-- Begin DistanceConditional
section ModuleScope_DistanceConditional

open Set
open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

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

end TalagrandConc.Subsequences.Proof
end ModuleScope_DistanceConditional
-- End DistanceConditional

-- Begin DistanceInduction
section ModuleScope_DistanceInduction

open Set
open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

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

end TalagrandConc.Subsequences.Proof
end ModuleScope_DistanceInduction
-- End DistanceInduction

-- Begin DistanceTail
section ModuleScope_DistanceTail

open Set
open scoped BigOperators
namespace TalagrandConc.Subsequences.Proof

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

end TalagrandConc.Subsequences.Proof
end ModuleScope_DistanceTail
-- End DistanceTail

-- Begin FiniteConfigurationProduct
section ModuleScope_FiniteConfigurationProduct

namespace TalagrandConc.Subsequences.Proof
open scoped BigOperators

lemma finite_configuration_product {K : Type*} [Fintype K] {N : ℕ}
    (p : K → ℝ) (hp0 : ∀ k,0≤p k) (hp : ∑ k,p k=1)
    (L : (Fin N → K) → ℕ) (hL : IsConfigurationFunction L)
    (a b : ℝ) (ha : 0≤a) (hab : a<b) :
    finiteMass p {x | (L x:ℝ)≤a} * finiteMass p {x | b≤(L x:ℝ)} ≤
      Real.exp (-((b-a)^2/(4*b))) := by
  by_cases hA : 0 < finiteMass p {x | (L x:ℝ)≤a}
  · have hb : 0<b := lt_of_le_of_lt ha hab
    have he : ((b-a)/Real.sqrt b)^2=(b-a)^2/b := by
      rw [div_pow,Real.sq_sqrt hb.le]
    have hsub : {x | b≤(L x:ℝ)} ⊆
        {x | ((b-a)/Real.sqrt b)^2≤distSq {y | (L y:ℝ)≤a} x} := by
      intro x hx
      rw [he]
      exact configuration_distance_bound L hL a b ha hab (finiteMass_pos_nonempty hA) x hx
    have h := finite_distance_product p hp0 hp N {x | (L x:ℝ)≤a} ((b-a)/Real.sqrt b)
    have hc := mul_le_mul_of_nonneg_left (finiteMass_mono hp0 hsub) hA.le
    have he2 : -(((b-a)/Real.sqrt b)^2/4) = -((b-a)^2/(4*b)) := by
      rw [he]
      ring
    rw [he2] at h
    exact hc.trans h
  · have hz : finiteMass p {x | (L x:ℝ)≤a}=0 :=
      le_antisymm (le_of_not_gt hA) (finiteMass_nonneg hp0 _)
    rw [hz,zero_mul]
    exact (Real.exp_pos _).le

end TalagrandConc.Subsequences.Proof
end ModuleScope_FiniteConfigurationProduct
-- End FiniteConfigurationProduct

-- Begin NativeProduct
section ModuleScope_NativeProduct

namespace TalagrandConc.Subsequences.Proof
open MeasureTheory

lemma configuration_product {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Fin N → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (L : (Fin N → Ω) → ℕ) (hL : IsConfigurationFunction L) (hm : Measurable L)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    (Measure.pi μ).real {x | (L x : ℝ) ≤ a} *
      (Measure.pi μ).real {x | b ≤ (L x : ℝ)} ≤
        Real.exp (-((b-a)^2/(4*b))) := by
  have hmR : Measurable (fun x => (L x : ℝ)) := (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hm
  apply two_event_product_transfer μ _ _
    (measurableSet_le hmR measurable_const)
    (measurableSet_le measurable_const hmR)
  intro K _ p hp0 hp v
  exact finite_configuration_product p hp0 hp (fun x => L (fun i => v i (x i)))
    (configuration_comp hL v) a b ha hab

end TalagrandConc.Subsequences.Proof
end ModuleScope_NativeProduct
-- End NativeProduct

-- Begin MedianTails
section ModuleScope_MedianTails

namespace TalagrandConc.Subsequences.Proof
open MeasureTheory

lemma median_configuration_tails {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : ∀ x, 0 ≤ Z x)
    (hprod : ∀ a b : ℝ, 0 ≤ a → a < b →
      P.real {x | Z x ≤ a} * P.real {x | b ≤ Z x} ≤ Real.exp (-((b-a)^2/(4*b))))
    (M : ℝ) (hM : TalagrandConc.BinPacking.IsMedian P Z M)
    (u : ℝ) (hu : 0 < u) :
    P {x | M + u ≤ Z x} ≤ ENNReal.ofReal (2 * Real.exp (-(u^2/(4*(M+u))))) ∧
      P {x | Z x ≤ M-u} ≤ ENNReal.ofReal (2 * Real.exp (-(u^2/(4*M)))) := by
  have hmlo : (1/2 : ℝ) ≤ P.real {x | Z x ≤ M} := by
    have hh := ENNReal.toReal_mono (measure_ne_top P _) hM.1
    norm_num at hh ⊢
    exact hh
  have hmhi : (1/2 : ℝ) ≤ P.real {x | M ≤ Z x} := by
    have hh := ENNReal.toReal_mono (measure_ne_top P _) hM.2
    norm_num at hh ⊢
    exact hh
  have hM0 : 0 ≤ M := by
    by_contra hn
    have he : {x | Z x ≤ M} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hn ((hZ x).trans hx)
    rw [he, measureReal_empty] at hmlo
    norm_num at hmlo
  constructor
  · have h := hprod M (M+u) hM0 (by linarith)
    have he : M+u-M = u := by ring
    rw [he] at h
    have hn := measureReal_nonneg (μ := P) (s := {x | M+u ≤ Z x})
    have hb : P.real {x | M+u ≤ Z x} ≤ 2 * Real.exp (-(u^2/(4*(M+u)))) := by
      nlinarith
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal hb
  · by_cases ha : 0 ≤ M-u
    · have h := hprod (M-u) M ha (by linarith)
      have he : M-(M-u) = u := by ring
      rw [he] at h
      have hn := measureReal_nonneg (μ := P) (s := {x | Z x ≤ M-u})
      have hb : P.real {x | Z x ≤ M-u} ≤ 2 * Real.exp (-(u^2/(4*M))) := by
        nlinarith
      rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
      exact ENNReal.ofReal_le_ofReal hb
    · have he : {x | Z x ≤ M-u} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        exact ha ((hZ x).trans hx)
      rw [he, measure_empty]
      exact bot_le

end TalagrandConc.Subsequences.Proof
end ModuleScope_MedianTails
-- End MedianTails

-- Begin LISBasic
section ModuleScope_LISBasic

namespace TalagrandConc.Subsequences.Proof

lemma admissible_le {α : Type*} [LinearOrder α] {N p : ℕ} {x : Fin N → α}
    (h : ∃ i : Fin p → Fin N, StrictMono i ∧ Monotone (x ∘ i)) : p ≤ N := by
  obtain ⟨i,hi,_⟩ := h
  simpa using Fintype.card_le_of_injective i hi.injective

lemma admissible_bdd {α : Type*} [LinearOrder α] {N : ℕ} (x : Fin N → α) :
    BddAbove {p : ℕ | ∃ i : Fin p → Fin N, StrictMono i ∧ Monotone (x ∘ i)} :=
  ⟨N,fun _ h => admissible_le h⟩

lemma lis_attained {α : Type*} [LinearOrder α] {N : ℕ} (x : Fin N → α) :
    ∃ i : Fin (lis x) → Fin N, StrictMono i ∧ Monotone (x ∘ i) := by
  apply Nat.sSup_mem _ (admissible_bdd x)
  exact ⟨0,Fin.elim0,by intro i; exact Fin.elim0 i,by intro i; exact Fin.elim0 i⟩

lemma le_lis_of_witness {α : Type*} [LinearOrder α] {N p : ℕ} {x : Fin N → α}
    (h : ∃ i : Fin p → Fin N, StrictMono i ∧ Monotone (x ∘ i)) : p ≤ lis x :=
  le_csSup (admissible_bdd x) h

lemma lis_le {α : Type*} [LinearOrder α] {N : ℕ} (x : Fin N → α) : lis x ≤ N :=
  admissible_le (lis_attained x)

lemma card_le_lis {α : Type*} [LinearOrder α] {N : ℕ} (x : Fin N → α)
    (J : Finset (Fin N)) (hJ : MonotoneOn x (J : Set (Fin N))) : J.card ≤ lis x := by
  apply le_lis_of_witness
  refine ⟨J.orderEmbOfFin rfl,(J.orderEmbOfFin rfl).strictMono,?_⟩
  intro i j hij
  exact hJ (J.orderEmbOfFin_mem rfl i) (J.orderEmbOfFin_mem rfl j)
    ((J.orderEmbOfFin rfl).monotone hij)

lemma lis_configuration {α : Type*} [LinearOrder α] {N : ℕ} :
    IsConfigurationFunction (lis : (Fin N → α) → ℕ) := by
  classical
  intro x
  obtain ⟨i,hi,hx⟩ := lis_attained x
  let J := Finset.univ.image i
  have hJ : J.card = lis x := by simp [J,Finset.card_image_of_injective _ hi.injective]
  refine ⟨J,hJ,fun y => card_le_lis y _ ?_⟩
  intro a ha b hb hab
  have ha' : a ∈ J ∧ y a = x a := by simpa only [Finset.mem_coe, Finset.mem_filter] using ha
  obtain ⟨ha,hya⟩ := ha'
  have hb' : b ∈ J ∧ y b = x b := by simpa only [Finset.mem_coe, Finset.mem_filter] using hb
  obtain ⟨hb,hyb⟩ := hb'
  obtain ⟨a',_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b',_,rfl⟩ := Finset.mem_image.mp hb
  rw [hya,hyb]
  exact hx (hi.le_iff_le.mp hab)

lemma le_lis_iff {α : Type*} [LinearOrder α] {N p : ℕ} (x : Fin N → α) :
    p ≤ lis x ↔ ∃ i : Fin p → Fin N, StrictMono i ∧ Monotone (x ∘ i) := by
  constructor
  · intro hp
    obtain ⟨i,hi,hx⟩ := lis_attained x
    let e : Fin p → Fin (lis x) := fun j => ⟨j.val,lt_of_lt_of_le j.isLt hp⟩
    have he : StrictMono e := by intro a b hab; exact hab
    exact ⟨i ∘ e,hi.comp he,hx.comp he.monotone⟩
  · exact le_lis_of_witness

end TalagrandConc.Subsequences.Proof
end ModuleScope_LISBasic
-- End LISBasic

-- Begin LISMeasurable
section ModuleScope_LISMeasurable

open MeasureTheory Set
namespace TalagrandConc.Subsequences.Proof

lemma measurable_lis {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] {N : ℕ} :
    Measurable (lis : (Fin N → α) → ℕ) := by
  apply measurable_of_Ici
  intro p
  have he : (lis : (Fin N → α) → ℕ) ⁻¹' Ici p =
      ⋃ i : Fin p → Fin N, ⋃ (_ : StrictMono i),
        ⋂ a : Fin p, ⋂ b : Fin p, ⋂ (_ : a ≤ b), {x | x (i a) ≤ x (i b)} := by
    ext x
    simp only [mem_preimage, mem_Ici, le_lis_iff, mem_iUnion, mem_iInter, mem_ofPred_eq]
    simp only [Monotone, Function.comp_apply, exists_prop]
  rw [he]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      MeasurableSet.iInter fun _ => measurableSet_le (measurable_pi_apply (i a))
        (measurable_pi_apply (i b))

end TalagrandConc.Subsequences.Proof
end ModuleScope_LISMeasurable
-- End LISMeasurable

-- Begin RootAssembly
section ModuleScope_RootAssembly

namespace TalagrandConc.Subsequences
open MeasureTheory

/-- Talagrand (1995), Theorem 7.1.2, for an arbitrary law `μ` on `[0,1]`. -/
theorem lis_concentration_anyLaw {N : ℕ} (μ : Measure unitInterval) [IsProbabilityMeasure μ] (M : ℝ)
    (hM : TalagrandConc.BinPacking.IsMedian (Measure.pi fun _ : Fin N => μ) (fun x => (lis x : ℝ)) M)
    (u : ℝ) (hu : 0 < u) :
    (Measure.pi fun _ : Fin N => μ) {x | M + u ≤ (lis x : ℝ)} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (4 * (M + u))))) ∧
      (Measure.pi fun _ : Fin N => μ) {x | (lis x : ℝ) ≤ M - u} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (4 * M)))) := by
  apply Proof.median_configuration_tails (Measure.pi fun _ : Fin N => μ)
    (fun x => (lis x : ℝ)) (fun _ => Nat.cast_nonneg _) ?_ M hM u hu
  intro a b ha hab
  exact Proof.configuration_product (fun _ : Fin N => μ) lis Proof.lis_configuration
    Proof.measurable_lis a b ha hab

end TalagrandConc.Subsequences
end ModuleScope_RootAssembly
-- End RootAssembly

-- Begin Solution
open MeasureTheory
open scoped ENNReal

theorem solution {N : ℕ} (μ : Measure unitInterval)
    [IsProbabilityMeasure μ] (M : ℝ)
    (hM : TalagrandConc.BinPacking.IsMedian (Measure.pi fun _ : Fin N => μ)
      (fun x => (TalagrandConc.Subsequences.lis x : ℝ)) M)
    (u : ℝ) (hu : 0 < u) :
    (Measure.pi fun _ : Fin N => μ) {x | M + u ≤ (TalagrandConc.Subsequences.lis x : ℝ)} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (4 * (M + u))))) ∧
      (Measure.pi fun _ : Fin N => μ) {x | (TalagrandConc.Subsequences.lis x : ℝ) ≤ M - u} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (4 * M)))) :=
  TalagrandConc.Subsequences.lis_concentration_anyLaw μ M hM u hu
